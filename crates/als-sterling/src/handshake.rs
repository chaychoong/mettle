//! The `Sec-WebSocket-Accept` derivation, hand-rolled (RFC 6455 §1.3).
//!
//! **Why this is ours and the framing is not.** RFC 6455's *framing* layer —
//! masking, fragmentation, interleaved control frames, the close handshake,
//! incremental UTF-8 validation — is where a WebSocket implementation actually
//! goes wrong, and that stays [`tungstenite`]'s job. Its *handshake* is one
//! fixed line of arithmetic: concatenate the client's key with a constant GUID,
//! SHA-1 it, base64 it, echo it back. Taking `tungstenite`'s `handshake`
//! feature for that alone pulled eleven crates (`http`, `httparse`,
//! `data-encoding`, `sha1` and its `digest`/`block-buffer`/`crypto-common`/
//! `const-oid`/`cpufeatures`/`hybrid-array`/`typenum` tail) into a workspace
//! that hand-writes its own CDCL solver — a trade this project's dependency bar
//! (STYLE P1/P2) does not clear.
//!
//! **This SHA-1 is not a security primitive** and must never be used as one.
//! RFC 6455 is explicit that the echo exists to prove the server understood the
//! WebSocket protocol, not to authenticate anything: the "secret" is sent in
//! plaintext in the same request. Nothing here is timing-sensitive, nothing
//! here resists collisions, and nothing else in mettle hashes anything.
//!
//! The implementation is FIPS 180-4 §6.1.2 read straight down, pinned below by
//! the standard's own vectors *and* by RFC 6455 §1.3's worked example — so the
//! hash core is checked independently of the end-to-end handshake, not only
//! through it.

/// The constant every WebSocket server concatenates onto the client's key
/// before hashing (RFC 6455 §1.3). Not a secret; it is printed in the RFC.
const WEBSOCKET_GUID: &str = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";

/// The `Sec-WebSocket-Accept` value for a client's `Sec-WebSocket-Key`.
///
/// The key is echoed as received — a server does not validate that it decodes
/// to 16 bytes, and RFC 6455 does not ask it to.
#[must_use]
pub(crate) fn derive_accept_key(request_key: &str) -> String {
    let mut input = String::with_capacity(request_key.len() + WEBSOCKET_GUID.len());
    input.push_str(request_key);
    input.push_str(WEBSOCKET_GUID);
    base64(&sha1(input.as_bytes()))
}

/// SHA-1 (FIPS 180-4 §6.1.2), returning the 20-byte digest.
#[allow(
    clippy::many_single_char_names,
    reason = "a, b, c, d, e, f, h, k and w are FIPS 180-4's own names for these \
              quantities; renaming them would make the code harder to check \
              against the standard, not easier to read (STYLE M1: faithful to \
              the specification being implemented)"
)]
fn sha1(message: &[u8]) -> [u8; 20] {
    // §5.3.1 initial hash value.
    let mut h: [u32; 5] = [
        0x6745_2301,
        0xEFCD_AB89,
        0x98BA_DCFE,
        0x1032_5476,
        0xC3D2_E1F0,
    ];

    // §5.1.1 padding: a `1` bit, then zeroes, then the length in bits as a
    // 64-bit big-endian integer, to a multiple of 64 bytes. Saturating rather
    // than wrapping on the length: mettle hashes ~60-byte handshake keys, and a
    // 2^61-byte message would be a wrong digest rather than a wrapped one.
    let bit_len = u64::try_from(message.len())
        .unwrap_or(u64::MAX)
        .saturating_mul(8);
    let mut padded = Vec::with_capacity(message.len() + 72);
    padded.extend_from_slice(message);
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for block in padded.chunks_exact(64) {
        // §6.1.2 step 1: the message schedule. The first sixteen words are the
        // block itself; `zip` stops there because a 64-byte block has exactly
        // sixteen 4-byte groups.
        let mut w = [0u32; 80];
        for (word, bytes) in w.iter_mut().zip(block.chunks_exact(4)) {
            *word = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }

        // §6.1.2 steps 2-3: eighty rounds over the working variables.
        let [mut a, mut b, mut c, mut d, mut e] = h;
        for (round, word) in w.iter().enumerate() {
            let (f, k) = match round {
                0..=19 => ((b & c) | (!b & d), 0x5A82_7999),
                20..=39 => (b ^ c ^ d, 0x6ED9_EBA1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1B_BCDC),
                _ => (b ^ c ^ d, 0xCA62_C1D6),
            };
            let t = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(*word);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = t;
        }

        // §6.1.2 step 4: the intermediate hash value.
        for (slot, value) in h.iter_mut().zip([a, b, c, d, e]) {
            *slot = slot.wrapping_add(value);
        }
    }

    let mut digest = [0u8; 20];
    for (out, word) in digest.chunks_exact_mut(4).zip(h) {
        out.copy_from_slice(&word.to_be_bytes());
    }
    digest
}

/// The standard base64 alphabet (RFC 4648 §4).
const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// Base64 with padding (RFC 4648 §4) — the only encoding the handshake needs.
fn base64(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for group in bytes.chunks(3) {
        // A short final group is zero-extended and its missing characters are
        // written as `=`, which is exactly what the padding rule says.
        let packed = u32::from(group[0]) << 16
            | u32::from(group.get(1).copied().unwrap_or(0)) << 8
            | u32::from(group.get(2).copied().unwrap_or(0));
        let sextet = |shift: u32| char::from(ALPHABET[((packed >> shift) & 0x3F) as usize]);
        out.push(sextet(18));
        out.push(sextet(12));
        out.push(if group.len() > 1 { sextet(6) } else { '=' });
        out.push(if group.len() > 2 { sextet(0) } else { '=' });
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(digest: &[u8; 20]) -> String {
        use std::fmt::Write as _;
        digest.iter().fold(String::new(), |mut out, byte| {
            let _ = write!(out, "{byte:02x}");
            out
        })
    }

    /// FIPS 180-4's own worked examples, plus the two boundary lengths where a
    /// hand-written padding rule goes wrong: a message that exactly fills a
    /// block's 56-byte data region, and one that spills into a second block.
    #[test]
    fn sha1_matches_the_published_vectors() {
        assert_eq!(
            hex(&sha1(b"")),
            "da39a3ee5e6b4b0d3255bfef95601890afd80709",
            "the empty message (one all-padding block)"
        );
        assert_eq!(
            hex(&sha1(b"abc")),
            "a9993e364706816aba3e25717850c26c9cd0d89d",
            "FIPS 180-4 one-block example"
        );
        assert_eq!(
            hex(&sha1(
                b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
            )),
            "84983e441c3bd26ebaae4aa1f95129e5e54670f1",
            "FIPS 180-4 two-block example — 56 bytes, so the length spills into \
             a second block"
        );
        assert_eq!(
            hex(&sha1(&vec![b'a'; 1_000_000])),
            "34aa973cd4c4daa4f61eeb2bdbad27316534016f",
            "FIPS 180-4 long message (a million 'a') — many blocks, and the \
             only vector that would catch a broken chaining step"
        );
    }

    /// RFC 4648 §10's test vectors — the padding cases are the whole risk.
    #[test]
    fn base64_matches_the_published_vectors() {
        assert_eq!(base64(b""), "");
        assert_eq!(base64(b"f"), "Zg==");
        assert_eq!(base64(b"fo"), "Zm8=");
        assert_eq!(base64(b"foo"), "Zm9v");
        assert_eq!(base64(b"foob"), "Zm9vYg==");
        assert_eq!(base64(b"fooba"), "Zm9vYmE=");
        assert_eq!(base64(b"foobar"), "Zm9vYmFy");
        // Every alphabet position, including `+` and `/`, which a
        // URL-safe-alphabet slip would get wrong.
        assert_eq!(base64(&[0xFB, 0xFF, 0xFE]), "+//+");
    }

    /// RFC 6455 §1.3's worked example, end to end.
    #[test]
    fn the_accept_key_matches_the_rfc_example() {
        assert_eq!(
            derive_accept_key("dGhlIHNhbXBsZSBub25jZQ=="),
            "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
        );
    }
}
