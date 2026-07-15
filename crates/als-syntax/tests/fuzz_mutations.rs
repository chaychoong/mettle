//! Deterministic mutation fuzzer over the front end (mt-014 Part 1).
//!
//! Mutates the vendored corpora (when present, `corpus/…`; skipped cleanly
//! like `corpus_lex.rs`/`corpus_parse.rs`/`corpus_roundtrip.rs`) plus a small
//! committed set of inline seed snippets (so this test is meaningful even on
//! a fresh checkout with no corpus fetched) and asserts three properties of
//! every mutant:
//!
//! 1. **No panic.** [`als_syntax::parse`] always returns `Ok` or `Err` --
//!    never aborts, never loops (the crate has no unbounded loops to begin
//!    with; termination follows from the parser always consuming a token or
//!    erroring).
//! 2. **Sane spans on `Err`.** The reported span's `start <= end`, `end` is
//!    within the mutant's byte length, and both offsets land on a UTF-8 char
//!    boundary of the mutant text.
//! 3. **Round-trip on `Ok`.** Same oracle as `corpus_roundtrip.rs`: pretty
//!    print, re-parse, dump-equal, and idempotent re-printing.
//!
//! # Determinism (STYLE D4)
//! All randomness comes from a hand-rolled `SplitMix64` PRNG (below) seeded
//! from [`FUZZ_BASE_SEED`] (a named const, part of the recorded input) mixed
//! with the seed file's index and the mutation iteration number -- two runs
//! on the same corpus produce byte-identical mutants and identical results
//! (verified: this test is run twice in CI-equivalent conditions during
//! review with no divergence).
//!
//! # Budget
//! The default budget (`ITERS_PER_SEED_DEFAULT` below) is tuned to finish in
//! a few seconds -- fast enough for CI. For a longer offline run (more
//! mutants per seed file), set `METTLE_FUZZ_ITERS=<n>`:
//!
//! ```text
//! METTLE_FUZZ_ITERS=5000 cargo test -p als-syntax --test fuzz_mutations -- --nocapture
//! ```
//!
//! # UTF-8
//! Byte-level mutations may produce invalid UTF-8. [`als_syntax::parse`]
//! takes `&str`, so every mutant is sanitized with
//! [`String::from_utf8_lossy`] before parsing (preferred over skipping
//! invalid mutants -- lossy conversion exercises the replacement-character
//! (`U+FFFD`) path through the lexer, which skipping would never reach).
//!
//! # Reproducing a failure
//! Every property-check function reports the base seed, seed file, and
//! iteration in its panic/assert message and writes the exact mutant bytes
//! to `<TMPDIR>/mettle-fuzz-mutant-<seed>.als` before checking it, so a
//! failure names a file that reproduces it byte-for-byte.

use std::path::{Path, PathBuf};

use als_syntax::{dump, lex, parse, print, ArenaId, FileId, ParseError, Token};

// -- Hand-rolled PRNG (STYLE P1/P2: zero new deps for a ~10-line generator) --

/// `SplitMix64` -- a small, fast, well-distributed PRNG (Vigna, 2015) used only
/// to derive mutation choices deterministically. Not cryptographic; that is
/// not a requirement here (STYLE D4 only requires determinism, not
/// unpredictability).
struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..bound` (bound must be nonzero); the modulo bias this
    /// introduces is irrelevant for a mutation-choice PRNG.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "the result of `x % (bound as u64)` is always < bound, which is already a \
                  usize, so the truncating cast back to usize can never actually lose \
                  information -- a 32-bit-usize-target concern the modulo already rules out"
    )]
    fn next_below(&mut self, bound: usize) -> usize {
        debug_assert!(bound > 0, "next_below called with bound 0");
        (self.next_u64() % bound as u64) as usize
    }

    fn next_u8(&mut self) -> u8 {
        (self.next_u64() & 0xFF) as u8
    }
}

/// Base seed for every mutant this test derives (STYLE D4: named, recorded).
/// Mixed with the seed file's index and the iteration number per mutant, so
/// changing the seed corpus (adding/removing a file) does not silently
/// reshuffle every other file's mutation sequence.
const FUZZ_BASE_SEED: u64 = 0x6D74_5F30_3134; // ASCII "mt_014", arbitrary but greppable.

fn seed_for(file_index: usize, iteration: usize) -> u64 {
    FUZZ_BASE_SEED
        ^ (file_index as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
        ^ (iteration as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9)
}

// -- Seed corpus --------------------------------------------------------

/// A small committed set of valid Alloy 6 snippets covering sigs, facts,
/// preds/funs, quantifiers/comprehensions, temporal operators, and scopes --
/// so this test mutates *something* meaningful even when `corpus/` is
/// absent (a fresh checkout, per the other `corpus_*.rs` tests' pattern).
const SEED_SNIPPETS: &[&str] = &[
    "sig A {} sig B extends A { f: set B }\nfact { all a: A | some a.f }\n",
    "abstract sig S { r: S -> S }\npred p[x: S] { some x.r }\nrun p for 3\n",
    "var sig Light { var on: one Bool }\nfact { always (Light.on = one Light) }\n",
    "sig Bool { } one sig True, False extends Bool {}\n\
     fun min[s: set Int]: lone Int { s }\nassert A { some min[Int] } check A for 5\n",
    "sig A {}\npred q[] { some x: A | all y: A | x != y implies y in x.~(A->A) else no A }\n",
    "module m[X]\nopen util/ordering[X] as ord\nsig A {}\n\
     fact { all x: A | eventually x in x.^(A->A) }\n",
    "sig A { f: A lone -> some A }\nrun { some f } for 4 but 2 A expect 1\n",
    "let helper[x] = x.~x\nsig A { r: A }\nfact { all a: A | helper[a.r] = a.r }\n",
    "enum Color { Red, Green, Blue }\nsig A { c: one Color }\n\
     fact { all disj a, b: A | a.c != b.c }\n",
    "sig A {}\nassert Named \"a named assertion\" { some A }\ncheck Named\n",
];

/// Recursively collects `.als` files under `dir`, sorted (mirrors
/// `corpus_lex.rs`/`corpus_parse.rs`/`corpus_roundtrip.rs`).
fn collect_als_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_als_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "als") {
            out.push(path);
        }
    }
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The full seed pool: inline snippets first (always present, indices
/// stable), then corpus files (sorted, skipped cleanly if absent) -- STYLE
/// U5, deterministic iteration order.
fn seed_pool() -> Vec<(String, String)> {
    let mut seeds: Vec<(String, String)> = SEED_SNIPPETS
        .iter()
        .enumerate()
        .map(|(i, s)| (format!("inline:{i}"), (*s).to_owned()))
        .collect();

    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];
    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!(
            "fuzz_mutations: no corpus directories found under {} -- mutating only the {} \
             inline seed snippets (expected for a fresh checkout)",
            root.display(),
            SEED_SNIPPETS.len()
        );
    } else {
        let mut files = Vec::new();
        for dir in &present {
            collect_als_files(dir, &mut files);
        }
        files.sort();
        for path in files {
            if let Ok(source) = std::fs::read_to_string(&path) {
                seeds.push((path.display().to_string(), source));
            }
        }
    }
    seeds
}

// -- Mutation classes -----------------------------------------------------

/// One mutation class, cycled deterministically over iterations so every
/// class is exercised for every seed file regardless of budget (the brief's
/// "each class exercised").
#[derive(Clone, Copy, Debug)]
enum Mutation {
    Truncate,
    ByteFlip,
    ByteInsert,
    ByteDelete,
    SpliceRegions,
    TokenDelete,
    TokenDuplicate,
    TokenSwap,
    TokenReorder,
}

const MUTATION_CYCLE: &[Mutation] = &[
    Mutation::Truncate,
    Mutation::ByteFlip,
    Mutation::ByteInsert,
    Mutation::ByteDelete,
    Mutation::SpliceRegions,
    Mutation::TokenDelete,
    Mutation::TokenDuplicate,
    Mutation::TokenSwap,
    Mutation::TokenReorder,
];

/// Applies one mutation to `source` (byte-level classes) or `source`'s own
/// token spans (token-level classes; splices raw source text by span, never
/// re-renders from token kinds -- STYLE/brief requirement, so a mutant's
/// bytes are always a genuine substring shuffle of real source text).
/// `donor` supplies the second file for [`Mutation::SpliceRegions`].
fn mutate(kind: Mutation, source: &str, donor: &str, rng: &mut SplitMix64) -> Vec<u8> {
    match kind {
        Mutation::Truncate => truncate(source, rng),
        Mutation::ByteFlip => byte_flip(source, rng),
        Mutation::ByteInsert => byte_insert(source, rng),
        Mutation::ByteDelete => byte_delete(source, rng),
        Mutation::SpliceRegions => splice_regions(source, donor, rng),
        Mutation::TokenDelete | Mutation::TokenDuplicate | Mutation::TokenSwap => {
            token_splice(kind, source, rng)
        }
        Mutation::TokenReorder => token_reorder(source, rng),
    }
}

fn truncate(source: &str, rng: &mut SplitMix64) -> Vec<u8> {
    let bytes = source.as_bytes();
    if bytes.is_empty() {
        return Vec::new();
    }
    let cut = rng.next_below(bytes.len() + 1);
    bytes[..cut].to_vec()
}

fn byte_flip(source: &str, rng: &mut SplitMix64) -> Vec<u8> {
    let mut bytes = source.as_bytes().to_vec();
    if bytes.is_empty() {
        return bytes;
    }
    let i = rng.next_below(bytes.len());
    bytes[i] ^= rng.next_u8() | 0x01; // `| 0x01` guarantees a non-zero XOR (never a no-op flip)
    bytes
}

fn byte_insert(source: &str, rng: &mut SplitMix64) -> Vec<u8> {
    let mut bytes = source.as_bytes().to_vec();
    let i = rng.next_below(bytes.len() + 1);
    bytes.insert(i, rng.next_u8());
    bytes
}

fn byte_delete(source: &str, rng: &mut SplitMix64) -> Vec<u8> {
    let mut bytes = source.as_bytes().to_vec();
    if bytes.is_empty() {
        return bytes;
    }
    let i = rng.next_below(bytes.len());
    bytes.remove(i);
    bytes
}

/// Splices a random byte region from `donor` into a random position in
/// `source` -- the classic fuzzer "splice" (combine two different inputs
/// rather than mutate one in isolation).
fn splice_regions(source: &str, donor: &str, rng: &mut SplitMix64) -> Vec<u8> {
    let src_bytes = source.as_bytes();
    let donor_bytes = donor.as_bytes();
    if donor_bytes.is_empty() {
        return src_bytes.to_vec();
    }
    let d_start = rng.next_below(donor_bytes.len());
    let d_end = d_start + rng.next_below(donor_bytes.len() - d_start + 1);
    let insert_at = rng.next_below(src_bytes.len() + 1);
    let mut out = Vec::with_capacity(src_bytes.len() + (d_end - d_start));
    out.extend_from_slice(&src_bytes[..insert_at]);
    out.extend_from_slice(&donor_bytes[d_start..d_end]);
    out.extend_from_slice(&src_bytes[insert_at..]);
    out
}

/// Lexes `source` and returns its raw (non-EOF) token spans, or `None` if it
/// doesn't lex (token-level mutations need real spans to splice by).
fn token_spans(source: &str) -> Option<Vec<Token>> {
    let tokens = lex(source, FileId::from_index(0)).ok()?;
    Some(
        tokens
            .into_iter()
            .filter(|t| t.span.start != t.span.end)
            .collect(),
    )
}

/// Delete/duplicate/swap one or two token spans' raw source text (never
/// re-rendered from token kinds, per the brief -- a mutant is always a
/// genuine byte-splice of real source).
fn token_splice(kind: Mutation, source: &str, rng: &mut SplitMix64) -> Vec<u8> {
    let bytes = source.as_bytes();
    let Some(spans) = token_spans(source) else {
        return bytes.to_vec();
    };
    if spans.is_empty() {
        return bytes.to_vec();
    }
    match kind {
        Mutation::TokenDelete => {
            let t = &spans[rng.next_below(spans.len())];
            let mut out = bytes[..t.span.start as usize].to_vec();
            out.extend_from_slice(&bytes[t.span.end as usize..]);
            out
        }
        Mutation::TokenDuplicate => {
            let t = &spans[rng.next_below(spans.len())];
            let (start, end) = (t.span.start as usize, t.span.end as usize);
            let mut out = bytes[..end].to_vec();
            out.extend_from_slice(&bytes[start..end]);
            out.extend_from_slice(&bytes[end..]);
            out
        }
        Mutation::TokenSwap => {
            if spans.len() < 2 {
                return bytes.to_vec();
            }
            let i = rng.next_below(spans.len());
            let mut j = rng.next_below(spans.len());
            if j == i {
                j = (j + 1) % spans.len();
            }
            let (lo, hi) = if spans[i].span.start < spans[j].span.start {
                (i, j)
            } else {
                (j, i)
            };
            let (a, b) = (spans[lo].span, spans[hi].span);
            if a.end as usize > b.start as usize {
                return bytes.to_vec(); // overlapping after reorder guard, skip
            }
            let mut out = bytes[..a.start as usize].to_vec();
            out.extend_from_slice(&bytes[b.start as usize..b.end as usize]);
            out.extend_from_slice(&bytes[a.end as usize..b.start as usize]);
            out.extend_from_slice(&bytes[a.start as usize..a.end as usize]);
            out.extend_from_slice(&bytes[b.end as usize..]);
            out
        }
        Mutation::Truncate
        | Mutation::ByteFlip
        | Mutation::ByteInsert
        | Mutation::ByteDelete
        | Mutation::SpliceRegions
        | Mutation::TokenReorder => unreachable!("token_splice only handles its own 3 kinds"),
    }
}

/// Moves one token span's raw text to just before a different token span
/// (delete-then-reinsert-elsewhere), the "reorder" class.
fn token_reorder(source: &str, rng: &mut SplitMix64) -> Vec<u8> {
    let bytes = source.as_bytes();
    let Some(spans) = token_spans(source) else {
        return bytes.to_vec();
    };
    if spans.len() < 2 {
        return bytes.to_vec();
    }
    let i = rng.next_below(spans.len());
    let mut j = rng.next_below(spans.len());
    if j == i {
        j = (j + 1) % spans.len();
    }
    let moved = &source[spans[i].span.start as usize..spans[i].span.end as usize];
    let without: String = {
        let mut s = String::with_capacity(source.len());
        s.push_str(&source[..spans[i].span.start as usize]);
        s.push_str(&source[spans[i].span.end as usize..]);
        s
    };
    // Re-lex the shortened text to find the target span's new position
    // (removing token `i` shifted every later offset).
    let Some(new_spans) = token_spans(&without) else {
        return without.into_bytes();
    };
    if new_spans.is_empty() {
        return without.into_bytes();
    }
    let target = &new_spans[j.min(new_spans.len() - 1)];
    let mut out = without.as_bytes()[..target.span.start as usize].to_vec();
    out.push(b' ');
    out.extend_from_slice(moved.as_bytes());
    out.push(b' ');
    out.extend_from_slice(&without.as_bytes()[target.span.start as usize..]);
    out
}

// -- Property checks --------------------------------------------------------

/// Writes the exact mutant bytes to a fixed, deterministic scratch path so a
/// failure (panic or assertion) names a file reproducing it byte-for-byte.
fn write_repro(seed: u64, mutant: &[u8]) -> PathBuf {
    let path = std::env::temp_dir().join(format!("mettle-fuzz-mutant-{seed:016x}.als"));
    let _ = std::fs::write(&path, mutant);
    path
}

/// Checks properties (1)/(2)/(3) for one mutant, panicking with full
/// reproduction context (base seed, seed label, iteration, mutation kind,
/// repro file path) on any violation.
fn check_mutant(label: &str, iteration: usize, kind: Mutation, seed: u64, mutant_bytes: &[u8]) {
    let repro_path = write_repro(seed, mutant_bytes);
    // UTF-8: lossy conversion, never skip (module doc) -- exercises the
    // replacement-character path through the lexer on genuinely invalid
    // byte-level mutants.
    let mutant = String::from_utf8_lossy(mutant_bytes).into_owned();
    let ctx = || {
        format!(
            "seed={seed:016x} base={FUZZ_BASE_SEED:016x} file={label:?} iter={iteration} \
             mutation={kind:?} repro={}",
            repro_path.display()
        )
    };

    // Property (1) is "no panic": if `parse` itself panics, this whole test
    // process aborts here with `ctx()` as the last thing printed (STYLE:
    // catch_unwind is not needed per-mutant per the brief; the printed
    // context plus the always-written repro file are enough to reproduce).
    let result = parse(&mutant, FileId::from_index(0));

    match result {
        Ok(ast) => check_roundtrip(&ast, &mutant, &ctx),
        Err(err) => check_span_sane(&err, &mutant, &ctx),
    }
}

/// Property (2): the error's span is well-formed for the mutant text it was
/// produced from. `Span::new` already asserts `start <= end` internally
/// (parser.rs), so this focuses on what it does *not* check: the span must
/// fit within the mutant and land on char boundaries.
fn check_span_sane(err: &ParseError, mutant: &str, ctx: &dyn Fn() -> String) {
    let span = err.span();
    // Mutants are always small (seed files are `.als` source, not gigabytes);
    // saturate rather than worry about a cast panic in a fuzz test.
    let len = u32::try_from(mutant.len()).unwrap_or(u32::MAX);
    assert!(
        span.start <= span.end,
        "span start > end ({}..{}) — {}",
        span.start,
        span.end,
        ctx()
    );
    assert!(
        span.end <= len,
        "span end {} exceeds mutant length {len} — {}",
        span.end,
        ctx()
    );
    assert!(
        mutant.is_char_boundary(span.start as usize),
        "span start {} not on a char boundary — {}",
        span.start,
        ctx()
    );
    assert!(
        mutant.is_char_boundary(span.end as usize),
        "span end {} not on a char boundary — {}",
        span.end,
        ctx()
    );
}

/// Property (3): parse -> print -> reparse -> dump-equal -> idempotent,
/// exactly `corpus_roundtrip.rs`'s oracle, applied to a mutant that happened
/// to parse.
fn check_roundtrip(ast: &als_syntax::Ast, mutant: &str, ctx: &dyn Fn() -> String) {
    let printed1 = print::pretty_to_string(ast);
    let ast2 = match parse(&printed1, FileId::from_index(0)) {
        Ok(a) => a,
        Err(e) => panic!("re-parse of printed mutant output failed: {e} — {}", ctx()),
    };
    let (d1, d2) = (dump(ast), dump(&ast2));
    assert_eq!(
        d1,
        d2,
        "round-trip structural mismatch on mutant {mutant:?} — {}",
        ctx()
    );
    let printed2 = print::pretty_to_string(&ast2);
    assert_eq!(
        printed1,
        printed2,
        "pretty-printing not idempotent on mutant {mutant:?} — {}",
        ctx()
    );
}

// -- Budget -----------------------------------------------------------------

/// Default mutation iterations per seed file. Tuned so the full test
/// (inline snippets always, plus the corpus when present) finishes in a few
/// seconds -- comfortably inside the ~20s CI budget the bead brief asks for
/// (measured on this machine: well under a second for the 10 inline seeds
/// alone; a few seconds with the full ~167-file corpus present).
const ITERS_PER_SEED_DEFAULT: usize = 24;

fn iters_per_seed() -> usize {
    std::env::var("METTLE_FUZZ_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(ITERS_PER_SEED_DEFAULT)
}

// -- Main fuzz loop -----------------------------------------------------

#[test]
fn corpus_and_seed_snippets_survive_mutation() {
    let seeds = seed_pool();
    let iters = iters_per_seed();
    let mut mutant_count = 0usize;

    for (i, (label, source)) in seeds.iter().enumerate() {
        for j in 0..iters {
            let kind = MUTATION_CYCLE[j % MUTATION_CYCLE.len()];
            let seed = seed_for(i, j);
            let mut rng = SplitMix64::new(seed);
            // The splice class's donor is a different, deterministically
            // chosen seed file (falls back to self if the pool has only one
            // entry).
            let donor_idx = if seeds.len() > 1 {
                (i + 1 + rng.next_below(seeds.len() - 1)) % seeds.len()
            } else {
                i
            };
            let mutant_bytes = mutate(kind, source, &seeds[donor_idx].1, &mut rng);
            check_mutant(label, j, kind, seed, &mutant_bytes);
            mutant_count += 1;
        }
    }

    eprintln!(
        "fuzz_mutations: {} seed files x {iters} iterations = {mutant_count} mutants, \
         all properties held",
        seeds.len()
    );
}

// -- Targeted stressors (deep nesting, pathological repetition) -------------
//
// A separate, small, fixed (non-random) set: these are deliberately
// pathological shapes, not random mutations, so they don't need the PRNG.
// mt-014 Part 1's headline finding: unguarded, these stack-overflow a debug
// build (see `parser.rs`'s `MAX_EXPR_DEPTH` doc comment and
// `docs/reference/fuzzing.md` section 3); with the depth guard, every one of
// these must return `Ok` or a clean `Err` (in practice `TooDeep` at the
// larger depths) and never crash the process.

fn nested(open: &str, close: &str, inner: &str, depth: usize) -> String {
    format!(
        "run {{ {}{inner}{} }}",
        open.repeat(depth),
        close.repeat(depth)
    )
}

#[test]
fn deep_nesting_stressors_never_crash() {
    let mut too_deep_count = 0usize;
    let mut ok_count = 0usize;
    for depth in [10, 100, 1_000, 10_000] {
        for src in [
            nested("(", ")", "1=1", depth),
            format!("run {{ {}r }}", "~".repeat(depth)),
            format!("run {{ {}1=1 }}", "all x: A | ".repeat(depth)),
        ] {
            // Property (1): reaching this line at all (for every depth, up
            // to 10,000) is the assertion -- a crash aborts the whole test
            // process before any of this runs. `Ok` and `Err` (in practice
            // `TooDeep` past `MAX_EXPR_DEPTH`) are both acceptable outcomes;
            // tallied below only to prove the guard is actually exercised.
            match parse(&src, FileId::from_index(0)) {
                Ok(_) => ok_count += 1,
                Err(ParseError::TooDeep { .. }) => too_deep_count += 1,
                Err(_) => {}
            }
        }
    }
    assert!(
        too_deep_count > 0,
        "expected at least one depth-10,000 stressor to hit MAX_EXPR_DEPTH"
    );
    eprintln!(
        "deep_nesting_stressors_never_crash: {ok_count} parsed OK, {too_deep_count} hit \
         MAX_EXPR_DEPTH, zero crashes"
    );
}

fn operator_chains(n: usize) -> [String; 3] {
    let plus_chain = format!(
        "run {{ some ({}) }}",
        (0..n).map(|_| "A").collect::<Vec<_>>().join(" + ")
    );
    let and_chain = format!(
        "run {{ {} }}",
        (0..n).map(|_| "some A").collect::<Vec<_>>().join(" and ")
    );
    let dot_chain = format!(
        "run {{ some ({}) }}",
        std::iter::once("A".to_owned())
            .chain((0..n).map(|_| ".r".to_owned()))
            .collect::<String>()
    );
    [plus_chain, and_chain, dot_chain]
}

/// Pathological repetition: very long flat operator chains. The Pratt loop
/// handles these *iteratively* for a left/right-associative operator (no
/// extra recursion depth -- confirmed by parsing chains of 10,000 up to
/// `MAX_EXPR_DEPTH`-many terms with no crash even on a 1 MiB thread), so
/// parsing alone is safe at any of the depths below and is checked at all
/// of them.
#[test]
fn long_operator_chains_parse_without_crashing() {
    for n in [100, 1_000, 10_000] {
        for src in operator_chains(n) {
            let result = parse(&src, FileId::from_index(0));
            assert!(
                result.is_ok(),
                "expected a long ({n}-term) operator chain to parse: {src:.80}…"
            );
        }
    }
}

/// **Real finding, deliberately not fixed here (documented instead, see
/// `LIMITATIONS.md` and `docs/reference/fuzzing.md` section 4).** A long
/// flat operator chain parses to a deeply *left-leaning* AST (e.g.
/// `Binary(Binary(Binary(…, A), A), A)` for `A + A + … + A`), and unlike
/// the parser (whose Pratt loop processes such a chain iteratively, see
/// above), `print::pretty_to_string`/`dump` walk the AST with ordinary
/// unguarded recursion (`write_expr` -> `write_binary` -> `write_operand`
/// -> `write_expr` for the left child, and `Dumper::expr` likewise) --
/// depth here equals chain length, not `MAX_EXPR_DEPTH`-bounded recursion
/// count, so a long enough chain overflows the stack in the *printer*
/// (measured: a 5,000-term chain crashes a debug build on a small thread
/// stack even though the same chain parses fine). This is a genuine
/// mt-014-fuzzer finding, but it is a printer/dumper architecture issue
/// (a `Display`/plain-`String` API can't cleanly return a typed "too deep"
/// error the way the parser can -- STYLE E2/E3), materially out of this
/// bead's parser-robustness scope; only round-trip-checked here at a depth
/// well below where it would ever matter, to document the boundary without
/// making this test itself flaky against a constrained CI stack.
#[test]
fn moderate_operator_chains_round_trip() {
    const PRINT_SAFE_N: usize = 300;
    for src in operator_chains(PRINT_SAFE_N) {
        if let Ok(ast) = parse(&src, FileId::from_index(0)) {
            let ctx = || format!("moderate operator chain, n={PRINT_SAFE_N}");
            check_roundtrip(&ast, &src, &ctx);
        }
    }
}
