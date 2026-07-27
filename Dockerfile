# mettle container image.
#
# Two stages: build with the exact pinned rustc (rust-toolchain.toml), then
# ship only the built binary on a minimal runtime base. The workspace is
# zero-C-dep (dist-workspace.toml, ADR-0016) -- als-solve's SAT solver is
# pure Rust -- so the runtime image only needs to satisfy dynamic glibc/libgcc
# linkage, not a solver's own native library.

# --- builder -----------------------------------------------------------
# Pinned to the exact compiler in rust-toolchain.toml: a different rustc is a
# different build, and this project gauges itself against one fixed solver
# build (STYLE D1). `-slim` trims apt's default image without dropping the
# toolchain itself.
FROM rust:1.97.0-slim AS builder

WORKDIR /build

# The whole workspace: `cargo build -p mettle` still needs every member's
# Cargo.toml to resolve (Cargo.lock pins the full graph), even though only
# one crate's sources end up in the image below. `.dockerignore` keeps this
# context to source + manifests -- no target/, corpus/, or oracle/.
COPY . .

# Only the binary crate: the workspace's conformance tooling
# (als-conform, oracle-diffing scripts) is a developer/CI concern, not
# something the shipped image needs to carry or build.
RUN cargo build --release -p mettle

# --- runtime -------------------------------------------------------------
# distroless/cc: glibc + libgcc + ca-certificates and nothing else, which is
# exactly what a zero-C-dep dynamically-linked Rust binary needs -- no shell,
# no package manager, smallest attack surface. (If a future dependency needs
# something distroless/cc doesn't carry, fall back to debian:bookworm-slim,
# which has the same glibc ABI plus a full userland to debug from.)
FROM gcr.io/distroless/cc-debian12

LABEL org.opencontainers.image.source="https://github.com/chaychoong/mettle" \
      org.opencontainers.image.description="A Rust reimplementation of the Alloy 6 language and analyzer" \
      org.opencontainers.image.licenses="MPL-2.0"

COPY --from=builder /build/target/release/mettle /mettle

# Commands take a file path argument (`mettle parse /work/m.als`); `/work` is
# the natural place to bind-mount a model directory into.
WORKDIR /work

ENTRYPOINT ["/mettle"]
