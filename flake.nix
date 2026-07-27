# flake.nix — mettle dev shell + package/app outputs.
#
# `nix develop` provides the whole toolchain the agent-operating guide and
# gates assume: rustc/cargo/rustfmt/clippy, JDK 21 (the conformance oracle's
# runtime — hermetic JDK de-flakes the jar harness across machines), and the
# small tools scripts/*.sh use (git, curl, python3, shellcheck).
#
# `nix run github:chaychoong/mettle` (mt-074, ADR-0016 Decision 4) builds and
# runs just the `mettle` binary — the CLI/evaluator/serve entry point — with
# no local rustup install required.
#
# --- nixpkgs pin -----------------------------------------------------------
# Branch: nixos-26.05 — the latest NixOS *stable* release branch as of
# 2026-07-22 (checked via `git ls-remote https://github.com/NixOS/nixpkgs.git`;
# nixos-25.05 still exists too but is two stable releases behind — 25.05 →
# 25.11 → 26.05 — and its default rustc tops out at 1.86.0, or 1.89.0 via the
# versioned rust_1_89 attribute).
# Rev: fd1462031fdee08f65fd0b4c6b64e22239a77870 (fetched 2026-07-22 via
#   git ls-remote https://github.com/NixOS/nixpkgs.git refs/heads/nixos-26.05
# — the exact rev is baked into the input URL below, so this flake resolves
# the same nixpkgs tree regardless of what the branch head moves to later).
#
# --- rustc pin: rust-overlay, not nixpkgs ----------------------------------
# nixos-26.05's newest packaged rustc is 1.95.0 (`rustPackages_1_95`) — short
# of mettle's pinned 1.97.0 (rust-toolchain.toml), and as of this pin no
# nixpkgs stable branch had packaged 1.97.x. Rather than keep tracking that
# gap (the previous version of this file ran the dev shell on 1.95.0 as a
# documented compromise), this flake now pulls oxalica/rust-overlay and
# builds the toolchain straight from `rust-toolchain.toml` via
# `rust-bin.fromRustupToolchainFile`. That makes rust-toolchain.toml the
# single authority for the exact version everywhere (rustup, CI, and nix) —
# this file can no longer drift from it; bumping the channel there is enough
# to re-pin nix too (mechanically — flake.lock still needs `nix flake update
# rust-overlay` to fetch that channel's actual toolchain artifacts).
#
# rust-overlay over fenix: both wrap the same upstream rustup-dist artifacts.
# rust-overlay's `fromRustupToolchainFile` reads `rust-toolchain.toml`
# directly (fenix needs a hash-pinned `fenix.toolchainOf` or a separate
# manifest-parsing helper), which is the tighter fit for "one file is the
# authority" here, and it's the more widely used option for this exact
# workflow.
#
# `rust-overlay.inputs.nixpkgs.follows = "nixpkgs"` below pins rust-overlay
# to the same nixpkgs tree as everything else in this flake, so there is one
# nixpkgs evaluation, not two.
#
# --- flake.lock --------------------------------------------------------
# Committed (since the 2026-07-24 nix migration onto a machine with nix
# installed — see docs/MIGRATION.md). `nix flake update rust-overlay` moves
# the pin; re-run and commit the lock when following a rust-toolchain.toml
# channel bump.
#
# --- determinism note -------------------------------------------------------
# The nix-built `mettle` binary uses the exact 1.97.0 toolchain pinned by
# rust-toolchain.toml, same as a `cargo build` on any other machine — but it
# is not claimed *byte-identical* to a cargo-built binary (different build
# environment: nixpkgs' linker/libc, build-id salting, etc. all vary that).
# mettle's determinism guarantee is about solver *output* (fixed solver
# build → byte-identical instances/counterexamples for a given model), which
# the pinned toolchain preserves regardless of which build environment
# produced the binary.

{
  description = "mettle: pinned rustc dev shell + package/app outputs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/fd1462031fdee08f65fd0b4c6b64e22239a77870";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    { self, nixpkgs, rust-overlay }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems f;

      # pkgs + the pinned toolchain, shared by devShells/packages/apps below.
      pkgsFor =
        system:
        import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };

      # `fromRustupToolchainFile` parses rust-toolchain.toml's `channel` and
      # `components` and fetches exactly that rustup-dist toolchain (1.97.0
      # + rustfmt + clippy, per that file) — no version duplicated here.
      toolchainFor = pkgs: pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
          rust = toolchainFor pkgs;
        in
        {
          default = pkgs.mkShell {
            packages = [
              rust
              pkgs.jdk21
              pkgs.git
              pkgs.curl
              pkgs.python3
              pkgs.shellcheck
            ];

            shellHook = ''
              echo "mettle dev shell: $(rustc --version)"
              echo "                  $(java -version 2>&1 | head -1)"
            '';
          };
        }
      );

      packages = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
          rust = toolchainFor pkgs;
          # makeRustPlatform swaps buildRustPackage's cargo/rustc for the
          # rust-overlay toolchain above, instead of nixpkgs' own — this is
          # what keeps the package build on the exact 1.97.0 pin.
          rustPlatform = pkgs.makeRustPlatform {
            cargo = rust;
            rustc = rust;
          };
        in
        {
          default = rustPlatform.buildRustPackage {
            pname = "mettle";
            # Same single-authority rule as the toolchain: the workspace
            # version lives in Cargo.toml, this file only reads it.
            version = (builtins.fromTOML (builtins.readFile ./Cargo.toml)).workspace.package.version;
            src = ./.;

            # Zero C dependencies in the workspace (per rust-toolchain.toml /
            # ADR-0016) — no cargoLock.outputHashes, no nativeBuildInputs for
            # a C toolchain, no linker fuss.
            cargoLock.lockFile = ./Cargo.lock;

            # The workspace also carries crates/als-conform's internal
            # `conform`/`resolve-gauge`/`solve-gauge` gauge binaries, which
            # are dev/CI tooling against the reference Alloy jar, not part of
            # the shipped product `nix run` should hand back. als-conform is
            # not a dependency of the `mettle` crate, so restricting the
            # build to `-p mettle` builds (and this package therefore only
            # installs) the `mettle` binary itself.
            cargoBuildFlags = [
              "-p"
              "mettle"
            ];

            # Off deliberately: the workspace's real correctness gauntlet is
            # the conformance scorecard (scripts/*.sh against the reference
            # Alloy jar, run in CI / by hand), which needs JDK + corpus + a
            # jar this sandboxed nix build phase doesn't have and shouldn't
            # try to reproduce. `cargo test -p mettle` alone (what doCheck
            # would run here) is a partial, misleading substitute for that —
            # better to run it explicitly in CI than imply package-build
            # green means gauge-green.
            doCheck = false;

            meta = {
              description = "Rust reimplementation of the Alloy 6 language and analyzer";
              homepage = "https://github.com/chaychoong/mettle";
              license = pkgs.lib.licenses.mpl20;
              mainProgram = "mettle";
            };
          };
        }
      );

      apps = forAllSystems (system: {
        default = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/mettle";
        };
      });
    };
}
