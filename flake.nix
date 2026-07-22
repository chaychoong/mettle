# flake.nix — mettle dev shell.
#
# `nix develop` provides the whole toolchain the agent-operating guide and
# gates assume: rustc/cargo/rustfmt/clippy, JDK 21 (the conformance oracle's
# runtime — hermetic JDK de-flakes the jar harness across machines), and the
# small tools scripts/*.sh use (git, curl, python3, shellcheck).
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
# nixos-26.05's newest packaged rustc is 1.95.0 (`rustPackages_1_95`) —
# short of mettle's pinned 1.97.0 (rust-toolchain.toml), which no nixpkgs
# stable branch had packaged as of this pin. rust-toolchain.toml remains the
# exact authority for rustup users (CI, or anyone not using this flake); this
# shell is the closest hermetic match nixpkgs currently offers. Re-pin the
# nixpkgs rev (and bump rustPackages_1_9N below) once a branch ships 1.97.x.
#
# --- flake.lock --------------------------------------------------------
# Not committed here — this flake was authored on a machine without nix
# installed (see docs/MIGRATION.md), so the lock could not be generated or
# verified locally. The FIRST `nix develop` on a real nix machine generates
# flake.lock from the pinned input above; commit it at that point so every
# later `nix develop` resolves an identical, hermetic tree.

{
  description = "mettle dev shell: pinned rustc + JDK 21 for the Alloy conformance harness";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/fd1462031fdee08f65fd0b4c6b64e22239a77870";

  outputs =
    { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems f;
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };
          rust = pkgs.rustPackages_1_95;
        in
        {
          default = pkgs.mkShell {
            packages = [
              rust.rustc
              rust.cargo
              rust.rustfmt
              rust.clippy
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
    };
}
