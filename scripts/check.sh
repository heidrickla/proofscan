#!/usr/bin/env bash
# The CI gates on a pristine extract of the staged tree (what a commit will hold): format, lint
# (with and without smt), tests, dependencies.
# Run from the repository root on Linux (WSL here), with libz3-dev, cargo-nextest and cargo-deny installed.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
tree=$(mktemp -d)
trap 'rm -rf "$tree"' EXIT
staged=$(git -C "$root" write-tree)
git -C "$root" archive "$staged" | tar -x -C "$tree"
cd "$tree"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$HOME/ps-target}" CARGO_TERM_COLOR=never
echo "checking staged tree $staged (HEAD $(git -C "$root" rev-parse --short HEAD)) in $tree"
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo clippy --locked --all-targets --features smt -- -D warnings
cargo nextest run --locked --features smt
cargo deny check
