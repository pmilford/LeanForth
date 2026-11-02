#!/usr/bin/env bash
# Install the pinned Lean 4.35.0 toolchain into PREFIX without elan.
#
# Usage: scripts/install-lean.sh PREFIX
# Afterwards run tests with LEAN=PREFIX/bin/lean.
#
# Linux x86-64 only. The download is rejected unless its SHA-256 matches the
# digest GitHub reports for the v4.35.0 release asset (read 2026-11-02 with
# `gh api repos/leanprover/lean4/releases/tags/v4.35.0`). The test scripts
# separately require Lean revision eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
set -euo pipefail

prefix=${1:?usage: install-lean.sh PREFIX}
version=4.35.0
asset=lean-$version-linux.tar.zst
url=https://github.com/leanprover/lean4/releases/download/v$version/$asset
sha256=7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d

if [ "$(uname -sm)" != 'Linux x86_64' ]; then
  printf 'install-lean.sh supports Linux x86_64 only; got %s\n' "$(uname -sm)" >&2
  exit 1
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

curl -fsSL --retry 3 -o "$work/$asset" "$url"
printf '%s  %s\n' "$sha256" "$work/$asset" | sha256sum -c --quiet -
mkdir -p "$prefix"
tar --zstd -xf "$work/$asset" -C "$prefix" --strip-components=1
"$prefix/bin/lean" --version
