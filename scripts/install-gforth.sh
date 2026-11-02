#!/usr/bin/env bash
# Build and install the pinned Gforth 1.0.0 from source into PREFIX.
#
# Usage: scripts/install-gforth.sh PREFIX
#
# Requires curl, a C compiler, make, m4, libtool-bin, libffi-dev, libltdl-dev
# and pkg-config (Ubuntu package names). The download is rejected unless its
# SHA-256 matches. That hash was observed on 2026-10-30 and recorded in
# docs/INSTALLATION_LOG.md; upstream does not publish an authenticated one.
# Emacs integration is installed under PREFIX, never into system directories.
set -euo pipefail

prefix=${1:?usage: install-gforth.sh PREFIX}
version=1.0.0
url=https://net2o.de/gforth-dist/Snapshots/$version/gforth-$version.tar.xz
sha256=79c880b68a4a9aa817b7067c21b79acd5b07149fad78f3f630320db410886fa6

case $prefix in /*) ;; *) prefix=$PWD/$prefix ;; esac
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

curl -fsSL --retry 3 -o "$work/gforth.tar.xz" "$url"
printf '%s  %s\n' "$sha256" "$work/gforth.tar.xz" | sha256sum -c --quiet -
tar -xJf "$work/gforth.tar.xz" -C "$work"
cd "$work/gforth-$version"
./configure --prefix="$prefix" --with-lispdir="$prefix/share/emacs/site-lisp"
make -j"$(nproc)"
make install
"$prefix/bin/gforth" --version
