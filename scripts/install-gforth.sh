#!/usr/bin/env bash
# Build and install the pinned Gforth 1.0.0 from source into PREFIX.
#
# Usage: scripts/install-gforth.sh PREFIX
#
# Requires curl, a C compiler, make, m4, libtool-bin, libffi-dev, libltdl-dev
# and pkg-config (Ubuntu package names). The download is rejected unless its
# SHA-256 matches. That hash was observed on 2026-10-30 and recorded in
# docs/development/INSTALLATION_LOG.md; upstream does not publish an authenticated one.
# Emacs integration is installed under PREFIX, never into system directories.
set -euo pipefail

prefix=${1:?usage: install-gforth.sh PREFIX}
version=1.0.0
url=https://net2o.de/gforth-dist/Snapshots/$version/gforth-$version.tar.xz
sha256=79c880b68a4a9aa817b7067c21b79acd5b07149fad78f3f630320db410886fa6

case $prefix in /*) ;; *) prefix=$PWD/$prefix ;; esac
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Gforth's build prints several thousand lines, among them warnings and "Error" lines of
# optional parts (its manual, an Emacs start file in /etc) that do not matter here. They go
# to a log; this script prints its own steps and, last, a line that says whether it worked.
mkdir -p "$prefix"
log=$prefix/install-gforth.log
: > "$log"
step() { printf 'install-gforth: %s\n' "$1"; }
failed() {
  printf '\ninstall-gforth: FAILED while %s. The last lines of %s:\n' "$1" "$log" >&2
  tail -n 25 "$log" >&2
  exit 1
}
step "downloading Gforth $version"
curl -fsSL --retry 3 -o "$work/gforth.tar.xz" "$url" || failed "downloading $url"
printf '%s  %s\n' "$sha256" "$work/gforth.tar.xz" | sha256sum -c --quiet - || failed "checking the download's SHA-256"
tar -xJf "$work/gforth.tar.xz" -C "$work"
cd "$work/gforth-$version"
step "configuring (the full output is in $log)"
./configure --prefix="$prefix" --with-lispdir="$prefix/share/emacs/site-lisp" >> "$log" 2>&1 || failed "configuring"
step "building, one to five minutes"
make -j"$(nproc)" >> "$log" 2>&1 || failed "building"
step "installing into $prefix"
make install >> "$log" 2>&1 || failed "installing"
found=$("$prefix/bin/gforth" --version 2>&1) || failed "running the installed gforth"
printf 'install-gforth: OK: %s is installed at %s\n' "$found" "$prefix/bin/gforth"
