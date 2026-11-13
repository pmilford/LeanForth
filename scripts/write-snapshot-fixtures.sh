#!/usr/bin/env bash
# Write the snapshot fixtures of one LeanForth commit (plan step 6.2.5c2;
# docs/design/SNAPSHOT_COMPATIBILITY.md section 6): the snapshots that the
# build at commit REV writes of a fixed set of small exports, which the
# tests load with later builds (tests/cli/test_leanforth.py, class
# OlderSnapshots). One folder per verdict version, tests/snapshots/v<V>,
# with a README.md naming the commit, the commands and each file's SHA-256.
#
# Usage: scripts/write-snapshot-fixtures.sh REV [OUT]
#   REV  the commit whose build writes the files (its tree is extracted with
#        git archive into a new temporary folder, removed by its exact path
#        at the end; nothing else is created or deleted)
#   OUT  the folder written (default: tests/snapshots/v<V>, V the verdict
#        version REV's src/kernel/verdict-version.fs holds); its .lfsnap
#        files and README.md are replaced, nothing else in it is touched
# The exports are this checkout's (Lean's exports, the same for every
# build); the engine is this checkout's pinned gforth-fast (or GFORTH).
# The run is the one bin/leanforth makes (src/main.fs -e cli-main), with
# LEANFORTH_COMMIT set to REV so that each file's information section
# names the build that wrote it.
# Exit status: 0 every file written; 1 otherwise (the message says which).
set -eu

root=$(cd "$(dirname "$0")/.." && pwd -P)
rev=${1:?usage: scripts/write-snapshot-fixtures.sh REV [OUT]}
commit=$(git -C "$root" rev-parse --verify "$rev^{commit}")
gforth=${GFORTH:-$root/.tools/gforth/bin/gforth-fast}
version=$(git -C "$root" show "$commit:src/kernel/verdict-version.fs" |
  sed -n 's/^\([0-9][0-9]*\) constant lf-verdict-version$/\1/p')
[ -n "$version" ] || { echo "error: no verdict version at $commit" >&2; exit 1; }
out=${2:-$root/tests/snapshots/v$version}
mkdir -p "$out"
out=$(cd "$out" && pwd -P)

tree=$(mktemp -d "${TMPDIR:-/tmp}/leanforth-fixtures.XXXXXX")
finish() { rm -r -- "$tree"; }
trap finish EXIT
git -C "$root" archive "$commit" | tar -x -C "$tree"

# One run of the build at REV; true when FILE was written.
written() {
  local file=$1; shift
  rm -f -- "$out/$file"
  LEANFORTH_COMMIT=$commit LEANFORTH_MODIFIED=false LEANFORTH_ENGINE=${gforth##*/} \
    "$gforth" "$tree/src/main.fs" -e cli-main check --save-snapshot "$out/$file" "$@" \
    </dev/null >/dev/null || true
  [ -s "$out/$file" ] || { echo "error: $file was not written ($*)" >&2; exit 1; }
  printf '| `%s` | `check --save-snapshot %s %s` |\n' "$file" "$file" "$*" >>"$tree/runs"
}
x=$root/tests
: >"$tree/runs"
written inductive.lfsnap "$x/cli/inductive.ndjson"
written nested.lfsnap "$x/cli/nested.ndjson"
written kinds.lfsnap --no-manifest "$x/core/reexport/kinds.ndjson"
written unfold.lfsnap "$x/cli/unfold.ndjson"
written let-b.lfsnap "$x/cli/let-b.ndjson"
written init-slice.lfsnap "$x/author/init-slice.ndjson"
written dependent.lfsnap --snapshot "$out/inductive.lfsnap" "$x/cli/dependent.ndjson"

{
  echo "# Snapshot fixtures of verdict version $version"
  echo
  echo "Written by \`scripts/write-snapshot-fixtures.sh $rev\` (plan step 6.2.5c2;"
  echo "[SNAPSHOT_COMPATIBILITY.md](../../../docs/design/SNAPSHOT_COMPATIBILITY.md)"
  echo "section 6): the build of commit \`$commit\`, run on"
  echo "\`$("$gforth" --version 2>&1 | head -1)\`, checked this checkout's exports"
  echo "(paths below are relative to \`tests/\`) and saved each snapshot; \`dependent\`"
  echo "is a layer on \`inductive\`. Each build that bumps the verdict version writes"
  echo "its own set; a set that leaves the window of two versions is deleted by name."
  echo
  echo "| File | Command |"
  echo "| --- | --- |"
  sed "s#$x/##g; s#$out/##g" "$tree/runs"
  echo
  echo "SHA-256 of each file:"
  echo
  echo '```text'
  (cd "$out" && sha256sum inductive.lfsnap nested.lfsnap kinds.lfsnap unfold.lfsnap \
    let-b.lfsnap init-slice.lfsnap dependent.lfsnap)
  echo '```'
} >"$out/README.md"
echo "written: $out (verdict version $version, commit $commit)"
