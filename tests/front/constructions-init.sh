#!/usr/bin/env bash
# Lean's generated definitions built by LeanForth against Lean's own, on all
# of Init (plan row FE6; make reference-constructions): Init exported with
# the pinned leanexport (the export of tests/core/compact-init.sh, checked
# by its SHA-256) and its manifest written; then for every inductive type
# whose T.casesOn, T.recOn or T.ctorIdx is in the export,
# src/front/constructions.fs, cases-several.fs and ctor-idx.fs build it
# from T.rec, T's type and constructors and tests/front/constructions-init.fs
# compares it with Lean's node for node. The counts must be the pinned ones
# below: every definition equal, exactly or up to binder names and binder
# information (which the kernel ignores and Lean's exporter shares terms
# by), none different; the unsupported ones are listed with their reasons.
# Then the binder names and information of every definition built are
# compared with pinned Lean's environment (tests/reference/
# constructions-binders.lean, getConstInfo, macro scopes erased; review
# fe6a M1) by tests/front/compare_binders.py: those that differ come from
# the export, which shows a shared term's names and information for T.rec
# and T's type (an exact source is owed, plan row FE6); their counts are
# pinned too. Uses gforth-fast beside $GFORTH when there is one. Needs
# pinned Lean 4.35.0 (LEAN), Gforth (GFORTH) and Python 3.
set -eu
lean=$(python3 "$(dirname "$0")/../../scripts/lean_pin.py" pinned)   # $LEAN or the pinned Lean, never a proxy
gforth=${GFORTH:-gforth}
version=$("$lean" --version)
case "$version" in
  'Lean (version 4.35.0,'*) ;;
  *) printf 'Expected Lean 4.35.0; got: %s\n' "$version" >&2; exit 1 ;;
esac
toolchain=$("$lean" --print-prefix)
leanexport=${LEANEXPORT:-$toolchain/bin/leanexport}   # the Makefile's may replay a cached run
fast="$(dirname "$gforth")/gforth-fast"
if [ -x "$fast" ]; then gforth=$fast; fi
work=$(mktemp -d)
names="init.ndjson init.ndjson.manifest.json forth.txt lean.txt binders.txt FE6Several.olean
  several.ndjson several.ndjson.manifest.json"
trap 'for n in $names; do rm -f "$work/$n"; done; rmdir "$work"' EXIT

# The unit tests' mutual fixture (tests/front/several.lean): pinned Lean
# builds it and scripts/export.sh reproduces its export byte for byte.
out=$(LEAN_PATH="$work" "$lean" -DwarningAsError=true -o "$work/FE6Several.olean" \
  tests/front/several.lean)
if [ "$out" != "'FE6.even_zero' does not depend on any axioms" ]; then
  printf 'Unexpected output from Lean for several.lean: %s\n' "$out" >&2
  exit 1
fi
LEAN="$lean" LEAN_PATH="$work" bash scripts/export.sh "$work/several.ndjson" FE6Several -- \
  FE6.Even.casesOn FE6.Odd.casesOn FE6.Even.recOn FE6.Odd.recOn FE6.Even.ctorIdx \
  FE6.Odd.ctorIdx >/dev/null
cmp tests/front/several.ndjson "$work/several.ndjson"
cmp tests/front/several.ndjson.manifest.json "$work/several.ndjson.manifest.json"
echo "tests/front/several.ndjson reproduced byte for byte"

PATH="$toolchain/bin:$PATH" "$leanexport" Init >"$work/init.ndjson"
digest=$(sha256sum "$work/init.ndjson" | cut -c1-64)
if [ "$digest" != c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179 ]; then
  printf 'Unexpected Init export: %s\n' "$digest" >&2
  exit 1
fi
python3 scripts/export_manifest.py "$work/init.ndjson" >/dev/null
"$gforth" tests/front/constructions-init.fs -e "s\" $work/init.ndjson\" fe6-report bye" \
  </dev/null >"$work/forth.txt"
grep -v '^sig ' "$work/forth.txt"
expected="casesOn generated 597 equal 436 equal-up-to-binders 161 different 0 unsupported 0
recOn generated 576 equal 539 equal-up-to-binders 37 different 0 unsupported 0
ctorIdx generated 397 equal 0 equal-up-to-binders 397 different 0 unsupported 0"
actual=$(grep ' generated ' "$work/forth.txt")
if [ "$actual" != "$expected" ]; then
  printf 'Counts differ from the pinned ones:\n%s\n' "$expected" >&2
  exit 1
fi
echo "casesOn, recOn and ctorIdx: the pinned counts, none different"
# The types LeanForth builds a ctorIdx for and Lean does not (review fe6a-2
# N1; src/front/ctor-idx.fs's header gives Lean's reasons): six declared
# before Nat, five private, and one built by stage0.
expected="extra BEq.ctorIdx
extra Decidable.ctorIdx
extra Empty.ctorIdx
extra Inhabited.ctorIdx
extra Lean.Grind.ToInt.ctorIdx
extra PEmpty.ctorIdx
extra PUnit.ctorIdx
extra _private.Init.Data.Format.Basic.0.Std.Format.SpaceResult.ctorIdx
extra _private.Init.Data.Format.Basic.0.Std.Format.State.ctorIdx
extra _private.Init.Data.Format.Basic.0.Std.Format.WorkGroup.ctorIdx
extra _private.Init.Data.Format.Basic.0.Std.Format.WorkItem.ctorIdx
extra _private.Init.Data.Range.Polymorphic.SInt.0.HasModel.ctorIdx"
actual=$(grep '^extra ' "$work/forth.txt" | LC_ALL=C sort)
if [ "$actual" != "$expected" ]; then
  printf 'The ctorIdx Lean has none of differ from the pinned ones:\n%s\n' "$expected" >&2
  exit 1
fi
echo "ctorIdx built where Lean has none: the twelve pinned types"

PATH="$toolchain/bin:$PATH" "$lean" -DwarningAsError=true --run \
  tests/reference/constructions-binders.lean >"$work/lean.txt"
python3 tests/front/compare_binders.py "$work/lean.txt" "$work/forth.txt" >"$work/binders.txt"
cat "$work/binders.txt"
expected="binders casesOn exact 565 names-differ 30 information-differs 2 not-in-lean 0
binders recOn exact 544 names-differ 30 information-differs 2 not-in-lean 0
binders ctorIdx exact 328 names-differ 69 information-differs 0 not-in-lean 0"
actual=$(grep '^binders ' "$work/binders.txt")
if [ "$actual" != "$expected" ]; then
  printf 'Binder counts against Lean'"'"'s environment differ from the pinned ones:\n%s\n' \
    "$expected" >&2
  exit 1
fi
echo "binders against Lean's environment: the pinned counts"
