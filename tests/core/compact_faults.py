#!/usr/bin/env python3
"""Planted faults for the compact store (ADR 0016; src/lib/slab.fs, htab.fs,
cons.fs, pools.fs and src/core/compact*.fs).

Each fault is a small change to one source file, planted in a scratch copy of
src/ and tests/. The compact store's unit tests (tests/lib/slab.fs, htab.fs,
cons.fs, tests/core/compact.fs) and the round trips of the five pinned
reference exports (tests/core/compact-verify.sh) then run on the copy, and
at least one of them must fail; a fault that every check passes is reported
and the script exits 1. The checks stop at the first failure, since a broken
store may then loop (each run is under a timeout).

Usage: GFORTH=path/to/gforth python3 tests/core/compact_faults.py [-v]
"""
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH") or str(ROOT / ".tools/gforth/bin/gforth")
if not os.path.isabs(GFORTH) and os.sep in GFORTH:
    GFORTH = str(ROOT / GFORTH)

UNIT_TESTS = ["tests/lib/slab.fs", "tests/lib/htab.fs", "tests/lib/cons.fs",
              "tests/core/compact.fs"]
EXPORTS = sorted(str(p.relative_to(ROOT)) for p in (ROOT / "tests/reference").glob("*.ndjson"))

# (what, file, text, change): text must occur exactly once in file.
FAULTS = [
    ("hash-consing ignores a record's second operand", "src/core/compact-tier.fs",
     ": quad-ab= ( addr1 addr2 -- flag ) quad-ab@ rot quad-ab@ d= ;",
     ": quad-ab= ( addr1 addr2 -- flag ) quad-ab@ drop rot quad-ab@ drop = ;"),
    ("names with the same hash are not compared by their text", "src/core/compact-names.fs",
     "if cons-key 2@ rot r> name-text-of compare 0=", "if 2drop r> drop true"),
    ("texts with the same hash are not compared", "src/lib/pools.fs",
     ": text-same ( n key cons -- flag ) rot swap text@ rot cons-key 2@ compare 0= ;",
     ": text-same ( n key cons -- flag ) 2drop drop true ;"),
    ("lists compare only their length", "src/lib/pools.fs",
     "over u32@ 1+ u32s tuck compare 0= ;", "2drop true ;"),
    ("a slab rollback does not restore the count", "src/lib/slab.fs",
     "over slab-mark-count @ over slab-used ! swap", "over slab-mark-count @ drop swap"),
    ("a set's rollback keeps the table entries of the records it gives back",
     "src/lib/cons.fs", "slab-mark-count @ over cons-forget", "slab-mark-count @ drop outcome-ok"),
    ("a reset does not move the generation, so old marks stay valid", "src/lib/slab.fs",
     "slab-epoch dup @ epoch+ swap ! ;", "slab-epoch drop ;"),
    ("off by one 32-bit field: a list item read one field early", "src/lib/pools.fs",
     ": tuple-item ( i t cons -- u ) cons-at swap 1+ u32s + u32@ ;",
     ": tuple-item ( i t cons -- u ) cons-at swap u32s + u32@ ;"),
    ("off by one 32-bit field: the data field overlaps the second operand",
     "src/core/compact-tier.fs", "  1 u32s +field quad-b       \\ second operand",
     "  0 u32s +field quad-b       \\ second operand"),
    ("growth allocates a new block without the old contents", "src/lib/slab.fs",
     ": slab-heap ( u addr -- addr' ior ) ?dup if swap resize else allocate then ;",
     ": slab-heap ( u addr -- addr' ior ) drop allocate ;"),
    ("Algorithm R moves entries whose home is the hole itself", "src/lib/htab.fs",
     "tuck r@ htab-home over - 1- r@ htab-mask @ and", "tuck r@ htab-home over - r@ htab-mask @ and"),
    ("a binder's body range is not lowered", "src/core/compact-exprs.fs",
     ": data-lower ( d -- d' ) dup data-range dup if 1- then", ": data-lower ( d -- d' ) dup data-range dup if then"),
    ("the depth is not capped", "src/core/compact-exprs.fs",
     "dup data-depth 1+ depth-max min depth-shift lshift", "dup data-depth 1+ depth-shift lshift"),
    ("a bound variable at Lean's limit is refused", "src/core/compact-exprs.fs",
     ": bvar-fits? ( index -- flag ) range-max u< ;", ": bvar-fits? ( index -- flag ) range-max 1- u< ;"),
    ("a constant's payload is part of its key", "src/core/compact-exprs.fs",
     ": key-head ( head -- head' ) dup head-tag tag-const = if head-tag then ;",
     ": key-head ( head -- head' ) ;"),
    ("a scratch build never looks in the input", "src/core/compact-exprs.fs",
     "  cons-first @ >r dup quad-a u32@ r@ u< swap quad-b u32@ r> u< and ;",
     "  2drop false ;"),
    ("a letE's body record is accepted as a child", "src/core/compact-exprs.fs",
     "cons-at dup record-body? if drop 0 false else", "cons-at dup drop false if drop 0 false else"),
    ("a sealed set still accepts records", "src/lib/cons.fs",
     ": cons-open? ( cons -- flag ) dup cons-sealed? 0= swap", ": cons-open? ( cons -- flag ) true swap"),
    ("the class limit allows one number more", "src/lib/cons.fs",
     "2dup u< if 2drop drop true else - u> then ;", "2dup u< if 2drop drop true else - 1+ u> then ;"),
    # The review of 2026-11-03 (issues 1-4).
    ("a set over a sealed extension is accepted (three tiers)", "src/lib/cons.fs",
     "dup cons-sealed? over cons-table htab-live? and swap cons-under @ 0= and ;",
     "dup cons-sealed? swap cons-table htab-live? and ;"),
    ("a find counts itself in a frozen table", "src/lib/htab.fs",
     ": htab-tick ( addr htab -- ) htab-frozen? if drop else 1 swap +! then ;",
     ": htab-tick ( addr htab -- ) drop 1 swap +! ;"),
    ("sealing does not freeze the table", "src/lib/cons.fs",
     "true over cons-sealed ! cons-table htab-freeze outcome-ok ;",
     "true swap cons-sealed ! outcome-ok ;"),
    ("a text from the own byte slab keeps its old address", "src/lib/cons.fs",
     "  dup cons-key-base @ dup 0< if 2drop exit then over cons-bytes slab-at\n"
     "  swap cons-key cell+ ! ;", "  drop ;"),
    ("a class's slab limit is not clamped to what a cell addresses", "src/lib/cons.fs",
     "  cons-class @ class-unit @ slab-limit-max swap spare+ min ;", "  drop cons-spare + ;"),
    ("a bound variable's index is compared after 1+", "src/core/compact-exprs.fs",
     ": bvar-fits? ( index -- flag ) range-max u< ;", ": bvar-fits? ( index -- flag ) 1+ range-max u> 0= ;"),
    ("a list's span wraps instead of saturating", "src/lib/pools.fs",
     "u32@ dup u32-mask <> if 1+ then ;", "u32@ 1+ ;"),
    ("a set whose numbers pass its limit still commits", "src/lib/cons.fs",
     "2dup u< if 2drop drop true else - u> then ;", "- u> ;"),
]


def run(cmd, cwd, seconds):
    try:
        done = subprocess.run(cmd, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=seconds)
        return done.returncode, done.stdout.decode(errors="replace")
    except subprocess.TimeoutExpired:
        return "timeout", ""


def checks_fail(tree):
    """The first check that fails on the tree, or None."""
    for test in UNIT_TESTS:
        code, out = run([GFORTH, test], tree, 120)
        if code != 0 or "INCORRECT" in out or "WRONG NUMBER" in out:
            return test
    for export in EXPORTS:
        code, out = run(["bash", "tests/core/compact-verify.sh", export, GFORTH, "60"], tree, 150)
        if code != 0:
            return "round trip of " + export
    return None


def main():
    verbose = "-v" in sys.argv
    with tempfile.TemporaryDirectory(prefix="compact-faults-") as tmp:
        base = pathlib.Path(tmp) / "tree"
        shutil.copytree(ROOT / "src", base / "src")
        shutil.copytree(ROOT / "tests", base / "tests")
        if checks_fail(base):
            raise SystemExit("the checks fail without a planted fault: " + checks_fail(base))
        caught = 0
        for what, rel, text, change in FAULTS:
            path = base / rel
            original = path.read_text()
            if original.count(text) != 1:
                raise SystemExit(f"fault text not found exactly once in {rel}: {text!r}")
            path.write_text(original.replace(text, change))
            failing = checks_fail(base)
            path.write_text(original)
            if failing:
                caught += 1
                if verbose:
                    print(f"caught: {what} ({failing})")
            else:
                print(f"NOT CAUGHT: {what}")
        print(f"{caught} of {len(FAULTS)} planted faults caught by the compact store's checks.")
        if caught != len(FAULTS):
            sys.exit(1)


if __name__ == "__main__":
    main()
