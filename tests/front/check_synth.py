#!/usr/bin/env python3
"""LeanForth's instance table against pinned Lean 4.35.0 on all of Init
(plans FE1e2 and FE1e3; docs/design/S1_INTERFACE.md §9, FE1E §3.2-§4).

Usage: python3 tests/front/check_synth.py EXPORT DATA
  EXPORT  Init's export (with its manifest beside it), DATA its
          elaboration data (scripts/export-elab.sh); tests/front/synth-init.sh
          makes both. Environment: LEAN (pinned Lean), GFORTH.

1. Every Init instance's class and keys, recomputed by LeanForth from its
   type (src/front/instances.fs, lf-inst-check), equal the data's: no
   instance is refused (error 112 or 113). Those whose check cannot finish
   (unverified: a definition the keys would unfold, plan S2) are counted
   and listed; S1's six tried candidates must be verified.
2. For each problem below, pinned Lean's getInstances list (the root
   goal's `[Meta.synthInstance.instances]` trace of `#synth`) equals
   LeanForth's lf-inst-candidates, name for name, in order: the stuck
   problems too, whose lists Lean prints before its stuck exit.
Exit status 0 when all agree, 1 otherwise.
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROBLEMS = [  # (LeanForth's label, Lean's #synth argument)
    ("OfNat ?T 0", "OfNat _ (nat_lit 0)"),
    ("OfNat Nat 0", "OfNat Nat (nat_lit 0)"),
    ("HAdd ?a ?b ?c", "HAdd _ _ _"),
    ("HAdd Nat Nat ?c", "HAdd Nat Nat _"),
    ("Add ?a", "Add _"),
    ("Add Nat", "Add Nat"),
    ("Mul Nat", "Mul Nat"),
    ("Sub Nat", "Sub Nat"),
    ("LE Nat", "LE Nat"),
    ("LT Nat", "LT Nat"),
    ("Inhabited Nat", "Inhabited Nat"),
    ("BEq Nat", "BEq Nat"),
    ("HMul Nat Nat ?c", "HMul Nat Nat _"),
]
TRIED = ["Lean.Grind.CommRing.OfCommSemiring.instOfNatQ", "instOfNatNat",
         "String.instHAddCharRaw", "instHAdd", "Lean.Grind.CommRing.OfCommSemiring.instAddQ",
         "instAddNat"]
LIMIT = 1800


def lean_lists():
    """Pinned Lean's root candidate list for each problem, by #synth line."""
    lean = os.environ.get("LEAN", str(ROOT / ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"))
    text = "set_option trace.Meta.synthInstance true\n" + "".join(
        f"#synth {arg}\n" for _, arg in PROBLEMS)
    with tempfile.TemporaryDirectory() as work:
        source = Path(work) / "synth.lean"
        source.write_text(text)
        done = subprocess.run([lean, "-j", "2", str(source)], capture_output=True, text=True,
                              stdin=subprocess.DEVNULL, timeout=LIMIT)
    # Each #synth's root search is a trace node at column 0; the first
    # instances list inside it (perhaps wrapped over lines) is the root's.
    lists, taking, text = [], False, ""
    for row in done.stdout.splitlines():
        if row.startswith("[Meta.synthInstance] "):
            lists.append(None)
        elif "[Meta.synthInstance.instances] #[" in row and lists and lists[-1] is None:
            taking, text = True, row.split("#[", 1)[1]
        elif taking:
            text += " " + row.strip()
        if taking and "]" in text:
            taking = False
            lists[-1] = [n.strip().lstrip("@") for n in text.split("]", 1)[0].split(",")]
    return lists + [None] * (len(PROBLEMS) - len(lists))


def forth_report(export, data):
    gforth = os.environ.get("GFORTH", str(ROOT / ".tools/gforth/bin/gforth"))
    fast = Path(gforth).with_name("gforth-fast")
    if fast.exists():
        gforth = str(fast)
    done = subprocess.run([gforth, "tests/front/synth-init.fs", "-e",
                           f's" {export}" s" {data}" synth-init bye'], cwd=ROOT,
                          capture_output=True, text=True, stdin=subprocess.DEVNULL, timeout=LIMIT)
    if done.returncode != 0:
        sys.exit(f"check_synth: LeanForth failed: {done.stdout[-400:]} {done.stderr[-400:]}")
    return done.stdout.splitlines()


def main(argv):
    export, data = argv[1], argv[2]
    failures = []
    rows = forth_report(export, data)
    counts = {m.group(1): int(m.group(2)) for m in
              (re.match(r"checked (\S+) (\d+)$", r) for r in rows) if m}
    bad = [r.split()[1:] for r in rows if r.startswith("instance ")]
    refused = [b for b in bad if b[1] == "invalid"]
    if refused:
        failures.append(f"instances refused (class or keys differ): {refused[:10]}")
    tried_bad = [b for b in bad if b[0] in TRIED]
    if tried_bad:
        failures.append(f"a candidate S1 tries is not verified: {tried_bad}")
    print(f"Init instances checked: {sum(counts.values())}; " +
          ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))
    for name, why in bad:
        print(f"  not verified: {name} ({why})")
    ours = {}
    for r in rows:
        m = re.match(r"problem (.*?): (.*)$", r)
        if m:
            ours[m.group(1)] = [x.strip() for x in m.group(2).split(",") if x.strip()]
    same = 0
    for (label, _), theirs in zip(PROBLEMS, lean_lists()):
        mine = ours.get(label)
        if theirs is None or mine != theirs:
            failures.append(f"{label}: Lean {theirs} LeanForth {mine}")
        else:
            same += 1
    print(f"getInstances: {same} of {len(PROBLEMS)} problems give pinned Lean's candidates in order")
    for f in failures:
        print(f"FAIL: {f}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
