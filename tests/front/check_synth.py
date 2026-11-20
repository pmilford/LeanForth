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
   (unverified: a Meta step the keys need is not ported yet, such as
   inferType of a lambda-headed application or nested lambdas, plan FE1c, or
   a string literal's key, S5) are counted and listed; S1's six tried
   candidates must be verified.
2. For each problem below, pinned Lean's getInstances list (the root
   goal's `[Meta.synthInstance.instances]` trace of `#synth`) equals
   LeanForth's lf-inst-candidates, name for name, in order: the stuck
   problems too, whose lists Lean prints before its stuck exit.
3. For each search below (plan FE1e5, src/front/synth.fs), LeanForth's
   lf-synth-instance gives pinned Lean's #synth answer, node for node
   (pp.all without @), "none" for Lean's failure, "stuck" for its stuck
   exit, and tries Lean's candidates in Lean's order (the `apply` trace
   lines of the root search). A search LeanForth answers unsupported is
   a temporary gap only when GAPS names it with the plan row that closes
   it, and then the candidates it tried must begin Lean's list; any
   other difference fails.
Exit status 0 when all agree, 1 otherwise.
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
import pathlib
import functools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
import lean_pin  # noqa: E402  $LEAN or the pinned Lean, refused unrun when an elan proxy

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
    # Plan S3a-ops C1: found after reduceDT unfolds the reducible GT.gt, and the first
    # candidates of a numeral `*` (Lean.Omega.IntList.instHMulInt's keys unfold IntList).
    # Raw literals, as LeanForth's goal: elaborating `20 > 10` would trace OfNat searches first.
    ("Decidable (20 > 10)", "Decidable (@GT.gt Nat instLTNat (nat_lit 20) (nat_lit 10))"),
    ("HMul ?a ?b ?c", "HMul _ _ _"),
    ("Mul ?a", "Mul _"),
]
TRIED = ["Lean.Grind.CommRing.OfCommSemiring.instOfNatQ", "instOfNatNat",
         "String.instHAddCharRaw", "instHAdd", "Lean.Grind.CommRing.OfCommSemiring.instAddQ",
         "instAddNat"]
SEARCHES = PROBLEMS[:6] + [  # S1's six problems, then Init's answered in a few levels
    ("Mul Nat", "Mul Nat"), ("Sub Nat", "Sub Nat"), ("LE Nat", "LE Nat"), ("LT Nat", "LT Nat"),
    ("Inhabited Nat", "Inhabited Nat"), ("BEq Nat", "BEq Nat"),
    ("HMul Nat Nat ?c", "HMul Nat Nat _"), ("HSub Nat Nat ?c", "HSub Nat Nat _"),
    ("HPow Nat Nat ?c", "HPow Nat Nat _"), ("OfNat Nat 5", "OfNat Nat (nat_lit 5)"),
    ("Add Prop", "Add Prop"), ("OfNat Bool 0", "OfNat Bool (nat_lit 0)"),
    ("Nonempty Nat", "Nonempty Nat"), ("Mod Nat", "Mod Nat"), ("Div Nat", "Div Nat"),
    ("HMod Nat Nat ?c", "HMod Nat Nat _"), ("Max Nat", "Max Nat"), ("Min Nat", "Min Nat"),
    ("Inhabited Prop", "Inhabited Prop"), ("Inhabited Bool", "Inhabited Bool"),
    ("Pow Nat Nat", "Pow Nat Nat"), ("NatPow Nat", "NatPow Nat"), ("Neg Int", "Neg Int"),
    ("Add Int", "Add Int"),
]
OUT_PARAM = "plan S2 merge A: lazy delta (unification unfolds the out-parameter's outParam)"
GAPS = {  # search: the plan row that closes the gap (LeanForth answers unsupported until then)
    "HAdd Nat Nat ?c": OUT_PARAM, "HMul Nat Nat ?c": OUT_PARAM, "HSub Nat Nat ?c": OUT_PARAM,
    "HPow Nat Nat ?c": OUT_PARAM, "HMod Nat Nat ?c": OUT_PARAM,
    "BEq Nat": "plan S2 (whnf unfolds DecidableEq), then FE1e5b (a goal that is a pi: error 117)",
}
LIMIT = 1800


def lean_lists():
    """Pinned Lean's root candidate list for each problem, by #synth line."""
    lean = lean_pin.pinned_lean()
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


def lean_name(text):
    """The instance an apply trace line names: no @, no universe arguments."""
    return text.split(".{", 1)[0].split()[0].lstrip("@")


def lean_searches():
    """Pinned Lean's answer and tried candidates for each search, by #synth."""
    lean = lean_pin.pinned_lean()
    text = "set_option pp.all true\nset_option trace.Meta.synthInstance true\n" + "".join(
        f"#synth {arg}\n" for _, arg in SEARCHES)
    with tempfile.TemporaryDirectory() as work:
        source = Path(work) / "searches.lean"
        source.write_text(text)
        done = subprocess.run([lean, "-j", "2", str(source)], capture_output=True, text=True,
                              stdin=subprocess.DEVNULL, timeout=LIMIT)
    # Each #synth's root search is a trace node at column 0 (its first line
    # marks a stuck exit); its own lines are indented by exactly two spaces.
    found, result = [], None
    for row in done.stdout.splitlines():
        if row.startswith("[Meta.synthInstance] "):
            found.append({"result": "stuck" if "💥" in row else None, "tried": []})
            result = None
        elif not found:
            continue
        elif row.startswith("  [Meta.synthInstance.apply] "):
            found[-1]["tried"].append(lean_name(row.split(" apply ", 1)[1]))
            result = None
        elif row.startswith("  [Meta.synthInstance] result "):
            result = row.split(" result ", 1)[1].strip()
            found[-1]["result"] = "none" if result == "<not-available>" else result.replace("@", "")
        elif result is not None and row.startswith("   ") and "[Meta." not in row:
            found[-1]["result"] += " " + row.strip().replace("@", "")
        else:
            result = None
    return found + [None] * (len(SEARCHES) - len(found))


def compare_searches(rows, failures):
    ours = {}
    for r in rows:
        m = re.match(r"(synth|tried) (.*?): (.*)$", r)
        if m:
            ours.setdefault(m.group(2), {})[m.group(1)] = m.group(3).strip()
    same, gaps = 0, []
    for (label, _), theirs in zip(SEARCHES, lean_searches()):
        mine = ours.get(label, {})
        tried = [x.strip() for x in mine.get("tried", "").split(",") if x.strip()]
        result = mine.get("synth")
        if theirs is None:
            failures.append(f"{label}: no trace from pinned Lean")
        elif result == theirs["result"] and tried == theirs["tried"]:
            same += 1
        elif (result or "").startswith("unsupported") and label in GAPS \
                and theirs["tried"][:len(tried)] == tried:
            gaps.append(f"{label}: {result}, Lean {theirs['result']} ({GAPS[label]})")
        else:
            failures.append(f"search {label}: Lean {theirs['result']} after {theirs['tried']}; "
                            f"LeanForth {result} after {tried}")
    print(f"synthInstance: {same} of {len(SEARCHES)} searches give pinned Lean's answer "
          f"after the same candidates, {len(gaps)} known gaps")
    for g in gaps:
        print(f"  gap: {g}")


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
    compare_searches(rows, failures)
    for f in failures:
        print(f"FAIL: {f}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
