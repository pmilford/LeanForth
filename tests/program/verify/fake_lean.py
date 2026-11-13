#!/usr/bin/env python3
"""A stand-in for pinned Lean 4.35.0, its exporter and LeanForth's checker, for the fast
tests of leanforth verify (tests/program/test_program_verify.py). Untrusted test tool:
the driver never chooses it; a test names it as LEAN and LEANEXPORT, and replaces the
driver's checker command (program_receipt.LEANFORTH) inside its own process.

Usage (as each tool is called):
  fake_lean.py --version | --githash | --print-prefix
  fake_lean.py -DwarningAsError=true -o OUT.olean FILE.lean    as Lean compiling FILE
  fake_lean.py export MODULE -- NAME...                         as leanexport (LEANEXPORT)
  fake_lean.py leanforth version | check --json [OPTION]... EXPORT    as bin/leanforth

What it does is set by VERIFY_FAKE, a JSON object (every member optional):
  version    the Lean version it reports (default "4.35.0")
  lean       "ok"; "fail" (exit 1 with an error); "sleep" (sleep 30 s); "mutate" (print
             the program back with one line changed); "no-axioms" (no #print axioms lines);
             "touch" (append a line to the file it compiles); "no-post" (no printed post)
  axioms     {short theorem name: [axioms]} as Lean reports them (default propext,
             Quot.sound for every theorem)
  export     "ok"; "fail" (exit 1); "sleep"; "no-manifest" (an export export.sh's
             manifest writer refuses)
  check      LeanForth's check: "ok" (every declaration accepted; the default),
             "no-report", "invalid-read", "stopped", "not-run", "touch" (append a line
             to the export it checks)
  reportVersion  the check report's schemaVersion (default "0.4")
  snapshot   true: the report has a snapshot member (a development run's)
  extra      [names]: declarations of the export besides the generator's (accepted)
  drop       [short names]: the generator's program or post left out of the report
  verdicts   {short theorem name: verdict} for the theorems (default accepted; "absent":
             the report does not list it)
  bits       {short theorem name: axiomBits} for accepted theorems (default 5)
  notProvedBy  {short theorem name: [axioms outside the allowlist]}
  other      the verdict of a declaration of the export that is not a theorem
  exit       LeanForth's exit status (default: 0 when every verdict is accepted, else 1)
As Lean it prints the program back: the IR file the generated file's header names,
without source locations, the way the model's render prints it. As the checker it
names the theorems of the obligations file beside the export.
"""
import json
import os
from pathlib import Path
import re
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
FAKE = json.loads(os.environ.get("VERIFY_FAKE", "{}"))
COUNTS = ("accepted", "skipped", "rejected", "unknown", "unsupported", "invalid", "exhausted",
          "full", "notChecked")


def theorems(lean_text):
    """(namespace, short theorem names) of a generated obligations file."""
    spaces = re.findall(r"^namespace (\w+)$", lean_text, re.M)
    return spaces[-1], re.findall(r"^#print axioms (\S+)$", lean_text, re.M)


def compile_lean(args):
    out, source = Path(args[args.index("-o") + 1]), Path(args[-1])
    behaviour = FAKE.get("lean", "ok")
    if behaviour == "sleep":
        time.sleep(30)
    if behaviour == "fail":
        print(f"{source}:1:0: error: unsolved goals")
        return 1
    text = source.read_text(encoding="utf-8")
    if behaviour == "touch":
        with open(source, "a", encoding="utf-8") as file:
            file.write("-- changed\n")
    ir = re.search(r"^  \S+ with (\S+) \(sha256", text, re.M).group(1)
    name, names = theorems(text)
    lines = [re.sub(r" @\d+:\d+$", "", line) for line in
             (ROOT / ir).read_text(encoding="utf-8").splitlines()]
    if behaviour == "mutate":
        lines[-2] = lines[-2].replace("min", "max") + " "
    print("\n".join([f"vc-program {name}", *lines, "vc-program-end"]))
    if behaviour != "no-post" and "vc-post-begin" in text:
        print(f"vc-post-begin\ndef ProgramVC.{name}.post : Cells → List Int → Prop :=\n"
              "fun c out => True\nvc-post-end")
        print(f"vc-statement-begin\nProgramVC.{name}.{names[-1]} (c : Cells) (pre1 : True) : "
              "True\nvc-statement-end")
    if behaviour != "no-axioms":
        for short in names:
            axioms = FAKE.get("axioms", {}).get(short, ["propext", "Quot.sound"])
            print(f"'ProgramVC.{name}.{short}' depends on axioms: [{', '.join(axioms)}]")
    out.write_bytes(b"")
    return 0


def export():
    behaviour = FAKE.get("export", "ok")
    if behaviour == "sleep":
        time.sleep(30)
    if behaviour == "fail":
        print("leanexport: unknown declaration", file=sys.stderr)
        return 1
    if behaviour == "no-manifest":
        sys.stdout.write("not an export\n")
        return 0
    sys.stdout.write((ROOT / "tests" / "cli" / "unfold.ndjson").read_text(encoding="utf-8"))
    return 0


def declaration(index, name, verdict, bits=5, not_proved=()):
    entry = {"index": index, "name": name, "verdict": verdict, "fuel": 10}
    if verdict == "accepted":
        entry.update(axiomBits=bits, notProved=bool(bits & 8))
        if not_proved:
            entry["notProvedBy"] = list(not_proved)
    return entry


def check(export_path):
    behaviour = FAKE.get("check", "ok")
    if behaviour == "no-report":
        print("internal fault: the run stopped", file=sys.stderr)
        return 5
    if behaviour == "touch":
        with open(export_path, "a", encoding="utf-8") as file:
            file.write("\n")
    name, names = theorems((export_path.parent / "obligations.lean").read_text(encoding="utf-8"))
    entries = [declaration(0, "ProgramIR.run", FAKE.get("other", "accepted"))]
    for short in ("program", "post"):
        if short not in FAKE.get("drop", ()):
            entries.append(declaration(len(entries), f"ProgramVC.{name}.{short}", "accepted"))
    for extra in FAKE.get("extra", ()):
        entries.append(declaration(len(entries), extra, "accepted"))
    for short in names:
        verdict = FAKE.get("verdicts", {}).get(short, "accepted")
        if verdict != "absent":   # a theorem the report does not list
            entries.append(declaration(
                len(entries), f"ProgramVC.{name}.{short}", verdict,
                FAKE.get("bits", {}).get(short, 5), FAKE.get("notProvedBy", {}).get(short, ())))
    counts = {key: 0 for key in COUNTS}
    for entry in entries:
        counts["notChecked" if entry["verdict"] == "not-checked" else entry["verdict"]] += 1
    counts = {"declarations": len(entries), **counts,
              "notProved": sum(e.get("notProved", False) for e in entries)}
    exit_status = FAKE.get("exit", 0 if counts["accepted"] == len(entries) else 1)
    report = {"schema": "leanforth-check-report",
              "schemaVersion": FAKE.get("reportVersion", "0.4"),
              "read": {"outcome": "invalid" if behaviour == "invalid-read" else "ok"},
              "run": "not-run" if behaviour == "not-run" else "invalid"
              if behaviour == "stopped" else "ok",
              "stopped": behaviour == "stopped", "declarations": entries, "counts": counts,
              "exitStatus": 4 if behaviour == "invalid-read" else exit_status}
    if FAKE.get("snapshot"):
        report["snapshot"] = {"layers": 1}
    print(json.dumps(report))
    return report["exitStatus"]


def main(args):
    if args == ["--version"]:
        print(f"Lean (version {FAKE.get('version', '4.35.0')}, x86_64-unknown-linux-gnu, "
              f"commit {COMMIT}, Release)")
    elif args == ["--githash"]:
        print(COMMIT)
    elif args == ["--print-prefix"]:
        print(HERE)
    elif "-o" in args:
        return compile_lean(args)
    elif args[:1] == ["leanforth"] and args[1:] == ["version"]:
        print("leanforth 0.1.0-dev")
    elif args[:3] == ["leanforth", "check", "--json"]:
        return check(Path(args[-1]))
    else:
        return export()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
