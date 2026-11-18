#!/usr/bin/env python3
"""S2's tactics against pinned Lean (plan S2, branch s2-tactics;
src/front/tactic-induction.fs, tactic-rewrite.fs, kabstract.fs,
meta-check.fs; docs/design/S2_INTERFACE.md 4, 5, 9 and appendix G).

1. FE1's rewriting form, the nested induction, the owner's proof set and
   merge B's midpoint, n + 0 = n by Eq.refl and by rfl (FILES) through
   `bin/leanforth check --env tests/front/s2-slice.ndjson --elab-data
   tests/front/s2-slice.elab.ndjson --steps -`: exit 0, each theorem
   accepted with no axiom; their types and values, dumped by
   tests/front/elab-dump.fs (s2-dump), equal pinned Lean's node for node
   (tests/front/s2-proofs.golden, the output of tests/front/s2-proofs.lean);
   the step log after the report (branch s2-steps, front/step-log.fs):
   every line valid by schemas/tactic-steps-1.schema.json, each header's
   count its step lines, the lines equal tests/front/s2-steps.golden
   (LeanForth's own log, reviewed; --write-steps writes it again); with
   --jobs 2 and with --steps FILE the same lines; a wrong proof (exit 4)
   writes none; --steps with an export is refused (exit 4).
2. The wrong proofs (WRONG, twins of tests/front/s2-wrong.lean's): exit 4,
   the error code and Lean's first message (the first lines of the error,
   as LeanForth prints them); the proofs not supported yet (UNSUPPORTED):
   exit 2 and the code.
3. No file under src/kernel/ or src/import/ names the smart-unfolding
   marker (core/annotations.fs, S2 merge B) outside a comment.
4. tests/front/s2-units.fs (kabstract, Meta.check) and s2-sweeps.fs (the
   heap refusing each allocation of 01-zero-add-rw.lf's run, isDefEq's
   fuel at each limit): exit 0, no failed test.
A harness self-test first checks that a changed golden line is told apart.
With --lean: pinned Lean writes the golden again (--write-golden keeps it)
and it must be unchanged, and pinned Lean refuses each wrong twin with the
message the LeanForth file must print.

Usage: GFORTH=... python3 tests/front/check_s2.py [--write-steps]
       GFORTH=... python3 tests/front/check_s2.py --tactics   (1 and 2 only: the
         planted faults' quick test, without the step log's extra runs and 4)
       GFORTH=... python3 tests/front/check_s2.py --steps-of FILE  (one log)
       LEAN=... python3 tests/front/check_s2.py --lean [--write-golden]
"""
import json
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
LIMIT = 600
SLICE = "tests/front/s2-slice.ndjson"
DATA = "tests/front/s2-slice.elab.ndjson"
GOLDEN = ROOT / "tests/front/s2-proofs.golden"
STEPS_GOLDEN = ROOT / "tests/front/s2-steps.golden"
sys.path.insert(0, str(ROOT / "tests/support"))
from schema_subset import Validator, load_strict  # noqa: E402
STEPS_SCHEMA = Validator(load_strict((ROOT / "schemas/tactic-steps-1.schema.json").read_text()))
# Each file and the theorems it declares, in order.
FILES = [("tests/front/01-zero-add-rw.lf", ["zero_add''"]),
         ("tests/front/04-nested-ih.lf", ["zero_add_nested"]),
         ("tests/front/ps-succ-add.lf", ["ps_succ_add"]),
         ("tests/front/ps-add-comm.lf", ["ps_zero_add", "ps_succ_add", "ps_add_comm"]),
         ("tests/front/ps-mul-add.lf", ["ps_add_assoc", "ps_mul_add"]),
         ("tests/front/ps-length-append.lf", ["ps_zero_add", "ps_succ_add",
                                              "ps_length_append"]),
         # S2 merge B's midpoint (smart unfolding: n + 0 unfolds to n).
         ("tests/front/00-add-zero.lf", ["add_zero'"]),
         ("tests/front/02-add-zero-rfl.lf", ["add_zero'"])]
# A file whose theorem has another name in tests/front/s2-proofs.lean,
# which declares both add_zero' forms.
ALIASES = {"tests/front/02-add-zero-rfl.lf": {"add_zero'": "add_zero_rfl'"}}
ADD_ZERO_RFL = ("Tactic `rfl` failed: The left-hand side\n  n + 0\nis not definitionally equal "
                "to the right-hand side\n  n + 1\n\nn : Nat\n\u22a2 n + 0 = n + 1")
# The wrong twins: file, code, Lean's message as LeanForth prints it.
GOAL = "case succ\nk : Nat\nih : 0 + k = k\n\u22a2 0 + (k + 1) = k + 1"
PLAIN = ("case zero\n\u22a2 0 + 0 = 0\n\ncase succ\nn\u271d : Nat\na\u271d : 0 + n\u271d = n\u271d\n"
         "\u22a2 0 + (n\u271d + 1) = n\u271d + 1")
WRONG = [("tests/front/s2w-pattern.lf", 215,
          "Tactic `rewrite` failed: Did not find an occurrence of the pattern",
          "  ?n * Nat.succ ?m\nin the target expression\n  0 + (k + 1) = k + 1\n\n" + GOAL),
         ("tests/front/s2w-alt-name.lf", 206, "Invalid alternative name `suc`: Expected `succ`",
          ""),
         ("tests/front/s2w-alt-missing.lf", 207, "Alternative `succ` has not been provided", ""),
         ("tests/front/s2w-alt-twice.lf", 213, "Duplicate alternative name `zero`", ""),
         ("tests/front/s2w-alt-names.lf", 208,
          "Too many variable names provided at alternative `succ`: 3 provided, but 2 expected",
          ""),
         ("tests/front/s2w-not-eq.lf", 218,
          "Invalid rewrite argument: Expected an equality or iff proof or definition name, "
          "but `k` is a value of type", "  Nat"),
         ("tests/front/s2w-rw-unsolved.lf", 89, "unsolved goals", "case succ\nk : Nat"),
         ("tests/front/s2w-induction-plain.lf", 89, "unsolved goals", PLAIN),
         ("tests/front/s2w-rw-empty.lf", 89, "unsolved goals", "n : Nat\n\u22a2 0 + n = n"),
         ("tests/front/s2w-add-zero-rfl.lf", 97, ADD_ZERO_RFL, "")]
# Forth unit tests and resource sweeps of S2's words (tester.fs).
UNITS = ["tests/front/s2-units.fs", "tests/front/s2-sweeps.fs"]
# Proofs LeanForth does not support yet: exit 2, the code and its text.
UNSUPPORTED = [("tests/front/s2w-rw-definition.lf", 99, "not supported yet: this case of the tactic"),
               # Lean tries a coercion (CoeT's instance search) before its type
               # mismatch: plan FE4 (w_add_zero in tests/front/s2-wrong.lean).
               ("tests/front/s2w-add-zero.lf", 131, "not supported yet: a coercion")]
# Pinned Lean's messages for the same proofs (tests/front/s2-wrong.lean),
# where its printer and LeanForth's agree (Lean prints (0 + k).succ,
# LeanForth Nat.succ (0 + k): plan 8.6).
LEAN_WRONG = ["Tactic `rewrite` failed: Did not find an occurrence of the pattern\n"
              "  ?n * Nat.succ ?m\nin the target expression\n  0 + (k + 1) = k + 1\n\n" + GOAL,
              "Invalid alternative name `suc`: Expected `succ`",
              "Alternative `succ` has not been provided",
              "Duplicate alternative name `zero`",
              "Too many variable names provided at alternative `succ`: 3 provided, but 2 expected",
              "Invalid rewrite argument: Expected an equality or iff proof or definition name, "
              "but `k` is a value of type\n  Nat",
              "unsolved goals\ncase succ\nk : Nat",
              "unsolved goals\n" + PLAIN,
              "unsolved goals\nn : Nat\n\u22a2 0 + n = n",
              ADD_ZERO_RFL,
              "Type mismatch\n  Eq.refl n\nhas type\n  n = n\nbut is expected to have type\n"
              "  n + 0 = n + 1"]


class Failure(Exception):
    pass


def run(args):
    return subprocess.run(args, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                          text=True, timeout=LIMIT, env=dict(os.environ, GFORTH=GFORTH))


def check(path, *more):
    done = run(["bin/leanforth", "check", "--env", SLICE, "--elab-data", DATA, *more, path])
    return done.returncode, done.stdout + done.stderr


def step_lines(out):
    """The step log's lines: those after the report that are JSON objects."""
    return [line for line in out.splitlines() if line.startswith("{")]


def check_log(path, lines):
    """Schema, counts: each header's steps, then that many step lines."""
    expected = 0
    for line in lines:
        record = load_strict(line)
        errors = list(STEPS_SCHEMA.errors(record))
        if errors:
            raise Failure(f"{path}: step log line not valid: {errors}\n  {line}")
        if "tactic_steps" in record:
            if expected:
                raise Failure(f"{path}: a header where {expected} more steps are due")
            expected, number = record["tactic_steps"]["steps"], 0
            continue
        number += 1
        if not expected or record["step"] != number or record["parent"] >= number:
            raise Failure(f"{path}: step {record['step']} out of order\n  {line}")
        expected -= 1
    tactics = ":= by" in (ROOT / path).read_text(encoding="utf-8")
    if expected or bool(lines) != tactics:
        raise Failure(f"{path}: a step log missing, cut short or for no tactic proof: {lines}")


def dump(path):
    done = run([GFORTH, "tests/front/elab-dump.fs", "-e", f's" {path}" s2-dump bye'])
    if done.returncode != 0:
        raise Failure(f"elab-dump.fs {path}: exit {done.returncode}\n{done.stdout}{done.stderr}")
    return [line for line in done.stdout.splitlines() if " type " in line or " value " in line]


def aliased(path, line):
    """A dumped line under the name s2-proofs.lean gives its theorem."""
    name, rest = line.split(" ", 1)
    return ALIASES.get(path, {}).get(name, name) + " " + rest


def golden():
    return {line.split(" ", 2)[0] + " " + line.split(" ", 2)[1]: line
            for line in GOLDEN.read_text(encoding="utf-8").splitlines()}


def self_test(want):
    if len(want) != 20:
        raise Failure(f"harness self-test: {len(want)} golden lines, expected 20")
    wrong = dict(want)
    key = next(iter(wrong))
    wrong[key] = wrong[key].replace("#0", "#1", 1)
    if wrong == want:
        raise Failure("harness self-test: a changed line is not told apart")
    schema_self_test()


def schema_self_test():
    """The step schema's names ([format], owner 2026-11-17): any well-formed Lean or Mathlib
    tactic name and any non-blank word validate; a malformed name or a blank word does not."""
    step = {"goal_before": None, "goals_after": [], "parent": 0, "source": "1:1", "step": 1,
            "tactic": "rfl", "word": "by-rfl"}
    for tactic, word in (("norm_num", "by-norm-num"), ("exact?", "by-exact?"), ("cases'", "|")):
        if list(STEPS_SCHEMA.errors(dict(step, tactic=tactic, word=word))):
            raise Failure(f"harness self-test: the step schema refuses tactic {tactic!r}")
    for tactic, word in (("Norm_num", "by-rfl"), ("norm num", "by-rfl"), ("?rfl", "by-rfl"),
                         ("rfl", ""), ("rfl", "by rfl")):
        if not list(STEPS_SCHEMA.errors(dict(step, tactic=tactic, word=word))):
            raise Failure(f"harness self-test: the step schema takes {tactic!r} {word!r}")


def check_files(want):
    logs = []
    for path, names in FILES:
        code, out = check(path, "--steps", "-")
        if code != 0:
            raise Failure(f"{path}: exit {code}\n{out}")
        check_log(path, step_lines(out))
        logs += step_lines(out)
        for name in names:
            if f"\n{name}: accepted; axioms: none" not in "\n" + out:
                raise Failure(f"{path}: {name} not accepted with no axiom\n{out}")
        for line in dump(path):
            line = aliased(path, line)
            key = " ".join(line.split(" ", 2)[:2])
            if want.get(key) != line:
                raise Failure(f"{path}: {key} differs from pinned Lean's:\n  LeanForth: {line}\n"
                              f"  Lean:      {want.get(key)}")
    return logs


def check_steps(logs):
    """The log against its golden file; --jobs 2, --steps FILE, a wrong
    proof and an export."""
    if "--write-steps" in sys.argv:
        STEPS_GOLDEN.write_text("\n".join(logs) + "\n", encoding="utf-8")
    if logs != STEPS_GOLDEN.read_text(encoding="utf-8").splitlines():
        raise Failure("the step log differs from tests/front/s2-steps.golden "
                      "(python3 tests/front/check_s2.py --write-steps after a review)")
    path = FILES[1][0]
    alone = [line for line in logs if line in step_lines(check(path, "--steps", "-")[1])]
    code, out = check(path, "--jobs", "2", "--steps", "-")
    if code != 0 or step_lines(out) != alone:
        raise Failure(f"{path} with --jobs 2: exit {code}, another step log\n{out}")
    with tempfile.TemporaryDirectory() as work:
        log = pathlib.Path(work) / "steps.ndjson"
        code, out = check(path, "--steps", str(log))
        if code != 0 or step_lines(out) or log.read_text(encoding="utf-8").splitlines() != alone:
            raise Failure(f"{path} with --steps FILE: exit {code}, another step log\n{out}")
    code, out = check(WRONG[0][0], "--steps", "-")
    if code != 4 or step_lines(out):
        raise Failure(f"{WRONG[0][0]}: exit {code}, a step log for a wrong proof\n{out}")
    done = run(["bin/leanforth", "check", "--steps", "-", SLICE])
    if done.returncode != 4 or "--steps goes only with a LeanForth text" not in done.stdout:
        raise Failure(f"--steps with an export: exit {done.returncode}\n{done.stdout}")


def check_wrong():
    for path, number, message, detail in WRONG:
        code, out = check(path)
        line = f"error {number} at "
        if code != 4 or line not in out or message not in out or detail not in out:
            raise Failure(f"{path}: exit {code}, expected 4 with {line}{message!r} "
                          f"and {detail!r}\n{out}")
    for path, number, message in UNSUPPORTED:
        code, out = check(path)
        if code != 2 or f"error {number} at " not in out or message not in out:
            raise Failure(f"{path}: exit {code}, expected 2 with error {number}, {message!r}\n{out}")


MATCH = '{"mdata":{"entries":[[["sunfoldMatch"],{"bool":true}]],"expr":'
# An inert body (format 3.1, MATHLIB_FRONT.md O1) through the whole run:
# Nat.add's first sunfoldMatch made an inert node in a copy of the data,
# read with --no-manifest (the manifest binds the real data). A proof that
# smart-unfolds Nat.add answers unsupported; one that does not is accepted.
INERT_RUNS = [("tests/front/02-add-zero-rfl.lf", 2, "error 93 at "),
              ("tests/front/s2w-add-zero-rfl.lf", 2, ""),
              ("tests/front/09-zero-add-rfl.lf", 0, "")]


def inert_data():
    """The slice's data with Nat.add's body holding an inert node, as format 3.1."""
    head, body = (ROOT / DATA).read_text(encoding="utf-8").split("\n", 1)
    lines = body.split("\n")
    i = next(i for i, x in enumerate(lines) if x.startswith('{"sunfold":{') and
             '"name":["Nat","add"],' in x and MATCH in x)
    expr = lines[i].split(MATCH, 1)[1].split("}", 1)[0]
    lines[i] = lines[i].replace(MATCH + expr + "}}", f'{{"inert":{{"expr":{expr},"key":"save_info"}}}}', 1)
    body = "\n".join(lines)
    header = json.loads(head)
    header["elab_data"].update(format_version="3.1",
                               records_sha256=hashlib.sha256(body.encode()).hexdigest())
    return json.dumps(header, sort_keys=True, separators=(",", ":")) + "\n" + body


def check_inert():
    with tempfile.TemporaryDirectory() as work:
        data = pathlib.Path(work) / "inert.elab.ndjson"
        data.write_text(inert_data(), encoding="utf-8")
        for path, want, text in INERT_RUNS:
            done = run(["bin/leanforth", "check", "--no-manifest", "--env", SLICE,
                        "--elab-data", str(data), path])
            out = done.stdout + done.stderr
            if done.returncode != want or text not in out:
                raise Failure(f"inert body, {path}: exit {done.returncode}, expected {want} "
                              f"with {text!r}\n{out}")


def check_units():
    for path in UNITS:
        done = run([GFORTH, path])
        if done.returncode != 0 or "INCORRECT" in done.stdout + done.stderr \
                or "WRONG" in done.stdout + done.stderr:
            raise Failure(f"{path}: exit {done.returncode}\n{done.stdout}{done.stderr}")


# The smart-unfolding marker (src/core/annotations.fs, core tag 17; S2
# merge B) is front-end only: no kernel or importer file may name it.
MARKER = re.compile(r"lf-annot|lf-tag-annotation|annotations\.fs")
BOUNDARY = ["src/kernel", "src/import"]


def marker_lines(texts):
    """(path, line number) of each line that names the marker, comment
    lines (a backslash first) left out."""
    return [(path, n) for path, text in texts for n, line in enumerate(text.splitlines(), 1)
            if not line.lstrip().startswith("\\") and MARKER.search(line)]


def check_boundary():
    planted = [("x.fs", ": t ( -- ) lf-tag-annotation drop ;"), ("y.fs", "\\ annotations.fs")]
    if marker_lines(planted) != [("x.fs", 1)]:
        raise Failure("harness self-test: a marker named in code is not told apart from a comment")
    texts = [(str(f.relative_to(ROOT)), f.read_text(encoding="utf-8"))
             for d in BOUNDARY for f in sorted((ROOT / d).rglob("*.fs"))]
    found = marker_lines(texts)
    if found or not texts:
        raise Failure(f"the smart-unfolding marker named under {BOUNDARY}: {found}")
    return len(texts)


def check_lean(write):
    done = run([LEAN, "-DwarningAsError=true", "tests/front/s2-proofs.lean"])
    if done.returncode != 0:
        raise Failure(f"s2-proofs.lean: exit {done.returncode}\n{done.stdout}{done.stderr}")
    if write:
        GOLDEN.write_text(done.stdout, encoding="utf-8")
    elif done.stdout.splitlines() != GOLDEN.read_text(encoding="utf-8").splitlines():
        raise Failure("s2-proofs.lean: pinned Lean's output is not s2-proofs.golden")
    done = run([LEAN, "-DwarningAsError=true", "tests/front/s2-wrong.lean"])
    out = done.stdout + done.stderr
    missing = [text for text in LEAN_WRONG if text not in out]
    if done.returncode == 0 or missing:
        raise Failure(f"s2-wrong.lean: exit {done.returncode}, missing {missing}\n{out}")


def steps_of(path):
    """One file's step log against its part of the golden file (the faults'
    quick test)."""
    code, out = check(path, "--steps", "-")
    lines = step_lines(out)
    check_log(path, lines)
    if code != 0 or "\n".join(lines) not in STEPS_GOLDEN.read_text(encoding="utf-8"):
        raise Failure(f"{path}: exit {code}, a step log not in {STEPS_GOLDEN.name}\n{out}")
    print(f"check_s2 --steps-of {path}: {len(lines)} lines valid and as golden")


def main():
    if "--steps-of" in sys.argv:
        steps_of(sys.argv[sys.argv.index("--steps-of") + 1])
        return
    want = golden()
    self_test(want)
    if "--lean" in sys.argv:
        check_lean("--write-golden" in sys.argv)
        print(f"check_s2 --lean: s2-proofs.lean gives {GOLDEN.name}; s2-wrong.lean gives "
              f"the {len(LEAN_WRONG)} messages; harness self-test passed")
        return
    files = check_boundary()
    logs = check_files(want)
    check_wrong()
    check_inert()
    if "--tactics" in sys.argv:
        print(f"check_s2 --tactics: {len(FILES)} files accepted as pinned Lean's, "
              f"{len(WRONG)} wrong proofs refused with Lean's messages")
        return
    check_steps(logs)
    check_units()
    print(f"check_s2: no kernel or importer file ({files}) names the smart-unfolding marker; "
          f"{len(FILES)} files accepted, their {len(want)} type and value lines "
          f"equal pinned Lean's node for node, their step logs valid and as golden; "
          f"{len(WRONG)} wrong proofs refused with Lean's "
          f"messages; {len(UNSUPPORTED)} unsupported; an inert body unused in "
          f"{len(INERT_RUNS)} runs; {len(UNITS)} unit files pass; "
          f"harness self-test passed")


if __name__ == "__main__":
    try:
        main()
    except (Failure, subprocess.TimeoutExpired) as exc:
        print(f"check_s2: {exc}", file=sys.stderr)
        sys.exit(1)
