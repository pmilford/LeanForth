#!/usr/bin/env python3
"""Format 4 of the elaboration data (plan FE9, slice SD-a of docs/design/TACTIC_SIMP.md):
the writer's congr records and defeq tags, and the check reading them.

  python3 tests/front/test_simp_data.py [--write-fixtures]

1. The fixtures of tests/front/simp-data/ (read by tests/front/simp-data.fs, the reader's
   unit test, each with its expected refusal) are as this file writes them: format-4 data
   for the simp slice's export (tests/front/simp-slice.ndjson), hand-written: dite's,
   ite's and HSub.hSub's congruence lemmas (each one Lean's mkSimpCongrTheorem takes),
   Nat.add_zero's defeq tag, and one damaged file per refusal. --write-fixtures writes
   them.
2. The finisher (scripts/export_elab.py --format 4) on hand-made RAW against the simp
   slice: congr records kept with their function and lemma, sorted by function and rank
   (ite's rank 1 after its rank 0, though its text sorts first),
   left out without their function; refused for an export with the function but not the
   lemma, a RAW and a --format that disagree, a rank gap, hypotheses not increasing, a
   defeq tag of a definition.
3. bin/leanforth check on the simp slice with its real format-4 data (written by
   ELAB_FORMAT=4 scripts/export-elab.sh, 7 congr records, 33 defeq tags since simp slice
   SL1a-1 grew the slice) accepts
   tests/front/simp-data/sd-id.lf; with the good fixture too (the export's manifest copied
   without its binding); damaged fixtures refused with their codes and lines.
"""
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import export_elab  # noqa: E402

SLICE = ROOT / "tests/front/simp-slice.ndjson"
DATA = ROOT / "tests/front/simp-slice.elab.ndjson"
FIXTURES = ROOT / "tests/front/simp-data"
TEXT = FIXTURES / "sd-id.lf"
LEANFORTH = ROOT / "bin/leanforth"
LIMIT = int(os.environ.get("TEST_TIMEOUT", "600"))
HEAD = json.loads(DATA.read_text().split("\n", 1)[0])["elab_data"]


def text(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def congr(fun, name, hyps, rank, priority=1000):
    return text({"congr": {"fun": fun, "hyps": hyps, "name": name, "priority": priority,
                           "rank": rank}})


def defeq(name):
    return text({"tag": {"name": name, "tag": "defeq"}})


C_DITE = congr(["dite"], ["dite_congr"], [9, 10, 11], 0)
C_ITE = congr(["ite"], ["ite_congr"], [9, 10, 11], 0)
# Nat.succ_sub_succ_eq_sub: succ n - succ m = n - m, both sides HSub.hSub's call of six
# arguments, so Lean's mkSimpCongrTheorem takes it (no hypotheses: n and m are on the left).
C_SUB = congr(["HSub", "hSub"], ["Nat", "succ_sub_succ_eq_sub"], [], 0)
# ite_eq_left: (if c then a else b) = a; its right side is no call of ite, so Lean refuses it
# as a congr lemma (error 37). The slice has one lemma Lean takes per function, so the order
# and priority cases file it at rank 1, where the run's checks, made before the head, see it.
X_ITE1 = congr(["ite"], ["ite_eq_left"], [2], 1, 500)
T_ADD = defeq(["Nat", "add_zero"])
GOOD = [C_DITE, C_ITE, C_SUB, T_ADD]


def assemble(lines, version=4, drop=None, **counted):
    """A file for the simp slice holding lines, its header counting them."""
    body = "".join(r + "\n" for r in lines)
    counts = dict.fromkeys(export_elab.KINDS, 0)
    if version != 4:
        del counts["congr"]
        if version != "3.2":
            del counts["binder_kinds"]
    for line in lines:
        kind = next(iter(json.loads(line)))
        if kind in counts:
            counts[kind] += 1
    counts.update(counted)
    if drop:
        del counts[drop]
    head = dict(HEAD, format_version=version, records=counts,
                records_sha256=hashlib.sha256(body.encode()).hexdigest())
    return text({"elab_data": head}) + "\n" + body


def swap(old, new, records=GOOD):
    return [new if r == old else r for r in records]


# name: (file text, outcome, line, code), as tests/front/simp-data.fs expects them.
CASES = {
    "good": (assemble(GOOD), "ok", 0, 0),
    "plain32": (assemble([], "3.2"), "ok", 0, 0),
    "plain3": (assemble([], 3), "ok", 0, 0),
    "plain31": (assemble([], "3.1"), "ok", 0, 0),
    "v3-congr": (assemble(GOOD[:3], 3), "invalid", 2, 11),
    "v32-defeq": (assemble([T_ADD], "3.2"), "invalid", 2, 10),
    "v5": (assemble(GOOD, 5), "unsupported", 1, 7),
    "v41": (assemble(GOOD, "4.1"), "unsupported", 1, 7),
    "unknown-kind": (assemble(GOOD + ['{"simp":{"name":["ite_congr"]}}']), "invalid", 6, 11),
    "no-hyps": (assemble(swap(C_DITE, C_DITE.replace('"hyps":[9,10,11],', ""))),
                "invalid", 2, 10),
    "rank-text": (assemble(swap(C_DITE, C_DITE.replace('"rank":0', '"rank":"0"'))),
                  "invalid", 2, 10),
    "priority-big": (assemble(swap(C_DITE, C_DITE.replace("1000", "4294967296"))),
                     "unsupported", 2, 19),
    "name-unknown": (assemble(swap(C_DITE, C_DITE.replace('["dite_congr"]', '["no_such"]'))),
                     "invalid", 2, 12),
    "name-def": (assemble(swap(C_DITE, C_DITE.replace('["dite_congr"]', '["dite"]'))),
                 "invalid", 2, 14),
    "fun-unknown": (assemble(swap(C_DITE, C_DITE.replace('["dite"]', '["no_such"]'))),
                    "invalid", 2, 12),
    "twice": (assemble(swap(C_SUB, congr(["ite"], ["ite_congr"], [9], 1))), "invalid", 4, 47),
    "order-swap": (assemble([C_DITE, X_ITE1, C_ITE, T_ADD]), "invalid", 3, 48),
    "order-gap": (assemble(swap(C_SUB, X_ITE1.replace('"rank":1', '"rank":2'))),
                  "invalid", 4, 48),
    "order-split": (assemble([C_ITE, C_DITE, X_ITE1, T_ADD]), "invalid", 4, 48),
    "order-again": (assemble(swap(C_SUB, X_ITE1.replace('"rank":1', '"rank":0'))),
                    "invalid", 4, 48),
    "hyps-beyond": (assemble(swap(C_SUB, C_SUB.replace("[]", "[2]"))), "invalid", 4, 37),
    "fun-other": (assemble(swap(C_DITE, C_DITE.replace('["dite"]', '["Decidable","decide"]'))),
                  "invalid", 2, 37),
    "fun-swapped": (assemble([C_DITE.replace('["dite"]', '["ite"]'), C_ITE.replace('["ite"]', '["dite"]'),
                              C_SUB, T_ADD]), "invalid", 2, 37),
    "not-eq": (assemble(swap(C_SUB, congr(["ite"], ["of_eq_true"], [1], 1, 500))), "invalid", 4, 37),
    # Lean's funName: both sides call fun with as many arguments (re-check of simp-sd-a, A).
    "ite_eq_left": (assemble(swap(C_SUB, X_ITE1)), "invalid", 4, 37),
    "iff_self": (assemble(swap(C_SUB, congr(["Iff"], ["iff_self"], [], 0))), "invalid", 4, 37),
    "prio-rising": (assemble([C_DITE, C_ITE.replace("1000", "400"), X_ITE1, T_ADD]),
                    "invalid", 4, 48),
    # An equal priority continues the run: refused only at the head, past the run's checks.
    "prio-equal": (assemble(swap(C_SUB, X_ITE1.replace("500", "1000"))), "invalid", 4, 37),
    "hyps-down": (assemble(swap(C_DITE, C_DITE.replace("[9,10,11]", "[10,9,11]"))),
                  "invalid", 2, 37),
    "defeq-def": (assemble(GOOD + [defeq(["ite"])]), "invalid", 6, 14),
    "defeq-twice": (assemble(GOOD + [T_ADD]), "invalid", 6, 29),
    "tag-unknown": (assemble(GOOD + [T_ADD.replace('"defeq"', '"defeqs"')]), "invalid", 6, 10),
    "count-missing": (assemble(GOOD, drop="congr"), "invalid", 1, 10),
    "count-wrong": (assemble(GOOD, congr=2), "invalid", 5, 20),
}


def fail(message):
    print(f"test_simp_data.py: FAIL: {message}", file=sys.stderr)
    sys.exit(1)


def fixtures(write):
    for name, (data, _, _, _) in CASES.items():
        path = FIXTURES / f"{name}.elab.ndjson"
        if write:
            path.write_text(data, encoding="utf-8")
        elif not path.exists() or path.read_text(encoding="utf-8") != data:
            fail(f"{path.relative_to(ROOT)} is not as this file writes it (--write-fixtures)")


RAW_HEAD = text({"lean": {"githash": export_elab.LEAN_GITHASH,
                          "version": export_elab.LEAN_VERSION},
                 "modules": ["Init"], "simp": True})


def finish(work, lines, form=4, head=RAW_HEAD):
    raw = work / "raw.txt"
    raw.write_text(head + "\n" + "".join(r + "\n" for r in lines))
    out = work / "out.elab.ndjson"
    done = subprocess.run([sys.executable, str(ROOT / "scripts/export_elab.py"), str(raw),
                           str(work / "slice.ndjson"), str(out), "--format", str(form)],
                          capture_output=True, text=True, timeout=LIMIT)
    return done.returncode, done.stdout + done.stderr, out


def writer_cases(work):
    absent = congr(["List", "filterMap"], ["List", "filterMap_congr"], [4], 0)
    status, said, out = finish(work, [X_ITE1, absent, C_ITE, C_DITE, T_ADD])
    lines = out.read_text().split("\n") if status == 0 else []
    if status or json.loads(lines[0])["elab_data"]["format_version"] != 4 \
            or lines[-5:-1] != [T_ADD, C_DITE, C_ITE, X_ITE1] or "3 congr;" not in said \
            or "; 1 defeq tags" not in said:
        fail(f"the finisher's format 4: {status} {said} {lines[-4:]}")
    bad = {"a function without its lemma": ([congr(["ite"], ["List", "filterMap_congr"], [0], 0)],
                                            4, RAW_HEAD, "but not its congruence lemma"),
           "simp RAW, format 3": ([C_ITE], 3, RAW_HEAD, "written with export_elab.lean --simp"),
           "plain RAW, format 4": ([C_ITE], 4, RAW_HEAD.replace(',"simp":true', ""),
                                   "written without export_elab.lean --simp"),
           "a defeq tag without --simp": ([T_ADD], 3, RAW_HEAD.replace(',"simp":true', ""),
                                          "a format-4 record in RAW without --simp"),
           "a rank gap": ([X_ITE1], 4, RAW_HEAD, "congruence lemmas of [\"ite\"] are not 0, 1, 2"),
           "hypotheses down": ([C_DITE.replace("[9,10,11]", "[10,9]")], 4, RAW_HEAD,
                               "not a list of increasing"),
           "a defeq tag of a definition": ([defeq(["ite"])], 4, RAW_HEAD,
                                           "not of the kind expected")}
    for name, (lines, form, head, why) in bad.items():
        status, said, _ = finish(work, lines, form, head)
        if status != 1 or why not in said:
            fail(f"the finisher on {name}: {status} {said}")


def check(env, data):
    done = subprocess.run([str(LEANFORTH), "check", "--env", str(env), "--elab-data", str(data),
                           str(TEXT)], stdin=subprocess.DEVNULL, capture_output=True,
                          text=True, timeout=LIMIT)
    return done.returncode, done.stdout + done.stderr


def count_line(said):
    return next((line for line in said.splitlines() if line.startswith("elaboration data:")), "")


def check_cases(work):
    status, said = check(SLICE, DATA)
    if status or "sd_id: accepted" not in said:
        fail(f"the simp slice's own format-4 data: {status} {said[-300:]}")
    if not count_line(said).endswith(", 7 congruence lemmas, 33 defeq tags"):
        fail(f"the count line of format-4 data: {count_line(said)!r}")
    status, said = check(work / "slice.ndjson", FIXTURES / "plain32.elab.ndjson")
    if status or not count_line(said).endswith(" smart-unfolding bodies"):
        fail(f"the count line of format-3.2 data: {status} {count_line(said)!r}")
    for name in ("good", "v3-congr", "twice", "order-swap", "hyps-beyond"):
        _, outcome, line, code = CASES[name]
        status, said = check(work / "slice.ndjson", FIXTURES / f"{name}.elab.ndjson")
        want = "sd_id: accepted" if outcome == "ok" else f"refused at line {line} (error {code})"
        if want not in said or (status == 0) != (outcome == "ok"):
            fail(f"check with {name}: {status} {said[-300:]}")


def main(argv):
    fixtures("--write-fixtures" in argv)
    with tempfile.TemporaryDirectory() as tmp:
        work = pathlib.Path(tmp)
        (work / "slice.ndjson").write_bytes(SLICE.read_bytes())
        manifest = json.loads((ROOT / f"{SLICE}.manifest.json").read_text())
        del manifest["elab_records_sha256"]   # the fixtures are not the bound data
        (work / "slice.ndjson.manifest.json").write_text(json.dumps(manifest, indent=2))
        writer_cases(work)
        check_cases(work)
    print(f"simp data (format 4): all tests passed ({len(CASES)} fixtures, 8 finisher runs, "
          "6 checks)")


if __name__ == "__main__":
    main(sys.argv[1:])
