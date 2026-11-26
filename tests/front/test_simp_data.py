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
import export_simp  # noqa: E402

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


def realized(fun, kinds, kind="congr_simp", name=None):
    return text({"realized": {"arg_kinds": kinds, "fun": fun, "kind": kind,
                              "name": name or fun + ["congr_simp"]}})


R_DECIDE = realized(["Decidable", "decide"], [1, 3])
R_ITE = realized(["ite"], [0, 1, 3, 1, 1])
GOOD = [C_DITE, C_ITE, C_SUB, T_ADD]
GOOD41 = GOOD + [R_DECIDE, R_ITE]
# The default simp set (format 4.1, simp group 4), records as scripts/export_simp.py writes
# them for the slice: the set, Nat.add_zero (an rfl lemma, rank 33 under HAdd.hAdd's root),
# imp_not_self's left-out lemma (its _simp_1 helper not in the slice), Eq.ndrec to unfold and
# Char.isValue (a pre dsimproc). Each damaged copy is refused at its line (2-7 are GOOD41's).
S_SET = '{"simp_set":{"name":["simp"],"simprocs":["simprocAttr"]}}'
S_ADD0 = ('{"simp_lemma":{"backward_rfl":true,"inv":false,"keys":[{"arity":6,"const":["HAdd",'
          '"hAdd"]},{"arity":0,"const":["Nat"]},{"arity":0,"const":["Nat"]},{"arity":0,'
          '"const":["Nat"]},"star","star",{"lit":"0"}],"origin":["Nat","add_zero"],"perm":false,'
          '"post":true,"priority":1000,"proof":["Nat","add_zero"],"rank":33,"rfl":true,'
          '"set":["simp"]}}')
S_LEFT = ('{"simp_left_out":{"keys":["arrow","star"],"origin":["imp_not_self"],"post":true,'
          '"priority":1000,"proof":["imp_not_self","_simp_1"],"rank":0,'
          '"reason":"not_exported","set":["simp"]}}')
S_UNFOLD = '{"simp_unfold":{"name":["Eq","ndrec"],"set":["simp"]}}'
S_PROC = ('{"simproc":{"dsimproc":true,"keys":[{"arity":1,"const":["Char","ofNat"]},"star"],'
          '"name":["Char","isValue"],"post":false,"rank":0}}')
SET41 = GOOD41 + [S_SET, S_ADD0, S_LEFT, S_UNFOLD, S_PROC]


def set41(old, new):
    return assemble([new if r == old else r for r in SET41], "4.1")


def assemble(lines, version=4, drop=None, **counted):
    """A file for the simp slice holding lines, its header counting them."""
    body = "".join(r + "\n" for r in lines)
    counts = dict.fromkeys(export_elab.KINDS, 0)
    if version == "4.1":   # format 4.1 counts the default simp set's kinds too
        counts.update(dict.fromkeys(export_simp.SET_KINDS, 0))
    else:
        del counts["realized"]
    if version not in (4, "4.1"):
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
    "v41-uncounted": (assemble(GOOD, "4.1", drop="realized"), "invalid", 1, 10),
    "good41": (assemble(GOOD41, "4.1"), "ok", 0, 0),
    "v4-realized": (assemble(GOOD + [R_DECIDE]), "invalid", 6, 11),
    "real-other": (assemble(GOOD + [R_DECIDE.replace('["Decidable","decide"],"kind"',
                                                     '["ite"],"kind"')], "4.1"),
                   "invalid", 6, 37),
    "real-kind": (assemble(GOOD + [R_DECIDE.replace('"kind":"congr_simp"', '"kind":"simp_helper"')], "4.1"),
                  "invalid", 6, 10),
    "real-kinds-big": (assemble(GOOD + [R_DECIDE.replace("[1,3]", "[1,4]")], "4.1"),
                       "invalid", 6, 10),
    "real-kinds-text": (assemble(GOOD + [R_DECIDE.replace("[1,3]", '"13"')], "4.1"),
                        "invalid", 6, 10),
    "real-twice": (assemble(GOOD41 + [R_DECIDE], "4.1"), "invalid", 8, 49),
    "real-congr-name": (assemble(GOOD + [R_ITE.replace('["ite","congr_simp"]', '["ite_congr"]')],
                                 "4.1"), "invalid", 6, 37),
    "real-kinds-short": (assemble(GOOD + [R_ITE.replace("[0,1,3,1,1]", "[0,1,3,1]")], "4.1"),
                         "invalid", 6, 37),
    "real-kinds-long": (assemble(GOOD + [R_ITE.replace("[0,1,3,1,1]", "[0,1,3,1,1,1]")], "4.1"),
                        "ok", 0, 0),
    "real-def": (assemble(GOOD + [R_ITE.replace('["ite","congr_simp"]', '["ite"]')], "4.1"),
                 "invalid", 6, 14),
    "real-unknown": (assemble(GOOD + [R_ITE.replace('["ite","congr_simp"]', '["no_such"]')],
                              "4.1"), "invalid", 6, 12),
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
    "set41": (assemble(SET41, "4.1"), "ok", 0, 0),
    "set-twice": (assemble(SET41 + [S_SET], "4.1"), "invalid", 13, 52),
    "set-other": (set41(S_SET, S_SET.replace('"name":["simp"]', '"name":["seval"]')),
                  "invalid", 8, 52),
    "set-procs": (set41(S_SET, S_SET.replace("simprocAttr", "sevalprocAttr")), "invalid", 8, 52),
    "set-name-long": (set41(S_SET, S_SET.replace('"name":["simp"]', '"name":["simp","x"]')),
                      "invalid", 8, 52),
    "lemma-set": (set41(S_ADD0, S_ADD0.replace('"set":["simp"]', '"set":["seval"]')),
                  "invalid", 9, 52),
    "lemma-rfl": (set41(S_ADD0, S_ADD0.replace('"rfl":true', '"rfl":false')), "invalid", 9, 50),
    "lemma-proof-def": (set41(S_ADD0, S_ADD0.replace('"proof":["Nat","add_zero"]',
                                                     '"proof":["Nat","add"]')), "invalid", 9, 14),
    "lemma-unknown": (set41(S_ADD0, S_ADD0.replace('"origin":["Nat","add_zero"]',
                                                   '"origin":["no_such"]')), "invalid", 9, 12),
    "lemma-keys-cut": (set41(S_ADD0, S_ADD0.replace(',{"lit":"0"}', '')), "invalid", 9, 30),
    "lemma-bool": (set41(S_ADD0, S_ADD0.replace('"perm":false', '"perm":0')), "invalid", 9, 10),
    "lemma-inv": (set41(S_ADD0, S_ADD0.replace('"inv":false', '"inv":"no"')), "invalid", 9, 10),
    "left-known": (set41(S_LEFT, S_LEFT.replace('["imp_not_self","_simp_1"]',
                                                '["Nat","add_zero"]').replace(
                                                    '["imp_not_self"]', '["Nat","add_zero"]')),
                   "invalid", 10, 51),
    "left-reason": (set41(S_LEFT, S_LEFT.replace("not_exported", "erased")), "invalid", 10, 10),
    "left-name": (set41(S_LEFT, S_LEFT.replace('"origin":["imp_not_self"]', '"origin":"x"')),
                  "invalid", 10, 10),
    "unfold-unknown": (set41(S_UNFOLD, S_UNFOLD.replace('["Eq","ndrec"]', '["no_such"]')),
                       "invalid", 11, 12),
    "proc-name": (set41(S_PROC, S_PROC.replace('["Char","isValue"]', '[]')), "invalid", 12, 10),
    "proc-keys-cut": (set41(S_PROC, S_PROC.replace(',"star"', '')), "invalid", 12, 30),
    "v4-lemma": (assemble(GOOD + [S_ADD0]), "invalid", 6, 11),
    "set41-uncounted": (assemble(SET41, "4.1", drop="simp_lemma"), "invalid", 1, 10),
    "set-name-text": (set41(S_SET, S_SET.replace('"name":["simp"]', '"name":"simp"')),
                      "invalid", 8, 52),
    "left-proof-name": (set41(S_LEFT, S_LEFT.replace('"proof":["imp_not_self","_simp_1"]',
                                                     '"proof":"x"')), "invalid", 10, 10),
    "lemma-pre": (set41(S_ADD0, S_ADD0.replace('"post":true', '"post":false')), "ok", 0, 0),
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
           "simp RAW, format 3": ([C_ITE], 3, RAW_HEAD, "written with export_simp.lean's"),
           "plain RAW, format 4": ([C_ITE], 4, RAW_HEAD.replace(',"simp":true', ""),
                                   "written without export_simp.lean's"),
           "plain RAW, format 4.1": ([C_ITE], "4.1", RAW_HEAD.replace(',"simp":true', ""),
                                     "written without export_simp.lean's"),
           "a defeq tag without --simp": ([T_ADD], 3, RAW_HEAD.replace(',"simp":true', ""),
                                          "a format-4 record in RAW without export_simp"),
           "a realized record of another name": (
               [realized(["ite"], [1], name=["Decidable", "decide", "congr_simp"])], "4.1",
               RAW_HEAD, "is not [\"ite\"]'s congr_simp"),
           "a realized record of another kind": (
               [realized(["Decidable", "decide"], [1, 3], kind="simp_helper")], "4.1", RAW_HEAD,
               "realized: unknown kind"),
           "an argument kind beyond 3": ([realized(["Decidable", "decide"], [1, 4])], "4.1",
                                         RAW_HEAD, "arg_kinds is not a list of the numbers 0-3"),

           "a rank gap": ([X_ITE1], 4, RAW_HEAD, "congruence lemmas of [\"ite\"] are not 0, 1, 2"),
           "hypotheses down": ([C_DITE.replace("[9,10,11]", "[10,9]")], 4, RAW_HEAD,
                               "not a list of increasing"),
           "a defeq tag of a definition": ([defeq(["ite"])], 4, RAW_HEAD,
                                           "not of the kind expected")}
    for name, (lines, form, head, why) in bad.items():
        status, said, _ = finish(work, lines, form, head)
        if status != 1 or why not in said:
            fail(f"the finisher on {name}: {status} {said}")
    # Format 4.1 (slice SD-b): a realized record kept when the export has the theorem and
    # its function, left out without the theorem (Init's export lacks 20 of 256); format 4
    # writes none (each counted as left out), byte for byte as before.
    gone = realized(["Nat", "add"], [1, 1])
    raw = [C_ITE, gone, R_DECIDE, T_ADD]
    status, said, out = finish(work, raw, "4.1")
    lines = out.read_text().split("\n") if status == 0 else []
    if status or json.loads(lines[0])["elab_data"]["format_version"] != "4.1" \
            or lines[-4:-1] != [T_ADD, C_ITE, R_DECIDE] or "1 realized;" not in said \
            or ", 1 realized; 0 sunfold" not in said:
        fail(f"the finisher's format 4.1: {status} {said} {lines[-4:]}")
    status, said, out = finish(work, raw, 4)
    if status or '"realized"' in out.read_text() or ", 1 congr;" not in said:
        fail(f"the finisher's format 4 with realized records: {status} {said}")


def set_finish(work, lines, form):
    raw = work / "raw.txt"
    raw.write_text(RAW_HEAD + "\n" + "".join(r + "\n" for r in lines))
    out = work / "set.elab.ndjson"
    done = subprocess.run([sys.executable, str(ROOT / "scripts/export_simp.py"), str(raw),
                           str(work / "slice.ndjson"), str(out), "--format", str(form)],
                          capture_output=True, text=True, timeout=LIMIT)
    return done.returncode, done.stdout + done.stderr, out


def set_finisher_cases(work):
    """scripts/export_simp.py on hand-made RAW against the simp slice: a lemma kept, one whose
    proof the slice lacks left out (its rank kept), one under a root the slice lacks dropped;
    the same for definitions to unfold and simprocs; format 4 drops them all, byte for byte
    export_elab.py's; refused: a rank gap, a proof that is no theorem, a malformed record."""
    add0 = S_ADD0.replace('"rank":33', '"rank":0')
    helper = add0.replace('"proof":["Nat","add_zero"]', '"proof":["Nat","add_zero","_simp_9"]'
                          ).replace('"rank":0', '"rank":1')
    far = ('{"simp_lemma":{"backward_rfl":false,"inv":false,"keys":[{"arity":0,"const":["No",'
           '"such"]}],"origin":["No","such_eq"],"perm":false,"post":true,"priority":1000,'
           '"proof":["No","such_eq"],"rank":0,"rfl":false,"set":["simp"]}}')
    gone = S_UNFOLD.replace('["Eq","ndrec"]', '["No","such"]')
    far_proc = S_PROC.replace('["Char","ofNat"]', '["No","such"]')
    raw = [C_ITE, T_ADD, S_SET, add0, helper, far, S_UNFOLD, gone, S_PROC, far_proc]
    status, said, out = set_finish(work, raw, "4.1")
    lines = out.read_text().split("\n") if status == 0 else []
    counts = json.loads(lines[0])["elab_data"]["records"] if lines else {}
    left = json.loads(lines[-4])["simp_left_out"] if len(lines) > 4 else {}
    if status or [counts.get(k) for k in export_simp.SET_KINDS] != [1, 1, 1, 1, 1] \
            or left.get("proof") != ["Nat", "add_zero", "_simp_9"] or left.get("rank") != 1 \
            or "3 default-set records left out or dropped" not in said:
        fail(f"export_simp.py's format 4.1: {status} {said} {lines[-6:]}")
    status, said, out = set_finish(work, raw, 4)
    plain = finish(work, [C_ITE, T_ADD], 4)[2].read_text()
    if status or out.read_text() != plain:
        fail(f"export_simp.py's format 4 is not export_elab.py's: {status} {said}")
    bad = {"a rank gap": [S_ADD0], "a proof that is no theorem":
           [add0.replace('"proof":["Nat","add_zero"]', '"proof":["Nat","add"]')],
           "a lemma without its rank": [add0.replace(',"rank":0', "")]}
    whys = ["are not 0, 1, 2", "its proof is no theorem", "not a simp_lemma record"]
    for (name, lines), why in zip(bad.items(), whys):
        status, said, _ = set_finish(work, [S_SET] + lines, "4.1")
        if status != 1 or why not in said:
            fail(f"export_simp.py on {name}: {status} {said}")


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
    if not count_line(said).endswith(", 9 congruence lemmas, 33 defeq tags, "
                                      "5 realized congruence theorems, 194 default simp "
                                      "lemmas, 4203 left out, 207 simprocs, 2 definitions "
                                      "to unfold"):
        fail(f"the count line of format-4 data: {count_line(said)!r}")
    status, said = check(work / "slice.ndjson", FIXTURES / "plain32.elab.ndjson")
    if status or not count_line(said).endswith(" smart-unfolding bodies"):
        fail(f"the count line of format-3.2 data: {status} {count_line(said)!r}")
    for name in ("good", "good41", "v3-congr", "twice", "order-swap", "hyps-beyond",
                 "real-other", "v4-realized"):
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
        set_finisher_cases(work)
        check_cases(work)
    print(f"simp data (formats 4 and 4.1): all tests passed ({len(CASES)} fixtures, 14 finisher "
          "runs, 11 checks)")


if __name__ == "__main__":
    main(sys.argv[1:])
