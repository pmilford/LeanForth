#!/usr/bin/env python3
"""LeanForth against the inductive table (plan tasks 5.2.1a, 5.2.1b and 5.2.5a; ADR
0015 §13, test plan 1).

Runs pinned Lean on tests/reference/inductive-expected.lean, which prints
the table's rows (equal to tests/reference/inductive-expected.tsv, checked
here too) and then every case as the lean4export file of what Lean checked
(between `ndjson-begin ID NAMES` and `ndjson-end` lines; NAMES are the case's
own constants). Each file is checked by LeanForth (tests/core/inductive-table.fs:
staged, fed, every declaration checked); a row's LeanForth outcome is the first
outcome that is not accepted among the case's own declarations, in input order,
else accepted; a file the feed refuses gives the feed's outcome. A row `after.*`
(declarations after a block, whose verdict is the last one's) is judged on the
file's last declarations, those its marker names: an earlier declaration of the
file may have the same name. A case whose marker names nothing (the empty block,
which declares no constant) is judged on its declarations without a name: the one
the importer stages for an empty block (ADR 0016 amendment 1).

Required of each row:
  - a row of a task done (DONE_TASKS): the table's `leanforth` column, except
    the rows of PENDING, which must give exactly the outcome recorded there
    (each with the reason and the task that will give the table's column);
  - a row of REQUIRED (a later task's row that a part done decides): exactly
    the table's column;
  - a row of GAPS (a later task's row Lean accepts, unknown here): exactly the
    outcome recorded there, with the task that closes the gap;
  - any other row: unsupported or unknown, or exactly the table's column;
    never another decided outcome, never accepted where the table does not
    say accepted.
Prints one line per row that LeanForth decides, a summary, and fails (exit 1)
on any difference. Needs LEAN (pinned Lean 4.35.0, or the Makefile's cache
stand-in) and GFORTH. Test-only.
"""
import os
import re
import subprocess
import sys
import tempfile

LEAN_FILE = "tests/reference/inductive-expected.lean"
TSV = "tests/reference/inductive-expected.tsv"
FIXTURES = "tests/core/check-block-cases"
DONE_TASKS = {"5.2.1a", "5.2.1b", "5.2.3", "5.2.5a"}
# Rows of the tasks done (DONE_TASKS) that LeanForth cannot decide yet: id ->
# (outcome now, reason, ending with the task that closes it). Each needs
# something outside those tasks; the same rule reached without the dependency
# is a row of its own (the twin given), which must give the table's column.
# Never accepted, never a verdict Lean does not give.
PENDING = {
    "after.b3-swapped-then-iota-lean-rule": ("unknown",
        "iota on Lean's generated recursor, which no slot holds (the block was refused by"
        " B3), is not ported (diagnostic 81; iota.fs reduces a slot's recursor). Closed by"
        " a follow-up of task 5.2.1b (iota with the generated recursor's rules)"),
    "after.b3-swapped-then-iota-forged-rule": ("unknown",
        "as after.b3-swapped-then-iota-lean-rule. Closed by the same follow-up"),
    "after.recursor-left-out-then-lookup-during-block": ("unknown",
        "positivity puts every field in whnf, as Lean does (task 5.2.3: whnf may refuse);"
        " this field's whnf needs iota on Lean's generated recursor, which no slot holds"
        " (diagnostic 81). Closed by the follow-up of task 5.2.1b (iota with the generated"
        " recursor's rules)"),
    "after.list-left-out-then-lookup-during-param-block": ("unknown",
        "as after.recursor-left-out-then-lookup-during-block. Closed by the same follow-up"),
    "lit.string-expansion": ("unsupported",
        "a string literal (U2): not needed by Nat.add_zero's closure, so left out of task"
        " 5.2.3. Closed by a string-literal follow-up of task 5.2.3 (L4)"),
    "lit.string-expansion-wrong": ("unsupported",
        "as lit.string-expansion. Closed by the same follow-up"),
    "after.redex-type-left-out-then-use-rec": ("unknown",
        "IE.U2's type is a Sort only after whnf, so its block left no recipe of the"
        " generated recursor (ADR 0015 decision 12): a use of IE.U2.rec is unknown"
        " (diagnostic 77); twin after.unit-left-out-then-use-rec. Closed when the"
        " rebuild (generated-recursor.fs) walks the telescope with whnf.fs's whnf, as"
        " the block check does since task 5.2.1b's switch (a follow-up)"),
}
# Rows of later tasks whose file refers to a constant it does not declare,
# which the importer refuses (invalid) before any check, where Lean rejects
# the declaration concerned: id -> reason, ending with the task that closes
# it (5.2.6; the row's own task does not lift the importer's refusal).
UNCLOSED = {
    "names.reserved-nested-prefix": "the constructor names _nested.T, declared nowhere."
        " Closed by task 5.2.6 (verdicts per declaration for a file not closed)",
    "quotinit.without-eq": "the quotient records' types name Eq, absent from the file."
        " Closed by task 5.2.6 (verdicts per declaration for a file not closed)",
    "replay-quot.ind-unknown-constant": "Quot.ind's type names IE.nowhere, declared"
        " nowhere (add_quot never reads it). Closed by task 5.2.6 (verdicts per"
        " declaration for a file not closed)",
}
# Rows of a later task where LeanForth answers unknown and Lean accepts, a gap
# with its reason and the task that closes it (owner, 2026-11-04: never a
# difference; each must give exactly this outcome until then).
GAPS = {
    "quotinit.twice": ("unknown",
        "a second quotient record of a name, which add_quot accepts unchanged (quot.cpp"
        " 48-49): LeanForth holds one constant per slot (diagnostic 77). Closed by the"
        " follow-up of task 5.2.4 (all four constants at the first record)"),
    "after.quot-then-mk-declared-then-used": ("unknown",
        "Lean's Quot.mk used where no slot holds it (the file's only Quot.mk refused):"
        " diagnostic 77. Closed by the same follow-up of task 5.2.4"),
}
# Rows of a later task that a part of it already done decides: each must give
# exactly the table's column (id -> the part that decides it).
REQUIRED = {row: "task 5.2.1c's K part (Lean's to_cnstr_when_K, iota.fs)" for row in (
    "iota.eq-refl", "k.eq-variable-proof", "k.eq-different-ends", "k.eq-ends-defeq",
    "k.type-through-definition", "k.true-variable-proof", "k.eq-different-ends-wrong")}
REQUIRED.update({row: "task 5.2.4's Q1 and Q2 (add_quot and quot_reduce_rec, quot.fs)"
                 for row in ("quot.lift-on-mk", "quot.lift-on-mk-wrong",
                             "quot.lift-stuck-on-variable", "quotinit.with-eq",
                             "quotinit.eq-wrong-shape", "replay-quot.original",
                             "replay-quot.mk-given-quot-type",
                             "replay-quot.lift-universe-dropped",
                             "replay-quot.lift-params-repeated",
                             "replay-quot.mk-loose-bvar", "replay-quot.mk-mdata-type",
                             "quot.lift-extra-argument", "quot.lift-extra-argument-wrong",
                             "quot.lift-unapplied-eta", "quot.ind-on-mk",
                             "after.user-quot-lift-not-reduced")})
REQUIRED.update({row: "task 5.2.4's add_quot check_name on all four names (review rvAX)"
                 for row in ("quotinit.name-taken", "after.quot-mk-declared-then-lift-on-it",
                             "after.quot-then-mk-declared", "after.quot-then-lift-declared",
                             "after.quot-then-ind-declared")})
REQUIRED.update({row: "tasks 5.3.1 and 4.2.6 (axioms and opaque declarations)"
                 for row in ("postulate.declared-and-used", "postulate.propext-altered",
                             "postulate.propext-forged-iff", "postulate.propext-own-iff",
                             "postulate.propext-iff-one-param", "postulate.propext-iff-mutual",
                             "postulate.sound-own-quot-names", "replay-iff.flagged-then-propext",
                             "opaque.accepted", "opaque.wrong-value", "opaque.never-unfolds",
                             "opaque.unfolds-as-definition")})
# The axiom bits (src/core/axiom-allowlist.fs) LeanForth must report for
# declarations of these rows: 8 is an axiom outside the allowlist, so NOT
# PROVED (a file's own axiom; propext with another statement, or with
# Lean's statement about an Iff that is not Lean's); 1 is propext proved.
AXIOM_BITS = {
    "postulate.declared-and-used": {"IE.Secret": 8, "IE.secret": 8, "IE.usesSecret": 8},
    "postulate.propext-altered": {"propext": 8, "IE.anything": 8},
    "postulate.propext-forged-iff": {"propext": 8, "IE.collapse": 8},
    "postulate.propext-own-iff": {"propext": 1},
    "postulate.propext-iff-one-param": {"propext": 8},
    "postulate.propext-iff-mutual": {"propext": 8},
    "postulate.sound-own-quot-names": {"Quot.sound": 8},
    "replay-iff.flagged-then-propext": {"propext": 8},
    "opaque.accepted": {"IE.hidden": 0},
}
OUTCOME = {"accepted": "ok"}


def run_lean(lean):
    run = subprocess.run([lean, "-DwarningAsError=true", LEAN_FILE], stdin=subprocess.DEVNULL,
                         capture_output=True, text=True, timeout=600)
    if run.returncode != 0:
        sys.stdout.write(run.stdout + run.stderr)
        raise SystemExit("inductive-table: Lean failed on " + LEAN_FILE)
    return run.stdout


def split(output):
    """The rows' text, and the cases: (id, own names, NDJSON text)."""
    head, _, rest = output.partition("ndjson-begin\t")
    cases = []
    for chunk in ("ndjson-begin\t" + rest).split("ndjson-begin\t")[1:]:
        first, _, body = chunk.partition("\n")
        body, _, _ = body.partition("ndjson-end\n")
        case_id, names = first.split("\t")
        cases.append((case_id, [n for n in names.split(",") if n], body))
    return head, cases


def forth_script(paths):
    lines = [f"include {os.path.abspath('tests/core/inductive-table.fs')}"]
    lines += [f's" {p}" table-case' for p in paths]
    lines.append("bye")
    return "\n".join(lines) + "\n"


def run_forth(gforth, folder, paths):
    """Check every file, a new Gforth after a case that spent the context:
    per file, its (feed outcome or None, [(name, outcome)] in input order,
    {first declaration: (diagnostic, step)})."""
    results, start = [], 0
    while start < len(paths):
        script = os.path.join(folder, "run.fs")
        with open(script, "w", encoding="utf-8") as out:
            out.write(forth_script(paths[start:]))
        run = subprocess.run([gforth, script], stdin=subprocess.DEVNULL, capture_output=True,
                             text=True, timeout=1200)
        done = parse_forth(run.stdout)
        if not done:
            sys.stdout.write(run.stdout + run.stderr)
            raise SystemExit("inductive-table: Gforth checked no case")
        results += done
        start += len(done)
    return results


def parse_forth(text):
    results, feed, decls, checks, bits = [], None, [], {}, {}
    for line in text.splitlines():
        part = line.split("\t")
        if part[0] == "feed":
            feed = part[1]
        elif part[0] == "check":
            checks[int(part[1])] = (int(part[2]), int(part[3]))
        elif part[0] == "decl":
            decls.append((int(part[1]), part[2], part[3]))
            bits[part[2]] = int(part[4])
        elif part[0] == "case-end":
            results.append((feed, decls, checks, bits))
            feed, decls, checks, bits = None, [], {}, {}
    return results


def axiom_differences(case_id, result):
    """The axiom bits of a row of AXIOM_BITS: exactly those given."""
    return [f"{case_id}: {name} has axiom bits {result[3].get(name)}, required {want}"
            for name, want in AXIOM_BITS.get(case_id, {}).items()
            if result[3].get(name) != want]


def row_outcome(case_id, own, result):
    feed, decls, checks, _ = result
    if feed is not None:
        return feed, ""
    if not own:
        mine = [d for d in decls if d[1] == ""]
    elif case_id.startswith("after."):
        mine = decls[-len(own):]
        if [d[1] for d in mine] != own:
            return "missing", "the last declarations are not the marker's"
    else:
        mine = [d for d in decls if d[1] in set(own)]
    if not mine:
        return "missing", ""
    for index, _, outcome in mine:
        if outcome != "ok":
            first = max(k for k in checks if k <= index) if checks else index
            code, step = checks.get(first, (0, 0))
            return outcome, f"diagnostic {code}, block step {step}"
    return "ok", ""


def stale_fixtures(cases):
    """tests/core/check-block-cases/ID.ndjson (tests/core/check-block.fs,
    make test) must be Lean's file for row ID, byte for byte; ID.invalid
    too (a file no export can be, which the reader refuses)."""
    bodies = {case_id: body for case_id, _, body in cases}
    failures = []
    for name in sorted(os.listdir(FIXTURES)):
        case_id = name.rsplit(".", 1)[0]
        with open(os.path.join(FIXTURES, name), encoding="utf-8") as fixture:
            if bodies.get(case_id) != fixture.read():
                failures.append(f"{FIXTURES}/{name}: not Lean's file for row {case_id}")
    print(f"inductive-table: the {len(os.listdir(FIXTURES))} files of {FIXTURES}"
          f" checked against Lean's")
    return failures


def main():
    lean = os.environ.get("LEAN", "lean")
    gforth = os.environ.get("GFORTH", "gforth")
    head, cases = split(run_lean(lean))
    with open(TSV, encoding="utf-8") as tsv:
        if head != tsv.read():
            raise SystemExit(f"inductive-table: Lean's rows differ from {TSV}")
    rows = {}
    for line in head.splitlines()[1:]:
        fields = line.split("\t")
        rows[fields[0]] = fields
    with tempfile.TemporaryDirectory() as folder:
        paths = []
        for k, (case_id, _, body) in enumerate(cases):
            path = os.path.join(folder, f"case{k:03d}.ndjson")
            with open(path, "w", encoding="utf-8") as out:
                out.write(body)
            paths.append(path)
        results = run_forth(gforth, folder, paths)
    failures, tally = [], {}
    for (case_id, own, _), result in zip(cases, results):
        if case_id not in rows:
            failures.append(f"{case_id}: a case without a row")
            continue
        _, lean_verdict, leanforth, rule, task, _ = rows[case_id]
        got, why = row_outcome(case_id, own, result)
        want = OUTCOME.get(leanforth, leanforth)
        tally[(task in DONE_TASKS, got)] = tally.get((task in DONE_TASKS, got), 0) + 1
        if task in DONE_TASKS:
            expected = PENDING.get(case_id, (want, ""))[0]
            ok = got == expected
            if case_id in PENDING and ok:
                print(f"pending {case_id}: {got} ({PENDING[case_id][1]})")
        elif case_id in REQUIRED:
            ok = got == want
        elif case_id in UNCLOSED:
            ok = got in ("invalid", "unsupported", "unknown", want)
            print(f"unclosed {case_id}: {got} ({UNCLOSED[case_id]})")
        elif case_id in GAPS:
            ok = got == GAPS[case_id][0]
            print(f"gap {case_id}: {got} ({GAPS[case_id][1]})")
        else:
            ok = got in ("unsupported", "unknown") or got == want
        if not ok:
            failures.append(f"{case_id} (task {task}, rule {rule}, Lean {lean_verdict}):"
                            f" LeanForth {got} {why}, required {want}")
        elif got not in ("unsupported", "unknown") or task in DONE_TASKS:
            print(f"{case_id}\t{task}\t{rule}\tLean {lean_verdict}\tLeanForth {got}")
        failures += axiom_differences(case_id, result)
    missing = set(rows) - {c[0] for c in cases}
    failures += [f"{r}: a row without a case" for r in sorted(missing)]
    failures += stale_fixtures(cases)
    done = sum(n for (d, _), n in tally.items() if d)
    later = sum(n for (d, _), n in tally.items() if not d)
    print(f"inductive-table: {len(cases)} cases; tasks 5.2.1a-b, 5.2.3, 5.2.5a rows {done}:",
          ", ".join(f"{o} {n}" for (d, o), n in sorted(tally.items()) if d),
          f"(pending {len(PENDING)}); later tasks' rows {later}:",
          ", ".join(f"{o} {n}" for (d, o), n in sorted(tally.items()) if not d))
    for failure in failures:
        print("  DIFFERENCE " + failure)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
