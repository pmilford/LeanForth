#!/usr/bin/env python3
"""LeanForth against the inductive table (plan task 5.2.1a; ADR 0015 §13,
test plan 1).

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
file may have the same name.

Required of each row:
  - a row of a task done (DONE_TASKS): the table's `leanforth` column, except
    the rows of PENDING, which must give exactly the outcome recorded there
    (each with the reason and the task that will give the table's column);
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
DONE_TASKS = {"5.2.1a"}
# Rows of task 5.2.1a that LeanForth cannot decide yet: id -> (outcome now,
# reason, ending with the task that closes it). Each needs something outside
# task 5.2.1a; the table's own row with "Nat" replaced, or the same rule
# reached without the dependency, is a row of its own (the twin given), which
# must give the table's column. Never accepted, never a verdict Lean does not
# give.
PENDING = {
    "universe.type-not-a-sort": ("unsupported",
        "uses Nat, a recursive type: K5; twin universe.type-not-a-sort-param."
        " Closed by task 5.2.1b (recursive blocks)"),
    "result.other-type": ("unsupported",
        "uses Nat: K5; twin result.other-type-sort. Closed by task 5.2.1b"),
    "params.constructor-mismatch": ("unsupported",
        "uses Nat: K5; twin params.constructor-mismatch-sort. Closed by task 5.2.1b"),
    "names.already-declared": ("unsupported",
        "redeclares Nat, which is unsupported: K5 on N2; twin"
        " names.already-declared-earlier. Closed by task 5.2.1b"),
    "params.constructor-binder-defeq": ("unknown",
        "C2 needs id Type unfolded: K1; twin params.constructor-binder-beta."
        " Closed by task 4.2.2 (unfolding, delta)"),
    "names.empty-block": ("invalid",
        "an empty block record holds no declaration that could carry Lean's verdict"
        " (emptyBlock), and lean4export never writes one: the reader refuses the file"
        " (B0). No task closes it yet: whether the importer should stage it as a"
        " declaration the checker rejects is an [import] question for the owner"),
}
# Rows of later tasks whose file refers to a constant it does not declare,
# which the importer refuses (invalid) before any check: id -> reason.
UNCLOSED = {
    "names.reserved-nested-prefix": "the constructor names _nested.T, declared nowhere",
    "quotinit.without-eq": "the quotient records' types name Eq, absent from the file",
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
    results, feed, decls, checks = [], None, [], {}
    for line in text.splitlines():
        part = line.split("\t")
        if part[0] == "feed":
            feed = part[1]
        elif part[0] == "check":
            checks[int(part[1])] = (int(part[2]), int(part[3]))
        elif part[0] == "decl":
            decls.append((int(part[1]), part[2], part[3]))
        elif part[0] == "case-end":
            results.append((feed, decls, checks))
            feed, decls, checks = None, [], {}
    return results


def row_outcome(case_id, own, result):
    feed, decls, checks = result
    if feed is not None:
        return feed, ""
    if case_id.startswith("after."):
        mine = decls[-len(own):] if own else []
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
        elif case_id in UNCLOSED:
            ok = got in ("invalid", "unsupported", "unknown", want)
            print(f"unclosed {case_id}: {got} ({UNCLOSED[case_id]})")
        else:
            ok = got in ("unsupported", "unknown") or got == want
        if not ok:
            failures.append(f"{case_id} (task {task}, rule {rule}, Lean {lean_verdict}):"
                            f" LeanForth {got} {why}, required {want}")
        elif got not in ("unsupported", "unknown") or task in DONE_TASKS:
            print(f"{case_id}\t{task}\t{rule}\tLean {lean_verdict}\tLeanForth {got}")
    missing = set(rows) - {c[0] for c in cases}
    failures += [f"{r}: a row without a case" for r in sorted(missing)]
    failures += stale_fixtures(cases)
    done = sum(n for (d, _), n in tally.items() if d)
    later = sum(n for (d, _), n in tally.items() if not d)
    print(f"inductive-table: {len(cases)} cases; task 5.2.1a rows {done}:",
          ", ".join(f"{o} {n}" for (d, o), n in sorted(tally.items()) if d),
          f"(pending {len(PENDING)}); later tasks' rows {later}:",
          ", ".join(f"{o} {n}" for (d, o), n in sorted(tally.items()) if not d))
    for failure in failures:
        print("  DIFFERENCE " + failure)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
