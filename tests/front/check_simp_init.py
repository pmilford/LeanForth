#!/usr/bin/env python3
"""by-simp on Init's one-line simp proofs against pinned Lean's re-run (simp group 4, pass 3;
make reference-simp-init, tests/front/simp-init.sh; the measurement of
docs/development/measurements/simp-init-2026-11-26).

    python3 tests/front/check_simp_init.py LEAN.ndjson EXPORT DATA SNAPSHOT WORK [--only N,..]

LEAN.ndjson is tests/front/simp-init.lean's output: one line per measured theorem with pinned
Lean's re-run (closed or not, its term), and the theorem as LeanForth text ("lf") or why it
cannot be written ("lf_why"). EXPORT is Init's export (its manifest beside it, naming DATA's
records), DATA its format-4.1 elaboration data, SNAPSHOT Init's snapshot (make parallel-init),
WORK a folder for the texts and the runs.

1. N: the theorems of shape `simp` and `simp [..]`; each one that can be written is a file
   WORK/lf/si_NNNN.lf with by-simp or by-simp[ ... ].
2. tests/front/simp-init.fs (Gforth 1.0) runs every file against EXPORT and DATA in one process:
   ok, or the authoring error with the backtrace of its first unsupported throw.
3. The texts that ran go into one file, WORK/ran.lf, checked by bin/leanforth's own check
   against SNAPSHOT and DATA (gforth-fast src/main.fs tests/front/elab-dump.fs, cli-dump: each
   declaration printed as it is handed to the kernel); a text that stops there is taken out
   and the file checked again.
4. Each theorem the kernel accepted is compared with Lean's: its type with Lean's statement
   and its value with Lean's re-run term, node for node. K counts those equal to both.

5. The fixed cases of tests/front/simp-init-cases/ (each file's Lean twin in its first lines,
   which pinned Lean proves: the review of simp group 4's B1 probes) run in step 2 beside the
   texts; each must stop with error 99 (not supported yet), never be accepted with another
   term nor refused with Lean's error. And DATA's simproc records must be
   tests/front/simp-data/init-simprocs.fs's (each a row of simp/simprocs/guards.fs's table or
   a port): a new Lean's simproc fails the run.

The report says K of N; U, the theorems not supported (error 99) by reason, the reason
the word that refused (the backtrace's first frame outside meta-must.fs); the other
errors by code; the theorems that cannot be written by why. Three counts must be 0, else
the run fails and names them (a BUG): accepted with a term other than Lean's, accepted where
Lean's re-run fails, and accepted with a statement LeanForth elaborates differently from
Lean's (the dumped types differ): simp-init.lean writes a text only when pinned Lean reads
its Lean twin as the theorem's own statement (review of simp group 4, M2), so a difference
is LeanForth's elaborator's. The report goes to WORK/report.json and standard output.
"""
import collections
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
FRAME = re.compile(r"^\s*(\S+\.fs):(\d+):\d+:\s+\d+\s+\$[0-9A-Fa-f]+\s+(\S+)")
ERROR = re.compile(r"error (\d+) at line:col (\d+):\d+")
VERDICT = re.compile(r"^(si_\d+): (accepted|rejected|unknown|unsupported)\S*")
STALE = ("(this build: ", "carry: a snapshot of verdict version",
         "this build reads snapshots of verdict versions", "newer than this build's",
         "the snapshot was refused")
# The word that refused, by file and word (or a text its line holds): the reason.
SKIPPED = ("tests/front/simp-init.fs", "tactic-run.fs", "author/errors.fs", "/share/gforth/")
# The Meta layer's throwing faces (front/meta-must.fs): the engine that refused.
META = {"lf-defeq!": "unification (isDefEq) not supported",
        "lf-defeq-approx!": "unification (isDefEq) not supported",
        "lf-whnf!": "whnf not supported", "lf-whnf-r!": "whnf not supported",
        "lf-whnf-d!": "whnf not supported", "lf-infer!": "type inference not supported",
        "lf-is-prop!": "type inference not supported", "lf-level!": "type inference not supported",
        "lf-instantiate!": "instantiation not supported"}
REASONS = [
    ("simp/args.fs", "sar-decl", "swap if", "bracket: a theorem with <- (Lean's auxiliary lemma)"),
    ("simp/args.fs", "sar-decl", "lf-is-prop!", "bracket: a definition or simproc (unfold)"),
    ("simp/args.fs", None, None, "bracket: another item"),
    ("simp/theorems.fs", "lf-simp-thm-usable", None, "left-out helper (a lemma the export lacks or the decoder refuses, reached in candidate order)"),
    ("simp/theorems.fs", "sth-same-keys", None, "recorded keys not the statement's (no_index)"),
    ("simp/theorems.fs", "sth-check", None, "lemma form: a perm lemma (acLt)"),
    ("simp/theorems.fs", "sth-lhs", None, "lemma form: a perm lemma (acLt)"),
    ("simp/theorems.fs", "sth-inner?", None, "lemma form: a perm test of compound terms"),
    ("simp/theorems.fs", None, None, "lemma form (theorems.fs {word})"),
    ("simp/simprocs.fs", None, None, "simproc family (guard only)"),
    ("simp/simprocs/", None, None, "simproc family (port)"),
    ("simp/rewrite.fs", None, "lf-simp-discharge", "conditional rule (the discharger)"),
    ("simp/rewrite.fs", None, None, "rewrite (binderNameHint)"),
    ("simp/main.fs", None, "sm-unfold?", "unfold (a definition the set unfolds)"),
    ("simp/main.fs", "sm-iota-check", None, "matcher, recursor or projection (reduceStep)"),
    ("simp/main.fs", "sm-head-check", None, "matcher, recursor or projection (reduceStep)"),
    ("simp/main.fs", None, "sm-odd-tag?", "let, projection, annotation or raw literal node"),
    ("simp/main.fs", "sm-dsimp", None, "dsimp (a dependent argument)"),
    ("simp/main.fs", None, None, "walk (main.fs {word})"),
    ("simp/congr.fs", None, None, "congruence (congr.fs {word})"),
    ("simp/types.fs", "lf-simp-congr-fun", None, "congruence: a function's proof (congrFun, SL1b)"),
    ("simp/types.fs", "lf-simp-sides", None, "a rule whose statement is no Eq (a helper theorem, SL3d)"),
    ("simp/types.fs", None, None, "types.fs {word}"),
    ("simp/preprocess.fs", None, None, "bracket hypothesis preprocessing"),
    ("simp/default-set.fs", None, None, "default set"),
]
GROUPS = [("simproc family", ("simproc family",)), ("left-out helper", ("left-out",)),
          ("conditional rule", ("conditional",)), ("unfold", ("unfold",)),
          ("matcher", ("matcher",)), ("<- theorem item", ("with <-",))]


class Failure(Exception):
    pass


def enclosing(path, line):
    """The colon definition of path holding line, and that line's text."""
    lines = pathlib.Path(path).read_text(encoding="utf-8").splitlines()
    text = lines[line - 1] if 0 < line <= len(lines) else ""
    for k in range(line - 1, -1, -1):
        m = re.match(r"^:\s+(\S+)", lines[k]) if k < len(lines) else None
        if m:
            return m.group(1), text
        if lines[k].startswith(":noname"):
            return ":noname", text
    return "?", text


def reason(frames):
    """The reason of a refusal, from its backtrace's frames (file, line, word called)."""
    for path, line, _ in frames:
        if any(skip in path for skip in SKIPPED):
            continue
        word, text = enclosing(path, line)
        if path.endswith("meta-must.fs"):
            if word in META:
                return META[word]
            continue
        rel = path.split("/src/front/", 1)[-1]
        for where, name, holds, why in REASONS:
            if where in rel and (name is None or name == word) and (holds is None or holds in text):
                return why.format(word=word)
        return f"other ({rel} {word})"
    return "a refusal of the tactic's own (no unsupported throw recorded)"


def group(why):
    for name, keys in GROUPS:
        if any(k in why for k in keys):
            return name
    return "other"


CASES = ROOT / "tests/front/simp-init-cases"
SIMPROCS = ROOT / "tests/front/simp-data/init-simprocs.fs"


def add_cases(work):
    """The fixed cases, written beside the texts and added to the list: their names."""
    names = []
    for path in sorted(CASES.glob("*.lf")):
        name = f"case_{path.stem}"
        (work / "lf" / f"{name}.lf").write_text(path.read_text(encoding="utf-8"), encoding="utf-8")
        names.append(name)
    with open(work / "list.txt", "a", encoding="utf-8") as out:
        out.writelines(f"{work / 'lf' / n}.lf\n" for n in names)
    return names


def simprocs_listed(data):
    """DATA's simproc records against the committed list: the differences, as text."""
    listed = {tuple(line.split()[1:4]) for line in SIMPROCS.read_text(encoding="utf-8").splitlines()
              if line.startswith("init-simproc: ")}
    found = set()
    for line in open(data, encoding="utf-8"):
        if line.startswith('{"simproc"'):
            r = json.loads(line)["simproc"]
            name = ".".join(str(p) for p in r["name"]).split("._@.")[0]
            found.add((name, "post" if r["post"] else "pre", "d" if r["dsimproc"] else "s"))
    return sorted(f"{' '.join(t)} ({'not listed' if t in found else 'not in the data'})"
                  for t in found ^ listed)


def lean_rows(path):
    rows = [json.loads(line) for line in open(path, encoding="utf-8") if line.startswith("{")]
    return [r for r in rows if r.get("shape") in ("bare", "brackets")]


def write_texts(rows, work):
    folder = work / "lf"
    folder.mkdir(parents=True, exist_ok=True)
    names = {}
    for k, row in enumerate(rows):
        if row.get("lf"):
            name = f"si_{k:04d}"
            (folder / f"{name}.lf").write_text(row["lf"].replace("THEOREM", name), encoding="utf-8")
            names[name] = row
    (work / "list.txt").write_text("".join(f"{folder / n}.lf\n" for n in names), encoding="utf-8")
    return names


def phase1(export, data, work):
    """tests/front/simp-init.fs over the list: {name: (code, line, frames)}, code 0 for ok."""
    words = f's" {export}" s" {data}" s" {work / "list.txt"}" simp-init-run bye'
    done = subprocess.run([GFORTH, "tests/front/simp-init.fs", "-e", words], cwd=ROOT,
                          stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=3600)
    (work / "phase1.txt").write_text(done.stdout + done.stderr, encoding="utf-8")
    if done.returncode != 0:
        raise Failure(f"simp-init.fs: exit {done.returncode}\n{done.stderr[-2000:]}")
    out = {}
    for record in re.split(r"\n(?=ok |error |thrown )", "\n" + done.stdout):
        head = record.strip().split(" ", 2)
        if len(head) < 2 or head[0] not in ("ok", "error", "thrown"):
            continue
        name = pathlib.Path(head[1]).stem
        if head[0] == "ok":
            out[name] = (0, 0, [])
        elif head[0] == "thrown":
            out[name] = (-1, 0, [])
        else:
            m = ERROR.search(record)
            frames = [(f.group(1), int(f.group(2)), f.group(3)) for f in map(FRAME.match, record.splitlines()) if f]
            out[name] = (int(m.group(1)), int(m.group(2)), frames) if m else (-2, 0, frames)
    return out


def phase2(names, ran, snapshot, data, work):
    """bin/leanforth's check of the texts that ran, one file, a text that stops taken out:
    {name: (verdict, type, value)} and {name: (code, line)} for the ones taken out."""
    fast = os.environ.get("GFORTH_FAST") or pathlib.Path(GFORTH).parent / "gforth-fast"
    engine = str(fast) if pathlib.Path(fast).exists() else GFORTH
    left, stopped = list(ran), {}
    while left:
        path = work / "ran.lf"
        path.write_text("".join((work / "lf" / f"{n}.lf").read_text(encoding="utf-8") for n in left),
                        encoding="utf-8")
        argv = [engine, "src/main.fs", "tests/front/elab-dump.fs", "-e", "cli-dump (bye)", "check",
                "--snapshot", str(snapshot), "--elab-data", str(data), str(path)]
        done = subprocess.run(argv, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                              text=True, timeout=3600)
        out = done.stdout + done.stderr
        (work / "phase2.txt").write_text(out, encoding="utf-8")
        stale = next((s for s in STALE if s in out), None)
        if stale:
            raise Failure(f"{snapshot} is not this build's snapshot ({stale}); make parallel-init")
        m = re.search(r"not checked: error (\d+) at line:col (\d+):", out)
        if not m:
            break
        bad, line = theorem_at(left, work, int(m.group(2)))
        stopped[bad] = (int(m.group(1)), line)
        left.remove(bad)
    verdicts, dumped = {}, collections.defaultdict(dict)
    for line in out.splitlines():
        v = VERDICT.match(line)
        if v:
            verdicts[v.group(1)] = v.group(2)
        d = re.match(r"^(si_\d+) (type|value) (.*)$", line)
        if d:
            dumped[d.group(1)][d.group(2)] = d.group(3)
    return {n: (verdicts.get(n), dumped[n].get("type"), dumped[n].get("value")) for n in left}, stopped


def theorem_at(left, work, line):
    """The theorem of ran.lf whose text holds line, and the line in that text."""
    at = 0
    for n in left:
        size = len((work / "lf" / f"{n}.lf").read_text(encoding="utf-8").splitlines())
        if line <= at + size:
            return n, line - at
        at += size
    raise Failure(f"ran.lf: no theorem holds line {line}")


def main(argv):
    lean, export, data, snapshot, work = (pathlib.Path(a).resolve() for a in argv[1:6])
    work.mkdir(parents=True, exist_ok=True)
    rows = lean_rows(lean)
    names = write_texts(rows, work)
    if "--only" in argv:
        keep = set(argv[argv.index("--only") + 1].split(","))
        names = {n: r for n, r in names.items() if n in keep}
        (work / "list.txt").write_text("".join(f"{work / 'lf' / n}.lf\n" for n in names))
    cases = add_cases(work)
    ran1 = phase1(export, data, work)
    ran = [n for n in names if ran1.get(n, (-3,))[0] == 0]
    checked, stopped = phase2(names, ran, snapshot, data, work)
    report = collections.OrderedDict()
    k, bugs, other_statement, unwritten = [], [], [], collections.Counter()
    unsupported, errors, not_accepted = collections.Counter(), collections.Counter(), []
    detail = {}
    for row in rows:
        if not row.get("lf"):
            unwritten[row.get("lf_why", "a harness error of the Lean run")] += 1
    for n, row in names.items():
        code, line, frames = ran1.get(n, (-3, 0, []))
        by_simp = row["lf"].count("\n") - 1
        if n in checked:
            verdict, typ, value = checked[n]
            if verdict != "accepted":
                not_accepted.append(n)
                detail[n] = f"phase 2 verdict {verdict}"
            elif not row.get("closed"):
                bugs.append(f"{n} {row['name']}: accepted where Lean's re-run fails ({row.get('why')})")
            elif typ != row.get("type"):
                other_statement.append(n)
                detail[n] = "statement elaborated differently"
                bugs.append(f"{n} {row['name']}: accepted with a statement other than Lean's")
            elif value != row.get("term"):
                bugs.append(f"{n} {row['name']}: accepted with a term other than Lean's")
            else:
                k.append(n)
            continue
        if n in stopped:
            code, line = stopped[n]
            frames = []
            detail[n] = f"phase 2 error {code}"
        if code == 99 and line == by_simp:
            why = reason(frames)
            unsupported[why] += 1
            detail[n] = why
        else:
            where = "by-simp" if line == by_simp else "statement"
            errors[f"error {code} at the {where}"] += 1
            detail.setdefault(n, f"error {code} at the {where}")
    for n in cases:
        if ran1.get(n, (-3,))[0] != 99:
            bugs.append(f"{n}: error {ran1.get(n, (-3,))[0]}, expected 99 (not supported yet)")
    bugs += [f"simproc record {d}" for d in simprocs_listed(data)]
    lean_closed = sum(1 for r in rows if r.get("closed"))
    groups = collections.Counter()
    for why, count in unsupported.items():
        groups[group(why)] += count
    report.update(N=len(rows), L=lean_closed, written=len(names), K=len(k), bugs=bugs,
                  unsupported=sum(unsupported.values()), unsupported_by_reason=dict(unsupported.most_common()),
                  unsupported_groups=dict(groups.most_common()), errors=dict(errors.most_common()),
                  statement_differs=len(other_statement), not_accepted=not_accepted,
                  cases={n: ran1.get(n, (-3,))[0] for n in cases},
                  unwritten=dict(unwritten.most_common()), accepted=k, detail=detail)
    (work / "report.json").write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n",
                                      encoding="utf-8")
    print(f"reference-simp-init: {len(k)} of {len(rows)} accepted with terms equal to pinned Lean's "
          f"re-run node for node (L = {lean_closed} closed by Lean's re-run); {len(names)} written, "
          f"{len(rows) - len(names)} cannot be written")
    print(f"  U = {sum(unsupported.values())} not supported yet (99) by reason group: "
          + ", ".join(f"{g} {c}" for g, c in groups.most_common()))
    for why, count in unsupported.most_common():
        print(f"    {count:4d}  {why}")
    for what, count in errors.most_common():
        print(f"  {count:4d}  {what}")
    print(f"  {len(other_statement)} accepted with a statement LeanForth elaborates differently "
          f"(a BUG); {len(not_accepted)} not accepted by the kernel")
    for why, count in unwritten.most_common():
        print(f"  {count:4d}  cannot be written: {why}")
    print(f"  {sum(1 for b in bugs if 'other than' in b)} accepted with a different term; "
          f"{sum(1 for b in bugs if 'fails' in b)} accepted where Lean's re-run fails")
    if bugs or not_accepted:
        for b in bugs + [f"{n}: not accepted by the kernel" for n in not_accepted]:
            print(f"BUG: {b}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except (Failure, subprocess.TimeoutExpired) as exc:
        print(f"reference-simp-init: {exc}", file=sys.stderr)
        sys.exit(1)
