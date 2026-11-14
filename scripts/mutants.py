#!/usr/bin/env python3
"""Planted faults (mutation testing, plan task 1.4.2): make mutants.

Usage (from the repository root):
  python3 scripts/mutants.py [--list FILE] [--root DIR] [--gforth GFORTH]
                             [--only ID,...] [--quick] [--check]
                             [--timeout SECONDS] [--tmpdir DIR]

The list (default tests/mutants/faults.toml) holds one [[fault]] table per
planted fault:
  id          a unique name, lower case, digits and hyphens;
  file        the file the fault changes, relative to the root;
  old         text that must occur in that file exactly once;
  new         its replacement, the fault;
  test        the shell command, run in the copy's root with bash, that
              must catch it, i.e. fail (exit nonzero or time out); $GFORTH
              names the Gforth to use, also exported to the command;
  reason      one line: what the fault breaks and why the test sees it;
  equivalent  optional: why no test can catch it (it behaves exactly as
              the original), so it is expected to survive;
  gap         optional: a known test gap it shows, expected to survive
              until a test is added;
  quick       optional, true: part of the sample that --quick runs.

Every entry's old text is checked first: one that does not occur exactly
once is stale (the code changed under it). Then the root's files are copied
into a new temporary directory outside the root, and every distinct test
command runs once on the unchanged copy, which it must pass. Then each fault
in turn is written into the copy, the changed file checked to still load (a
Forth file on its own and silently, as make smoke requires; a Python file
must parse), its test run, and the file restored. The
working tree itself is only ever read: its files are listed and hashed
before and after, and any change stops the run with exit status 3.

Each fault is reported as caught or survived. The run fails (exit 1) when
an entry is stale, a changed file does not load (the test would then prove
nothing), a fault expected to be caught survives, or a fault
listed as equivalent or as a gap is caught (the list must then be
corrected). Exit 2 means the list is malformed, a test failed on the
unchanged copy, or the temporary directory would lie inside the root.
--check only validates the list and looks for stale entries, running
nothing. --quick runs the faults marked quick (every entry is still checked
for staleness); --only runs the named ones.

The history rule (plan 9.4.8j; the s1-synth review's B1, where one commit
overwrote 13 faults' replacement texts so that their files no longer
loaded, unnoticed): a commit may change the file, the original text (old)
or the replacement text (new) of a fault that existed before it only when
its message names that fault's id (review reuse-out-2 L2: re-targeting a
fault is as much a change as rewriting it). --check also reads every commit
of BASE..HEAD (--base, default main: the branch's own commits; none on main
itself) that changed the list and fails for each such change without the id
in its message; --history checks only this, for make test. A merge counts
only for a text that differs from every parent's. A list that does not
parse hides nothing: a commit is compared with the nearest version before
it that parses (first parents), so breaking the list in one commit and
repairing it, changed, in the next still needs the name. The rule is not
retroactive: a commit whose own scripts/mutants.py predates it (has no
RETARGET_RULE line) is held only to naming changes of new, as it was then.
"""
import argparse
import hashlib
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_LIST = "tests/mutants/faults.toml"
REQUIRED = ("id", "file", "old", "new", "test", "reason")
OPTIONAL = ("equivalent", "gap", "quick")
ID = re.compile(r"^[a-z0-9][a-z0-9-]*$")
# Directories never copied: version control, the local toolchains (linked
# instead when present, see copy_tree), agents' scratch files and make's
# shared results (build/, ignored by git; review L3 of speed-lf).
SKIPPED = {".git", ".tools", ".claude", "__pycache__", ".profiling", "build"}
# Environment variables of an enclosing make that must not reach a test.
MAKE_VARIABLES = ("MAKEFLAGS", "MAKELEVEL", "MFLAGS", "MAKEOVERRIDES")


class ListError(Exception):
    """The fault list is malformed."""


def text_field(fault, key, where, single_line=False):
    value = fault[key]
    if not isinstance(value, str) or (key != "new" and not value):
        raise ListError(f"{where}: {key} must be a non-empty string")
    if single_line and "\n" in value:
        raise ListError(f"{where}: {key} must be one line")
    return value


def check_fault(fault, index, seen):
    where = f"fault {index + 1}"
    if not isinstance(fault, dict):
        raise ListError(f"{where}: not a table")
    unknown = set(fault) - set(REQUIRED) - set(OPTIONAL)
    missing = [key for key in REQUIRED if key not in fault]
    if unknown or missing:
        raise ListError(f"{where}: unknown keys {sorted(unknown)}, missing {missing}")
    ident = text_field(fault, "id", where, True)
    where = f"fault {ident}"
    if not ID.match(ident) or ident in seen:
        raise ListError(f"{where}: id must be unique, lower case, digits and hyphens")
    seen.add(ident)
    name = text_field(fault, "file", where, True)
    if name.startswith("/") or ".." in Path(name).parts:
        raise ListError(f"{where}: file must be a path inside the root")
    if text_field(fault, "old", where) == text_field(fault, "new", where):
        raise ListError(f"{where}: new must differ from old")
    text_field(fault, "test", where, True)
    text_field(fault, "reason", where, True)
    for key in ("equivalent", "gap"):
        if key in fault:
            text_field(fault, key, where, True)
    if "equivalent" in fault and "gap" in fault:
        raise ListError(f"{where}: equivalent and gap exclude each other")
    if not isinstance(fault.get("quick", False), bool):
        raise ListError(f"{where}: quick must be true or false")


def load_list(path):
    """The validated list of faults (dicts) in the TOML file at path."""
    try:
        with open(path, "rb") as handle:
            data = tomllib.load(handle)
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise ListError(f"{path}: {error}") from error
    if set(data) != {"fault"} or not isinstance(data["fault"], list):
        raise ListError(f"{path}: expected only [[fault]] tables")
    seen = set()
    for index, fault in enumerate(data["fault"]):
        check_fault(fault, index, seen)
    return data["fault"]


def git_text(root, *args):
    """Git's output in root, or None when git fails (no repository, an unknown revision)."""
    try:
        run = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True,
                             timeout=120)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return run.stdout if run.returncode == 0 else None


def replacements(text):
    """{id: (file, old, new)} of a fault list's text; None when it does not parse."""
    try:
        faults = tomllib.loads(text or "").get("fault", [])
    except tomllib.TOMLDecodeError:
        return None
    return {f["id"]: (f.get("file"), f.get("old"), f.get("new"))
            for f in faults if isinstance(f, dict) and "id" in f}


# The marker of the file/old/new rule (review reuse-out-2 L2), read in each commit's own copy.
RETARGET_RULE = "a fault's file, old and new text are all named when they change"


def judged_whole(root, commit):
    """Whether commit is held to the whole rule (file, old and new): its tree's
    scripts/mutants.py states it, or it has no such file (a repository of its own)."""
    text = git_text(root, "show", f"{commit}:scripts/mutants.py")
    return text is None or RETARGET_RULE in text


def parsed_before(root, list_name, commit, limit=200):
    """replacements() of the list at commit, or at the nearest first-parent ancestor whose list
    parses ({} when none within limit commits, or no list there)."""
    for _ in range(limit):
        text = git_text(root, "show", f"{commit}:{list_name}")
        found = replacements(text)
        if found is not None:
            return found
        parent = (git_text(root, "rev-parse", "--verify", "--quiet", f"{commit}^") or "").strip()
        if not parent:
            return {}
        commit = parent
    return {}


def names_fault(message, ident):
    """Whether a commit message names the fault ident (as a whole id, not inside another)."""
    return re.search(r"(?<![a-z0-9-])" + re.escape(ident) + r"(?![a-z0-9-])", message) is not None


def unnamed_replacements(root, list_name, base):
    """[(commit, id)] for every commit of BASE..HEAD that changed the file, old or new text of a
    fault that existed before it without naming the fault in its message. A commit whose list
    does not parse is skipped; the next one is compared with the last list before it that
    parses."""
    listing = git_text(root, "log", "--format=%H %P", f"{base}..HEAD", "--", list_name)
    problems = []
    for line in (listing or "").splitlines():
        commit, *parents = line.split()
        after = replacements(git_text(root, "show", f"{commit}:{list_name}"))
        if after is None:
            continue
        before = [parsed_before(root, list_name, p) for p in parents]
        if not judged_whole(root, commit):
            after = {k: v[2] for k, v in after.items()}
            before = [{k: v[2] for k, v in b.items()} for b in before]
        message = git_text(root, "log", "-1", "--format=%B", commit) or ""
        for ident, new in sorted(after.items()):
            olds = [b[ident] for b in before if ident in b]
            if olds and all(old != new for old in olds) and not names_fault(message, ident):
                problems.append((commit[:12], ident))
    return problems


def history_problems(root, list_path, base):
    """The history rule's failures, printed; their number."""
    try:
        name = str(list_path.resolve().relative_to(root))
    except ValueError:
        return 0
    problems = unnamed_replacements(root, name, base)
    for commit, ident in problems:
        print(f"{'REPLACED UNNAMED':<34} {ident:<44} commit {commit} changes its file, old or "
              f"new text without naming it")
    return len(problems)


def expected(fault):
    """'caught', or why the fault is expected to survive."""
    if "equivalent" in fault:
        return "known equivalent"
    if "gap" in fault:
        return "known gap"
    return "caught"


def stale_reason(root, fault):
    """None when the old text occurs exactly once in the file, else why not."""
    path = root / fault["file"]
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return "file missing or unreadable"
    count = text.count(fault["old"])
    return None if count == 1 else f"old text found {count} times"


def tree_files(root):
    """The root's files to copy: git's tracked and new, not ignored, files when
    the root is a git checkout, else every file outside SKIPPED."""
    if (root / ".git").exists():
        listing = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--cached", "--others",
             "--exclude-standard"], capture_output=True, check=True).stdout
        names = [name for name in listing.decode("utf-8").split("\0") if name]
    else:
        names = []
        for directory, subdirectories, files in os.walk(root):
            subdirectories[:] = [d for d in subdirectories if d not in SKIPPED]
            base = Path(directory).relative_to(root)
            names.extend(str(base / name) for name in files)
    return sorted(name for name in set(names)
                  if Path(name).parts[0] not in SKIPPED
                  and (root / name).is_file() and not (root / name).is_symlink())


def copy_tree(root, target):
    """Copy the root's files into target. A .tools directory or link in the
    root is linked, not copied, so that a test finds the local toolchains."""
    for name in tree_files(root):
        destination = target / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / name, destination)
        shutil.copymode(root / name, destination)
    if (root / ".tools").exists():
        os.symlink((root / ".tools").resolve(), target / ".tools")


def fingerprint(root, names):
    """Content hash and modification time of each named file of the root."""
    result = {}
    for name in sorted(names):
        path = root / name
        data = path.read_bytes()
        result[name] = (hashlib.sha256(data).hexdigest(), path.stat().st_mtime_ns)
    return result


def run_test(command, cwd, env, timeout):
    """(exit status or None on timeout, output) of command run with bash."""
    process = subprocess.Popen(["bash", "-c", command], cwd=cwd, env=env,
                               stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, start_new_session=True)
    try:
        output, _ = process.communicate(timeout=timeout)
        return process.returncode, output
    except subprocess.TimeoutExpired:
        for sig, grace in ((signal.SIGTERM, 5), (signal.SIGKILL, None)):
            try:
                os.killpg(process.pid, sig)
            except ProcessLookupError:
                break
            try:
                output, _ = process.communicate(timeout=grace)
                break
            except subprocess.TimeoutExpired:
                continue
        return None, output or b""


def tail(output, lines=6):
    text = output.decode("utf-8", "replace").rstrip().splitlines()
    return "\n".join("    | " + line for line in text[-lines:])


def test_environment(gforth):
    env = {key: value for key, value in os.environ.items() if key not in MAKE_VARIABLES}
    strict = str(Path(__file__).resolve().parent / "gforth-strict.sh")
    if gforth != strict:  # tests run Gforth through the exit-status wrapper
        env["LEANFORTH_GFORTH"] = gforth
        gforth = strict
    env["GFORTH"] = gforth
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


def resolve_gforth(root, given):
    if given is None:
        local = root / ".tools/gforth/bin/gforth"
        given = str(local) if local.exists() else "gforth"
    if "/" in given:
        given = str((Path.cwd() / given).resolve())
    return given


def controls(faults, copy, env, timeout):
    """Run every distinct test once on the unchanged copy: True when all pass."""
    good = True
    for command in dict.fromkeys(fault["test"] for fault in faults):
        status, output = run_test(command, copy, env, timeout)
        if status != 0:
            good = False
            why = "timed out" if status is None else f"exit {status}"
            print(f"control FAILED ({why}) on the unchanged copy: {command}\n{tail(output)}")
    return good


def load_command(name):
    """A command that fails when the changed file no longer loads on its own
    (a Forth module, silently, as make smoke requires) or parses (Python);
    None for other files."""
    if name.endswith(".fs"):
        return (f'out=$("$GFORTH" {shlex.quote(name)} -e bye 2>&1); status=$?; '
                'printf "%s\\n" "$out"; [ $status = 0 ] && [ -z "$out" ]')
    if name.endswith(".py"):
        return f"python3 -c 'import ast, sys; ast.parse(open(sys.argv[1]).read())' {shlex.quote(name)}"
    return None


def plant(copy, fault, env, timeout):
    """Write fault into the copy, check that the file still loads, run the
    fault's test and restore the file: (verdict, how, output), the verdict
    'caught', 'survived' or 'broken' (the changed file does not load, so
    the test proves nothing)."""
    path = copy / fault["file"]
    original = path.read_bytes()
    text = original.decode("utf-8")
    path.write_bytes(text.replace(fault["old"], fault["new"], 1).encode("utf-8"))
    try:
        loads = load_command(fault["file"])
        if loads:
            status, output = run_test(loads, copy, env, timeout)
            if status != 0:
                return "broken", "no load", output
        status, output = run_test(fault["test"], copy, env, timeout)
    finally:
        path.write_bytes(original)
    if status is None:
        return "caught", "timeout", output
    return ("caught" if status != 0 else "survived"), f"exit {status}", output


def report(fault, verdict, how, seconds, output):
    """Print one fault's result; True when it is as the list expects."""
    want = expected(fault)
    if verdict == "broken":
        line = "BROKEN: the change does not load"
    elif verdict == "caught":
        line = "caught" if want == "caught" else f"CAUGHT, listed as {want}"
    else:
        line = f"survived ({want})" if want != "caught" else "SURVIVED"
    print(f"{line:<34} {fault['id']:<44} {how:<8} {seconds:5.1f}s", flush=True)
    good = verdict != "broken" and (verdict == "caught") == (want == "caught")
    if not good:
        print(f"    {fault['file']}: {fault['reason']}\n    test: {fault['test']}")
        if verdict != "survived":
            print(tail(output))
    return good


def selected(faults, args, stale):
    chosen = [f for f in faults if f["id"] not in stale]
    if args.quick:
        chosen = [f for f in chosen if f.get("quick")]
    if args.only:
        wanted = set(args.only.split(","))
        unknown = wanted - {f["id"] for f in faults}
        if unknown:
            raise ListError(f"--only names unknown faults: {sorted(unknown)}")
        chosen = [f for f in chosen if f["id"] in wanted]
    return chosen


def inside(path, root):
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except ValueError:
        return False


def run_faults(root, chosen, args):
    """Plant each chosen fault in a temporary copy: (exit status, counts)."""
    gforth = resolve_gforth(root, args.gforth)
    env = test_environment(gforth)
    base = Path(args.tmpdir) if args.tmpdir else Path(tempfile.gettempdir())
    if inside(base, root):
        print(f"refused: the temporary directory {base} lies inside the root {root}")
        return 2, None
    work = Path(tempfile.mkdtemp(prefix="leanforth-mutants-", dir=base))
    try:
        copy = work / "tree"
        copy.mkdir()
        copy_tree(root, copy)
        # The tests' scratch files (tests/support/scratch.fs) go to this run's own folder.
        (work / "scratch").mkdir()
        env["LF_TEST_SCRATCH"] = str(work / "scratch")
        if not controls(chosen, copy, env, args.timeout):
            return 2, None
        counts = {"caught": 0, "known equivalent": 0, "known gap": 0, "unexpected": 0}
        for fault in chosen:
            started = time.monotonic()
            verdict, how, output = plant(copy, fault, env, args.timeout)
            if not report(fault, verdict, how, time.monotonic() - started, output):
                counts["unexpected"] += 1
            elif verdict == "caught":
                counts["caught"] += 1
            else:
                counts[expected(fault)] += 1
        return (1 if counts["unexpected"] else 0), counts
    finally:
        shutil.rmtree(work, ignore_errors=True)


def summary(chosen, counts, stale):
    survived = counts["known equivalent"] + counts["known gap"]
    print(f"mutants: {len(chosen)} run, {counts['caught']} caught, {survived} survived as "
          f"listed ({counts['known equivalent']} known equivalent, "
          f"{counts['known gap']} known gaps), {counts['unexpected']} not as listed, "
          f"{len(stale)} stale")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--list", default=None)
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--gforth", default=os.environ.get("GFORTH"))
    parser.add_argument("--only", default=None)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--history", action="store_true")
    parser.add_argument("--base", default="main")
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--tmpdir", default=None)
    args = parser.parse_args(argv)
    root = Path(args.root).resolve()
    list_path = Path(args.list) if args.list else root / DEFAULT_LIST
    try:
        faults = load_list(list_path)
    except ListError as error:
        print(f"bad fault list: {error}")
        return 2
    if args.history:
        unnamed = history_problems(root, list_path, args.base)
        print(f"mutants: {len(faults)} entries, {unnamed} replacement texts changed unnamed "
              f"since {args.base}")
        return 1 if unnamed else 0
    stale = {}
    for fault in faults:
        why = stale_reason(root, fault)
        if why:
            stale[fault["id"]] = why
            print(f"{'STALE':<34} {fault['id']:<44} {fault['file']}: {why}")
    if args.check:
        unnamed = history_problems(root, list_path, args.base)
        print(f"mutants: {len(faults)} entries, {len(stale)} stale, {unnamed} replacement texts "
              f"changed unnamed since {args.base}")
        return 1 if stale or unnamed else 0
    try:
        chosen = selected(faults, args, stale)
    except ListError as error:
        print(f"bad arguments: {error}")
        return 2
    before = fingerprint(root, set(tree_files(root)))
    status, counts = run_faults(root, chosen, args)
    after = fingerprint(root, set(tree_files(root)))
    if after != before:
        changed = sorted(n for n in set(before) | set(after) if before.get(n) != after.get(n))
        print(f"FAILED: the working tree changed during the run: {', '.join(changed)}")
        return 3
    if counts is None:
        return status
    summary(chosen, counts, stale)
    return 1 if status or stale else 0


if __name__ == "__main__":
    sys.exit(main())
