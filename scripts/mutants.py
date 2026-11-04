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
in turn is written into the copy, its test run, and the file restored. The
working tree itself is only ever read: its files are listed and hashed
before and after, and any change stops the run with exit status 3.

Each fault is reported as caught or survived. The run fails (exit 1) when
an entry is stale, a fault expected to be caught survives, or a fault
listed as equivalent or as a gap is caught (the list must then be
corrected). Exit 2 means the list is malformed, a test failed on the
unchanged copy, or the temporary directory would lie inside the root.
--check only validates the list and looks for stale entries, running
nothing. --quick runs the faults marked quick (every entry is still checked
for staleness); --only runs the named ones.
"""
import argparse
import hashlib
import os
import re
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
# instead when present, see copy_tree) and agents' scratch files.
SKIPPED = {".git", ".tools", ".claude", "__pycache__", ".profiling"}
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


def plant(copy, fault, env, timeout):
    """Run fault's test with the fault written into the copy: (caught, how)."""
    path = copy / fault["file"]
    original = path.read_bytes()
    text = original.decode("utf-8")
    path.write_bytes(text.replace(fault["old"], fault["new"], 1).encode("utf-8"))
    try:
        status, output = run_test(fault["test"], copy, env, timeout)
    finally:
        path.write_bytes(original)
    if status is None:
        return True, "timeout", output
    return status != 0, f"exit {status}", output


def report(fault, caught, how, seconds, output):
    """Print one fault's result; True when it is as the list expects."""
    want = expected(fault)
    if caught:
        verdict = "caught" if want == "caught" else f"CAUGHT, listed as {want}"
    else:
        verdict = f"survived ({want})" if want != "caught" else "SURVIVED"
    print(f"{verdict:<34} {fault['id']:<44} {how:<8} {seconds:5.1f}s", flush=True)
    good = caught == (want == "caught")
    if not good:
        print(f"    {fault['file']}: {fault['reason']}\n    test: {fault['test']}")
        if caught:
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
        if not controls(chosen, copy, env, args.timeout):
            return 2, None
        counts = {"caught": 0, "known equivalent": 0, "known gap": 0, "unexpected": 0}
        for fault in chosen:
            started = time.monotonic()
            caught, how, output = plant(copy, fault, env, args.timeout)
            if not report(fault, caught, how, time.monotonic() - started, output):
                counts["unexpected"] += 1
            elif caught:
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
    stale = {}
    for fault in faults:
        why = stale_reason(root, fault)
        if why:
            stale[fault["id"]] = why
            print(f"{'STALE':<34} {fault['id']:<44} {fault['file']}: {why}")
    if args.check:
        print(f"mutants: {len(faults)} entries, {len(stale)} stale")
        return 1 if stale else 0
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
