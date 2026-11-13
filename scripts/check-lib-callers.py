#!/usr/bin/env python3
"""Fail when a general library has no caller (owner, 2026-11-13, plan 9.4.8f). Part of `make test`.

Usage: python3 scripts/check-lib-callers.py [ROOT]

Builds the require/include/needs graph of ROOT/src/**/*.fs (a path is resolved relative to the file that names it,
as src/README.md describes). A src/lib/*.fs file is "used" when some file outside src/lib/ reaches it through the
graph (lib/lib.fs counts as a hop: a module that requires it reaches every file it loads). A lib file that no
outside file reaches fails, unless tests/lib-callers-allowlist.json lists it with a plan row id and a reason:

    {"src/lib/x.fs": {"plan": "9.4.8a", "reason": "its first callers merge with ..."}}

An allowlist entry for a file that is used, that does not exist, or that lacks a plan or a reason also fails, so
the list only shrinks. Lib files reached only from tests/ are reported (not failed).
"""
import json
import pathlib
import re
import sys

DEFAULT_ROOT = pathlib.Path(__file__).resolve().parent.parent
LOAD = re.compile(r"^\s*(?:require|include|needs)\s+(\S+)", re.IGNORECASE)


def loads(path):
    """Resolved files that `path` requires, includes or needs (trailing comments are ignored)."""
    found = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = LOAD.match(line)
        if m and m.group(1).endswith(".fs"):
            found.append((path.parent / m.group(1)).resolve())
    return found


def reach(edges, start):
    seen, todo = set(), list(start)
    while todo:
        for g in edges.get(todo.pop(), []):
            if g not in seen:
                seen.add(g)
                todo.append(g)
    return seen


def analyse(root):
    """(libs, used outside lib/, used by tests only) as sets of root-relative strings."""
    root = root.resolve()
    srcs = sorted((root / "src").rglob("*.fs"))
    tests = sorted((root / "tests").rglob("*.fs")) if (root / "tests").exists() else []
    libs = {f for f in (root / "src/lib").glob("*.fs")}
    edges = {f: loads(f) for f in srcs + tests}
    by_src = reach(edges, [f for f in srcs if f not in libs]) & libs
    by_tests = (reach(edges, tests) & libs) - by_src

    def rel(files):
        return {str(p.relative_to(root)) for p in files}
    return rel(libs), rel(by_src), rel(by_tests)


def problems(root, allow):
    libs, used, tests_only = analyse(root)
    out = []
    for lib in sorted(libs - used):
        entry = allow.get(lib)
        if entry is None:
            out.append(f"{lib}: no file outside src/lib/ requires it (use it, remove it, or list it in "
                       f"tests/lib-callers-allowlist.json with a plan row id and a reason)")
        elif not (entry.get("plan") and entry.get("reason")):
            out.append(f"{lib}: allowlist entry needs a plan row id and a reason")
    for name in sorted(allow):
        if name in used:
            out.append(f"{name}: stale allowlist entry, the file is used now (delete the entry)")
        elif name not in libs:
            out.append(f"{name}: allowlist entry names no src/lib/ file")
    return out, sorted(tests_only), sorted(set(allow) & (libs - used))


def main(argv):
    root = pathlib.Path(argv[0]).resolve() if argv else DEFAULT_ROOT
    path = root / "tests/lib-callers-allowlist.json"
    allow = json.loads(path.read_text()) if path.exists() else {}
    bad, tests_only, listed = problems(root, allow)
    for name in tests_only:
        print(f"note: {name} is used by tests only")
    for name in listed:
        print(f"note: {name} has no caller yet (allowed: plan {allow[name].get('plan')})")
    if bad:
        print("lib callers: a library with no caller (AGENTS.md, Reuse first):")
        for p in bad:
            print("  " + p)
        return 1
    print("lib callers: every src/lib/ file is used outside lib/ or listed with a plan row")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
