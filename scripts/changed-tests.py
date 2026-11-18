#!/usr/bin/env python3
"""The Make targets that use a changed file: make test-changed, check-changed.

Usage (from the repository root):
  python3 scripts/changed-tests.py [--base REF] [--why] [--files FILE...] test|check

Prints, on one line, every leaf target of `make test` (or `make check`) that
uses a file that differs from the merge base of REF (default main) and the
working tree, new untracked files included (or the files given by --files);
with --why, also each chosen target's changed files on stderr.

A target uses the files its recipe names (as `make -n` expands it, globs
included) and, transitively, what those programs use: a Forth file's
require and include; a Python file's imports of a module beside it or in
scripts/; and the repository paths (src/, tests/, scripts/, docs/) named in
the code of Forth, Python and shell files, comments and Python docstrings
left out. Lean files, the fault list and data files are used but not
followed further. Rules cover what that misses: a changed Forth source
selects check-portable-forth and smoke, a changed Markdown file check-docs,
a changed Makefile every target.

This is a heuristic for an agent's inner loop, not a proof that the other
targets are unaffected: at the end of a branch run its change tier's suites
(make tier; scripts/test-tier.py builds the tiers on these functions). Most
tests load src/main.fs, so a change to a checker module still selects most
targets. Needs git, make and Python 3.
"""
import argparse
import glob
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

PATH = re.compile(r"(?<![\w./-])(?:\./)?((?:src|tests|scripts|docs|bin)/[\w.*/+-]*[\w*])")
# A root folder's path behind a variable that names the checkout ($root/src/main.fs,
# ${ROOT}/bin/leanforth, {ROOT}/tests/x, $(CURDIR)/scripts/y): read as the path itself.
ROOT_VARIABLE = re.compile(r"(?:\$\{?\w+\}?|\$\(\w+\)|\{\w+\})/(?=(?:src|tests|scripts|docs|bin)/)")
FORTH_LOAD = re.compile(r"\b(?:require|include|needs)\s+(\S+\.fs)\b", re.IGNORECASE)
PY_IMPORT = re.compile(r"^\s*(?:from\s+(\w+)\s+import|import\s+(\w+))", re.MULTILINE)
# Anchored at the start of the text (\A), comment lines matched one line at a
# time: the earlier form (DOTALL, re.sub at every position) backtracked over
# whole files and took minutes per run (2026-11-13).
DOCSTRING = re.compile(r'\A(?:#[^\n]*\n|[ \t]*\n)*(?:"""|\'\'\')[\s\S]*?(?:"""|\'\'\')')
COMMENT = {".fs": "\\", ".py": "#", ".sh": "#"}
# make check is make test plus check-rest (the Makefile, plan 9.4.6).
AGGREGATES = {"test": ["test"], "check": ["check", "test", "check-rest", "test-differential"]}
# A target-specific variable line of make's database ("target: VAR := value").
TARGET_VARIABLE = re.compile(r"^\s*[\w.-]+\s*(?:::=|:=|\?=|\+=|!=|=)")
# sys.path.insert(0, "dir") and sys.path.append("dir"): a directory Python imports from.
SYS_PATH = re.compile(r"""sys\.path\.(?:insert|append)\([^"'\n]*["']([^"']+)["']""")
# Joined paths: "tests" / "core" / "x.ndjson", os.path.join("tests", "core", "x").
JOINED = re.compile(r"""["'](?:src|tests|scripts|docs|bin)["'](?:\s*[/,]\s*["'][^"'\n]+["'])+""")
SUPPORT = "tests/support"
TEXT_LIMIT = 2 * 1024 * 1024


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout


def changed_files(base):
    merge_base = git("merge-base", base, "HEAD").strip()
    names = git("diff", "--name-only", merge_base).splitlines()
    names += git("ls-files", "--others", "--exclude-standard").splitlines()
    return sorted(set(names))


def make_env():
    """The environment without an enclosing make's flags (its jobs, its goals)."""
    return {k: v for k, v in os.environ.items()
            if k not in ("MAKEFLAGS", "MAKELEVEL", "MFLAGS", "MAKEOVERRIDES")}


def prerequisites_of(aggregate):
    """{target: [prerequisite, ...]} from make's database, first rule line each."""
    database = subprocess.run(["make", "-pn", aggregate], capture_output=True, text=True,
                              env=make_env()).stdout
    prerequisites = {}
    for line in database.splitlines():
        match = re.match(r"^([\w-]+):(?!=)(.*)$", line)
        if match and match.group(1) not in prerequisites and not TARGET_VARIABLE.match(match.group(2)):
            prerequisites[match.group(1)] = match.group(2).replace("|", " ").split()
    return prerequisites


def leaf_targets(aggregate, prerequisites=None):
    """The prerequisites of the aggregate's targets, aggregates left out, in make's order."""
    prerequisites = prerequisites if prerequisites is not None else prerequisites_of(aggregate)
    targets = []
    for name in AGGREGATES[aggregate]:
        targets += [t for t in prerequisites.get(name, []) if t not in AGGREGATES["check"]]
    return list(dict.fromkeys(targets))


def recipe(target):
    return subprocess.run(["make", "-n", "--no-print-directory", "-j1", target],
                          capture_output=True, text=True, env=make_env()).stdout


def named_files(text):
    """Repository files a text names: paths, with globs expanded (a folder's
    name alone, as comments use it, does not select its files)."""
    found = set()
    for token in PATH.findall(ROOT_VARIABLE.sub(" ", text)):
        for path in (glob.glob(token) if "*" in token else [token]):
            if os.path.isfile(path):
                found.add(os.path.normpath(path))
    return found


def kind(path):
    """A program's language as its extension (.fs, .py, .sh; a file of bin/ without one is a
    shell script, as bin/leanforth is), or another extension for data."""
    ext = os.path.splitext(path)[1]
    return ".sh" if not ext and path.startswith("bin/") else ext


def code_of(path, text):
    """The text of a program without its comment lines and module docstring."""
    if path.endswith(".py"):
        text = DOCSTRING.sub("", text, count=1)
    mark = COMMENT[kind(path)]
    return "\n".join(line for line in text.splitlines() if not line.lstrip().startswith(mark))


def forth_loads(path, text):
    """The files a Forth file loads (require, include, needs; beside it or from the root)."""
    found = set()
    for name in FORTH_LOAD.findall(text):
        for base in (os.path.dirname(path), "."):
            candidate = os.path.normpath(os.path.join(base, name))
            if os.path.isfile(candidate):
                found.add(candidate)
    return found


def used_files(path, text):
    """The files one program uses: named paths, Forth loads, Python imports."""
    found = named_files(code_of(path, text))
    if kind(path) in (".py", ".sh"):
        for joined in JOINED.findall(code_of(path, text)):
            found |= named_files("/".join(re.findall(r"""["']([^"'\n]+)["']""", joined)))
    folder = os.path.dirname(path)
    if path.endswith(".fs"):
        found |= forth_loads(path, text)
    if path.endswith(".py"):
        for first, second in PY_IMPORT.findall(text):
            bases = [folder, "scripts", SUPPORT] + SYS_PATH.findall(text)
            for base in bases:
                candidate = os.path.normpath(os.path.join(base, (first or second) + ".py"))
                if os.path.isfile(candidate):
                    found.add(candidate)
    return found


def closure(start, cache):
    """Every file the start files use, following programs (not Lean or data)."""
    seen, todo = set(), list(start)
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        seen.add(path)
        if kind(path) not in COMMENT:
            continue
        if path not in cache:
            try:
                with open(path, encoding="utf-8", errors="replace") as stream:
                    cache[path] = used_files(path, stream.read(TEXT_LIMIT))
            except OSError:
                cache[path] = set()
        todo += cache[path] - seen
    return seen


# --- a target's inputs, for per-target reuse (scripts/tested-tree.py) -------------------
# input_files widens closure() until a record may be keyed on what it finds: every file a
# program could read through a path built at run time is in it, or the target is marked
# unresolved and is never reused. More files only cost reuse; a missed file would be unsafe.
QUOTED = re.compile(r"""["']([\w.+-]+(?:/[\w.+-]+)*/?)["']""")
# A bare file name (not the last part of a path, which PATH and the literals resolve exactly).
BASENAME = re.compile(r"(?<![\w./+-])([\w+-][\w.+-]*\.[A-Za-z]\w*)(?![\w/+-])")
GLOB_EXT = re.compile(r"""\*(\.\w+)|endswith\(\s*\(?\s*["'](\.\w+)["']""")
LISTING = re.compile(r"\b(?:r?glob|os\.walk|listdir|iterdir|scandir)\b|\bfor \w+ in [^;\n]*\*")
TEMPLATE = re.compile(r"((?:src|tests|scripts|docs|bin)/(?:[\w.+-]+/)*)[\w.+-]*(?:\{|\$|%|[\"']\s*\+)")
# What makes a program's inputs unknowable from the tree: git's index or history, files outside
# the checkout (machine-local exports, the home folder), or an export named by the environment.
UNRESOLVED = (
    # A git command that reads more than HEAD's name (rev-parse) or whether the worktree is
    # clean (diff --quiet), which bin/leanforth and its tests print as information.
    (re.compile(r"""\bgit\b[^\n]*?[\s"'](?:log|show|ls-files|ls-tree|merge-base|rev-list|blame|status|"""
                r"""cat-file|grep|init|clone|diff(?!["',\s]+--quiet))\b"""), "reads git's index or history"),
    (re.compile(r"\.tools/(?!gforth\b|elan\b)|expanduser|\$\{?HOME\}?/|environ[^\n]*\bHOME\b|(?<![\w.])~/"),
     "reads files outside the checkout"),
    (re.compile(r"\b(?:INIT_EXPORT|MATHLIB|ENGINE_GATE_\w+)\b"), "reads an export the environment names"),
)


def tracked_files():
    """{path: blob id} of every file of HEAD's tree."""
    listing = subprocess.run(["git", "ls-tree", "-r", "HEAD"], capture_output=True, text=True, check=True).stdout
    out = {}
    for line in listing.splitlines():
        meta, path = line.split("\t", 1)
        out[path] = meta.split()[2]
    return out


def under(folder, tracked):
    """The tracked files below FOLDER ("" for none)."""
    prefix = folder.rstrip("/") + "/"
    return {p for p in tracked if p.startswith(prefix)} if folder.strip("/.") else set()


def program_inputs(path, text, tracked, index):
    """(files it runs or loads beyond used_files(), files it may read, reasons its inputs are
    unknown) of one program. Runs or loads: a literal name beside it or at the root. May read:
    its own folder's files (a test of tests/), every file under a folder a literal names,
    every file of a basename it names, of a folder whose name it quotes, of an extension it
    lists, under the folder a path template starts in. A listing of a folder none of these
    names is unresolved, as are the UNRESOLVED markers. INDEX is file_index(TRACKED).
    A Forth source of src/ (the product, which reads only what it loads and the files its
    command line names, which the recipe or test names) contributes its loads alone."""
    code = ROOT_VARIABLE.sub(" ", code_of(path, text))
    folder = os.path.dirname(path)
    runs, found = set(), set()
    if path.startswith("src/") and path.endswith(".fs"):
        return set(), set(), [f"{path} {why}" for rule, why in UNRESOLVED if rule.search(code)]
    reasons = [f"{path} {why}" for rule, why in UNRESOLVED if rule.search(code)]
    if path.startswith("tests/"):
        found |= under(folder, tracked)
    bounded = False
    for literal in QUOTED.findall(code) + PATH.findall(code):
        for base in (folder, "."):
            candidate = os.path.normpath(os.path.join(base, literal))
            if candidate in tracked:
                runs.add(candidate)
            elif under(candidate, tracked):
                found |= under(candidate, tracked)
                bounded = True
        if kind(path) in (".py", ".sh") and "/" not in literal.strip("/"):
            named = index["folder"].get(literal.strip("/"), set())
            found |= named
            bounded = bounded or bool(named)
    for name in BASENAME.findall(code):
        found |= index["basename"].get(name, set())
    for first, second in GLOB_EXT.findall(code):
        found |= index["ext"].get(first or second, set())
        bounded = True
    for prefix in TEMPLATE.findall(code):
        found |= under(prefix, tracked)
        bounded = True
    if LISTING.search(code) and not bounded and not path.startswith("tests/"):
        reasons.append(f"{path} lists a folder the finder cannot name")
    return runs, found - runs, reasons


def file_index(tracked):
    index = {"basename": {}, "folder": {}, "ext": {}}
    for path in tracked:
        index["basename"].setdefault(os.path.basename(path), set()).add(path)
        index["ext"].setdefault(os.path.splitext(path)[1], set()).add(path)
        parts = path.split("/")[:-1]
        for depth, name in enumerate(parts):
            index["folder"].setdefault(name, set()).update(under("/".join(parts[:depth + 1]), tracked)
                                                           if depth == len(parts) - 1 else {path})
    return index


def input_files(start, tracked, cache, index=None):
    """(every tracked file the start files may read, [reasons they cannot be known]): closure()
    with the files program_inputs() says each program runs, to a fixed point, and the files it
    says they may read (read, not followed: a file found only by its name or folder is data).
    CACHE maps a program to its (followed, read, reasons); INDEX is file_index(TRACKED)."""
    index = index or file_index(tracked)
    seen, todo, reasons, read = set(), list(start), [], set()
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        seen.add(path)
        if kind(path) not in COMMENT:
            continue
        if path not in cache:
            try:
                with open(path, encoding="utf-8", errors="replace") as stream:
                    text = stream.read(TEXT_LIMIT)
            except OSError:
                cache[path] = (set(), set(), [f"{path} cannot be read"])
            else:
                runs, data, why = program_inputs(path, text, tracked, index)
                uses = forth_loads(path, text) if path.startswith("src/") and path.endswith(".fs") \
                    else used_files(path, text)
                cache[path] = (uses | runs, data, why)
        files, data, why = cache[path]
        reasons += why
        read |= data
        todo += files - seen
    return {p for p in seen | read if p in tracked}, sorted(set(reasons))


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", default="main")
    parser.add_argument("--why", action="store_true")
    parser.add_argument("--files", nargs="+", help="these files instead of git's changes")
    parser.add_argument("aggregate", choices=sorted(AGGREGATES))
    args = parser.parse_args()
    changed = args.files or changed_files(args.base)
    targets = leaf_targets(args.aggregate)
    if "Makefile" in changed:
        if args.why:
            print("the Makefile changed: every target", file=sys.stderr)
        print(" ".join(targets))
        return 0
    with ThreadPoolExecutor(max_workers=8) as pool:
        recipes = dict(zip(targets, pool.map(recipe, targets)))
    cache, chosen, used = {}, [], set()
    for target in targets:
        uses = closure(named_files(recipes[target]), cache)
        hits = [name for name in changed if name in uses]
        hits += [name for name in changed if name.startswith("src/") and name.endswith(".fs")
                 and target in ("check-portable-forth", "smoke")]
        hits += [name for name in changed if name.endswith(".md") and target == "check-docs"]
        if hits:
            chosen.append(target)
            used.update(hits)
            if args.why:
                print(f"{target}: {' '.join(sorted(set(hits)))}", file=sys.stderr)
    unused = [name for name in changed if name not in used]
    if args.why and unused:
        print(f"no target uses: {' '.join(unused)}", file=sys.stderr)
    print(" ".join(chosen))
    return 0


if __name__ == "__main__":
    sys.exit(main())
