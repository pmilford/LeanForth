#!/usr/bin/env python3
"""Whether a branch's tactic plug-ins are confined (tactic plug-in design, slice (a1);
TACTIC_PLUGINS.md of branch tactic-plugin-design, sections 2.4 and 3, decision 2 approved by the owner 2026-11-17).

Usage (from the repository root):
  python3 scripts/check-tactic-plugins.py [--base REF] [--files FILE...]

A branch that adds a tactic file (a new src/front/tactics/NAME.fs) is confined when every file it
changes is one of: a file of src/front/tactics/ (the tactic files and the list all.fs), a file of
tests/front/tactics/NAME/ for a tactic NAME it adds or changes, the fault file
tests/mutants/faults.d/NAME.toml of such a tactic, a batch's own tests and faults
(tests/front/tactics/batch-*/ and tests/mutants/faults.d/batch-*.toml; plan row TB2, one test
directory for several tactics), a goal operation of src/front/meta-tactic/ that is new or only
gains lines (git's count of deleted lines 0) and whose definitions shadow no word (none defined
twice in it, none another Forth file of src/ defines: what loaded before it means what it meant),
or documentation (scripts/test-tier.py's docs tier: Markdown, docs/, ...); and every tactic file
it adds or changes
  - writes no hook: no `is` and no `defer!`,
  - writes no data word another file defines: no `W !`, `W +!`, `W c!`, `W 2!` or `to W` for a W
    that a variable, value, create, buffer: or 2variable of another Forth file of src/ defines,
  - calls a row setter (lf-tactic-...!) only for its own kinds: the word before it is defined in
    the same file, and is no alias of another file's kind (a constant or value made from one, or a
    colon definition that names one: review tactic-move L1), or it is one of the eleven fixed kinds
    of the runner (tactic-syntax.fs: kinds 1-11, which the step-log goldens fix, so they are never
    re-registered through lf-tactic:) and FIXED_KINDS gives it to this very file,
    src/front/tactics/NAME.fs (by-intro: to src/front/tactics/intro.fs, plan 9.4.8l-I; a file of
    another folder with the same name owns none).
Comments and strings are left out. Only a confined branch gets the "tactic" change tier
(scripts/test-tier.py): the front end's unit tests, every end-to-end run of .lf files, the S1/S2
pinned-Lean comparisons (reference-front), the source rules, the changed files' coverage and
faults. Any other branch, or one this check refuses, gets the tier its files give (a tactic file
is loaded by src/main.fs, so the full tier); the daily full run is the safety net.

Prints what it found. Exit status: 0 confined, 1 a tactic file breaks a rule (each printed),
3 not confined or no tactic file added (the reasons printed; nothing is wrong), 2 usage or git
error.
"""
import argparse
import os
import re
import subprocess
import sys

TACTICS = "src/front/tactics/"
META_TACTIC = "src/front/meta-tactic/"
TACTIC_TESTS = "tests/front/tactics/"
FAULTS_DIR = "tests/mutants/faults.d/"
BATCH = re.compile(r"^(tests/front/tactics/batch-[\w-]+/|tests/mutants/faults\.d/batch-[\w-]+\.toml$)")
DOC_FOLDERS = ("docs/", ".claude/", ".codex/", "prompts/")
DATA_WORD = re.compile(r"(?i)(?:^|\s)(?:2?variable|2?value|create|buffer:|fvariable)\s+(\S+)")
DEFINES = re.compile(r"(?i)^(?::|2?variable|2?value|2?constant|create|defer|buffer:|fvariable|value|"
                     r"\+field|field:|cfield:|ffield:|2field:)$")
STORES = {"!", "+!", "c!", "2!", "w!", "l!", "f!"}
HOOKS = {"is", "defer!"}
SETTER = re.compile(r"(?i)^lf-tactic-[\w-]*!$")
# The runner's fixed kinds (src/front/tactic-syntax.fs, kinds 1-11) and the tactic file that owns
# each one's row (its action, end and alternatives); None: the runner's own (by, by-sorry, and the
# alternative |, whose row tactic-run.fs's lf-tactic-alt! sets for the block holding it, plan 9.4.8l-I
# commit C4: tactics/induction.fs sets it through its own tac-k-with).
FIXED_KINDS = {
    "tac-k-by": None, "tac-k-rfl": "rfl", "tac-k-exact": "exact", "tac-k-intro": "intro",
    "tac-k-induction": "induction", "tac-k-with": "induction", "tac-k-alt": None,
    "tac-k-case": "case", "tac-k-rw": "rewrite", "tac-k-rewrite": "rewrite", "tac-k-sorry": None,
}


KIND_WORD = re.compile(r"(?i)^tac-k-")


def owns(path, kind, own):
    """Whether the tactic file PATH may set a row of KIND: its own kind, or a fixed kind given to it
    (the file src/front/tactics/NAME.fs itself, compared as a whole path)."""
    name = FIXED_KINDS.get(kind)
    return kind in own or (name is not None and os.path.normpath(path) == f"{TACTICS}{name}.fs")


def aliases(toks, own):
    """The words TOKS define from a kind they do not define (X constant W, X value W, or a colon
    definition naming X, for X a fixed kind or another file's tac-k- word): never own kinds."""
    foreign = lambda w: w in FIXED_KINDS or (KIND_WORD.match(w) and w not in own)
    found, k = set(), 0
    while k < len(toks) - 1:
        if toks[k] == ":":
            end = toks.index(";", k) if ";" in toks[k:] else len(toks)
            if any(foreign(w) for w in toks[k + 2:end]):
                found.add(toks[k + 1])
            k = end
        elif toks[k + 1] in ("constant", "value", "2constant") and k + 2 < len(toks) and foreign(toks[k]):
            found.add(toks[k + 2])
        k += 1
    return found


def git(*args):
    run = subprocess.run(["git", *args], capture_output=True, text=True)
    if run.returncode != 0:
        print(f"check-tactic-plugins: git {' '.join(args)}: {run.stderr.strip()}", file=sys.stderr)
        raise SystemExit(2)
    return run.stdout


def is_doc(path):
    return path.endswith(".md") or path.startswith(DOC_FOLDERS) or path in ("LICENSE", ".gitignore")


STRING_START = {'s"', '."', 'c"', 'abort"', 's\\"', '.\\"'}


def tokens(text):
    """The Forth tokens of TEXT, lower case, without comments (backslash to the line's end,
    parentheses, across lines too) and strings (s" ." c" abort" to the closing quote)."""
    out, closing = [], None
    for line in text.splitlines():
        if closing == '"':
            closing = None
        for word in line.split():
            if closing:
                if word.endswith(closing):
                    closing = None
                continue
            if word == "\\":
                break
            if word in ("(", ".("):
                closing = ")"
            elif word.lower() in STRING_START:
                closing = '"'
            else:
                out.append(word.lower())
    return out


def defined_in(toks):
    """The words TOKS define (the word after a defining word)."""
    return {toks[k + 1] for k in range(len(toks) - 1) if DEFINES.match(toks[k])}


def outside_colons(toks):
    """TOKS without the bodies of colon definitions: a create inside one (a defining word's, as
    portability.fs's +field: create over ,) defines no data word of the file."""
    out, inside = [], False
    for word in toks:
        if word == ":":
            inside = True
        elif word == ";":
            inside = False
        elif not inside:
            out.append(word)
    return out


def data_words(skip):
    """The data words (variable, value, create, buffer:) the Forth files of src/ define, but SKIP."""
    found = set()
    for path in subprocess.run(["git", "ls-files", "src"], capture_output=True, text=True).stdout.split():
        if path.endswith(".fs") and path not in skip:
            try:
                with open(path, encoding="utf-8", errors="replace") as stream:
                    text = " ".join(outside_colons(tokens(stream.read())))
                    found |= {w.lower() for w in DATA_WORD.findall(text)}
            except OSError:
                continue
    return found


def definitions(skip):
    """The words the Forth files of src/ define (lower case), but SKIP: what a goal operation's
    file may not define again."""
    found = set()
    for path in subprocess.run(["git", "ls-files", "src"], capture_output=True, text=True).stdout.split():
        if path.endswith(".fs") and path != skip:
            try:
                with open(path, encoding="utf-8", errors="replace") as stream:
                    found |= defined_in(tokens(stream.read()))
            except OSError:
                continue
    return found


def shadowed(text, elsewhere):
    """The words TEXT defines twice, or that ELSEWHERE (other files' definitions) holds."""
    toks = tokens(text)
    names = [toks[k + 1] for k in range(len(toks) - 1) if DEFINES.match(toks[k])]
    return sorted({n for n in names if names.count(n) > 1 or n in elsewhere})


def meta_reason(status, path, text, deleted, elsewhere):
    """Why the goal operation PATH (status, its text, its deleted-line count or None) keeps the
    branch from being confined, or None: new, or added lines only, and shadowing nothing."""
    if status != "A" and deleted != 0:
        return f"{path} changes or removes lines of a goal operation (only new lines confine a branch)"
    words = shadowed(text, elsewhere(path))
    if words:
        return f"{path} defines {', '.join(words)} again (a word of another file or of its own)"
    return None


def rule_problems(path, text, foreign):
    """The rule breaks of one tactic file; FOREIGN is the data words other files define."""
    toks, problems = tokens(text), []
    own = defined_in(toks)
    own -= aliases(toks, own)
    for k, word in enumerate(toks):
        before = toks[k - 1] if k else ""
        if word in HOOKS:
            problems.append(f"{path}: writes a hook ({word}); a plug-in calls the API, it never reassigns a hook")
        elif word in STORES and before in foreign and before not in own:
            problems.append(f"{path}: writes {before} ({before} {word}), a data word of another file")
        elif word == "to" and k + 1 < len(toks) and toks[k + 1] in foreign and toks[k + 1] not in own:
            problems.append(f"{path}: writes {toks[k + 1]} (to {toks[k + 1]}), a data word of another file")
        elif SETTER.match(word) and not owns(path, before, own):
            problems.append(f"{path}: calls {word} for {before or 'nothing'}, not a kind this file defines")
    return problems


def changed_files(base):
    merge_base = git("merge-base", base, "HEAD").strip()
    found = {}
    for line in git("diff", "--name-status", "--no-renames", merge_base).splitlines():
        status, path = line.split("\t", 1)
        found[path] = status[0]
    for path in git("ls-files", "--others", "--exclude-standard").splitlines():
        found.setdefault(path, "A")
    return sorted((s, p) for p, s in found.items())


def deleted_lines(*revs):
    """{path: lines git's diff of REVS (a base and the worktree, or two commits) deletes}."""
    found = {}
    for line in git("diff", "--numstat", "--no-renames", *revs).splitlines():
        added, removed, path = line.split("\t", 2)
        found[path] = int(removed) if removed.isdigit() else None
    return found


def check(changed, read=None, deleted=None, elsewhere=None):
    """{"confined": bool, "problems": [rule breaks], "reasons": [why not confined], "tactics": [names]}
    for CHANGED ([(status, path)]). READ ( path -- text or None ) reads the worktree. DELETED
    ({path: deleted lines}) tells a goal operation that only gains lines; without it a changed
    one is refused. ELSEWHERE ( path -- set ) gives the words other Forth files define."""
    read = read or (lambda p: open(p, encoding="utf-8", errors="replace").read() if os.path.isfile(p) else None)
    deleted = deleted or {}
    elsewhere = elsewhere or definitions
    tactic_files = [(s, p) for s, p in changed if p.startswith(TACTICS) and p.endswith(".fs")]
    names = {os.path.splitext(os.path.basename(p))[0] for s, p in tactic_files if s != "D"} - {"all"}
    added = [p for s, p in tactic_files if s == "A" and not p.endswith("/all.fs")]
    reasons, problems = [], []
    if not added:
        reasons.append("no tactic file is added (src/front/tactics/NAME.fs)")
    for status, path in changed:
        allowed = (path.startswith(TACTICS) or is_doc(path)
                   or any(path.startswith(f"{TACTIC_TESTS}{n}/") for n in names)
                   or path in {f"{FAULTS_DIR}{n}.toml" for n in names}
                   or bool(added and BATCH.match(path)))
        if status != "D" and path.startswith(META_TACTIC) and path.endswith(".fs"):
            why = meta_reason(status, path, read(path) or "", deleted.get(path), elsewhere)
            if why:
                reasons.append(why)
            continue
        if status == "D" and not is_doc(path):
            allowed = False
        if not allowed:
            reasons.append(f"{path} lies outside the tactic's own files")
    # A goal operation that confines keeps the tactic files' rules too (no hook, no other file's data).
    plug_ins = tactic_files + [(s, p) for s, p in changed if p.startswith(META_TACTIC) and p.endswith(".fs")]
    if tactic_files:
        foreign = data_words({p for _, p in plug_ins})
        for status, path in plug_ins:
            if status != "D":
                problems += rule_problems(path, read(path) or "", foreign)
    return {"confined": not reasons and not problems, "problems": problems, "reasons": reasons,
            "tactics": sorted(names)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", default="main")
    parser.add_argument("--files", nargs="+", help="these files (as added) instead of git's changes")
    args = parser.parse_args(argv)
    os.chdir(git("rev-parse", "--show-toplevel").strip())
    changed = [("A" if os.path.exists(p) else "D", os.path.normpath(p)) for p in args.files] if args.files \
        else changed_files(args.base)
    deleted = {} if args.files else deleted_lines(git("merge-base", args.base, "HEAD").strip())
    result = check(changed, deleted=deleted)
    for problem in result["problems"]:
        print(f"check-tactic-plugins: {problem}", file=sys.stderr)
    if result["problems"]:
        return 1
    if result["reasons"]:
        print("check-tactic-plugins: not confined (the tier its files give applies): " + "; ".join(result["reasons"]))
        return 3
    print(f"check-tactic-plugins: confined: the tactic tier applies ({', '.join(result['tactics'])})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
