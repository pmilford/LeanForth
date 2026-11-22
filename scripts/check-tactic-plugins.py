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
directory for several tactics), a goal operation of src/front/meta-tactic/ that is new or is its
text at the merge base with named colon definitions put between its definitions (every
definition of the base token for token the same and in order, comments aside; review of
2026-11-21) and whose new words shadow nothing (none defined twice in it, none another Forth file
of src/ defines, none a Forth file of src/ or tests/ uses at the merge base, Gforth's host words
such as ndrop among them; the defining words are Forth's and Gforth's and the project's own, such
as context-slab:, lfa-code: and lf-tactic:, found as colon definitions that use one), or
documentation (scripts/test-tier.py's docs tier: Markdown, docs/, ...); and every tactic file it
adds or changes
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
import functools
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
DEFINES = re.compile(r"(?i)^(?::|2?variable|2?value|2?constant|create|defer|buffer:|fvariable|fvalue|"
                     r"fconstant|value|\+field|field:|cfield:|ffield:|2field:|sfield:|dffield:|"
                     r"begin-structure|synonym|alias|marker|user|wordlist:)$")
# Words that make a colon definition a defining word of its own (with DEFINES): what calls one
# reads the next word of the input as a name (defining_words).
PARSES = {"create", "parse-name", "parse-word"}
TRAILERS = {"immediate", "compile-only", "restrict"}
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
    parentheses, across lines too), strings (s" ." c" abort" to the closing quote) and the
    character after char or [char] (in [char] : no definition starts)."""
    out, closing = [], None
    for line in text.splitlines():
        if closing == '"':
            closing = None
        for word in line.split():
            if closing == "char":
                closing = None
                continue
            if closing:
                if word.endswith(closing):
                    closing = None
                continue
            if word.lower() in ("char", "[char]"):
                closing = "char"
            if word == "\\":
                break
            if word in ("(", ".("):
                closing = ")"
            elif word.lower() in STRING_START:
                closing = '"'
            else:
                out.append(word.lower())
    return out


def segments(toks):
    """TOKS cut into colon definitions (: or :noname to its ;, with immediate or compile-only
    after it) and the runs of other words between them, as tuples."""
    out, run, k = [], [], 0
    while k < len(toks):
        if toks[k] not in (":", ":noname"):
            run.append(toks[k])
            k += 1
            continue
        if run:
            out.append(tuple(run))
            run = []
        try:
            end = toks.index(";", k) + 1
        except ValueError:
            end = len(toks)
        while end < len(toks) and toks[end] in TRAILERS:
            end += 1
        out.append(tuple(toks[k:end]))
        k = end
    return out + [tuple(run)] if run else out


def is_defining(word, defining=frozenset()):
    return bool(DEFINES.match(word)) or word in defining


def names_defined(toks, defining=frozenset()):
    """The names TOKS define, in order, repeats kept: each colon definition's, and outside colon
    definitions the word after a defining word (DEFINES, or one of DEFINING)."""
    out = []
    for seg in segments(toks):
        if seg[0] == ":":
            out += seg[1:2]
        elif seg[0] != ":noname":
            out += [seg[k + 1] for k in range(len(seg) - 1) if is_defining(seg[k], defining)]
    return out


def defined_in(toks, defining=frozenset()):
    """The words TOKS define (the word after a defining word outside a colon definition)."""
    return set(names_defined(toks, defining))


def defining_words(token_lists):
    """The project's defining words: each colon definition of TOKEN_LISTS whose body uses a
    defining word (DEFINES, or one found so far) or reads a name (PARSES), to a fixed point:
    member-colon (its :), member: and context-slab: through it, lfa-code: (constant), lf-tactic:
    (parse-name)."""
    bodies = [(seg[1], set(seg[2:])) for toks in token_lists for seg in segments(toks)
              if seg[0] == ":" and len(seg) > 1]
    found = {name for name, body in bodies if body & PARSES or any(DEFINES.match(w) for w in body)}
    grown = True
    while grown:
        grown = False
        for name, body in bodies:
            if name not in found and body & found:
                found.add(name)
                grown = True
    return found


def only_added(base_toks, toks):
    """Whether TOKS is BASE_TOKS with named colon definitions put between its segments, every
    segment of the base kept, unchanged and in order: a word put inside a definition, a moved or
    removed one, a new constant or :noname changes what the file's callers get."""
    old, j = segments(base_toks), 0
    for seg in segments(toks):
        if j < len(old) and seg == old[j]:
            j += 1
        elif seg[0] != ":":
            return False
    return j == len(old)


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


@functools.lru_cache(maxsize=None)
def corpus():
    """{path: tokens} of the Forth files git tracks in src/ and tests/ (the worktree's text)."""
    found = {}
    for path in subprocess.run(["git", "ls-files", "src", "tests"], capture_output=True, text=True).stdout.split():
        if path.endswith(".fs"):
            try:
                with open(path, encoding="utf-8", errors="replace") as stream:
                    found[path] = tokens(stream.read())
            except OSError:
                continue
    return found


def sources():
    return {path: toks for path, toks in corpus().items() if path.startswith("src/")}


@functools.lru_cache(maxsize=None)
def src_defining():
    """The defining words of src/ (defining_words)."""
    return frozenset(defining_words(sources().values()))


def data_words(skip):
    """The data words (variable, value, create, buffer:) the Forth files of src/ define, but SKIP."""
    found = set()
    for path, toks in sources().items():
        if path not in skip:
            found |= {w.lower() for w in DATA_WORD.findall(" ".join(outside_colons(toks)))}
    return found


def definitions(skip):
    """The words the Forth files of src/ define (lower case), but SKIP: what a goal operation's
    file may not define again."""
    return {w for path, toks in sources().items() if path != skip
            for w in names_defined(toks, src_defining())}


def references(changed, base):
    """The words the Forth files of src/ and tests/ use at the merge base: every file but those
    CHANGED adds, a changed one's text at the base (BASE ( path -- text or None ); without it, the
    worktree's). What a new definition must not take over from the files loaded after it: a
    Gforth host word such as ndrop, another file's word, one a defining word of its own made."""
    status = {path: s for s, path in changed}
    found = set()
    for path, toks in corpus().items():
        if status.get(path) == "A":
            continue
        if path in status and base:
            toks = tokens(base(path) or "")
        found.update(toks)
    return found


def shadowed(text, elsewhere, base_text=None, used=frozenset(), defining=frozenset()):
    """(again, taken): the words TEXT defines twice or newly (not in BASE_TEXT) defines that
    ELSEWHERE (other files' definitions) holds; and those it newly defines that USED (the words
    the files use at the merge base) holds."""
    names = names_defined(tokens(text), defining)
    old = defined_in(tokens(base_text or ""), defining)
    new = {n for n in names if n not in old}
    again = {n for n in names if names.count(n) > 1} | (new & set(elsewhere))
    return sorted(again), sorted((new & set(used)) - again)


def meta_reason(status, path, text, base_text, elsewhere, used, defining):
    """Why the goal operation PATH (status, its text and its text at the merge base or None)
    keeps the branch from being confined, or None: new, or the base's with new colon definitions
    only, and none of its new words defined elsewhere or used by another file."""
    if status != "A" and base_text is None:
        return f"{path}: its text at the merge base is not known (only new definitions confine a branch)"
    if status != "A" and not only_added(tokens(base_text), tokens(text)):
        return (f"{path} changes, moves or removes a definition of a goal operation, or adds what is no "
                "colon definition (only new colon definitions confine a branch)")
    again, taken = shadowed(text, elsewhere(path), base_text, used, defining)
    if again:
        return f"{path} defines {', '.join(again)} again (a word of another file or of its own)"
    if taken:
        return (f"{path} defines {', '.join(taken)}, which Forth files already use (a Gforth host word "
                "or another file's: the files loaded after it would call the new one)")
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


def at_rev(rev):
    """A BASE for check: ( path -- the file's text at commit REV, or None )."""
    def read(path):
        run = subprocess.run(["git", "show", f"{rev}:{path}"], capture_output=True, text=True)
        return run.stdout if run.returncode == 0 else None
    return read


def check(changed, read=None, base=None, elsewhere=None, used=None, defining=None):
    """{"confined": bool, "problems": [rule breaks], "reasons": [why not confined], "tactics": [names]}
    for CHANGED ([(status, path)]). READ ( path -- text or None ) reads the worktree, BASE
    ( path -- text or None ) the merge base (at_rev; without it a changed goal operation is
    refused). ELSEWHERE ( path -- set ) gives the words other Forth files of src/ define, USED the
    words the Forth files use at the merge base (references), DEFINING the defining words
    (src_defining)."""
    read = read or (lambda p: open(p, encoding="utf-8", errors="replace").read() if os.path.isfile(p) else None)
    base = base or (lambda p: None)
    elsewhere = elsewhere or definitions
    defining = src_defining() if defining is None else defining
    # The merge base's words are read once, and only when a goal operation is changed.
    used_now = (lambda: used) if used is not None else functools.lru_cache(maxsize=None)(
        lambda: references(changed, base))
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
            why = meta_reason(status, path, read(path) or "", base(path), elsewhere, used_now(), defining)
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
    base = None if args.files else at_rev(git("merge-base", args.base, "HEAD").strip())
    result = check(changed, base=base)
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
