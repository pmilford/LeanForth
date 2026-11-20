#!/usr/bin/env python3
"""Ratchet on duplicated Forth code (owner, 2026-11-13, plans 9.4.8f and 9.4.8k). Part of `make test`.

Usage: python3 scripts/check-duplicates.py [--update-baseline] [--report] [--counts] [ROOT]
       python3 scripts/check-duplicates.py --explain GROUP | --plan [ROOT]
       python3 scripts/check-duplicates.py --extract GROUP --word NAME --stack "( a -- b )" --home FILE
                                           [--after WORD] [--comment TEXT] [--add-require] [--dry-run] [ROOT]
       python3 scripts/check-duplicates.py --extract-table FILE [--add-require] [--dry-run] [ROOT]
       python3 scripts/check-duplicates.py --rewrite --from "TOKENS" --to "TOKENS" [--paths PATH ...]
                                           [--add-require [FILE]] [--dry-run] [ROOT]

Parses the colon definitions of ROOT/src/**/*.fs (comments `\\ ...` and `( ... )` dropped; strings after `s"`, `."`,
`c"`, `abort"`, `s\\"`, `.(` and the word after `[char]`/`char` are single tokens) and lower-cases them. Words
defined in src/lib/ are shared vocabulary and stay literal everywhere. Each body gets two normal forms:

- The shape form alpha-renames every word defined in the same file (by `:`, `constant`, `variable`, `create`,
  `value`, `defer`, `+field`, `begin-structure`, `synonym` or any defining word whose name ends in `:`, such as
  `field:`, `context-slab:` or `store:`, but never a string literal that ends in `:`, such as `." fuel:"`) to a
  placeholder numbered by first appearance in the body. Copies whose
  helpers were renamed (`in-foo`, `ib-foo`) have one shape; so do parallel words that differ only in which local
  helper or field they use (a family: `lf-x-first@` and `lf-x-second@`).
- The copy form replaces every call of a colon word defined outside lib/ by that word's role: the hash of its own
  copy form (in the same file if it is defined there, else its only definition in src/), computed bottom-up;
  a constant of the same file defined from a number (`16 constant tag-nat`) by that number; other data words
  of the same file are placeholders as in the shape form. A copy that calls the original file's
  helpers (beta-inst.fs calling instantiate.fs's words where instantiate.fs calls its own) or its own renamed
  copies of them therefore has the original's copy form, though the shapes differ.

Definitions whose normal forms are identical form a group (shape groups, then copy groups not already inside a
shape group); groups of two or more definitions are duplicates.

MIN_TOKENS = 6 (8 until 2026-11-13). A body of five tokens or fewer is a trivial word (`: x-ok? ok? ;`, `: x-size
( n ) 8 * ;`, a field fetch); two files agree on those by accident and merging them would not make anything simpler.
At six and seven tokens the groups are still mostly real logic (a test of two fields, a loop step, a table
read): of the 83 groups outside src/front that the minimum of six added on main dc50d8eb, two in three were
copies (merged in reuse-out-2, or accepted with a reason) or families, and 28 false positives (idioms such as
the guarded test `dup a? if b else drop false then`), so the minimum is six. At five the groups are mostly
accessor pairs and idioms. (Stack comments do not count: they are dropped like all comments.)

Ratchet: tests/duplicates-baseline.json holds today's groups, keyed by a hash of the normal form, each with its
members (file:word) and a `reason` saying why it stays: `false positive: ...` (equal text, unrelated meaning; say
why it is not a copy), `accepted: ...` (a merge would make the code worse; say why), or `planned: <plan row> ...`
and `family, table-driven later: <plan row> ...` (a named pass merges it), whose text must name a plan row id
(as check-forth-quality.py's PLAN_ID reads one: 9.4.8k, FE1i-4, S2). The check fails when a group appears that is
not in the baseline, a baseline group has a member its record does not list (a copy added, even where another
went), or a group has no reason or a planned one without a plan row. Fixing a group (fewer members) never fails. Rewrite the
baseline with --update-baseline only in a reviewed commit, as for tests/forth-quality-baseline.json; it keeps the
reason of every group whose key or member list is unchanged, and leaves new ones without, so the check then fails
until each has a reason. --report prints every group, cross-file groups first; --counts the groups by folder.

Removing a group (owner, 2026-11-19; TESTING_STRATEGY.md "Removing a duplicate group"). A group is exact when
its members are the same tokens and each word in them names the same definition from every member's file
(its own, else the one its require closure loads), and no unprefixed number sits in a file that changes BASE;
else it is a shape group. GROUP is a key or a unique prefix of one.
- --explain GROUP prints the phrase, exact or shape and why, and each member: file:line, name, stack comment,
  folder, the wordlist in force there (module-open, set-current) and its source lines.
- --plan lists every group whose reason is not a false positive, by copies x tokens: exact or shape, the
  files and their folders, the lowest folder all members may require (src/README.md's layering; MAY_REQUIRE),
  a file every member loads that sees the phrase's words (the suggested --home), and the existing word:
  a member every other member's file loads, which they can call as it is.
- --extract GROUP --word NAME --stack S --home FILE defines `: NAME S PHRASE ;` (a comment line above it) in
  FILE, after --after WORD, else above the first member in FILE, else before its last module-close, else at
  its end; public when a member lives in another file and the place is private (ADR 0010); and replaces the
  phrase by NAME in every member, token for token, the rest of each line kept. It refuses a shape group, a
  NAME that exists with another body, a home that does not see a word of the phrase, and a member's file that
  does not load FILE, naming the require (--add-require adds it). A member named NAME, or one in FILE, is
  used as the word instead of a new one. The whole is worked out on a scratch copy of src/ and checked with
  the detector there: no group may appear or grow (the baseline drops the group and re-keys groups whose
  members are unchanged); then written, checked again, and restored on any difference. It prints the files
  and lines changed, planted faults whose text moved, and the members rewritten in src/kernel, src/core and
  src/import under "EXACT EXTRACTION BY SCRIPT", for the owner's report. --dry-run prints the diff only.
- --extract-table FILE applies one extraction per line (`group word "( stack )" home [after|-] ["comment"]`,
  shell quoting, # comments), all or none.

Rewriting a phrase (2026-11-19, clean-up round 3): --rewrite --from "TOKENS" --to "TOKENS" replaces every
occurrence of a phrase by another in the files of src/ (or of --paths, files or folders), token for token:
whitespace and line breaks do not matter, case does not (the replacement is written as given), and nothing in a
comment or a string is ever matched (`s\\"` strings end at their first unescaped quote; `[char] (` is a
character, not a comment). $NAME in --from is a wildcard for one word name (never a number, a string, a
control-flow, frame, stack, defining or parsing word such as `dup`, `constant` or `[']`), the same word wherever
it recurs; --to may use it, and the word's text is kept. A match with a comment between its tokens, right after
a word that reads the next one as a name (`'`, `[']`, `postpone`, `to`, `is`, `:`, a defining word), or inside
the definition of a word --to calls, is left and listed. A wildcard may still bind a value or a variable as
well as a constant: the tool does not check that evaluating it in a new order changes nothing. A file that cannot see a word --to adds is refused with the require it needs; --add-require adds the
require of the one file defining the word, or of FILE when given. Planted faults (tests/mutants/faults.toml and
faults.d/*.toml) on a changed file whose old text no longer occurs once are carried over by the same rewrite of
their old and new texts, and listed by id: name each in the commit message (mutants.py's history rule);
where the mutation lies inside the phrase, the old text alone is carried (the mutant then puts the old phrase back,
mutated); one whose old text holds only part of the phrase is named for a hand re-target. The result is checked with the detector on a
scratch copy first: a new or grown duplicate group refuses the whole (nothing written); groups it removes leave
the baseline. It prints each site as file:line word and, under "REWRITE BY SCRIPT", the sites in src/kernel,
src/core and src/import for the owner's report. --dry-run prints the diff only.
"""
import collections
import difflib
import hashlib
import importlib.util
import json
import os
import pathlib
import re
import shlex
import shutil
import sys
import tempfile

DEFAULT_ROOT = pathlib.Path(__file__).resolve().parent.parent
MIN_TOKENS = 6
STRING_OPENERS = {"s\"", ".\"", "c\"", "abort\"", "s\\\"", ".\\\"", ".("}
CHAR_WORDS = {"[char]", "char"}
DEFINERS = {"constant", "variable", "2constant", "2variable", "value", "2value", "create", "defer",
            "fvariable", "fconstant", "buffer:", "+field", "begin-structure", "synonym"}
NOT_DEFINERS = {"{:", "[:"}
REASONS = ("false positive:", "family, table-driven later:", "accepted:", "planned:")
PLANNED = ("family, table-driven later:", "planned:")


def plan_id():
    """check-forth-quality.py's PLAN_ID, the one reading of a plan row id."""
    spec = importlib.util.spec_from_file_location("cfq", pathlib.Path(__file__).with_name("check-forth-quality.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.PLAN_ID


PLAN_ID = plan_id()


def tokens(text):
    """(token, line) pairs of Forth source with comments removed; a string literal is one token."""
    return [(tok, line) for tok, line, _, _ in spans(text)]


def definer(word):
    """True for a word that defines the next word of the input: a standard one or a name ending in `:`; never a
    string literal (one token with a space, such as `." fuel:"`)."""
    return word in DEFINERS or (word.endswith(":") and len(word) > 1 and word not in NOT_DEFINERS
                                and " " not in word)


NUMBER = re.compile(r"-?(\$[0-9a-f]+|#?[0-9]+|%[01]+)")


def definitions(path, values=None):
    """[(name, line, body tokens)] of the colon definitions of a file, and its set of defined names; fills
    values {name: literal} for each `<number> constant <name>`."""
    return definitions_of_text(path.read_text(encoding="utf-8", errors="replace"), values)


def definitions_of_text(text, values=None):
    """definitions() of a file's text."""
    toks = tokens(text)
    defs, names, i = [], set(), 0
    values = {} if values is None else values
    while i < len(toks):
        word, line = toks[i]
        if word == ":" and i + 1 < len(toks):
            name, j = toks[i + 1][0], i + 2
            while j < len(toks) and toks[j][0] != ";":
                j += 1
            defs.append((name, line, [t for t, _ in toks[i + 2:j]]))
            names.add(name)
            i = j
        elif definer(word) and i + 1 < len(toks):
            names.add(toks[i + 1][0])
            if word == "constant" and i > 0 and NUMBER.fullmatch(toks[i - 1][0]):
                values[toks[i + 1][0]] = toks[i - 1][0]
        i += 1
    return defs, names


def normal_form(body, names, role=None):
    """The body with each file-local word replaced by a placeholder numbered by first appearance; with
    role ( word -> str or None ), each word that has a role is replaced by it first."""
    seen, out, skip = {}, [], False
    for t in body:
        r = None if skip or t in CHAR_WORDS or role is None else role(t)
        if skip:
            out.append(t)
            skip = False
        elif t in CHAR_WORDS:
            out.append(t)
            skip = True
        elif r is not None:
            out.append(r)
        elif t in names:
            out.append("#%d" % seen.setdefault(t, len(seen)))
        else:
            out.append(t)
    return out


def digest(form):
    return hashlib.sha1(" ".join(form).encode()).hexdigest()[:12]


class Tree:
    """The parsed definitions of ROOT/src and the roles of their colon words."""

    def __init__(self, root):
        self.root = root.resolve()
        self.values = collections.defaultdict(dict)          # path -> {constant: its literal value}
        self.parsed = {path: definitions(path, self.values[path])
                       for path in sorted((self.root / "src").rglob("*.fs"))}
        self.shared = set().union(*[names for path, (_, names) in self.parsed.items()
                                    if path.parent.name == "lib"])
        self.colon = collections.defaultdict(list)          # name -> [(path, index)], outside lib/
        for path, (defs, _) in self.parsed.items():
            if path.parent.name != "lib":
                for k, (name, _, _) in enumerate(defs):
                    self.colon[name].append((path, k))
        self.roles, self.busy = {}, set()

    def callee(self, word, path):
        """The definition a call of word in path reaches: the file's own last one, else the only one in src/."""
        if word in self.shared:
            return None
        found = self.colon.get(word, [])
        own = [d for d in found if d[0] == path]
        return own[-1] if own else (found[0] if len(found) == 1 else None)

    def role(self, ref):
        """The copy-form hash of the definition ref = (path, index); a cycle leaves the word a placeholder."""
        if ref not in self.roles:
            self.busy.add(ref)
            self.roles[ref] = "@" + digest(self.copy_form(*ref))
            self.busy.discard(ref)
        return self.roles[ref]

    def copy_form(self, path, k):
        defs, names = self.parsed[path]

        def role(word):
            if word in self.values[path]:
                return "=" + self.values[path][word]
            ref = self.callee(word, path)
            return None if ref is None or ref in self.busy else self.role(ref)
        return normal_form(defs[k][2], names - self.shared, role)

    def forms(self):
        """[(member, shape form, copy form)] for every colon definition; member = (file, line, name)."""
        out = []
        for path, (defs, names) in self.parsed.items():
            rel = str(path.relative_to(self.root))
            for k, (name, line, body) in enumerate(defs):
                out.append(((rel, line, name), normal_form(body, names - self.shared),
                            self.copy_form(path, k)))
        return out


def groups(root, min_tokens=MIN_TOKENS):
    """{key: {"tokens": n, "kind": "shape"|"copy", "members": [(file, line, name)]}} for every group of 2 or
    more identical bodies: the shape groups, then each copy group that no single shape group contains."""
    shape, copy = collections.defaultdict(list), collections.defaultdict(list)
    for member, sform, cform in Tree(root).forms():
        if len(sform) >= min_tokens:
            shape[digest(sform)].append((member, len(sform)))
            copy["c" + digest(cform)[1:]].append((member, len(cform)))
    found = {k: {"tokens": v[0][1], "kind": "shape", "members": [m for m, _ in v]}
             for k, v in shape.items() if len(v) > 1}
    covered = [set(g["members"]) for g in found.values()]
    for k, v in copy.items():
        members = [m for m, _ in v]
        if len(v) > 1 and not any(set(members) <= c for c in covered):
            found[k] = {"tokens": v[0][1], "kind": "copy", "members": members}
    return found


def spans_files(group):
    return len({f for f, _, _ in group["members"]}) > 1


def label(key, group):
    kind = "across files" if spans_files(group) else "within a file"
    return f"{key} ({group['tokens']} tokens, {len(group['members'])} copies, {group['kind']}, {kind})"


def names_of(group):
    return sorted(f"{f}:{name}" for f, _, name in group["members"])


def reason_problem(reason):
    """Why a baseline reason does not hold, or None: it must start with one of REASONS, and a planned one must
    name a plan row."""
    reason = str(reason or "")
    if not reason.startswith(REASONS):
        return f"group without a reason ({' | '.join(REASONS)})"
    if reason.startswith(PLANNED) and not PLAN_ID.search(reason):
        return "planned group without a plan row id (such as 9.4.8k)"
    return None


def added_members(group, old):
    """The members of group that the baseline record old does not list (as many times as it lists them)."""
    extra = collections.Counter(names_of(group)) - collections.Counter(old.get("members", []))
    return sorted(extra.elements())


def ratchet(now, base):
    problems = []
    for key, group in sorted(now.items()):
        old = base.get(key)
        added = added_members(group, old) if old is not None else None
        if old is None or added:
            what = "new duplicate group" if old is None else "group has members its record does not list"
            problems.append(f"{what}: {label(key, group)}")
            problems += [f"    {f}:{line} {name}" for f, line, name in group["members"]
                         if old is None or f"{f}:{name}" in added]
        elif reason_problem(old.get("reason")):
            problems.append(f"{reason_problem(old.get('reason'))}: {label(key, group)}")
    return problems


def baseline_of(now, old=None):
    """The baseline for groups now, keeping each reason of old whose key or member list is unchanged."""
    old = old or {}
    by_members = {tuple(sorted(v["members"])): v.get("reason") for v in old.values() if v.get("reason")}
    out = {}
    for k, g in sorted(now.items()):
        entry = {"tokens": g["tokens"], "copies": len(g["members"]), "kind": g["kind"],
                 "members": [f"{f}:{name}" for f, _, name in g["members"]]}
        reason = old.get(k, {}).get("reason") or by_members.get(tuple(names_of(g)))
        if reason:
            entry["reason"] = reason
        out[k] = entry
    return out


def folder(group):
    """The folder of a group: front when any copy is in src/front, else its folders joined by +."""
    found = sorted({f.split("/")[1] for f, _, _ in group["members"]})
    return "front" if "front" in found else "+".join(found)


def counts(now):
    tally = collections.Counter(folder(g) for g in now.values())
    print(f"{len(now)} groups; outside src/front {sum(c for k, c in tally.items() if k != 'front')}")
    for name, c in sorted(tally.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {name}: {c}")


def report(now, base):
    order = sorted(now.items(), key=lambda kv: (not spans_files(kv[1]), -kv[1]["tokens"] * len(kv[1]["members"])))
    for key, group in order:
        print(label(key, group))
        if base.get(key, {}).get("reason"):
            print("    reason: " + base[key]["reason"])
        for f, line, name in group["members"]:
            print(f"    {f}:{line} {name}")


# --- removing a group: explain, plan and extract (owner, 2026-11-19, "Tools first") -----------------
#
# A group is EXACT when its members' bodies are the same tokens and every word in them names the same
# definition from each member's file (the file's own, else the one its require closure loads); only an
# exact group can be replaced by one word without a review of meaning, since the word's body is then
# the members' text itself (OWNER_DECISIONS.md, "Clean-up: the stack approved": exact-phrase
# extractions made by this script merge after the Forth review and the tier). Any other group is a
# SHAPE group: the same code over different words.

# src/README.md's layering ("Rules" and the folder table): what a file of each folder may require.
# kernel, core and lib as the rules say; present, author and front as their rows say (front reads
# import only for the stage's names); import uses the kernel's public words (its row); cli all but
# program; program's row names no rule, so the folders it loads today (lib, author) are taken.
MAY_REQUIRE = {
    "lib": {"lib"},
    "core": {"lib", "core"},
    "kernel": {"lib", "core", "kernel"},
    "present": {"lib", "core", "present"},
    "author": {"lib", "core", "present", "author"},
    "front": {"lib", "core", "present", "author", "import", "front"},
    "import": {"lib", "core", "kernel", "import"},
    "program": {"lib", "author", "program"},
    "cli": {"lib", "core", "kernel", "import", "present", "author", "front", "cli"},
}
LAYER_ORDER = ["lib", "core", "present", "kernel", "author", "import", "front", "program", "cli"]
REVIEWED = ("src/kernel/", "src/core/", "src/import/")
LOADERS = {"require", "include", "needs"}
# Words a phrase cut out of a longer body may not hold: they reach the caller's frame.
FRAME_WORDS = {"exit", ">r", "r>", "r@", "2>r", "2r>", "2r@", "rdrop", "i", "j", "leave", "unloop",
               "recurse", "{:", "?leave"}
LINE_LIMIT = 100
# Words that may close a file after its last definition: the new word goes above them.
CLOSERS = {"[then]", "[endif]", "module-close", "decimal"}     # and `base !`


def spans(text):
    """(token, line, start, end) of Forth source with comments removed: tokens() with each token's
    offsets in TEXT (a string literal from its opener to its closing quote)."""
    out, i, line, n = [], 0, 1, len(text)
    while i < n:
        if text[i].isspace():
            line += text[i] == "\n"
            i += 1
            continue
        j = i
        while j < n and not text[j].isspace():
            j += 1
        tok, start, begin = text[i:j], line, i
        i = j
        low = tok.lower()
        if low == "\\":
            while i < n and text[i] != "\n":
                i += 1
        elif low == "(":
            while i < n and text[i] != ")":
                line += text[i] == "\n"
                i += 1
            i += 1
        elif low in STRING_OPENERS:
            end = ")" if low == ".(" else "\""
            k = i + 1
            while k < n and text[k] != end:
                line += text[k] == "\n"
                k += 2 if low.endswith("\\\"") and text[k] == "\\" else 1
            k = min(k, n)
            out.append((low + " " + text[i + 1:k], start, begin, min(k + 1, n)))
            i = k + 1
        elif low in CHAR_WORDS:
            while i < n and text[i] in " \t":
                i += 1
            k = i
            while k < n and not text[k].isspace():
                k += 1
            out.append((low + " " + text[i:k], start, begin, k))
            i = k
        else:
            out.append((low, start, begin, j))
    return out


class Definition:
    """A colon definition of a Source: name, line, token range (the `:` and the `;`), wordlist."""

    def __init__(self, source, colon, semi, context):
        self.source, self.colon, self.semi, self.context = source, colon, semi, context
        self.name = source.toks[colon + 1][0]
        self.line = source.toks[colon][1]
        self.body_range = (colon + 2, semi)

    @property
    def body(self):
        return [t[0] for t in self.source.toks[slice(*self.body_range)]]

    def raw(self, k):
        """The source text of body token K."""
        tok = self.source.toks[self.body_range[0] + k]
        return self.source.text[tok[2]:tok[3]]

    def stack_comment(self):
        text, at = self.source.text, self.source.toks[self.colon + 1][3]
        match = re.match(r"\s+(\(\s[^)]*\))", text[at:])
        return " ".join(match[1].split()) if match else ""

    def source_lines(self):
        first = self.line
        last = self.source.toks[self.semi][1] if self.semi < len(self.source.toks) else first
        return self.source.text.split("\n")[first - 1:last]

    def end_offset(self):
        return self.source.toks[self.semi][3] if self.semi < len(self.source.toks) else len(self.source.text)


class Source:
    """One Forth file: its tokens with offsets, colon definitions, defined names, requires and the
    wordlist in force at each top-level place (module-open, set-current, module-close; ADR 0010)."""

    def __init__(self, root, rel, text=None):
        self.rel, self.root = rel, root
        self.text = text if text is not None else (root / rel).read_text(encoding="utf-8", errors="replace")
        self.toks = spans(self.text)
        self.defs, self.defined, self.requires, self.marks = [], {}, [], []
        context, saved, i = "default", [], 0
        while i < len(self.toks):
            word, line = self.toks[i][0], self.toks[i][1]
            before = self.toks[i - 1][0] if i else ""
            if word == ":" and i + 1 < len(self.toks):
                j = i + 2
                while j < len(self.toks) and self.toks[j][0] != ";":
                    j += 1
                self.defs.append(Definition(self, i, j, context))
                self.defined.setdefault(self.toks[i + 1][0], i)
                i = j
            elif definer(word) and i + 1 < len(self.toks):
                self.defined.setdefault(self.toks[i + 1][0], i)
            elif word == "module-open":
                saved.append(context)
                context = f"{before} (private: module-open at line {line})"
                self.marks.append((self.toks[i][2], context))
            elif word == "module-close":
                context = saved.pop() if saved else "default"
                self.marks.append((self.toks[i][2], context))
            elif word == "set-current":
                private = "private" in before or "internal" in before
                context = (f"{before} ({'private' if private else 'public'}: set-current at line {line})"
                           if re.fullmatch(r"[\w-]+", before) and before != "get-current"
                           else f"restored at line {line} ({before} set-current)")
                self.marks.append((self.toks[i][2], context))
            elif word in LOADERS and i + 1 < len(self.toks):
                self.requires.append(self.toks[i + 1][0])
            i += 1

    def context_at(self, offset):
        found = "default"
        for at, context in self.marks:
            if at < offset:
                found = context
        return found

    def public_wordlist(self):
        """The public wordlist this file switches to with set-current (lf-lib in a library), or None."""
        names = [c.split()[0] for _, c in self.marks if "(public:" in c]
        return collections.Counter(names).most_common(1)[0][0] if names else None

    def private_wordlist(self, context):
        return context.split()[0] if context.split() and "private" in context else None


class Workspace:
    """Every Forth file of ROOT/src as Sources, with their require closures and word resolution."""

    def __init__(self, root, texts=None):
        self.root = pathlib.Path(root)
        texts = texts or {}
        names = sorted(str(p.relative_to(self.root)) for p in (self.root / "src").rglob("*.fs"))
        self.sources = {rel: Source(self.root, rel, texts.get(rel)) for rel in names}
        self.where = collections.defaultdict(list)          # name -> [file]
        for rel, src in self.sources.items():
            for name in src.defined:
                self.where[name].append(rel)
        self.closures = {}

    def loads(self, rel):
        """The files REL requires directly, as paths of the tree."""
        out = []
        for name in self.sources[rel].requires:
            for base in (os.path.dirname(rel), "."):
                candidate = os.path.normpath(os.path.join(base, name))
                if candidate in self.sources:
                    out.append(candidate)
                    break
        return out

    def closure(self, rel):
        """Every file REL loads, directly or not (not REL itself)."""
        if rel not in self.closures:
            seen, todo = set(), list(self.loads(rel))
            while todo:
                f = todo.pop()
                if f not in seen and f != rel:
                    seen.add(f)
                    todo += self.loads(f)
            self.closures[rel] = seen
        return self.closures[rel]

    def resolve(self, word, rel):
        """The file whose definition of WORD a use in REL reaches: REL's own, else the one file of its
        closure that defines it; a tuple of files when several do, None when none of src/ does (a
        Gforth word), "?" when only files REL does not load define it."""
        if word in self.sources[rel].defined:
            return rel
        seen = [f for f in self.where.get(word, []) if f in self.closure(rel)]
        if len(seen) == 1:
            return seen[0]
        if seen:
            return tuple(sorted(seen))
        return "?" if word in self.where else None

    def definition(self, rel, name, line=None):
        found = [d for d in self.sources[rel].defs if d.name == name and (line is None or d.line == line)]
        return found[-1] if found else None


def layer(rel):
    parts = pathlib.PurePath(rel).parts
    return parts[1] if len(parts) > 2 and parts[0] == "src" else "main"


def members_of(ws, group):
    """The Definitions of a group's members, in order."""
    return [ws.definition(f, name, line) or ws.definition(f, name) for f, line, name in group["members"]]


def words_of(body):
    """The tokens of a body that may name words: no string, no number, no character after char."""
    out, skip = [], False
    for t in body:
        if skip:
            skip = False
        elif t in CHAR_WORDS:
            skip = True
        elif " " not in t and not NUMBER.fullmatch(t):
            out.append(t)
    return out


def uses_base(src):
    return any(t[0] in ("hex", "base") for t in src.toks)


def exactness(ws, defs):
    """(True, why) when DEFS are an exact group; else (False, the first difference)."""
    bodies = [d.body for d in defs]
    if any(b != bodies[0] for b in bodies):
        k = next(i for i in range(max(map(len, bodies))) if len({tuple(b[i:i + 1]) for b in bodies}) > 1)
        seen = ", ".join(f"{d.name}: {(d.body[k:k + 1] or ['(end)'])[0]}" for d in defs)
        return False, f"token {k + 1} differs ({seen})"
    for word in sorted(set(words_of(bodies[0]))):
        reach = {d.source.rel: ws.resolve(word, d.source.rel) for d in defs}
        if len(set(reach.values())) > 1:
            return False, f"the same text, but `{word}` names " + "; ".join(
                f"{where} in {rel}" for rel, where in reach.items())
    if any(NUMBER.fullmatch(t) and t[0] not in "$#%-" for t in bodies[0]) and \
            any(uses_base(d.source) for d in defs):
        return False, "a number in a file that changes BASE may read differently"
    return True, "identical tokens, each word the same definition from every member's file"


def phrase_text(definition):
    return " ".join(definition.raw(k) for k in range(len(definition.body)))


def find_group(now, wanted):
    hits = [k for k in now if k.startswith(wanted)]
    if len(hits) != 1:
        raise SystemExit(f"duplicates: {'no' if not hits else 'more than one'} group key starts with {wanted!r}"
                         + (f" ({', '.join(sorted(hits))})" if hits else ""))
    return hits[0]


def explain(root, wanted, base):
    now = groups(root)
    key = find_group(now, wanted)
    group, ws = now[key], Workspace(root)
    defs = members_of(ws, group)
    exact, why = exactness(ws, defs)
    print(label(key, group))
    print(f"  {'EXACT' if exact else 'SHAPE'}: {why}")
    print(f"  phrase: {phrase_text(defs[0])}")
    if base.get(key, {}).get("reason"):
        print(f"  reason: {base[key]['reason']}")
    for d in defs:
        print(f"  {d.source.rel}:{d.line} {d.name} {d.stack_comment()}  [{layer(d.source.rel)}; wordlist: {d.context}]")
        if not exact:
            print(f"      tokens: {phrase_text(d)}")
        for text in d.source_lines():
            print(f"      | {text}")
    return 0


def home_files(ws, defs):
    """Files of src/ that every member's file loads (or is) and that see every word of the phrase."""
    files = [d.source.rel for d in defs]
    common = set.intersection(*[ws.closure(f) | {f} for f in files])
    needed = {ws.resolve(w, files[0]) for w in words_of(defs[0].body)} - {None}
    return [f for f in common if ws.sources[f].defs
            and all(isinstance(n, str) and (n == f or n in ws.closure(f)) for n in needed)]


def suggested_layer(ws, defs):
    """The lowest folder every member's folder may require (src/README.md) that may require the folders
    of the phrase's words, or None."""
    member_layers = {layer(d.source.rel) for d in defs}
    needed = set()
    for w in words_of(defs[0].body):
        where = ws.resolve(w, defs[0].source.rel)
        for f in (where if isinstance(where, tuple) else [where]):
            if f not in (None, "?"):
                needed.add(layer(f))
    for name in LAYER_ORDER:
        if all(name in MAY_REQUIRE.get(m, set()) for m in member_layers) and needed <= MAY_REQUIRE[name]:
            return name
    return None


def existing_word(ws, defs):
    """A member every other member's file loads: the word the others can call as it is."""
    for d in defs:
        if all(o is d or d.source.rel == o.source.rel or d.source.rel in ws.closure(o.source.rel) for o in defs):
            return d
    return None


def plan_rows(root, base):
    now, ws = groups(root), Workspace(root)
    rows = []
    for key, group in now.items():
        reason = base.get(key, {}).get("reason", "")
        if reason.startswith("false positive:"):
            continue
        defs = members_of(ws, group)
        exact = exactness(ws, defs)[0]
        homes = home_files(ws, defs) if exact else []
        best = max(homes, key=lambda f: (len(ws.closure(f)), f)) if homes else None
        found = existing_word(ws, defs) if exact else None
        rows.append({"key": key, "exact": exact, "copies": len(defs), "tokens": group["tokens"],
                     "score": len(defs) * group["tokens"],
                     "files": sorted({f"{d.source.rel} ({layer(d.source.rel)})" for d in defs}),
                     "layer": suggested_layer(ws, defs), "home": best,
                     "existing": f"{found.source.rel}:{found.name}" if found else None,
                     "reason": reason.split(":")[0] or "(none)"})
    return sorted(rows, key=lambda r: (-r["score"], r["key"]))


def plan(root, base):
    rows = plan_rows(root, base)
    print(f"{'score':>5} {'key':<12} {'kind':<5} {'n':>2}x{'tok':<3} reason / suggested home / existing word / files")
    for r in rows:
        home = r["home"] or (f"src/{r['layer']}/ (no file every member loads)" if r["layer"] else "none")
        print(f"{r['score']:>5} {r['key']:<12} {'exact' if r['exact'] else 'shape':<5} "
              f"{r['copies']:>2}x{r['tokens']:<3} {r['reason']}; home {home}"
              + (f"; existing {r['existing']}" if r["existing"] else ""))
        print("        " + ", ".join(r["files"]))
    exact = [r for r in rows if r["exact"]]
    print(f"{len(rows)} groups not false positive: {len(exact)} exact ({sum(1 for r in exact if r['existing'])} "
          f"with an existing word every member can call), {len(rows) - len(exact)} shape")
    return 0


# --- extract ------------------------------------------------------------------------------------------

class Refusal(Exception):
    """An extraction the script will not make, with the reason."""


def occurrences(body, phrase):
    """Start indices of the non-overlapping occurrences of PHRASE in BODY (token lists)."""
    out, k = [], 0
    while k + len(phrase) <= len(body):
        if body[k:k + len(phrase)] == phrase:
            out.append(k)
            k += len(phrase)
        else:
            k += 1
    return out


def replace_phrase(definition, phrase, name):
    """Edits (start, end, text) that replace each occurrence of PHRASE in DEFINITION's body by NAME;
    a phrase cut out of a longer body may not hold a word that reaches the caller's frame."""
    body = definition.body
    found = occurrences(body, phrase)
    if len(found) * len(phrase) < len(body) and FRAME_WORDS & set(phrase):
        raise Refusal(f"{definition.name}: the phrase is part of a longer body and holds "
                      f"{', '.join(sorted(FRAME_WORDS & set(phrase)))}")
    toks, first = definition.source.toks, definition.body_range[0]
    return [(toks[first + k][2], toks[first + k + len(phrase) - 1][3], name) for k in found]


def apply_edits(text, edits):
    for start, end, new in sorted(edits, reverse=True):
        text = text[:start] + new + text[end:]
    return text


def line_end(text, offset):
    at = text.find("\n", offset)
    return len(text) if at < 0 else at + 1


def line_start(text, offset):
    return text.rfind("\n", 0, offset) + 1


def new_definition(name, stack, phrase, comment):
    head = f": {name} {stack}".rstrip()
    lines = [f"\\ {comment}"] if comment else []
    one = f"{head} {phrase} ;"
    if len(one) <= LINE_LIMIT:
        return lines + [one]
    lines.append(head)
    current = " "
    for word in phrase.split(" ") + [";"]:
        if len(current) + 1 + len(word) > LINE_LIMIT and current.strip():
            lines.append(current)
            current = " "
        current += " " + word
    return lines + [current]


def insertion_point(ws, home, after, defs):
    """The offset in HOME where the new word goes, and what to say about it."""
    src = ws.sources[home]
    firsts = [d for d in defs if d.source.rel == home]
    if after:
        target = ws.definition(home, after.lower())
        if target is None:
            raise Refusal(f"--after {after}: {home} defines no word {after}")
        at = line_end(src.text, target.end_offset())
        late = [d for d in firsts if src.toks[d.colon][2] < at]
        if late:
            raise Refusal(f"--after {after} puts the word below {late[0].name} ({home}:{late[0].line}), "
                          "a member that must call it; name an earlier word")
        return at, f"after {after}"
    if firsts:
        first = min(firsts, key=lambda d: d.colon)
        at = line_start(src.text, src.toks[first.colon][2])
        while at > 0:   # above the comment lines directly over the first member
            prev = line_start(src.text, at - 1)
            if not src.text[prev:at].lstrip().startswith("\\") or src.text[prev:at].strip() == "\\":
                break
            at = prev
        return at, f"above {first.name}, the first member in {home}"
    closes = [t for t in src.toks if t[0] == "module-close"]
    if closes:
        return line_start(src.text, closes[-1][2]), "at the end, before module-close"
    k = len(src.toks)      # above the closing lines: BASE given back, the load guard's [then]
    while k:
        if src.toks[k - 1][0] in CLOSERS:
            k -= 1
        elif k > 1 and [t[0] for t in src.toks[k - 2:k]] == ["base", "!"]:
            k -= 2
        else:
            break
    if k == len(src.toks):
        return len(src.text), "at the end"
    at = line_start(src.text, src.toks[k][2])
    if k and src.toks[k - 1][2] >= at:
        raise Refusal(f"the end of {src.rel} shares a line with its closing words: give --after WORD")
    return at, f"at the end, before `{src.text[at:].strip().splitlines()[0]}`"


def require_text(member, home):
    rel = os.path.relpath(home, os.path.dirname(member))
    return f"require {rel if rel.startswith('..') else './' + rel}"


def add_require(src, line):
    """(offset, text): the require line after SRC's last top-level require, else above its first code."""
    loads = [t for t in src.toks if t[0] in LOADERS]
    if loads:
        at = line_end(src.text, loads[-1][2])
    else:
        at = line_start(src.text, src.toks[0][2]) if src.toks else len(src.text)
    return at, line + "\n"


class Extraction:
    """One extraction worked out on a Workspace: the new texts of the files it changes."""

    def __init__(self, ws, group_key, group, name, stack, home, after=None, comment=None, add_requires=False):
        self.ws, self.key, self.name = ws, group_key, name.lower()
        self.home = os.path.normpath(home)
        self.texts, self.notes, self.rewritten = {}, [], []
        if self.home not in ws.sources:
            raise Refusal(f"--home {home} is no Forth file of src/")
        defs = members_of(ws, group)
        exact, why = exactness(ws, defs)
        if not exact:
            raise Refusal(f"group {group_key} is a shape group, not an exact one ({why}): "
                          "its members differ, so one word cannot replace them unchanged; --explain shows them")
        phrase, text = defs[0].body, phrase_text(defs[0])
        users = self.word_in_use(defs, phrase)
        edits = collections.defaultdict(list)
        if users is None:
            at, where = insertion_point(ws, self.home, after, defs)
            self.check_visible(defs, phrase, at)
            block = new_definition(name, stack, text, comment or f"{name}: shared by "
                                   + ", ".join(d.name for d in defs) + " (check-duplicates.py --extract)")
            block = self.in_public(at, block, defs)
            lead = "\n" if at and not ws.sources[self.home].text[:at].endswith("\n") else ""
            edits[self.home].append((at, at, lead + "\n".join(block) + "\n"))
            self.notes.append(f"defined {name} in {self.home}, {where}")
            callee = name
        else:
            callee = users.name
            self.notes.append(f"used the existing word {users.name} ({users.source.rel}:{users.line})")
        for d in defs:
            if users is not None and d is users:
                continue
            edits[d.source.rel] += replace_phrase(d, phrase, callee)
            self.rewritten.append(f"{d.source.rel}:{d.line} {d.name}")
        target = users.source.rel if users is not None else self.home
        for d in defs:
            rel = d.source.rel
            if rel == target or target in ws.closure(rel):
                continue
            if rel in ws.closure(target):
                raise Refusal(f"{target} loads {rel}, so {rel} cannot load {target}: choose another --home")
            line = require_text(rel, target)
            if not add_requires:
                raise Refusal(f"{rel} does not load {target}, directly or not: it needs `{line}` "
                              "(give --add-require to add it)")
            at = add_require(ws.sources[rel], line)[0]
            edits[rel].append((at, at, line + "\n"))
            self.notes.append(f"added `{line}` to {rel}")
        for rel, changes in edits.items():
            self.texts[rel] = apply_edits(ws.sources[rel].text, changes)

    def word_in_use(self, defs, phrase):
        """The member to call instead of a new word: one named NAME, or one in HOME; refuses a NAME that
        exists with another body."""
        for d in defs:
            if d.name == self.name:
                return d
        for rel in self.ws.where.get(self.name, []):
            other = self.ws.definition(rel, self.name)
            raise Refusal(f"{self.name} already exists with another body ({rel}"
                          + (f":{other.line})" if other else ", not a colon definition)"))
        in_home = [d for d in defs if d.source.rel == self.home]
        return in_home[0] if in_home else None

    def check_visible(self, defs, phrase, at):
        """Every word of the phrase that src/ defines must be one HOME loads, or defines above AT."""
        closure = self.ws.closure(self.home)
        for w in sorted(set(words_of(phrase))):
            where = self.ws.resolve(w, defs[0].source.rel)
            if where is None:
                continue
            if not isinstance(where, str) or where == "?" or (where != self.home and where not in closure):
                raise Refusal(f"{self.home} cannot see `{w}` (defined in {where}): choose a --home that loads it")
            src = self.ws.sources[self.home]
            if where == self.home and src.toks[src.defined[w]][2] >= at:
                raise Refusal(f"`{w}` is defined in {self.home} below the place of the new word")

    def in_public(self, at, block, defs):
        """BLOCK wrapped to compile into the public wordlist when the place is private and a member
        lives in another file."""
        src = self.ws.sources[self.home]
        context = src.context_at(at)
        private = src.private_wordlist(context)
        if not private or all(d.source.rel == self.home for d in defs):
            return block
        public = src.public_wordlist()
        if public is None:
            raise Refusal(f"{self.home} is private at that place ({context}) and names no public wordlist")
        self.notes.append(f"compiled into {public} (public): {self.home} is private there")
        return [f"{public} set-current"] + block + [f"{private} set-current"]


def write_texts(root, texts):
    for rel, text in texts.items():
        (pathlib.Path(root) / rel).write_text(text, encoding="utf-8")


def diff_lines(root, texts):
    out = []
    for rel, new in sorted(texts.items()):
        old = (pathlib.Path(root) / rel).read_text(encoding="utf-8", errors="replace")
        out += difflib.unified_diff(old.splitlines(True), new.splitlines(True), "a/" + rel, "b/" + rel)
    return out


def rekeyed(before, after, removed):
    """(problems, new baseline mapping): each group AFTER matched to one BEFORE by key or by member list;
    a group matching none is new, one with members its match lacks has grown."""
    by_members = {tuple(names_of(g)): k for k, g in before.items()}
    problems, moves = [], {}
    for key, group in after.items():
        old = key if key in before and key not in removed else by_members.get(tuple(names_of(group)))
        if old is None or old in removed:
            problems.append(f"new group {label(key, group)}: " + ", ".join(names_of(group)))
        elif added_members(group, {"members": names_of(before[old])}):
            problems.append(f"group {key} grew: " + ", ".join(added_members(group, {"members": names_of(before[old])})))
        elif old != key:
            moves[old] = key
    return problems, moves


def fault_problems(root, texts):
    """Planted faults (tests/mutants) whose old text the new texts no longer hold exactly once."""
    try:
        mutants = importlib.util.spec_from_file_location("mutants", pathlib.Path(root) / "scripts/mutants.py")
        module = importlib.util.module_from_spec(mutants)
        mutants.loader.exec_module(module)
        faults = module.load_list(pathlib.Path(root) / "tests/mutants/faults.toml")
    except Exception:       # no fault list or runner in this tree: nothing to check
        return []
    return [f"fault {f['id']} ({f['file']}): its old text now occurs {texts[f['file']].count(f['old'])} times; "
            "re-target it" for f in faults if f["file"] in texts and texts[f["file"]].count(f["old"]) != 1]


def extract(root, specs, base, dry_run=False, add_requires=False):
    """Apply SPECS (dicts: group, word, stack, home, after, comment) in order, all or none: worked out
    on a scratch copy of src/, checked there with the detector, then written. The exit status."""
    root = pathlib.Path(root)
    before = groups(root)
    wanted = [(find_group(before, s["group"]), s) for s in specs]
    with tempfile.TemporaryDirectory(prefix="leanforth-extract-") as scratch:
        shutil.copytree(root / "src", pathlib.Path(scratch) / "src")
        texts, done, current = {}, [], dict(before)
        try:
            for key, spec in wanted:
                members = names_of(before[key])
                live = next((k for k, g in current.items() if names_of(g) == members), None)
                if live is None:
                    raise Refusal(f"group {key} changed under an earlier extraction of the table")
                one = Extraction(Workspace(scratch), live, current[live], spec["word"], spec.get("stack", ""),
                                 spec["home"], spec.get("after"), spec.get("comment"), add_requires)
                write_texts(scratch, one.texts)
                texts.update(one.texts)
                done.append((key, spec, one))
                current = groups(pathlib.Path(scratch))
        except Refusal as why:
            print(f"refused: {why}")
            return 1
        problems, moves = rekeyed(before, current, {k for k, _, _ in done})
        if problems:
            print("refused: the extraction would change other groups (nothing written):")
            print("\n".join("  " + p for p in problems))
            return 1
    new_base = {k: v for k, v in base.items() if k not in {key for key, _, _ in done}}
    for old, new in moves.items():
        if old in new_base:
            entry = baseline_of({new: current[new]})[new]
            if new_base[old].get("reason"):
                entry["reason"] = new_base[old]["reason"]
            del new_base[old]
            new_base[new] = entry
    base_text = json.dumps(new_base, indent=1, sort_keys=True) + "\n"
    base_path = root / "tests/duplicates-baseline.json"
    diff = diff_lines(root, texts)
    if dry_run:
        print("".join(diff), end="")
        if base_path.exists() and base_path.read_text() != base_text:
            print(f"(and tests/duplicates-baseline.json: {len(done)} group(s) removed, {len(moves)} re-keyed)")
        extraction_report(done, texts, diff, root, dry_run=True)
        return 0
    originals = {rel: (root / rel).read_text(encoding="utf-8") for rel in texts}
    old_base = base_path.read_text() if base_path.exists() else None
    write_texts(root, texts)
    base_path.write_text(base_text)
    after = groups(root)
    if {k: names_of(g) for k, g in after.items()} != {k: names_of(g) for k, g in current.items()}:
        write_texts(root, originals)
        if old_base is None:
            base_path.unlink()
        else:
            base_path.write_text(old_base)
        print("refused: the written tree's groups differ from the checked copy's; every file restored")
        return 1
    extraction_report(done, texts, diff, root)
    return 0


def extraction_report(done, texts, diff, root, dry_run=False):
    added = sum(1 for d in diff if d.startswith("+") and not d.startswith("+++"))
    removed = sum(1 for d in diff if d.startswith("-") and not d.startswith("---"))
    print(f"{'would change' if dry_run else 'changed'} {len(texts)} file(s), +{added} -{removed} lines: "
          + ", ".join(sorted(texts)))
    reviewed = []
    for key, spec, one in done:
        for note in one.notes:
            print(f"  {key}: {note}")
        print(f"  {key}: members rewritten: " + ", ".join(one.rewritten))
        reviewed += [(key, spec, m) for m in one.rewritten if m.startswith(REVIEWED)]
    for problem in fault_problems(root, texts):
        print("  warning: " + problem)
    print("EXACT EXTRACTION BY SCRIPT (scripts/check-duplicates.py --extract; OWNER_DECISIONS.md "
          "\"Clean-up: the stack approved\"): members rewritten in src/kernel, src/core and src/import:")
    for key, spec, member in reviewed:
        print(f"- {member} -> {spec['word']} (group {key}, in {spec['home']})")
    if not reviewed:
        print("- none")


# --- rewrite ------------------------------------------------------------------------------------------

WILDCARD = re.compile(r"\$[A-Za-z][A-Za-z0-9_]*")
# Words that take the next word of the input as a name or a character, not as a call: a phrase may not
# start right after one (`['] dup ...`, `postpone dup ...`), and a wildcard never binds one.
PARSING_WORDS = {"'", "[']", "postpone", "[compile]", "char", "[char]", "to", "+to", "is", "[is]",
                 "action-of", "defers", "[defined]", "[undefined]", "marker", ":"}
# The stack words: a wildcard binding one would change the phrase's stack effect (`dup over = ...`).
STACK_WORDS = {"dup", "drop", "swap", "over", "rot", "-rot", "nip", "tuck", "pick", "roll", "?dup",
               "2dup", "2drop", "2swap", "2over", "2rot", "2nip", "2tuck", "3dup", "3drop", "depth"}
# What a wildcard never stands for: the caller's frame, control flow, stack words, defining and parsing
# words, as the chained form would tick or move it.
NOT_A_NAME = FRAME_WORDS | LOADERS | PARSING_WORDS | STACK_WORDS | DEFINERS | {
    ";", ":noname", "[:", ";]", "if", "else", "then", "endif", "ahead", "begin", "while", "repeat",
    "until", "again", "do", "?do", "loop", "+loop", "case", "of", "endof", "endcase",
    "literal", "[", "]", "does>", "immediate", "\\", "("}


def names_next(word):
    """True for a word after which the next word of the input is a name or a character, not a call."""
    return word in PARSING_WORDS or definer(word)
MEASURE_LIMIT = 90          # forth-metrics.py's long line


class Pattern:
    """A phrase rewrite: --from tokens (lower case; $NAME a wildcard for one word name, the same word
    wherever it recurs) and the --to tokens, which may use the wildcards of --from."""

    def __init__(self, frm, to):
        self.frm = [t if WILDCARD.fullmatch(t) else t.lower() for t in frm.split()]
        self.to = [t if WILDCARD.fullmatch(t) else t.lower() for t in to.split()]
        if not self.frm:
            raise Refusal("--from is empty")
        slots = {t for t in self.frm if WILDCARD.fullmatch(t)}
        unknown = sorted({t for t in self.to if WILDCARD.fullmatch(t)} - slots)
        if unknown:
            raise Refusal(f"--to uses {', '.join(unknown)}, which --from does not bind")
        if any(" " in t for t in self.frm + self.to):
            raise Refusal("a phrase may not hold a string literal")
        self.new_words = sorted({t for t in words_of(self.to) if not WILDCARD.fullmatch(t)}
                                - set(self.frm) - NOT_A_NAME)

    def match(self, toks, k):
        """{wildcard: token index} when the phrase starts at toks[k], else None."""
        bound = {}
        if k + len(self.frm) > len(toks):
            return None
        for i, p in enumerate(self.frm):
            tok = toks[k + i][0]
            if not WILDCARD.fullmatch(p):
                if tok != p:
                    return None
            elif " " in tok or NUMBER.fullmatch(tok) or tok in NOT_A_NAME or definer(tok):
                return None
            elif p in bound and toks[bound[p]][0] != tok:
                return None
            else:
                bound.setdefault(p, k + i)
        return bound

    def text(self, raw, bound):
        """The replacement, each wildcard by the raw source text of the token it bound."""
        return " ".join(raw(bound[t]) if t in bound else t for t in self.to)

    def sites(self, text):
        """[(start, end, replacement, first token index, problem or None)] of the non-overlapping matches
        in TEXT; a match with a comment between its tokens is a site with a problem, not rewritten."""
        toks, out, k = spans(text), [], 0
        while k < len(toks):
            bound = self.match(toks, k)
            if bound is None:
                k += 1
                continue
            last = k + len(self.frm) - 1
            gaps = [text[toks[i][3]:toks[i + 1][2]] for i in range(k, last)]
            problem = "a comment inside the phrase" if any(g.strip() for g in gaps) else None
            if k > 0 and names_next(toks[k - 1][0]):
                problem = f"after `{toks[k - 1][0]}`, which reads its first word as a name"
            new = self.text(lambda i: text[toks[i][2]:toks[i][3]], bound)
            out.append((toks[k][2], toks[last][3], new, k, problem))
            k = last + 1
        return out

    def apply(self, text):
        """TEXT rewritten at every site without a problem, and the number of such sites."""
        good = [(s, e, new) for s, e, new, _, problem in self.sites(text) if problem is None]
        return apply_edits(text, good), len(good)


class Rewrite:
    """A phrase rewrite worked out on a Workspace: the new texts of the src/ files it changes, the
    sites, the sites left and the requires added."""

    def __init__(self, ws, pattern, paths, home=None, allowed=False):
        self.ws, self.pattern = ws, pattern
        self.texts, self.sites, self.left, self.notes = {}, [], [], []
        for word in pattern.new_words:
            if not ws.where.get(word):
                self.notes.append(f"`{word}` is defined nowhere in src/: taken as a Gforth word")
        for rel in sorted(ws.sources):
            if paths and not any(rel == p or rel.startswith(p.rstrip("/") + "/") for p in paths):
                continue
            src = ws.sources[rel]
            edits = []
            for start, end, new, k, problem in pattern.sites(src.text):
                where = self.definition_at(src, k)
                place = f"{rel}:{src.toks[k][1]} {where.name if where else '(outside a definition)'}"
                if problem is None and where is not None and where.name in pattern.to:
                    problem = f"inside the definition of {where.name}, which the new phrase calls"
                if problem:
                    self.left.append(f"{place}: {problem}")
                    continue
                edits.append((start, end, new))
                self.sites.append(place)
            if edits:
                edits += self.requires(rel, edits, home, allowed)
                self.texts[rel] = apply_edits(src.text, edits)

    @staticmethod
    def definition_at(src, k):
        return next((d for d in src.defs if d.colon < k < d.semi), None)

    def requires(self, rel, edits, given, allowed):
        """The require edits REL needs to see each new word of the phrase; refuses a word it cannot see."""
        out, first = [], min(s for s, _, _ in edits)
        for word in self.pattern.new_words:
            where = self.ws.resolve(word, rel)
            if where is None:
                continue                      # a Gforth or standard word
            if isinstance(where, tuple):
                raise Refusal(f"{rel}: `{word}` is defined by several files it loads ({', '.join(where)})")
            src = self.ws.sources[rel]
            if where == rel:
                if src.toks[src.defined[word]][2] > first:
                    raise Refusal(f"{rel}: `{word}` is defined below the first place it would be used")
                continue
            if where != "?":
                continue
            home = given or self.home_of(word)
            if not allowed:
                raise Refusal(f"{rel} does not load the definition of `{word}`: it needs "
                              f"`{require_text(rel, home)}` (give --add-require to add it)")
            if rel in self.ws.closure(home) or rel == home:
                raise Refusal(f"{home} loads {rel}, so {rel} cannot load it")
            line = require_text(rel, home)
            if any(t == line + "\n" for _, _, t in out):
                continue
            at = add_require(self.ws.sources[rel], line)[0]
            out.append((at, at, line + "\n"))
            self.notes.append(f"added `{line}` to {rel}")
        return out

    def home_of(self, word):
        files = self.ws.where.get(word, [])
        if len(files) != 1:
            raise Refusal(f"`{word}` is defined in {len(files)} files ({', '.join(files)}): "
                          "name the one to load with --add-require FILE")
        return files[0]


FAULT_HEAD = re.compile(r"^\[\[fault\]\]\s*$", re.M)


def fault_files(root):
    folder = pathlib.Path(root) / "tests/mutants"
    return [p for p in [folder / "faults.toml"] + sorted((folder / "faults.d").glob("*.toml")) if p.exists()]


def fault_rewrites(root, pattern, texts):
    """({toml path: new text}, [(id, new changed?)], [notes]): the planted faults on a changed file whose
    old text the new file no longer holds, re-targeted by the same rewrite of their old and new texts; where
    the mutation lies inside the phrase (the rewrite does not apply to the new text), only the old text is
    re-targeted, so the mutant puts the old phrase back with its mutation."""
    import tomllib
    changed, done, problems, kept = {}, [], [], []
    for path in fault_files(root):
        text = path.read_text(encoding="utf-8")
        entries = tomllib.loads(text).get("fault", [])
        heads = [m.start() for m in FAULT_HEAD.finditer(text)] + [len(text)]
        if len(heads) - 1 != len(entries):
            problems.append(f"{path.relative_to(root)}: its [[fault]] heads and entries disagree; not read")
            continue
        out, cursor = [], 0
        for k, fault in enumerate(entries):
            new_file = texts.get(fault.get("file"))
            if new_file is None or new_file.count(fault["old"]) == 1:
                continue
            old, n_old = pattern.apply(fault["old"])
            new, n_new = pattern.apply(fault["new"])
            if n_old == 0 or new_file.count(old) != 1:
                problems.append(f"fault {fault['id']} ({fault['file']}): its old text no longer occurs once "
                                "and the rewrite cannot carry it over; re-target it by hand")
                continue
            if n_new != n_old:      # the mutation is inside the phrase: the mutant puts back the old,
                new = fault["new"]  # mutated text in place of the rewritten one, which still tests the caller
                kept.append(fault["id"])
            block = text[heads[k]:heads[k + 1]]
            for key, before, after in (("old", fault["old"], old), ("new", fault["new"], new)):
                if before == after:
                    continue
                quoted = f"{key} = '''{before}'''"
                if block.count(quoted) != 1 or "'''" in after:
                    problems.append(f"fault {fault['id']}: its {key} text is not one '''-quoted string; "
                                    "re-target it by hand")
                    break
                block = block.replace(quoted, f"{key} = '''{after}'''")
            else:
                out.append((heads[k], heads[k + 1], block))
                done.append((fault["id"], new != fault["new"]))
        if out:
            new_text = apply_edits(text, out)
            parsed = tomllib.loads(new_text).get("fault", [])
            if len(parsed) != len(entries):
                problems.append(f"{path.relative_to(root)}: the re-targeted list does not parse back")
                continue
            changed[path] = new_text
    problems += [f"fault {i}: the mutation is inside the phrase; its new text, the old phrase mutated, now "
                 "replaces the rewritten line" for i in kept]
    return changed, done, problems


def rewrite(root, frm, to, paths, home=None, allowed=False, dry_run=False):
    """Rewrite every occurrence of the phrase FRM by TO in ROOT/src (or PATHS), worked out on a scratch copy
    and checked with the detector, then written with the planted faults it moved; a file that cannot see a
    new word of TO gets the require of HOME (else of the one file defining the word) when ALLOWED. The exit
    status."""
    root = pathlib.Path(root)
    try:
        pattern = Pattern(frm, to)
        if home:
            home = os.path.normpath(home)
            if not (root / home).is_file():
                raise Refusal(f"--add-require {home}: no such file")
        one = Rewrite(Workspace(root), pattern, paths, home, allowed or bool(home))
    except Refusal as why:
        print(f"refused: {why}")
        return 1
    for left in one.left:
        print(f"  left: {left}")
    if not one.texts:
        print("rewrote nothing: the phrase occurs nowhere it may be rewritten")
        return 0 if not one.left else 1
    before = groups(root)
    with tempfile.TemporaryDirectory(prefix="leanforth-rewrite-") as scratch:
        shutil.copytree(root / "src", pathlib.Path(scratch) / "src")
        write_texts(scratch, one.texts)
        after = groups(pathlib.Path(scratch))
    path = root / "tests/duplicates-baseline.json"
    base = json.loads(path.read_text()) if path.exists() else {}
    new_base = baseline_of(after, base)
    unexplained = [k for k, v in new_base.items() if reason_problem(v.get("reason")) and k not in base]
    grown = [k for k, g in after.items() if k in base and added_members(g, base[k])]
    if unexplained or grown:
        print("refused: the rewrite would make a duplicate group or add a member to one (nothing written):")
        for k in unexplained + grown:
            print("  " + label(k, after[k]) + ": " + ", ".join(names_of(after[k])))
        return 1
    faults, moved, problems = fault_rewrites(root, pattern, one.texts)
    gone = sorted(set(base) - set(new_base))
    diff = diff_lines(root, one.texts)
    if dry_run:
        print("".join(diff), end="")
    else:
        write_texts(root, one.texts)
        for fpath, text in faults.items():
            fpath.write_text(text, encoding="utf-8")
        path.write_text(json.dumps(new_base, indent=1, sort_keys=True) + "\n")
    rewrite_report(one, diff, moved, problems, gone, dry_run)
    return 0


def rewrite_report(one, diff, moved, problems, gone, dry_run):
    added = sum(1 for d in diff if d.startswith("+") and not d.startswith("+++"))
    removed = sum(1 for d in diff if d.startswith("-") and not d.startswith("---"))
    print(f"{'would rewrite' if dry_run else 'rewrote'} {len(one.sites)} site(s) in {len(one.texts)} file(s), "
          f"+{added} -{removed} lines:")
    for site in one.sites:
        print(f"  {site}")
    for note in one.notes:
        print(f"  {note}")
    long = [d[1:].rstrip("\n") for d in diff if d.startswith("+") and not d.startswith("+++")
            and len(d.rstrip("\n")) - 1 > MEASURE_LIMIT]
    for line in long:
        print(f"  warning: a line over {MEASURE_LIMIT} characters: {line.strip()[:60]}...")
    if gone:
        print(f"  duplicate groups gone: {', '.join(gone)}")
    print("  planted faults re-targeted (name each in the commit message): " + (", ".join(f"{i}{' (new text changed)' if n else ''}"
                                                       for i, n in moved) or "none"))
    for problem in problems:
        print("  warning: " + problem)
    print("REWRITE BY SCRIPT (scripts/check-duplicates.py --rewrite): sites in src/kernel, src/core and "
          "src/import:")
    reviewed = [s for s in one.sites if s.startswith(REVIEWED)]
    print("\n".join(f"- {s}" for s in reviewed) or "- none")


def table_specs(path):
    """The extractions of an --extract-table file: one per line, `group word "( stack )" home [after]
    ["comment"]` (shell quoting), blank lines and # comments skipped."""
    specs = []
    for number, line in enumerate(pathlib.Path(path).read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = shlex.split(line)
        if not 4 <= len(parts) <= 6:
            raise SystemExit(f"{path}:{number}: expected group word stack home [after] [comment]")
        spec = dict(zip(("group", "word", "stack", "home", "after", "comment"), parts))
        if spec.get("after") in ("", "-"):
            spec["after"] = None
        specs.append(spec)
    return specs


def option(argv, name):
    if name not in argv:
        return None
    k = argv.index(name)
    if k + 1 >= len(argv):
        raise SystemExit(f"{name} needs a value")
    return argv[k + 1]


VALUED = ("--explain", "--extract", "--word", "--stack", "--home", "--after", "--comment", "--extract-table",
          "--from", "--to")


def rewrite_options(argv):
    """(argv without --paths' values and --add-require's file, the paths, the file or None): --paths takes
    every relative path after it, --add-require one argument ending in .fs when one follows."""
    rest, paths, home, k = [], [], None, 0
    while k < len(argv):
        a = argv[k]
        if a == "--paths":
            k += 1
            while k < len(argv) and not argv[k].startswith("--") and not os.path.isabs(argv[k]):
                paths.append(os.path.normpath(argv[k]))
                k += 1
            continue
        rest.append(a)
        if a == "--add-require" and k + 1 < len(argv) and argv[k + 1].endswith(".fs"):
            home = argv[k + 1]
            k += 1
        k += 1
    return rest, paths, home


def main(argv):
    argv, paths, home = rewrite_options(argv)
    values = {name: option(argv, name) for name in VALUED}
    args, skip = [], False
    for a in argv:
        if skip or a in VALUED:
            skip = not skip
            continue
        if not a.startswith("--"):
            args.append(a)
    root = pathlib.Path(args[0]).resolve() if args else DEFAULT_ROOT
    path = root / "tests/duplicates-baseline.json"
    base = json.loads(path.read_text()) if path.exists() else {}
    if "--rewrite" in argv:
        if values["--from"] is None or values["--to"] is None:
            raise SystemExit("--rewrite needs --from \"TOKENS\" and --to \"TOKENS\"")
        return rewrite(root, values["--from"], values["--to"], paths, home, "--add-require" in argv,
                       "--dry-run" in argv)
    if values["--explain"]:
        return explain(root, values["--explain"], base)
    if "--plan" in argv:
        return plan(root, base)
    if values["--extract"] or values["--extract-table"]:
        if values["--extract-table"]:
            specs = table_specs(values["--extract-table"])
        elif not (values["--word"] and values["--home"]):
            raise SystemExit("--extract GROUP needs --word NAME and --home FILE (and --stack \"( a -- b )\")")
        else:
            specs = [{"group": values["--extract"], "word": values["--word"], "stack": values["--stack"] or "",
                      "home": values["--home"], "after": values["--after"], "comment": values["--comment"]}]
        return extract(root, specs, base, "--dry-run" in argv, "--add-require" in argv)
    now = groups(root)
    if "--update-baseline" in argv:
        new = baseline_of(now, base)
        path.write_text(json.dumps(new, indent=1, sort_keys=True) + "\n")
        missing = sum(1 for v in new.values() if reason_problem(v.get("reason")))
        print(f"wrote {path.relative_to(root)}: {len(now)} groups, {missing} without a reason that holds")
        return 0
    if "--report" in argv:
        report(now, base)
    if "--counts" in argv:
        counts(now)
    problems = ratchet(now, base)
    if problems:
        print("duplicates: identical Forth code beyond tests/duplicates-baseline.json (share one word or a "
              "library word, or give the group a reason; update the baseline only in a reviewed commit):")
        print("\n".join("  " + p for p in problems))
        return 1
    print(f"duplicates: {len(now)} baseline groups, each with a reason, none new or grown "
          f"(bodies of {MIN_TOKENS}+ tokens)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
