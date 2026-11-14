#!/usr/bin/env python3
"""Ratchet on duplicated Forth code (owner, 2026-11-13, plans 9.4.8f and 9.4.8k). Part of `make test`.

Usage: python3 scripts/check-duplicates.py [--update-baseline] [--report] [--counts] [ROOT]

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
"""
import collections
import hashlib
import importlib.util
import json
import pathlib
import re
import sys

DEFAULT_ROOT = pathlib.Path(__file__).resolve().parent.parent
MIN_TOKENS = 6
STRING_OPENERS = {"s\"", ".\"", "c\"", "abort\"", "s\\\"", ".("}
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
    out, i, line, n = [], 0, 1, len(text)
    while i < n:
        if text[i].isspace():
            line += text[i] == "\n"
            i += 1
            continue
        j = i
        while j < n and not text[j].isspace():
            j += 1
        tok, start = text[i:j], line
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
                k += 1
            out.append((low + " " + text[i + 1:k], start))
            i = k + 1
        else:
            out.append((low, start))
    return out


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


def main(argv):
    args = [a for a in argv if not a.startswith("--")]
    root = pathlib.Path(args[0]).resolve() if args else DEFAULT_ROOT
    path = root / "tests/duplicates-baseline.json"
    base = json.loads(path.read_text()) if path.exists() else {}
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
