"""Test-only: the first checker's end-to-end cases as lean4export exports.

tests/reference/first-checker-terms.lean prints each case of the
first-checker, binder-domain and universe-scope tables as text (CASE and
DECL lines; tests/support/first-checker-driver.fs reads them into the
checker's stores directly). case_exports turns that text into one lean4export
3.1.0 NDJSON export per case, so tests/core/lean-differential.py can also run
every case through the stage and the feed (src/import/stage.fs and feed.fs,
tests/support/fed-checker-driver.fs): the same declarations, in the same
order, read the way a real export is read.

The export is built as the driver builds the stores: a name is one string
component, the token's text; equal levels and expressions are one record;
binders are anonymous with default binder information; a definition has
height 1 (hints {"regular": 1}), other kinds are safe. A let (E) becomes
a letE record (plan task 4.2.3). An unsupported form (Xlit, Xmdata, Xproj)
becomes a small expression of that form, which the feed turns into the
same leaf as the driver (core/unsupported-forms.fs).
Not an exporter, a reader or a checker; it never accepts anything.
"""
import json

META = {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                 "format": {"version": "3.1.0"},
                 "lean": {"githash": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc",
                          "version": "4.35.0"}}}


class CaseError(ValueError):
    pass


class Export:
    """One export: its lines, and the numbers of the records made so far."""

    def __init__(self):
        self.lines = [META]
        self.names, self.levels, self.exprs = {}, {("zero",): 0}, {}
        self.params = []          # universe parameter names, in order of use

    def name(self, text):
        if text not in self.names:
            self.names[text] = len(self.names) + 1
            self.lines.append({"in": self.names[text], "str": {"pre": 0, "str": text}})
        return self.names[text]

    def level(self, key, body):
        if key not in self.levels:
            self.levels[key] = len(self.levels)
            self.lines.append({"il": self.levels[key], **body})
        return self.levels[key]

    def expr(self, key, body):
        if key not in self.exprs:
            self.exprs[key] = len(self.exprs)
            self.lines.append({"ie": self.exprs[key], **body})
        return self.exprs[key]

    def note_param(self, text):
        if text not in self.params:
            self.params.append(text)

    def text(self):
        return "".join(json.dumps(line, sort_keys=True, separators=(",", ":")) + "\n"
                       for line in self.lines)


class Reader:
    """The tokens of one DECL line, read in the driver's prefix forms."""

    def __init__(self, export, words):
        self.export, self.words, self.at = export, words, 0

    def token(self):
        if self.at >= len(self.words):
            raise CaseError("missing token")
        self.at += 1
        return self.words[self.at - 1]

    def expect(self, word):
        if self.token() != word:
            raise CaseError(f"expected {word}")

    def number(self):
        return int(self.token())

    # Levels and terms are read iteratively, with explicit stacks, so that
    # cases thousands of levels deep (the depth table) need no recursion.
    def level(self):
        pending = []          # [tag, children so far]
        while True:
            tag = self.token()
            if tag == "z":
                value = 0
            elif tag in ("s", "m", "i"):
                pending.append([tag, []])
                continue
            elif tag == "p":
                text = self.token()
                self.export.note_param(text)
                name = self.export.name(text)
                value = self.export.level(("param", name), {"param": name})
            else:
                raise CaseError(f"level {tag}")
            while True:
                if not pending:
                    return value
                frame = pending[-1]
                frame[1].append(value)
                if len(frame[1]) < (1 if frame[0] == "s" else 2):
                    break
                pending.pop()
                value = self.made_level(frame[0], frame[1])

    def made_level(self, tag, children):
        if tag == "s":
            return self.export.level(("succ", children[0]), {"succ": children[0]})
        kind = "max" if tag == "m" else "imax"
        return self.export.level((kind, *children), {kind: children})

    def sort(self, level):
        return self.export.expr(("sort", level), {"sort": level})

    def constant(self):
        name = self.export.name(self.token())
        levels = [self.level() for _ in range(self.number())]
        return self.export.expr(("const", name, *levels),
                                {"const": {"name": name, "us": levels}})

    def unsupported(self, form):
        zero = self.sort(0)
        if form == "Xlit":
            return self.export.expr(("lit",), {"natVal": "0"})
        if form == "Xmdata":
            return self.export.expr(("mdata",), {"mdata": {"data": {}, "expr": zero}})
        if form == "Xproj":
            name = self.export.name("Prod")
            return self.export.expr(("proj",), {"proj": {
                "idx": 0, "struct": zero, "typeName": name}})
        raise CaseError(f"form {form}")

    def made_let(self, nondep, children):
        kind, value, body = children
        return self.export.expr(("let", nondep, kind, value, body), {"letE": {
            "body": body, "name": 0, "nondep": nondep, "type": kind, "value": value}})

    def made_term(self, word, children):
        first, second = children
        if word == "A":
            return self.export.expr(("app", first, second), {"app": {"arg": second, "fn": first}})
        kind = "lam" if word == "L" else "forallE"
        return self.export.expr((kind, first, second), {kind: {
            "binderInfo": "default", "body": second, "name": 0, "type": first}})

    def term(self):
        pending = []          # [word, children so far]
        while True:
            word = self.token()
            if word == "S":
                value = self.sort(self.level())
            elif word == "V":
                index = self.number()
                value = self.export.expr(("bvar", index), {"bvar": index})
            elif word in ("A", "L", "P"):
                pending.append([word, []])
                continue
            elif word == "E":
                pending.append([(word, self.number() != 0), []])
                continue
            elif word == "C":
                value = self.constant()
            elif word.startswith("X"):
                value = self.unsupported(word)
            else:
                raise CaseError(f"term {word}")
            while True:
                if not pending:
                    return value
                frame = pending[-1]
                frame[1].append(value)
                if len(frame[1]) < (3 if isinstance(frame[0], tuple) else 2):
                    break
                pending.pop()
                if isinstance(frame[0], tuple):
                    value = self.made_let(frame[0][1], frame[1])
                else:
                    value = self.made_term(frame[0], frame[1])

    def declaration(self):
        self.token()                       # before or check
        kind, safety = self.token(), self.token()
        name = self.export.name(self.token())
        texts = [self.token() for _ in range(self.number())]
        for text in texts:
            self.export.note_param(text)
        params = [self.export.name(text) for text in texts]
        self.expect("TYPE")
        claim = self.term()
        self.expect("VALUE")
        value = None if self.words[self.at] == "none" else self.term()
        head = {"levelParams": params, "name": name, "type": claim}
        if kind == "def":
            record = {"def": {**head, "all": [name], "hints": {"regular": 1},
                              "safety": safety, "value": value}}
        elif safety != "safe":
            raise CaseError(f"a {kind} that is {safety}")
        elif kind == "thm":
            record = {"thm": {**head, "all": [name], "value": value}}
        elif kind == "opq":
            record = {"opaque": {**head, "all": [name], "isUnsafe": False, "value": value}}
        elif kind == "ax":
            record = {"axiom": {**head, "isUnsafe": False}}
        else:
            raise CaseError(f"kind {kind}")
        self.export.lines.append(record)


def case_params(text):
    """Each case of the text, in order, as (id, the universe parameter names
    it declares or uses)."""
    return [(case, export_of(case_text).params) for case, case_text in case_texts(text)]


def case_texts(text):
    """The text split by case: (id, its DECL lines)."""
    cases, case, lines = [], None, []
    for line in text.splitlines():
        word, rest = line.split(" ", 1)
        if word == "CASE":
            if case is not None:
                cases.append((case, lines))
            case, lines = rest, []
        elif word == "DECL" and case is not None:
            lines.append(rest)
        else:
            raise CaseError(f"unexpected line {line!r}")
    if case is not None:
        cases.append((case, lines))
    return cases


def export_of(lines):
    export = Export()
    for rest in lines:
        Reader(export, rest.split()).declaration()
    return export


def case_exports(text):
    """Each case of the text, in order, as (id, export text)."""
    cases, export, case = [], None, None
    for line in text.splitlines():
        word, rest = line.split(" ", 1)
        if word == "CASE":
            if export:
                cases.append((case, export.text()))
            case, export = rest, Export()
        elif word == "DECL" and export:
            Reader(export, rest.split()).declaration()
        else:
            raise CaseError(f"unexpected line {line!r}")
    if export:
        cases.append((case, export.text()))
    return cases
