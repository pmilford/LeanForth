"""Outcome contract of the untrusted NDJSON preview: every case pins its code.

The three owner outcomes are accepted (unchecked data), rejected
(``LF_PREVIEW_MALFORMED``) and unsupported (``LF_PREVIEW_UNSUPPORTED``);
``LF_PREVIEW_LIMIT`` is the resource outcome. No test here accepts a bare
failure: each negative case pins its error code and NDJSON line.

``make test`` runs these classes through tests/core/test_ndjson_preview.py,
which imports them; this file can also be run directly.
"""
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path("tests/support")))
from ndjson_preview import (MAX_DECLARATIONS, MAX_LINE, MAX_NAMES, MAX_NODES, MAX_TOTAL,
                            OUTPUT_VERSION, PreviewError, main, preview)

MALFORMED = "LF_PREVIEW_MALFORMED"
UNSUPPORTED = "LF_PREVIEW_UNSUPPORTED"
LIMIT = "LF_PREVIEW_LIMIT"
FIXTURES = ("composition", "identity", "type-identity", "poly-identity", "constant-fixture")
COMP = Path("tests/reference/composition.ndjson").read_text(encoding="utf-8").splitlines()
CONST = Path("tests/reference/constant-fixture.ndjson").read_text(encoding="utf-8").splitlines()
META = COMP[0]
N = len(COMP)  # A record inserted before the theorem occupies line N.
DEF_LINE = 14  # fixtureId's definition in the constant fixture.
# Real pinned Lean 4.35.0 exports from scratch probes (axiom export and an
# inductive record from `inductive ProbeColor | red | green`).
AXIOM_EXPORT = [
    META,
    '{"in":1,"str":{"pre":0,"str":"probeAxiom"}}',
    '{"ie":0,"sort":0}',
    '{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}',
]
INDUCTIVE_RECORD = (
    '{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,'
    '"numFields":0,"numParams":0,"type":1},{"cidx":1,"induct":1,"isUnsafe":false,'
    '"levelParams":[],"name":3,"numFields":0,"numParams":0,"type":1}],"recs":[{"all":[1],'
    '"isUnsafe":false,"k":false,"levelParams":[5],"name":4,"numIndices":0,"numMinors":2,'
    '"numMotives":1,"numParams":0,"rules":[{"ctor":2,"nfields":0,"rhs":18},{"ctor":3,'
    '"nfields":0,"rhs":21}],"type":15}],"types":[{"all":[1],"ctors":[2,3],"isRec":false,'
    '"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,'
    '"numNested":0,"numParams":0,"type":0}]}}')


def stream(records):
    """Encode NDJSON lines from bytes, text or JSON records, LF-terminated."""
    lines = []
    for record in records:
        if isinstance(record, bytes):
            lines.append(record)
        elif isinstance(record, str):
            lines.append(record.encode("utf-8"))
        else:
            lines.append(json.dumps(record, ensure_ascii=False).encode("utf-8"))
    return b"".join(line + b"\n" for line in lines)


def before_theorem(*records, base=COMP):
    return base[:-1] + list(records) + base[-1:]


def theorem(path, value):
    record = json.loads(COMP[-1])
    set_path(record["thm"], path, value)
    return COMP[:-1] + [record]


def replace_theorem(record):
    return COMP[:-1] + [record]


def set_path(target, path, value):
    for key in path[:-1]:
        target = target[key]
    target[path[-1]] = value


def definition(path, value):
    lines = list(CONST)
    record = json.loads(lines[DEF_LINE - 1])
    set_path(record["def"], path, value)
    lines[DEF_LINE - 1] = json.dumps(record)
    return lines


ANY_LINE = object()


class PreviewAssertions:
    """Exact-outcome assertions shared by the preview test modules."""

    def assertPreviewError(self, code, data, line=ANY_LINE):
        """Require one structured failure with this code (and line, if given).

        ``line`` is the 1-based NDJSON line; None means no line (empty input).
        """
        if not isinstance(data, bytes):
            data = stream(data)
        with self.assertRaises(PreviewError) as raised:
            preview(io.BytesIO(data))
        error = raised.exception
        self.assertEqual(error.code, code, f"{error} (line {error.line})")
        if line is not ANY_LINE:
            self.assertEqual(error.line, line, f"{error} ({error.code})")
        return error

    def assertAccepted(self, data):
        if not isinstance(data, bytes):
            data = stream(data)
        result = preview(io.BytesIO(data))
        self.assertIs(result["checked"], False)
        return result

    def assertCases(self, cases):
        for label, records, code, line in cases:
            with self.subTest(label):
                self.assertPreviewError(code, records, line)


class FramingTests(PreviewAssertions, unittest.TestCase):
    def test_encoding_and_framing_fail_closed(self):
        name = b'{"in":13,"str":{"pre":0,"str":"x%s"}}'
        self.assertCases([
            ("encoded surrogate bytes", before_theorem(name % b"\xed\xb2\x80"), MALFORMED, N),
            ("invalid byte", before_theorem(name % b"\xff"), MALFORMED, N),
            ("overlong encoding", before_theorem(name % b"\xc0\xaf"), MALFORMED, N),
            ("escaped lone surrogate", before_theorem(name % b"\\ud800"), MALFORMED, N),
            ("byte order mark", [b"\xef\xbb\xbf" + META.encode()] + COMP[1:], MALFORMED, 1),
            ("later byte order mark", before_theorem("﻿" + (name % b"").decode()),
             MALFORMED, N),
            ("CRLF line endings", "\r\n".join(COMP).encode() + b"\r\n", MALFORMED, 1),
            ("carriage return whitespace", before_theorem('{"in":13,\r"str":{"pre":0,"str":"a"}}'),
             MALFORMED, N),
            ("no final line feed", stream(COMP)[:-1], MALFORMED, N),
            ("blank line", before_theorem(""), MALFORMED, N),
            ("whitespace-only line", before_theorem("   "), MALFORMED, N),
            ("two objects on one line", COMP[:-1] + [COMP[-1] + COMP[-1]], MALFORMED, N),
            ("trailing garbage", COMP[:-1] + [COMP[-1] + " x"], MALFORMED, N),
            ("truncated object", COMP[:-1] + [COMP[-1][:-5]], MALFORMED, N),
            ("array record", [META, "[]"] + COMP[1:], MALFORMED, 2),
            ("null record", [META, "null"] + COMP[1:], MALFORMED, 2),
            ("number record", [META, "1"] + COMP[1:], MALFORMED, 2),
            ("string record", [META, '"x"'] + COMP[1:], MALFORMED, 2),
            ("deep nesting", [META, "[" * 2000 + "]" * 2000] + COMP[1:], MALFORMED, 2),
            ("Infinity", before_theorem('{"ie":21,"sort":Infinity}'), MALFORMED, N),
            ("NaN", before_theorem('{"ie":21,"bvar":NaN}'), MALFORMED, N),
            ("nested duplicate key",
             COMP[:-1] + [COMP[-1].replace('"type":10', '"type":10,"type":10')], MALFORMED, N),
            ("empty stream", b"", MALFORMED, None),
            ("metadata only", [META], MALFORMED, 1),
        ])

    def test_valid_unicode_text_is_preserved(self):
        for component, raw in (("é", "é"), ("α", "α"), ("\U0001F600", "\\ud83d\\ude00"),
                               ("a\0b", "a\\u0000b"), ("", "")):
            with self.subTest(component=component):
                record = '{"in":13,"str":{"pre":0,"str":"%s"}}' % raw
                result = self.assertAccepted(before_theorem(record))
                self.assertEqual(result["names"][13]["component"], component)


class ClassificationTests(PreviewAssertions, unittest.TestCase):
    def meta(self, section, key, value):
        record = json.loads(META)
        record["meta"][section][key] = value
        return [record] + COMP[1:]

    def test_metadata(self):
        self.assertCases([
            ("metadata not first", COMP[1:2] + [META] + COMP[2:], MALFORMED, 1),
            ("metadata null", ['{"meta":null}'] + COMP[1:], MALFORMED, 1),
            ("extra metadata field", [META.replace('{"meta":{', '{"meta":{"x":1,')] + COMP[1:],
             MALFORMED, 1),
            ("extra top-level key", [META[:-1] + ',"x":1}'] + COMP[1:], MALFORMED, 1),
            ("repeated metadata", COMP + [META], MALFORMED, N + 1),
            ("numeric format version", self.meta("format", "version", 3.1), MALFORMED, 1),
            ("null githash", self.meta("lean", "githash", None), MALFORMED, 1),
            ("numeric exporter name", self.meta("exporter", "name", 7), MALFORMED, 1),
            ("other exporter", self.meta("exporter", "name", "other"), UNSUPPORTED, 1),
            ("exporter 3.2.0", self.meta("exporter", "version", "3.2.0"), UNSUPPORTED, 1),
            ("format 3.2.0", self.meta("format", "version", "3.2.0"), UNSUPPORTED, 1),
            ("Lean 4.36.0", self.meta("lean", "version", "4.36.0"), UNSUPPORTED, 1),
            ("other githash", self.meta("lean", "githash", "0" * 40), UNSUPPORTED, 1),
        ])

    def test_name_records(self):
        self.assertCases([
            ("both str and num", before_theorem(
                '{"in":13,"str":{"pre":0,"str":"a"},"num":{"pre":0,"i":1}}'), MALFORMED, N),
            ("index only", before_theorem('{"in":13}'), MALFORMED, N),
            ("text index", before_theorem('{"in":"not-a-name","unexpected":true}'), MALFORMED, N),
            ("skipped index", before_theorem('{"in":14,"str":{"pre":0,"str":"a"}}'), MALFORMED, N),
            ("repeated index", before_theorem('{"in":12,"str":{"pre":0,"str":"a"}}'), MALFORMED, N),
            ("far index", before_theorem('{"in":300,"str":{"pre":0,"str":"a"}}'), MALFORMED, N),
            ("redefines anonymous", [META, '{"in":0,"str":{"pre":0,"str":"a"}}'] + COMP[1:],
             MALFORMED, 2),
            ("forward prefix", before_theorem('{"in":13,"str":{"pre":13,"str":"a"}}'), MALFORMED, N),
            ("self prefix at start", [META, '{"in":1,"str":{"pre":1,"str":"bad"}}'] + COMP[2:],
             MALFORMED, 2),
            ("numeric text component", before_theorem('{"in":13,"str":{"pre":0,"str":5}}'),
             MALFORMED, N),
            ("null text component", before_theorem('{"in":13,"str":{"pre":0,"str":null}}'),
             MALFORMED, N),
            ("num with str key", before_theorem('{"in":13,"num":{"pre":0,"str":"a"}}'), MALFORMED, N),
            ("missing prefix", before_theorem('{"in":13,"str":{"str":"a"}}'), MALFORMED, N),
            ("extra name field", before_theorem('{"in":13,"str":{"pre":0,"str":"a","x":1}}'),
             MALFORMED, N),
        ])

    def test_level_and_expression_records(self):
        lam = '{"ie":21,"lam":{"name":0,"binderInfo":%s,"type":0,"body":0}}'
        self.assertCases([
            ("level without kind", before_theorem('{"il":1}'), MALFORMED, N),
            ("level with two kinds", before_theorem('{"il":1,"succ":0,"param":1}'), MALFORMED, N),
            ("unknown level kind", before_theorem('{"il":1,"bogus":0}'), MALFORMED, N),
            ("level metavariable", before_theorem('{"il":1,"mvar":1}'), MALFORMED, N),
            ("redefines level zero", before_theorem('{"il":0,"succ":0}'), MALFORMED, N),
            ("expression without kind", before_theorem('{"ie":21}'), MALFORMED, N),
            ("unknown expression kind", before_theorem('{"ie":21,"bogus":0}'), MALFORMED, N),
            ("free variable", before_theorem('{"ie":21,"fvar":0}'), MALFORMED, N),
            ("two expression kinds", before_theorem('{"ie":21,"sort":0,"bvar":0}'), MALFORMED, N),
            ("skipped expression", before_theorem('{"ie":22,"sort":0}'), MALFORMED, N),
            ("repeated expression", before_theorem('{"ie":20,"sort":0}'), MALFORMED, N),
            ("duplicate first expression",
             COMP[:4] + [COMP[3]] + COMP[4:], MALFORMED, 5),
            ("app missing argument", before_theorem('{"ie":21,"app":{"fn":0}}'), MALFORMED, N),
            ("app extra field", before_theorem('{"ie":21,"app":{"fn":0,"arg":0,"x":0}}'),
             MALFORMED, N),
            ("app self reference", before_theorem('{"ie":21,"app":{"fn":21,"arg":0}}'), MALFORMED, N),
            ("bogus binder information", before_theorem(lam % '"bogus"'), MALFORMED, N),
            ("numeric binder information", before_theorem(lam % "0"), MALFORMED, N),
            ("null binder information", before_theorem(lam % "null"), MALFORMED, N),
            ("lambda missing body", before_theorem(
                '{"ie":21,"lam":{"name":0,"binderInfo":"default","type":0}}'), MALFORMED, N),
            ("forall extra field", before_theorem(
                '{"ie":21,"forallE":{"name":0,"binderInfo":"default","type":0,"body":0,"x":0}}'),
             MALFORMED, N),
        ])

    def test_declaration_records(self):
        record = json.loads(COMP[-1])
        missing = {key: value for key, value in record["thm"].items() if key != "value"}
        self.assertCases([
            ("missing value", replace_theorem({"thm": missing}), MALFORMED, N),
            ("extra field", theorem(("extra",), 0), MALFORMED, N),
            ("null theorem", replace_theorem('{"thm":null}'), MALFORMED, N),
            ("list theorem", replace_theorem('{"thm":[]}'), MALFORMED, N),
            ("boolean name", theorem(("name",), True), MALFORMED, N),
            ("anonymous name", theorem(("name",), 0), MALFORMED, N),
            ("empty block", theorem(("all",), []), MALFORMED, N),
            ("text block", theorem(("all",), "bad"), MALFORMED, N),
            ("boolean block entry", theorem(("all",), [True]), MALFORMED, N),
            ("block without itself", theorem(("all",), [2]), MALFORMED, N),
            ("repeated block entry", theorem(("all",), [1, 1]), MALFORMED, N),
            ("mutual block without itself", theorem(("all",), [2, 3]), MALFORMED, N),
            ("extra top-level key", COMP[:-1] + [COMP[-1][:-1] + ',"x":1}'], MALFORMED, N),
            ("theorem and definition", COMP[:-1] + [COMP[-1][:-1] + ',"def":{}}'], MALFORMED, N),
            ("unknown record", COMP + ['{"unexpected":1}'], MALFORMED, N + 1),
            ("unknown declaration", COMP[:-1] + ['{"bogusDecl":{}}'], MALFORMED, N),
            ("empty record", COMP + ["{}"], MALFORMED, N + 1),
            ("bogus hints", definition(("hints",), "bogus"), MALFORMED, DEF_LINE),
            ("bogus safety", definition(("safety",), "bogus"), MALFORMED, DEF_LINE),
            ("list hints", definition(("hints",), []), MALFORMED, DEF_LINE),
        ])
        # An unused universe parameter is valid Lean; it is preserved as data.
        result = self.assertAccepted(theorem(("levelParams",), [2]))
        self.assertEqual(result["declarations"][0]["levelParams"], [2])

    def test_well_formed_unsupported_records(self):
        # fixturePoly's name (index 5) is only exported after fixtureId's record.
        mutual_definition = definition(("all",), [1, 5])
        quot ={"kind": "type", "levelParams": [], "name": 1, "type": 10}
        self.assertCases([
            ("let", before_theorem(
                '{"ie":21,"letE":{"body":0,"name":0,"nondep":false,"type":0,"value":0}}'),
             UNSUPPORTED, N),
            ("projection", before_theorem('{"ie":21,"proj":{"idx":0,"struct":0,"typeName":1}}'),
             UNSUPPORTED, N),
            ("natural literal", before_theorem('{"ie":21,"natVal":"0"}'), UNSUPPORTED, N),
            ("large natural literal", before_theorem('{"ie":21,"natVal":"4294967296"}'),
             UNSUPPORTED, N),
            ("string literal", before_theorem('{"ie":21,"strVal":"hi"}'), UNSUPPORTED, N),
            ("empty string literal", before_theorem('{"ie":21,"strVal":""}'), UNSUPPORTED, N),
            # No pinned export produced mdata; its payload is deliberately unvalidated.
            ("metadata expression", before_theorem('{"ie":21,"mdata":{"expr":0,"data":{}}}'),
             UNSUPPORTED, N),
            ("unvalidated metadata payload", before_theorem('{"ie":21,"mdata":7}'), UNSUPPORTED, N),
            ("real axiom export", AXIOM_EXPORT, UNSUPPORTED, 4),
            ("opaque", replace_theorem({"opaque": {"all": [1], "isUnsafe": False,
                                                   "levelParams": [], "name": 1, "type": 10,
                                                   "value": 20}}), UNSUPPORTED, N),
            *((f"quotient {kind}", replace_theorem({"quot": dict(quot, kind=kind)}), UNSUPPORTED, N)
              for kind in ("type", "ctor", "lift", "ind")),
            ("real inductive record", replace_theorem(INDUCTIVE_RECORD), UNSUPPORTED, N),
            ("mutual theorem", theorem(("all",), [1, 2]), UNSUPPORTED, N),
            ("mutual definition with a later name", mutual_definition, MALFORMED, DEF_LINE),
            ("mutual definition", definition(("all",), [1, 3]), UNSUPPORTED, DEF_LINE),
        ])

    def test_malformed_unsupported_records(self):
        let = {"body": 0, "name": 0, "nondep": False, "type": 0, "value": 0}
        proj = {"idx": 0, "struct": 0, "typeName": 1}
        axiom = json.loads(AXIOM_EXPORT[-1])["axiom"]
        inductive = json.loads(INDUCTIVE_RECORD)["inductive"]

        def expression(kind, payload):
            return before_theorem({"ie": 21, kind: payload})

        def axiom_with(**changes):
            return AXIOM_EXPORT[:-1] + [{"axiom": {**axiom, **changes}}]

        def inductive_with(key, value):
            return replace_theorem({"inductive": {**inductive, key: value}})

        bad_ctor = [dict(inductive["ctors"][0], extra=0)]
        bad_rule = [dict(inductive["recs"][0], rules=[{"ctor": 2, "nfields": 0}])]
        self.assertCases([
            ("let without nondep", expression("letE", {k: v for k, v in let.items()
                                                        if k != "nondep"}), MALFORMED, N),
            ("let numeric nondep", expression("letE", dict(let, nondep=0)), MALFORMED, N),
            ("let forward body", expression("letE", dict(let, body=21)), MALFORMED, N),
            ("let empty payload", expression("letE", {}), MALFORMED, N),
            ("projection anonymous type", expression("proj", dict(proj, typeName=0)),
             MALFORMED, N),
            ("projection negative index", expression("proj", dict(proj, idx=-1)), MALFORMED, N),
            ("projection forward struct", expression("proj", dict(proj, struct=21)),
             MALFORMED, N),
            ("numeric natural literal", expression("natVal", 5), MALFORMED, N),
            ("leading-zero natural literal", expression("natVal", "05"), MALFORMED, N),
            ("negative natural literal", expression("natVal", "-1"), MALFORMED, N),
            ("non-ASCII digit literal", expression("natVal", "５"), MALFORMED, N),
            ("empty natural literal", expression("natVal", ""), MALFORMED, N),
            ("numeric string literal", expression("strVal", 5), MALFORMED, N),
            ("lone surrogate string literal", before_theorem('{"ie":21,"strVal":"\\udc00"}'),
             MALFORMED, N),
            ("axiom without isUnsafe", AXIOM_EXPORT[:-1] + [
                {"axiom": {k: v for k, v in axiom.items() if k != "isUnsafe"}}], MALFORMED, 4),
            ("axiom numeric isUnsafe", axiom_with(isUnsafe=0), MALFORMED, 4),
            ("axiom anonymous", axiom_with(name=0), MALFORMED, 4),
            ("axiom forward type", axiom_with(type=1), MALFORMED, 4),
            ("axiom duplicate parameters", axiom_with(levelParams=[1, 1]), MALFORMED, 4),
            ("opaque empty block", replace_theorem({"opaque": {
                "all": [], "isUnsafe": False, "levelParams": [], "name": 1, "type": 10,
                "value": 20}}), MALFORMED, N),
            ("quotient bogus kind", replace_theorem({"quot": {
                "kind": "bogus", "levelParams": [], "name": 1, "type": 10}}), MALFORMED, N),
            ("inductive without types", inductive_with("types", []), MALFORMED, N),
            ("inductive text ctors", inductive_with("ctors", "bad"), MALFORMED, N),
            ("inductive extra ctor field", inductive_with("ctors", bad_ctor), MALFORMED, N),
            ("inductive short rule", inductive_with("recs", bad_rule), MALFORMED, N),
            ("inductive missing recs", replace_theorem({"inductive": {
                k: v for k, v in inductive.items() if k != "recs"}}), MALFORMED, N),
        ])


class LimitTests(PreviewAssertions, unittest.TestCase):
    def padded(self, line, size):
        """Pad a JSON line with spaces to ``size`` bytes, excluding its LF."""
        padding = size - len(line.encode("utf-8"))
        self.assertGreaterEqual(padding, 0)
        return line + " " * padding

    def test_line_length_boundary(self):
        self.assertAccepted(COMP[:-1] + [self.padded(COMP[-1], MAX_LINE - 1)])
        self.assertPreviewError(LIMIT, COMP[:-1] + [self.padded(COMP[-1], MAX_LINE)], N)
        self.assertPreviewError(LIMIT, COMP[:-1] + [self.padded(COMP[-1], MAX_LINE + 50)], N)
        # A final unterminated line at the size bound is malformed, not a limit.
        self.assertPreviewError(
            MALFORMED, stream(COMP[:-1]) + self.padded(COMP[-1], MAX_LINE).encode(), N)

    def test_total_size_boundary(self):
        lines = [META] + [json.dumps({"in": i, "str": {"pre": 0, "str": "p"}})
                          for i in range(1, 254)]
        lines += ['{"ie":0,"sort":0}',
                  '{"thm":{"all":[1],"levelParams":[],"name":1,"type":0,"value":0}}']
        lines = [self.padded(line, MAX_LINE - 1) for line in lines]
        data = stream(lines)
        self.assertEqual(len(data), MAX_TOTAL)
        self.assertAccepted(data)
        self.assertPreviewError(LIMIT, data + b'{"in":254,"str":{"pre":0,"str":"q"}}\n',
                                len(lines) + 1)

    def test_name_table_boundary(self):
        names = [json.dumps({"in": i, "str": {"pre": 0, "str": "n"}})
                 for i in range(13, MAX_NAMES + 2)]
        result = self.assertAccepted(before_theorem(*names[:-1]))
        self.assertEqual(len(result["names"]), MAX_NAMES + 1)  # includes anonymous
        self.assertPreviewError(LIMIT, before_theorem(*names), N + len(names) - 1)

    def test_expression_table_boundary(self):
        base = [META, '{"in":1,"str":{"pre":0,"str":"t"}}']
        nodes = [json.dumps({"ie": i, "sort": 0}) for i in range(MAX_NODES + 1)]
        claim = '{"thm":{"all":[1],"levelParams":[],"name":1,"type":0,"value":0}}'
        self.assertEqual(len(self.assertAccepted(base + nodes[:-1] + [claim])["expressions"]),
                         MAX_NODES)
        self.assertPreviewError(LIMIT, base + nodes + [claim], len(base) + len(nodes))

    def test_declaration_table_boundary(self):
        count = MAX_DECLARATIONS + 1
        lines = [META] + [json.dumps({"in": i, "str": {"pre": 0, "str": f"d{i}"}})
                          for i in range(1, count + 1)]
        lines.append('{"ie":0,"sort":0}')
        lines += [json.dumps({"thm": {"all": [i], "levelParams": [], "name": i,
                                      "type": 0, "value": 0}}) for i in range(1, count + 1)]
        self.assertEqual(len(self.assertAccepted(lines[:-1])["declarations"]), MAX_DECLARATIONS)
        self.assertPreviewError(LIMIT, lines, len(lines))

    def test_universe_argument_boundary(self):
        lines = list(CONST)
        record = json.loads(lines[15])
        record["const"]["us"] = [0] * 256
        lines[15] = json.dumps(record)
        self.assertEqual(len(self.assertAccepted(lines)["expressions"][7]["us"]), 256)
        record["const"]["us"] = [0] * 257
        lines[15] = json.dumps(record)
        self.assertPreviewError(LIMIT, lines, 16)


class NumericEdgeTests(PreviewAssertions, unittest.TestCase):
    """Integer fields reject non-naturals; Lean-valid large naturals are limits."""

    WRONG_TYPES = (-1, 1.0, "0", True, False, None, [0])

    def inserted(self, template, path):
        def build(value):
            record = json.loads(template)
            set_path(record, path, value)
            return before_theorem(record)
        return build

    def test_integer_fields(self):
        big = 2 ** 31
        inserted = self.inserted
        fields = [
            # (label, builder, line, outcome for 2**31)
            ("name index", inserted('{"in":13,"num":{"pre":0,"i":1}}', ("in",)), N, MALFORMED),
            ("name prefix", inserted('{"in":13,"num":{"pre":0,"i":1}}', ("num", "pre")),
             N, MALFORMED),
            ("name number", inserted('{"in":13,"num":{"pre":0,"i":1}}', ("num", "i")), N, LIMIT),
            ("level index", inserted('{"il":1,"succ":0}', ("il",)), N, MALFORMED),
            ("successor", inserted('{"il":1,"succ":0}', ("succ",)), N, MALFORMED),
            ("max operand", inserted('{"il":1,"max":[0,0]}', ("max", 0)), N, MALFORMED),
            ("imax operand", inserted('{"il":1,"imax":[0,0]}', ("imax", 1)), N, MALFORMED),
            ("parameter", inserted('{"il":1,"param":1}', ("param",)), N, MALFORMED),
            ("expression index", inserted('{"ie":21,"sort":0}', ("ie",)), N, MALFORMED),
            ("sort level", inserted('{"ie":21,"sort":0}', ("sort",)), N, MALFORMED),
            ("bound variable", inserted('{"ie":21,"bvar":0}', ("bvar",)), N, LIMIT),
            ("constant name", inserted('{"ie":21,"const":{"name":1,"us":[0]}}',
                                       ("const", "name")), N, MALFORMED),
            ("constant universe", inserted('{"ie":21,"const":{"name":1,"us":[0]}}',
                                           ("const", "us", 0)), N, MALFORMED),
            ("application function", inserted('{"ie":21,"app":{"fn":0,"arg":0}}',
                                              ("app", "fn")), N, MALFORMED),
            ("application argument", inserted('{"ie":21,"app":{"fn":0,"arg":0}}',
                                              ("app", "arg")), N, MALFORMED),
            ("binder name", inserted(
                '{"ie":21,"lam":{"name":0,"binderInfo":"default","type":0,"body":0}}',
                ("lam", "name")), N, MALFORMED),
            ("binder type", inserted(
                '{"ie":21,"forallE":{"name":0,"binderInfo":"default","type":0,"body":0}}',
                ("forallE", "type")), N, MALFORMED),
            ("binder body", inserted(
                '{"ie":21,"lam":{"name":0,"binderInfo":"default","type":0,"body":0}}',
                ("lam", "body")), N, MALFORMED),
            ("theorem name", lambda value: theorem(("name",), value), N, MALFORMED),
            ("theorem type", lambda value: theorem(("type",), value), N, MALFORMED),
            ("theorem value", lambda value: theorem(("value",), value), N, MALFORMED),
            ("universe parameter list", lambda value: theorem(("levelParams",), [value]),
             N, MALFORMED),
            ("block entry", lambda value: theorem(("all",), [value]), N, MALFORMED),
            ("reducibility height", lambda value: definition(("hints", "regular"), value),
             DEF_LINE, LIMIT),
        ]
        for label, build, line, large in fields:
            for value in self.WRONG_TYPES:
                with self.subTest(field=label, value=value):
                    self.assertPreviewError(MALFORMED, build(value), line)
            with self.subTest(field=label, value=big):
                self.assertPreviewError(large, build(big), line)

    def test_large_natural_boundaries(self):
        largest = 2 ** 31 - 1
        result = self.assertAccepted(before_theorem('{"in":13,"num":{"pre":0,"i":%d}}' % largest))
        self.assertEqual(result["names"][13]["component"], largest)
        result = self.assertAccepted(before_theorem('{"ie":21,"bvar":%d}' % largest))
        self.assertEqual(result["expressions"][21]["index"], largest)
        result = self.assertAccepted(definition(("hints", "regular"), largest))
        self.assertEqual(result["declarations"][0]["hints"], {"regular": largest})
        # Lean's reducibility height is a UInt32: beyond it is not Lean output.
        self.assertPreviewError(LIMIT, definition(("hints", "regular"), 2 ** 32 - 1), DEF_LINE)
        self.assertPreviewError(MALFORMED, definition(("hints", "regular"), 2 ** 32), DEF_LINE)


class CliContractTests(unittest.TestCase):
    COMMAND = [sys.executable, "tests/support/ndjson_preview.py"]
    KEYS = {"version", "checked", "dependenciesChecked", "cyclesChecked",
            "dependencyDiagnostics", "metadata", "names", "levels", "levelExpressions",
            "concreteLevelDataOnly", "expressions", "declarations"}

    def run_cli(self, data, seed="0"):
        return subprocess.run(self.COMMAND, input=data, capture_output=True,
                              env=dict(os.environ, PYTHONHASHSEED=seed))

    def test_success_output_contract(self):
        for name in FIXTURES:
            with self.subTest(name=name):
                raw = Path(f"tests/reference/{name}.ndjson").read_bytes()
                result = self.run_cli(raw)
                self.assertEqual((result.returncode, result.stderr), (0, b""))
                self.assertEqual(result.stdout.count(b"\n"), 1)
                expected = json.dumps(preview(io.BytesIO(raw)), ensure_ascii=True,
                                      sort_keys=True, separators=(",", ":")) + "\n"
                self.assertEqual(result.stdout, expected.encode("ascii"))
                output = json.loads(result.stdout)
                self.assertEqual(set(output), self.KEYS)
                self.assertEqual(output["version"], OUTPUT_VERSION)
                self.assertEqual(OUTPUT_VERSION, "0.4")
                for flag in ("checked", "dependenciesChecked", "cyclesChecked"):
                    self.assertIs(output[flag], False)

    def test_each_outcome_has_its_exit_code_and_no_partial_output(self):
        raw = Path("tests/reference/composition.ndjson").read_bytes()
        cases = [
            ("malformed", raw + b"{\n", 1, MALFORMED, N + 1),
            ("unsupported", stream(AXIOM_EXPORT), 2, UNSUPPORTED, 4),
            ("limit", raw + b" " * MAX_LINE + b"\n", 3, LIMIT, N + 1),
        ]
        for label, data, exit_code, code, line in cases:
            with self.subTest(label):
                result = self.run_cli(data)
                self.assertEqual(result.returncode, exit_code)
                self.assertEqual(result.stdout, b"")
                self.assertEqual(result.stderr.count(b"\n"), 1)
                report = json.loads(result.stderr)
                self.assertEqual(set(report), {"code", "line", "message"})
                self.assertEqual((report["code"], report["line"]), (code, line))

    def test_internal_fault_is_a_failure(self):
        class Broken:
            def readline(self, _size):
                raise OSError("read failed")

        stdout, stderr = io.StringIO(), io.StringIO()
        self.assertEqual(main(Broken(), stdout, stderr), 4)
        self.assertEqual(stdout.getvalue(), "")
        self.assertEqual(json.loads(stderr.getvalue())["code"], "LF_PREVIEW_INTERNAL")

    def test_output_is_byte_identical_across_hash_seeds(self):
        inputs = [Path(f"tests/reference/{name}.ndjson").read_bytes() for name in FIXTURES]
        inputs.append(stream(AXIOM_EXPORT))
        for data in inputs:
            runs = {(r.returncode, r.stdout, r.stderr)
                    for r in (self.run_cli(data, seed) for seed in ("0", "1", "4242"))}
            self.assertEqual(len(runs), 1)


if __name__ == "__main__":
    unittest.main()
