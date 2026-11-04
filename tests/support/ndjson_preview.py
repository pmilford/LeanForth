"""Development-only, untrusted preview of a narrow Lean NDJSON subset.

This tool does not check types or proofs, execute Forth, or register a theorem.
Its output is provisional test data, not a stable interchange/API format.

Every input ends in exactly one outcome: accepted as unchecked data (exit 0),
or one structured error. ``LF_PREVIEW_MALFORMED`` means the input is not a
well-formed pinned lean4export 3.1.0 stream; ``LF_PREVIEW_UNSUPPORTED`` means
a well-formed record this preview does not handle yet; ``LF_PREVIEW_LIMIT``
means a prototype resource bound was exceeded. No error yields partial output.
"""

import json
import sys

OUTPUT_VERSION = "0.4"
LEAN_HASH = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
MAX_LINE = 4096
MAX_TOTAL = 1048576
MAX_NAMES = 256
MAX_LEVELS = 256
MAX_NODES = 64
MAX_DECLARATIONS = 64
MAX_LEVEL_ARGUMENTS = 256
MAX_INTEGER = 2147483647
MAX_UINT32 = 4294967295

MALFORMED = "LF_PREVIEW_MALFORMED"
UNSUPPORTED = "LF_PREVIEW_UNSUPPORTED"
LIMIT = "LF_PREVIEW_LIMIT"
INTERNAL = "LF_PREVIEW_INTERNAL"
EXIT_CODES = {MALFORMED: 1, UNSUPPORTED: 2, LIMIT: 3, INTERNAL: 4}

BINDER_INFOS = ("default", "implicit", "strictImplicit", "instImplicit")
SAFETIES = ("safe", "unsafe", "partial")
QUOT_KINDS = ("type", "ctor", "lift", "ind")
DECLARATION_FIELDS = {
    "thm": {"all", "levelParams", "name", "type", "value"},
    "def": {"all", "hints", "levelParams", "name", "safety", "type", "value"},
}
# Shapes observed in pinned Lean 4.35.0 exports. These records are well formed
# but unsupported; validating their shape keeps malformed input distinguishable.
UNSUPPORTED_DECLARATION_FIELDS = {
    "axiom": {"isUnsafe", "levelParams", "name", "type"},
    "opaque": {"all", "isUnsafe", "levelParams", "name", "type", "value"},
    "quot": {"kind", "levelParams", "name", "type"},
    "inductive": {"ctors", "recs", "types"},
}
INDUCTIVE_FIELDS = {
    "types": {"all", "ctors", "isRec", "isReflexive", "isUnsafe", "levelParams", "name",
              "numIndices", "numNested", "numParams", "type"},
    "ctors": {"cidx", "induct", "isUnsafe", "levelParams", "name", "numFields",
              "numParams", "type"},
    "recs": {"all", "isUnsafe", "k", "levelParams", "name", "numIndices", "numMinors",
             "numMotives", "numParams", "rules", "type"},
}
RECURSOR_RULE_FIELDS = {"ctor", "nfields", "rhs"}
UNSUPPORTED_EXPRESSIONS = ("letE", "proj", "natVal", "strVal", "mdata")


class PreviewError(ValueError):
    """A structured preview failure; ``line`` is the 1-based NDJSON line."""

    def __init__(self, code, message, line=None):
        super().__init__(message)
        self.code = code
        self.line = line


def fail(message, code=MALFORMED):
    raise PreviewError(code, message)


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            fail("duplicate object key")
        result[key] = value
    return result


def is_natural(value):
    """JSON integers only: booleans, floats and strings are not numbers here."""
    return type(value) is int and value >= 0


def natural(value, maximum=MAX_INTEGER):
    """A Lean natural number; values beyond the preview bound are a limit."""
    if not is_natural(value):
        fail("expected a natural number")
    if value > maximum:
        fail("natural number exceeds the preview bound", LIMIT)
    return value


def reference(value, count):
    """An index of one of ``count`` earlier records in the same table."""
    if not is_natural(value) or value >= count:
        fail("reference is not an earlier record")
    return value


def record_index(value, expected, maximum):
    """Check a record's own sequential index, then the prototype bound."""
    if not is_natural(value) or value != expected:
        fail("nonsequential record index")
    if value > maximum:
        fail("record table limit exceeded", LIMIT)
    return value


def text(value):
    """A JSON string holding only Unicode scalar values (no lone surrogates)."""
    if not isinstance(value, str):
        fail("expected a string")
    try:
        value.encode("utf-8")
    except UnicodeEncodeError:
        fail("string is not valid Unicode")
    return value


def boolean(value):
    if type(value) is not bool:
        fail("expected a boolean")
    return value


def fields(value, expected):
    if not isinstance(value, dict) or set(value) != expected:
        fail("unexpected object fields")
    return value


def objects(value, expected):
    """A list of objects that each have exactly the expected fields."""
    if not isinstance(value, list):
        fail("expected a list")
    for item in value:
        fields(item, expected)
    return value


def name_list(value, names, name_keys):
    """Distinct non-anonymous name references; returns their structured keys."""
    if not isinstance(value, list):
        fail("expected a list of names")
    keys = []
    for item in value:
        index = reference(item, len(names))
        if index == 0 or name_keys[index] in keys:
            fail("anonymous or duplicate name in list")
        keys.append(name_keys[index])
    return keys


def check_level_parameter_scope(roots, nodes, level_expressions, name_keys, allowed):
    """Reject undeclared universe parameters reachable from these two roots.

    This is a bounded syntactic check, not a proof or full declaration check.
    Existing DAG references have already been validated by the decoder.
    """
    pending_nodes = list(roots)
    seen_nodes = set()
    pending_levels = []
    seen_levels = set()
    while pending_nodes:
        index = pending_nodes.pop()
        if index in seen_nodes:
            continue
        seen_nodes.add(index)
        node = nodes[index]
        if node["tag"] == "sort":
            pending_levels.append(node["levelIndex"])
        elif node["tag"] == "const":
            pending_levels.extend(node["us"])
        elif node["tag"] == "app":
            pending_nodes.extend((node["fn"], node["arg"]))
        elif node["tag"] in ("lam", "forallE"):
            pending_nodes.extend((node["type"], node["body"]))
    while pending_levels:
        index = pending_levels.pop()
        if index in seen_levels:
            continue
        seen_levels.add(index)
        level = level_expressions[index]
        if level["tag"] == "param":
            if name_keys[level["name"]] not in allowed:
                fail("undeclared universe parameter")
        elif level["tag"] == "succ":
            pending_levels.append(level["of"])
        elif level["tag"] in ("max", "imax"):
            pending_levels.extend((level["left"], level["right"]))


def observe_dependencies(declarations, nodes, name_keys):
    """Describe local constant references; this never validates dependencies.

    Expression DAGs and name references were checked by preview(). Work is
    bounded by its declaration and node limits; shared nodes are visited once
    per root. Structured-name aliases resolve by the same key as declarations.
    """
    by_name = {name_keys[decl["name"]]: index
               for index, decl in enumerate(declarations)}
    result = []
    for index, decl in enumerate(declarations):
        roots = {}
        for root_name in ("type", "value"):
            pending = [decl[root_name]]
            seen = set()
            while pending:
                current = pending.pop()
                if current in seen:
                    continue
                seen.add(current)
                node = nodes[current]
                if node["tag"] == "const":
                    roots.setdefault(current, set()).add(root_name)
                elif node["tag"] == "app":
                    pending.extend((node["fn"], node["arg"]))
                elif node["tag"] in ("lam", "forallE"):
                    pending.extend((node["type"], node["body"]))
        references = []
        for expression in sorted(roots):
            node = nodes[expression]
            target = by_name.get(name_keys[node["name"]])
            declared_arity = None if target is None else len(declarations[target]["levelParams"])
            provided_arity = len(node["us"])
            status = ("missing" if target is None else "self" if target == index
                      else "earlier_in_stream" if target < index else "later_in_stream")
            references.append({
                "expression": expression, "name": node["name"],
                "inType": "type" in roots[expression],
                "inValue": "value" in roots[expression],
                "targetRecord": target, "status": status,
                "providedUniverses": provided_arity, "declaredUniverses": declared_arity,
                "arityMatches": None if target is None else provided_arity == declared_arity,
            })
        result.append({"declaration": index, "references": references})
    return result


def decode_line(raw):
    """Strict framing: plain UTF-8 JSON terminated by one line feed.

    The pinned exporter emits LF-terminated UTF-8 without a byte order mark or
    carriage returns, so any of those (or invalid UTF-8) fails closed.
    """
    if not raw.endswith(b"\n"):
        fail("line is not terminated by a line feed")
    if b"\r" in raw:
        fail("carriage return in line")
    try:
        line = raw.decode("utf-8")  # strict: rejects encoded surrogates and overlongs
    except UnicodeDecodeError:
        fail("invalid UTF-8")
    if line.startswith("﻿"):
        fail("byte order mark")
    try:
        return json.loads(line, object_pairs_hook=object_pairs,
                          parse_constant=lambda _: fail("invalid JSON constant"))
    except PreviewError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError):
        fail("invalid JSON")


def check_metadata(record):
    meta = fields(record, {"meta"})["meta"]
    meta = fields(meta, {"exporter", "format", "lean"})
    exporter = fields(meta["exporter"], {"name", "version"})
    fmt = fields(meta["format"], {"version"})
    lean = fields(meta["lean"], {"version", "githash"})
    for value in (exporter["name"], exporter["version"], fmt["version"],
                  lean["version"], lean["githash"]):
        text(value)
    if (exporter != {"name": "lean4export", "version": "3.1.0"}
            or fmt["version"] != "3.1.0"
            or lean != {"version": "4.35.0", "githash": LEAN_HASH}):
        fail("unsupported exporter or Lean version", UNSUPPORTED)
    return meta


def check_unsupported_expression(kind, value, index, names):
    """Validate an observed unsupported expression's shape, then report it."""
    if kind == "letE":
        item = fields(value, {"body", "name", "nondep", "type", "value"})
        reference(item["name"], len(names))
        for key in ("type", "value", "body"):
            reference(item[key], index)
        boolean(item["nondep"])
    elif kind == "proj":
        item = fields(value, {"idx", "struct", "typeName"})
        if reference(item["typeName"], len(names)) == 0:
            fail("anonymous projection structure")
        reference(item["struct"], index)
        if not is_natural(item["idx"]):
            fail("projection index is not a natural number")
    elif kind == "natVal":
        if (not isinstance(value, str) or not value.isascii() or not value.isdigit()
                or (len(value) > 1 and value[0] == "0")):
            fail("natural literal is not canonical decimal text")
    elif kind == "strVal":
        text(value)
    # No pinned export has produced mdata, so its payload is not validated.
    fail(f"unsupported expression kind {kind}", UNSUPPORTED)


def check_unsupported_declaration(kind, value, names, name_keys, node_count):
    """Validate an observed unsupported declaration's shape, then report it."""
    item = fields(value, UNSUPPORTED_DECLARATION_FIELDS[kind])
    if kind == "inductive":
        for key, expected in INDUCTIVE_FIELDS.items():
            objects(item[key], expected)
        if not item["types"] and (item["ctors"] or item["recs"]):
            fail("inductive block without types")
        for recursor in item["recs"]:
            objects(recursor["rules"], RECURSOR_RULE_FIELDS)
    else:
        if reference(item["name"], len(names)) == 0:
            fail("anonymous declaration name")
        reference(item["type"], node_count)
        name_list(item["levelParams"], names, name_keys)
        if kind == "quot" and item["kind"] not in QUOT_KINDS:
            fail("invalid quotient kind")
        if kind in ("axiom", "opaque"):
            boolean(item["isUnsafe"])
        if kind == "opaque":
            reference(item["value"], node_count)
            if not name_list(item["all"], names, name_keys):
                fail("empty mutual block")
    fail(f"unsupported declaration kind {kind}", UNSUPPORTED)


def preview(stream):
    """Decode a bounded byte stream, returning unchecked records or raising."""
    names = [None]  # Lean name zero is anonymous.
    name_keys = [()]
    levels = [0]  # Export index zero denotes universe zero.
    level_expressions = [{"tag": "zero"}]
    nodes = []
    declarations = []
    declared = set()
    metadata = None
    total = 0
    line_no = 0

    def name_record(record):
        keys = set(record)
        if keys not in ({"in", "str"}, {"in", "num"}):
            fail("ambiguous or unknown name record")
        record_index(record["in"], len(names), MAX_NAMES)
        kind = "str" if "str" in record else "num"
        component_key = "str" if kind == "str" else "i"
        item = fields(record[kind], {"pre", component_key})
        prefix = reference(item["pre"], len(names))
        component = item[component_key]
        if kind == "str":
            text(component)
        else:
            natural(component)
        names.append({"kind": kind, "prefix": prefix, "component": component})
        name_keys.append(name_keys[prefix] + ((kind, component),))

    def level_record(record):
        index = record_index(record["il"], len(levels), MAX_LEVELS)
        kinds = set(record) - {"il"}
        if len(kinds) != 1:
            fail("ambiguous universe level")
        kind = next(iter(kinds))
        if kind == "succ":
            predecessor = reference(record[kind], index)
            if levels[predecessor] is not None and levels[predecessor] >= MAX_INTEGER:
                fail("universe level overflow", LIMIT)
            level = None if levels[predecessor] is None else levels[predecessor] + 1
            expression = {"tag": kind, "of": predecessor}
        elif kind in ("max", "imax"):
            pair = record[kind]
            if not isinstance(pair, list) or len(pair) != 2:
                fail("universe operation requires two references")
            left_index, right_index = (reference(ref, index) for ref in pair)
            left, right = levels[left_index], levels[right_index]
            if left is None or right is None:
                level = None
            else:
                level = 0 if kind == "imax" and right == 0 else max(left, right)
            expression = {"tag": kind, "left": left_index, "right": right_index}
        elif kind == "param":
            name = reference(record[kind], len(names))
            if name == 0:
                fail("anonymous universe parameter")
            level = None
            expression = {"tag": kind, "name": name}
        else:
            fail("unknown universe level kind")
        levels.append(level)
        level_expressions.append(expression)

    def expression_record(record):
        index = record_index(record["ie"], len(nodes), MAX_NODES - 1)
        kinds = set(record) - {"ie"}
        if len(kinds) != 1:
            fail("ambiguous expression record")
        kind = next(iter(kinds))
        if kind == "sort":
            level_index = reference(record[kind], len(levels))
            node = {"tag": "sort", "level": levels[level_index], "levelIndex": level_index}
        elif kind == "bvar":
            node = {"tag": kind, "index": natural(record[kind])}
        elif kind == "const":
            item = fields(record[kind], {"name", "us"})
            name = reference(item["name"], len(names))
            if name == 0:
                fail("anonymous constant name")
            args = item["us"]
            if not isinstance(args, list):
                fail("constant universe arguments are not a list")
            if len(args) > MAX_LEVEL_ARGUMENTS:
                fail("constant universe argument limit exceeded", LIMIT)
            for level in args:
                reference(level, len(levels))
            node = {"tag": "const", "name": name, "us": list(args)}
        elif kind in ("app", "lam", "forallE"):
            keys = {"fn", "arg"} if kind == "app" else {"name", "binderInfo", "type", "body"}
            item = fields(record[kind], keys)
            child_keys = ("fn", "arg") if kind == "app" else ("type", "body")
            for key in child_keys:
                reference(item[key], index)
            if kind != "app":
                reference(item["name"], len(names))
                if item["binderInfo"] not in BINDER_INFOS:
                    fail("invalid binder information")
            node = {"tag": kind, **item}
        elif kind in UNSUPPORTED_EXPRESSIONS:
            check_unsupported_expression(kind, record[kind], index, names)  # always raises
        else:
            fail("unknown expression kind")
        nodes.append(node)

    def declaration_record(declaration_kind, value):
        if len(declarations) >= MAX_DECLARATIONS:
            fail("declaration limit exceeded", LIMIT)
        item = fields(value, DECLARATION_FIELDS[declaration_kind])
        if declaration_kind == "def":
            hints = item["hints"]
            if isinstance(hints, dict):
                regular = fields(hints, {"regular"})["regular"]
                if not is_natural(regular) or regular > MAX_UINT32:
                    fail("reducibility height is not a UInt32")
                natural(regular)
            elif hints not in ("opaque", "abbrev"):
                fail("invalid reducibility hints")
            if item["safety"] not in SAFETIES:
                fail("invalid definition safety")
        name = reference(item["name"], len(names))
        if name == 0 or name_keys[name] in declared:
            fail("invalid or duplicate declaration name")
        reference(item["type"], len(nodes))
        reference(item["value"], len(nodes))
        param_keys = set(name_list(item["levelParams"], names, name_keys))
        block = name_list(item["all"], names, name_keys)
        if name_keys[name] not in block:
            fail("declaration is missing from its own block")
        check_level_parameter_scope((item["type"], item["value"]), nodes,
                                    level_expressions, name_keys, param_keys)
        if len(block) != 1:
            fail("mutual declaration is unsupported", UNSUPPORTED)
        declarations.append({"kind": declaration_kind, **item})
        declared.add(name_keys[name])

    while True:
        raw = stream.readline(MAX_LINE + 1)
        if not raw:
            break
        line_no += 1
        total += len(raw)
        try:
            if len(raw) > MAX_LINE or total > MAX_TOTAL:
                fail("input limit exceeded", LIMIT)
            record = decode_line(raw)
            if not isinstance(record, dict):
                fail("record is not an object")
            keys = set(record)
            if line_no == 1:
                if keys != {"meta"}:
                    fail("first record is not metadata")
                metadata = check_metadata(record)
            elif "meta" in keys:
                fail("repeated metadata record")
            elif "in" in keys:
                name_record(record)
            elif "il" in keys:
                level_record(record)
            elif "ie" in keys:
                expression_record(record)
            elif len(keys) == 1 and keys <= set(DECLARATION_FIELDS):
                kind = next(iter(keys))
                declaration_record(kind, record[kind])
            elif len(keys) == 1 and keys <= set(UNSUPPORTED_DECLARATION_FIELDS):
                kind = next(iter(keys))
                check_unsupported_declaration(kind, record[kind], names, name_keys, len(nodes))
            else:
                fail("unknown record kind")
        except PreviewError as error:
            error.line = line_no
            raise
    if metadata is None or not declarations:
        raise PreviewError(MALFORMED, "missing metadata or declaration", line_no or None)
    return {"version": OUTPUT_VERSION, "checked": False, "dependenciesChecked": False,
            "cyclesChecked": False,
            "dependencyDiagnostics": observe_dependencies(declarations, nodes, name_keys),
            "metadata": metadata,
            "names": names, "levels": levels, "levelExpressions": level_expressions,
            "concreteLevelDataOnly": all(level is not None for level in levels)
                and all(not decl["levelParams"] for decl in declarations),
            "expressions": nodes, "declarations": declarations}


def main(stdin=None, stdout=None, stderr=None):
    """CLI: exit 0 with one JSON line, or a nonzero code and one error line.

    Exit codes: 1 malformed, 2 unsupported, 3 limit, 4 internal fault. An
    internal fault is reported as a failure, never as an accepted preview.
    """
    stdin = sys.stdin.buffer if stdin is None else stdin
    stdout = sys.stdout if stdout is None else stdout
    stderr = sys.stderr if stderr is None else stderr
    try:
        result = preview(stdin)
    except PreviewError as error:
        report = {"code": error.code, "message": str(error), "line": error.line}
        print(json.dumps(report, sort_keys=True), file=stderr)
        return EXIT_CODES[error.code]
    except Exception as error:  # noqa: BLE001 - fail closed on any fault
        report = {"code": INTERNAL, "message": f"internal error: {type(error).__name__}",
                  "line": None}
        print(json.dumps(report, sort_keys=True), file=stderr)
        return EXIT_CODES[INTERNAL]
    print(json.dumps(result, ensure_ascii=True, sort_keys=True, separators=(",", ":")),
          file=stdout)
    return 0


if __name__ == "__main__":
    sys.exit(main())
