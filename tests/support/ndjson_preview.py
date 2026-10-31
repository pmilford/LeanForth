"""Development-only, untrusted preview of a narrow Lean NDJSON subset.

This tool does not check types or proofs, execute Forth, or register a theorem.
Its output is provisional test data, not a stable interchange/API format.
"""

import json
import sys

LEAN_HASH = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
MAX_LINE = 4096
MAX_TOTAL = 1048576
MAX_NAMES = 256
MAX_LEVELS = 256
MAX_NODES = 64
MAX_DECLARATIONS = 64
MAX_INTEGER = 2147483647


class PreviewError(ValueError):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


def fail(message, code="LF_PREVIEW_MALFORMED"):
    raise PreviewError(code, message)


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            fail("duplicate object key")
        result[key] = value
    return result


def integer(value, maximum=MAX_INTEGER):
    if type(value) is not int or not 0 <= value <= maximum:
        fail("integer out of range")
    return value


def fields(value, expected):
    if not isinstance(value, dict) or set(value) != expected:
        fail("unexpected object fields")
    return value


def preview(stream):
    """Decode a bounded byte stream, returning unchecked records or raising."""
    names = [None]  # Lean name zero is anonymous.
    name_keys = [()]
    levels = [0]  # Export index zero denotes universe zero.
    nodes = []
    declarations = []
    declared = set()
    metadata = None
    total = 0
    line_no = 0
    while True:
        raw = stream.readline(MAX_LINE + 1)
        if not raw:
            break
        line_no += 1
        total += len(raw)
        if len(raw) > MAX_LINE or total > MAX_TOTAL:
            fail("input limit exceeded", "LF_PREVIEW_LIMIT")
        try:
            record = json.loads(raw, object_pairs_hook=object_pairs,
                                parse_constant=lambda _: fail("invalid JSON constant"))
        except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as error:
            if isinstance(error, PreviewError):
                raise
            fail("invalid JSON")
        if not isinstance(record, dict):
            fail("record is not an object")
        if line_no == 1:
            meta = fields(record, {"meta"})["meta"]
            meta = fields(meta, {"exporter", "format", "lean"})
            exporter = fields(meta["exporter"], {"name", "version"})
            fmt = fields(meta["format"], {"version"})
            lean = fields(meta["lean"], {"version", "githash"})
            if (exporter != {"name": "lean4export", "version": "3.1.0"}
                    or fmt["version"] != "3.1.0"
                    or lean != {"version": "4.35.0", "githash": LEAN_HASH}):
                fail("unsupported exporter or Lean version", "LF_PREVIEW_UNSUPPORTED")
            metadata = meta
        elif set(record) in ({"in", "str"}, {"in", "num"}):
            index = integer(record["in"])
            if index > MAX_NAMES:
                fail("name limit exceeded", "LF_PREVIEW_LIMIT")
            if index != len(names):
                fail("nonsequential name index")
            kind = "str" if "str" in record else "num"
            component_key = "str" if kind == "str" else "i"
            item = fields(record[kind], {"pre", component_key})
            integer(item["pre"], index - 1)
            component = item[component_key]
            if kind == "str":
                if not isinstance(component, str):
                    fail("name component is not text")
            else:
                integer(component)
            names.append({"kind": kind, "prefix": item["pre"], "component": component})
            name_keys.append(name_keys[item["pre"]] + ((kind, component),))
        elif "il" in record:
            index = integer(record["il"])
            if index > MAX_LEVELS:
                fail("universe level limit exceeded", "LF_PREVIEW_LIMIT")
            if index != len(levels):
                fail("nonsequential universe level index")
            if set(record) != {"il", "succ"}:
                fail("unsupported universe level", "LF_PREVIEW_UNSUPPORTED")
            predecessor = integer(record["succ"], index - 1)
            if levels[predecessor] >= MAX_INTEGER:
                fail("universe level overflow", "LF_PREVIEW_LIMIT")
            levels.append(levels[predecessor] + 1)
        elif "ie" in record:
            index = integer(record["ie"])
            if index >= MAX_NODES:
                fail("expression limit exceeded", "LF_PREVIEW_LIMIT")
            if index != len(nodes):
                fail("nonsequential expression index")
            kinds = set(record) - {"ie"}
            if len(kinds) != 1:
                fail("ambiguous expression record")
            kind = next(iter(kinds))
            if kind == "sort":
                level_index = integer(record[kind], len(levels) - 1)
                node = {"tag": "sort", "level": levels[level_index], "levelIndex": level_index}
            elif kind == "bvar":
                node = {"tag": kind, "index": integer(record[kind])}
            elif kind in ("app", "lam", "forallE"):
                keys = {"fn", "arg"} if kind == "app" else {"name", "binderInfo", "type", "body"}
                item = fields(record[kind], keys)
                child_keys = ("fn", "arg") if kind == "app" else ("type", "body")
                for key in child_keys:
                    integer(item[key], index - 1)
                if kind != "app":
                    integer(item["name"], len(names) - 1)
                    if item["binderInfo"] not in ("default", "implicit", "strictImplicit", "instImplicit"):
                        fail("unsupported binder information", "LF_PREVIEW_UNSUPPORTED")
                node = {"tag": kind, **item}
            else:
                fail("unsupported expression kind", "LF_PREVIEW_UNSUPPORTED")
            nodes.append(node)
        elif set(record) == {"thm"}:
            if len(declarations) >= MAX_DECLARATIONS:
                fail("declaration limit exceeded", "LF_PREVIEW_LIMIT")
            item = fields(record["thm"], {"all", "levelParams", "name", "type", "value"})
            name = integer(item["name"], len(names) - 1)
            if name == 0 or name_keys[name] in declared:
                fail("invalid or duplicate declaration name")
            integer(item["type"], len(nodes) - 1)
            integer(item["value"], len(nodes) - 1)
            if item["levelParams"] != [] or item["all"] != [name] or type(item["all"][0]) is not int:
                fail("polymorphic or mutual theorem is unsupported", "LF_PREVIEW_UNSUPPORTED")
            declarations.append(dict(item))
            declared.add(name_keys[name])
        else:
            fail("unsupported record", "LF_PREVIEW_UNSUPPORTED")
    if metadata is None or not declarations:
        fail("missing metadata or theorem")
    return {"version": "0.1", "checked": False, "metadata": metadata,
            "names": names, "levels": levels, "expressions": nodes, "declarations": declarations}


def main():
    try:
        result = preview(sys.stdin.buffer)
    except PreviewError as error:
        print(json.dumps({"code": error.code, "message": str(error)}), file=sys.stderr)
        return 1
    print(json.dumps(result, ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
