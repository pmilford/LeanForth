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
            kinds = set(record) - {"il"}
            if len(kinds) != 1:
                fail("ambiguous universe level")
            kind = next(iter(kinds))
            if kind == "succ":
                predecessor = integer(record[kind], index - 1)
                if levels[predecessor] is not None and levels[predecessor] >= MAX_INTEGER:
                    fail("universe level overflow", "LF_PREVIEW_LIMIT")
                level = None if levels[predecessor] is None else levels[predecessor] + 1
                expression = {"tag": kind, "of": predecessor}
            elif kind in ("max", "imax"):
                pair = record[kind]
                if not isinstance(pair, list) or len(pair) != 2:
                    fail("universe operation requires two references")
                left_index, right_index = (integer(ref, index - 1) for ref in pair)
                left, right = levels[left_index], levels[right_index]
                if left is None or right is None:
                    level = None
                else:
                    level = 0 if kind == "imax" and right == 0 else max(left, right)
                expression = {"tag": kind, "left": left_index, "right": right_index}
            elif kind == "param":
                name = integer(record[kind], len(names) - 1)
                if name == 0:
                    fail("anonymous universe parameter")
                level = None
                expression = {"tag": kind, "name": name}
            else:
                fail("unsupported universe level", "LF_PREVIEW_UNSUPPORTED")
            levels.append(level)
            level_expressions.append(expression)
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
            params = item["levelParams"]
            if not isinstance(params, list):
                fail("level parameters are not a list")
            param_keys = set()
            for param in params:
                param = integer(param, len(names) - 1)
                if param == 0 or name_keys[param] in param_keys:
                    fail("anonymous or duplicate universe parameter")
                param_keys.add(name_keys[param])
            all_names = item["all"]
            if not isinstance(all_names, list) or len(all_names) != 1:
                fail("mutual theorem is unsupported", "LF_PREVIEW_UNSUPPORTED")
            all_name = integer(all_names[0], len(names) - 1)
            if name_keys[all_name] != name_keys[name]:
                fail("mutual theorem is unsupported", "LF_PREVIEW_UNSUPPORTED")
            check_level_parameter_scope((item["type"], item["value"]), nodes,
                                        level_expressions, name_keys, param_keys)
            declarations.append(dict(item))
            declared.add(name_keys[name])
        else:
            fail("unsupported record", "LF_PREVIEW_UNSUPPORTED")
    if metadata is None or not declarations:
        fail("missing metadata or theorem")
    return {"version": "0.1", "checked": False, "metadata": metadata,
            "names": names, "levels": levels, "levelExpressions": level_expressions,
            "concreteLevelDataOnly": all(level is not None for level in levels)
                and all(not decl["levelParams"] for decl in declarations),
            "expressions": nodes, "declarations": declarations}


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
