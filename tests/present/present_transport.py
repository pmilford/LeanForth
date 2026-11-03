"""Test-only byte transport of a pinned Lean export for the term printer.

Unlike the earlier transports (tests/support/fixture_transport.py and
export_definition.py), this one keeps what printing needs: structured
names, binder names and binder kinds, universe parameter names, constants
with their universe arguments, and declaration names. It decodes with the
NDJSON preview (tests/support/ndjson_preview.py), so malformed input is
refused there. The Forth NDJSON reader will replace it; it is not a public
format. tests/present/fixture-reader.fs reads the stream from stdin as data.

Every field is an unsigned 32-bit little-endian integer:
  names:   N, then per name: kind (1 string, 2 number), prefix (0 is the
           anonymous name, otherwise an earlier name), then for a string
           its length and that many raw UTF-8 bytes, for a number its value;
  levels:  L (records after the implicit zero), then per level: tag
           (1 succ, 2 max, 3 imax, 4 param), first, second (earlier level
           indices; a parameter's first field is its name index);
  terms:   E, then per term: tag, then 1 sort: level; 2 bvar: index;
           3 app: fn, arg; 4 lam and 5 pi: type, body, name, kind
           (0 default, 1 implicit, 2 strict implicit, 3 instance);
           7 const: name, count, that many level indices;
  decls:   D, then per declaration: kind (0 def, 1 theorem), name, count,
           that many parameter name indices, type, value.

Usage: python3 tests/present/present_transport.py FIXTURE.ndjson > stream
"""
import struct
import sys

sys.path.insert(0, "tests/support")
from ndjson_preview import preview  # noqa: E402

KINDS = {"default": 0, "implicit": 1, "strictImplicit": 2, "instImplicit": 3}
LEVEL_TAGS = {"succ": 1, "max": 2, "imax": 3, "param": 4}


def fields(*values):
    for value in values:
        if type(value) is not int or not 0 <= value < 2**32:
            raise ValueError("field outside the transport range")
    return struct.pack("<" + "I" * len(values), *values)


def encode_names(names):
    out = bytearray(fields(len(names) - 1))
    for name in names[1:]:
        if name["kind"] == "str":
            data = name["component"].encode("utf-8")
            out += fields(1, name["prefix"], len(data)) + data
        else:
            out += fields(2, name["prefix"], name["component"])
    return out


def encode_levels(levels):
    out = bytearray(fields(len(levels) - 1))
    for level in levels[1:]:
        tag = level["tag"]
        if tag == "succ":
            out += fields(1, level["of"], 0)
        elif tag in ("max", "imax"):
            out += fields(LEVEL_TAGS[tag], level["left"], level["right"])
        else:
            out += fields(4, level["name"], 0)
    return out


def encode_term(node):
    tag = node["tag"]
    if tag == "sort":
        return fields(1, node["levelIndex"])
    if tag == "bvar":
        return fields(2, node["index"])
    if tag == "app":
        return fields(3, node["fn"], node["arg"])
    if tag in ("lam", "forallE"):
        return fields(4 if tag == "lam" else 5, node["type"], node["body"], node["name"],
                      KINDS[node["binderInfo"]])
    if tag == "const":
        return fields(7, node["name"], len(node["us"]), *node["us"])
    raise ValueError("unsupported expression")


def encode_declaration(decl):
    kind = {"def": 0, "thm": 1}[decl["kind"]]
    params = decl["levelParams"]
    return fields(kind, decl["name"], len(params), *params, decl["type"], decl["value"])


def encode(decoded):
    out = encode_names(decoded["names"]) + encode_levels(decoded["levelExpressions"])
    out += fields(len(decoded["expressions"]))
    for node in decoded["expressions"]:
        out += encode_term(node)
    out += fields(len(decoded["declarations"]))
    for decl in decoded["declarations"]:
        out += encode_declaration(decl)
    return bytes(out)


def main(path):
    with open(path, "rb") as stream:
        sys.stdout.buffer.write(encode(preview(stream)))


if __name__ == "__main__":
    main(sys.argv[1])
