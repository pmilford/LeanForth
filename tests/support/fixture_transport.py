"""Test-only encoding of concrete preview data for the Forth probe.

This format is not a public API and creates no checked declaration. Symbolic
universe data must never be coerced to a concrete level by this adapter.
"""

import struct


def concrete_levels(decoded):
    """Recompute and cross-check the concrete graph; never resolve parameters."""
    expressions = decoded["levelExpressions"]
    if not expressions or expressions[0] != {"tag": "zero"}:
        raise ValueError("missing zero universe")
    levels = [0]

    def prior(index):
        if type(index) is not int or not 0 <= index < len(levels):
            raise ValueError("invalid universe reference")
        return levels[index]

    for expression in expressions[1:]:
        tag = expression.get("tag")
        if tag == "succ" and set(expression) == {"tag", "of"}:
            value = prior(expression["of"]) + 1
        elif tag in ("max", "imax") and set(expression) == {"tag", "left", "right"}:
            left, right = prior(expression["left"]), prior(expression["right"])
            value = 0 if tag == "imax" and right == 0 else max(left, right)
        else:
            raise ValueError("symbolic or malformed universe expression")
        if value > 2147483647:
            raise ValueError("universe outside transport range")
        levels.append(value)
    if decoded["levels"] != levels or any(type(level) is not int for level in decoded["levels"]):
        raise ValueError("inconsistent concrete universe values")
    return levels


def encode_concrete(decoded, declaration_index=0):
    if decoded.get("checked") is not False or decoded.get("concreteLevelDataOnly") is not True:
        raise ValueError("preview is not unchecked concrete-level data")
    declarations = decoded["declarations"]
    if any(decl["levelParams"] for decl in declarations):
        raise ValueError("polymorphic declarations are unsupported by this transport")
    levels = concrete_levels(decoded)
    if type(declaration_index) is not int or not 0 <= declaration_index < len(declarations):
        raise ValueError("invalid declaration index")
    declaration = declarations[declaration_index]
    if declaration.get("kind") != "thm":
        raise ValueError("only theorem fixtures are supported by this transport")
    nodes = decoded["expressions"]
    stream = bytearray(struct.pack("<III", len(nodes), declaration["type"], declaration["value"]))
    for index, node in enumerate(nodes):
        tag = node["tag"]
        if tag == "sort":
            level_index = node["levelIndex"]
            if (type(level_index) is not int or not 0 <= level_index < len(levels)
                    or type(node["level"]) is not int or node["level"] != levels[level_index]):
                raise ValueError("inconsistent sort universe")
            fields = (1, node["level"], 0)
        elif tag == "bvar":
            fields = (2, node["index"], 0)
        elif tag == "app":
            fields = (3, node["fn"], node["arg"])
        elif tag in ("lam", "forallE"):
            fields = (4 if tag == "lam" else 5, node["type"], node["body"])
        else:
            raise ValueError("unsupported expression")
        if any(type(value) is not int or not 0 <= value <= 2147483647 for value in fields):
            raise ValueError("field outside transport range")
        stream.extend(struct.pack("<IIII", index, *fields))
    return stream
