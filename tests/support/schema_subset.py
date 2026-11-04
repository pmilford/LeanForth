"""Validate JSON against a JSON Schema using only the Python standard library.

Usage: python3 tests/support/schema_subset.py SCHEMA FILE...
Prints each validation error and exits 1 if any file is invalid.

Implements the part of JSON Schema draft 2020-12 that the project's schemas
use, and fails closed on everything else: a schema keyword outside SUPPORTED,
a `$ref` that is not a local `#/...` pointer to a schema, or a keyword value
of the wrong shape raises SchemaError before any instance is validated. So a
schema can never appear to enforce a rule this validator does not implement.

Documents are parsed strictly by load_strict, which raises InstanceError
for: text that is not JSON; duplicate object keys; NaN and Infinity; any
number with a fraction or an exponent (the project's JSON has integers
only, and 1e-400 or 12.0000000000000001 would be read lossily); integers
outside I-JSON's exact range -(2**53-1)..2**53-1 (RFC 7493) unless the
caller widens it; lone surrogates; and nesting deeper than MAX_DEPTH.

Deviations from the standard, all on the strict side:
- `pattern` is a Python regular expression searched in the string, as the
  standard does, but `^`, `$` and `.` outside a character class mean what
  they mean in ECMA-262: the start and the end of the whole string (`\\A`,
  `\\Z`; Python's `$` also matches before a final newline), and any
  character but a line terminator (Python's `.` also matches a carriage
  return and U+2028). So `^...$` must match the whole string. Inline flags
  and a `]` first in a class, which differ between the two, are refused.
- `additionalProperties` must be a boolean.
- Formats, dynamic references, `unevaluated*`, `dependent*`, remote `$ref`
  and the other keywords not in SUPPORTED are refused.

The project owner's default is no new packages, so the `jsonschema` package
is not used (docs/programming/PROGRAM_RECEIPTS.md). Untrusted test tooling:
a receipt that validates is well formed, not true.
"""
import json
import re
import sys

# Keywords that only annotate; they never affect validity.
ANNOTATIONS = {"$schema", "$id", "$comment", "title", "description"}
SUPPORTED = ANNOTATIONS | {
    "$defs", "$ref", "type", "properties", "required", "additionalProperties",
    "const", "enum", "pattern", "minLength", "minimum", "maximum", "items",
    "minItems", "maxItems", "contains", "allOf", "anyOf", "if", "then", "else", "not",
}
TYPES = {"null", "boolean", "integer", "number", "string", "array", "object"}
# Keywords whose checking method is not named "_kw_" + keyword.
METHOD_NAMES = {"$ref": "ref", "if": "if_", "$defs": "", "then": "", "else": ""}


class SchemaError(Exception):
    """The schema uses a keyword or shape this validator does not implement."""


class InstanceError(Exception):
    """The document is not strict JSON."""


MAX_DEPTH = 64              # nesting of arrays and objects; a receipt needs 5
MAX_SAFE_INTEGER = 2 ** 53 - 1


def _pairs(items):
    result = {}
    for key, value in items:
        if key in result:
            raise InstanceError(f"duplicate key {key!r}")
        result[key] = value
    return result


def _constant(name):
    raise InstanceError(f"non-standard number {name}")


def _fraction(literal):
    raise InstanceError(f"number {literal[:40]} has a fraction or an exponent; "
                        "only integers are allowed")


def _integers(bound):
    """A parse_int hook refusing integers outside -bound..bound."""
    def integer(literal):
        if len(literal.lstrip("-")) > len(str(bound)) or abs(int(literal)) > bound:
            raise InstanceError(f"integer {literal[:40]} is outside -{bound}..{bound}")
        return int(literal)
    return integer


def _check_tree(value):
    """Refuse nesting deeper than MAX_DEPTH and strings with lone surrogates."""
    stack = [(value, 0)]
    while stack:
        node, depth = stack.pop()
        if depth > MAX_DEPTH:
            raise InstanceError(f"nested deeper than {MAX_DEPTH} levels")
        if isinstance(node, dict):
            stack += [(key, depth) for key in node] + [(v, depth + 1) for v in node.values()]
        elif isinstance(node, list):
            stack += [(item, depth + 1) for item in node]
        elif isinstance(node, str):
            try:
                node.encode("utf-8")
            except UnicodeEncodeError:
                raise InstanceError(f"lone surrogate in string {node[:40]!r}") from None


def load_strict(text, max_integer=MAX_SAFE_INTEGER):
    """Parse strict JSON (see the module's docstring), or raise InstanceError.

    max_integer widens the integer range for a file of the project that is
    not read by other tools, such as a list of 64-bit test cells.
    """
    try:
        value = json.loads(text, object_pairs_hook=_pairs, parse_constant=_constant,
                           parse_float=_fraction, parse_int=_integers(max_integer))
    except RecursionError:
        raise InstanceError(f"nested deeper than {MAX_DEPTH} levels") from None
    except json.JSONDecodeError as error:
        raise InstanceError(f"not JSON: {error}") from None
    _check_tree(value)
    return value


def is_number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def json_type(value):
    """The JSON type name of a parsed value; integral numbers are integers."""
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "boolean"
    if isinstance(value, int) or (isinstance(value, float) and value.is_integer()):
        return "integer"
    if isinstance(value, float):
        return "number"
    if isinstance(value, str):
        return "string"
    if isinstance(value, list):
        return "array"
    if isinstance(value, dict):
        return "object"
    raise InstanceError(f"not a JSON value: {value!r}")


def json_equal(left, right):
    """JSON equality: true is not 1, and 1 equals 1.0."""
    if is_number(left) and is_number(right):
        return left == right
    if type(left) is not type(right):
        return False
    if isinstance(left, list):
        return len(left) == len(right) and all(map(json_equal, left, right))
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(json_equal(left[k], right[k]) for k in left)
    return left == right


# ECMA-262's `.`: any character but a line terminator.
NOT_LINE_TERMINATOR = "[^\\n\\r\\u2028\\u2029]"
OUTSIDE_CLASS = {"^": r"\A", "$": r"\Z", ".": NOT_LINE_TERMINATOR}


def python_pattern(pattern):
    """The Python form of a schema pattern, with ECMA-262's `^`, `$` and `.`.

    Escapes and character classes are copied; outside a class `^` becomes
    `\\A`, `$` becomes `\\Z` and `.` excludes line terminators. Raises
    SchemaError for an inline flag such as `(?x)`, and for a `]` first in a
    class (literal in Python, the end of an empty class in ECMA-262).
    """
    out, i, in_class = [], 0, False
    while i < len(pattern):
        char = pattern[i]
        if char == "\\":
            out.append(pattern[i:i + 2])
            i += 2
            continue
        if in_class:
            in_class = char != "]"
        elif char == "[":
            in_class = True
            if pattern.startswith(("]", "^]"), i + 1):
                raise SchemaError(f"pattern {pattern!r}: a class may not start with ]")
        elif char == "(" and re.match(r"\(\?[-aiLmsux]", pattern[i:]):
            raise SchemaError(f"pattern {pattern!r}: inline flags are not supported")
        else:
            char = OUTSIDE_CLASS.get(char, char)
        out.append(char)
        i += 1
    return "".join(out)


def pointer_part(name):
    """A key as one JSON pointer segment (RFC 6901): ~ is ~0 and / is ~1."""
    return name.replace("~", "~0").replace("/", "~1")


class Validator:
    """A schema checked once for supported keywords, then used to validate."""

    def __init__(self, schema):
        self.root = schema
        self._schemas = set()      # JSON pointers of every subschema
        self._refs = []
        self._patterns = {}
        self._check(schema, "#")
        for ref in self._refs:
            if ref not in self._schemas:
                raise SchemaError(f"$ref {ref!r}: does not point at a schema")

    # Schema checking: fail closed on anything not implemented.

    def _check(self, schema, where):
        self._schemas.add(where)
        if isinstance(schema, bool):
            return
        if not isinstance(schema, dict):
            raise SchemaError(f"{where}: a schema must be an object or a boolean")
        unknown = set(schema) - SUPPORTED
        if unknown:
            raise SchemaError(f"{where}: unsupported keyword(s) {sorted(unknown)}")
        for key, value in schema.items():
            self._check_keyword(key, value, f"{where}/{pointer_part(key)}")

    def _check_keyword(self, key, value, where):
        if key in ANNOTATIONS:
            if not isinstance(value, str):
                raise SchemaError(f"{where}: must be a string")
        elif key in ("$defs", "properties"):
            self._need(isinstance(value, dict), where, "an object of schemas")
            for name, sub in value.items():
                self._check(sub, f"{where}/{pointer_part(name)}")
        elif key in ("items", "contains", "if", "then", "else", "not"):
            self._check(value, where)
        elif key in ("allOf", "anyOf"):
            self._need(isinstance(value, list) and value, where, "a non-empty array")
            for index, sub in enumerate(value):
                self._check(sub, f"{where}/{index}")
        elif key == "$ref":
            self._need(isinstance(value, str), where, "a string")
            self._resolve(value)
            self._refs.append(value)
        elif key == "type":
            names = value if isinstance(value, list) else [value]
            self._need(names and all(n in TYPES for n in names), where, "JSON type names")
        elif key == "required":
            self._need(isinstance(value, list) and all(isinstance(n, str) for n in value),
                       where, "an array of strings")
        elif key == "additionalProperties":
            self._need(isinstance(value, bool), where, "a boolean")
        elif key == "enum":
            self._need(isinstance(value, list) and value, where, "a non-empty array")
        elif key == "pattern":
            self._need(isinstance(value, str), where, "a string")
            self._patterns[value] = re.compile(python_pattern(value))
        elif key in ("minLength", "minItems", "maxItems"):
            self._need(isinstance(value, int) and not isinstance(value, bool) and value >= 0,
                       where, "a nonnegative integer")
        elif key in ("minimum", "maximum"):
            self._need(is_number(value), where, "a number")

    @staticmethod
    def _need(condition, where, what):
        if not condition:
            raise SchemaError(f"{where}: must be {what}")

    def _resolve(self, ref):
        if not ref.startswith("#/"):
            raise SchemaError(f"$ref {ref!r}: only local '#/...' references are supported")
        node = self.root
        for part in ref[2:].split("/"):
            part = part.replace("~1", "/").replace("~0", "~")
            if not isinstance(node, dict) or part not in node:
                raise SchemaError(f"$ref {ref!r} does not resolve")
            node = node[part]
        return node

    # Validation.

    def errors(self, instance):
        """Every error, as 'path: message'; empty when the instance is valid."""
        found = []
        self._validate(instance, self.root, "$", found)
        return found

    def _validate(self, value, schema, path, found):
        if schema is True:
            return
        if schema is False:
            found.append(f"{path}: no value is allowed here")
            return
        for key, rule in schema.items():
            # Annotations, $defs, then and else have no check of their own.
            check = getattr(self, "_kw_" + METHOD_NAMES.get(key, key), None)
            if check is not None:
                check(value, rule, schema, path, found)

    def _sub_valid(self, value, schema, path):
        found = []
        self._validate(value, schema, path, found)
        return not found

    def _kw_ref(self, value, ref, schema, path, found):
        self._validate(value, self._resolve(ref), path, found)

    def _kw_type(self, value, rule, schema, path, found):
        names = rule if isinstance(rule, list) else [rule]
        actual = json_type(value)
        if actual not in names and not (actual == "integer" and "number" in names):
            found.append(f"{path}: expected type {'/'.join(names)}, got {actual}")

    def _kw_const(self, value, rule, schema, path, found):
        if not json_equal(value, rule):
            found.append(f"{path}: must equal {json.dumps(rule, ensure_ascii=False)}")

    def _kw_enum(self, value, rule, schema, path, found):
        if not any(json_equal(value, option) for option in rule):
            found.append(f"{path}: {json.dumps(value, ensure_ascii=False)} is not one of "
                         f"{json.dumps(rule, ensure_ascii=False)}")

    def _kw_pattern(self, value, rule, schema, path, found):
        """A long pattern is cut in the message, followed by its schema's description."""
        if isinstance(value, str) and not self._patterns[rule].search(value):
            shown = rule if len(rule) <= 64 else rule[:24] + "…"
            why = f" ({schema['description']})" if len(rule) > 64 and "description" in schema \
                else ""
            found.append(f"{path}: does not match pattern {shown}{why}")

    def _kw_minLength(self, value, rule, schema, path, found):
        if isinstance(value, str) and len(value) < rule:
            found.append(f"{path}: shorter than {rule} character(s)")

    def _kw_minimum(self, value, rule, schema, path, found):
        if is_number(value) and value < rule:
            found.append(f"{path}: less than the minimum {rule}")

    def _kw_maximum(self, value, rule, schema, path, found):
        if is_number(value) and value > rule:
            found.append(f"{path}: greater than the maximum {rule}")

    def _kw_required(self, value, rule, schema, path, found):
        if isinstance(value, dict):
            for name in rule:
                if name not in value:
                    found.append(f"{path}: missing required property {name!r}")

    def _kw_properties(self, value, rule, schema, path, found):
        if isinstance(value, dict):
            for name, sub in rule.items():
                if name in value:
                    self._validate(value[name], sub, f"{path}.{name}", found)

    def _kw_additionalProperties(self, value, rule, schema, path, found):
        if isinstance(value, dict) and rule is False:
            for name in value:
                if name not in schema.get("properties", {}):
                    found.append(f"{path}: additional property {name!r} is not allowed")

    def _kw_items(self, value, rule, schema, path, found):
        if isinstance(value, list):
            for index, item in enumerate(value):
                self._validate(item, rule, f"{path}[{index}]", found)

    def _kw_minItems(self, value, rule, schema, path, found):
        if isinstance(value, list) and len(value) < rule:
            found.append(f"{path}: fewer than {rule} item(s)")

    def _kw_maxItems(self, value, rule, schema, path, found):
        if isinstance(value, list) and len(value) > rule:
            found.append(f"{path}: more than {rule} item(s)")

    def _kw_contains(self, value, rule, schema, path, found):
        if isinstance(value, list) and not any(
                self._sub_valid(item, rule, f"{path}[{i}]") for i, item in enumerate(value)):
            found.append(f"{path}: no item matches {describe(rule)}")

    def _kw_allOf(self, value, rule, schema, path, found):
        for sub in rule:
            self._validate(value, sub, path, found)

    def _kw_anyOf(self, value, rule, schema, path, found):
        if not any(self._sub_valid(value, sub, path) for sub in rule):
            found.append(f"{path}: matches none of the allowed forms")

    def _kw_not(self, value, rule, schema, path, found):
        if self._sub_valid(value, rule, path):
            found.append(f"{path}: matches a forbidden form")

    def _kw_if_(self, value, rule, schema, path, found):
        branch = "then" if self._sub_valid(value, rule, path) else "else"
        if branch in schema:
            self._validate(value, schema[branch], path, found)


def describe(schema):
    """A short description of a subschema for error messages."""
    if isinstance(schema, dict) and "$ref" in schema:
        return schema["$ref"]
    return json.dumps(schema, ensure_ascii=False, sort_keys=True)


def validate_file(validator, path):
    """Errors for one file, including strict-parsing errors."""
    try:
        with open(path, encoding="utf-8") as handle:
            instance = load_strict(handle.read())
    except (InstanceError, ValueError) as error:
        return [f"$: not strict JSON: {error}"]
    return validator.errors(instance)


def main(argv):
    if len(argv) < 3:
        print(__doc__.splitlines()[2], file=sys.stderr)
        return 2
    with open(argv[1], encoding="utf-8") as handle:
        validator = Validator(load_strict(handle.read()))
    status = 0
    for path in argv[2:]:
        problems = validate_file(validator, path)
        for problem in problems:
            print(f"{path}: {problem}")
        status = status or bool(problems)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
