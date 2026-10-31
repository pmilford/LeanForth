# Development preview of Lean NDJSON

`tests/support/ndjson_preview.py` is an untrusted Python 3 development tool,
not a supported runtime importer. It reads an export on standard input and
prints deterministic JSON with `checked: false`; malformed or unsupported
input yields a structured error on standard error, a nonzero exit status, and
no partial result. For example:

```sh
python3 tests/support/ndjson_preview.py < tests/reference/composition.ndjson
make test-composition-fixture
```

The preview supports the pinned Lean 4.35.0 and export format 3.1.0 metadata,
sequential string and numeric names, concrete successor universes, bound variables,
applications, lambdas, Pi expressions and non-polymorphic singleton theorem
records. Child and name references must refer to existing records. It preserves
binder metadata in its output, but does not check scope, types or proof terms.
Universe `max`, `imax`, and parameters, constants, axioms, definitions, inductives, recursors,
quotients, polymorphic and mutual declarations are unsupported, never assumed.

Universe records use sequential table indices: zero is implicit, and `succ`
refers to an earlier table entry. Sorts refer to a table index; the preview
preserves this index and resolves its concrete successor count. Different table
indices may resolve to the same level.

It bounds each input line to 4096 bytes, the stream to 1 MiB, names and explicit
universe entries to 256 each, expression nodes to 64 and declarations to 64.
JSON nesting is subject to the
Python decoder's recursion limit. These limits are prototype constraints, not a
Mathlib-scale design. The output format is not yet a versioned production API
or a stable serialization. No Python code is part of the trusted kernel.

The fixture test independently compares preview nodes against the existing
fixture inspector and feeds the resulting fields as test-only binary data to
the untrusted Forth staging and declaration probe. Neither the preview nor the
probe registers a theorem; declaration import and the trusted boundary require
independent human review. The pipeline currently covers composition, identity,
and a theorem quantified over `Type`. The general test-only byte protocol uses
little-endian nonnegative 32-bit fields up to 2,147,483,647, carrying declaration
indices and node records. A synthetic test stages and reads back level 256;
this is not a production serialization. An older, composition-specific test
still uses one-byte fields.
Altered values return non-success, and truncated or extended streams
fail. These examples do not demonstrate general Lean or Mathlib compatibility.
