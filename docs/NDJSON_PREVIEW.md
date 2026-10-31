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
sequential string and numeric names, successor, `max`, `imax`, and parameter
universe expressions, bound variables,
applications, lambdas, Pi expressions and singleton theorem
records. Child and name references must refer to existing records. It preserves
binder metadata in its output, but does not check scope, types or proof terms.
Constants, axioms, definitions, inductives, recursors, quotients and mutual
declarations are unsupported, never assumed. Polymorphic theorem metadata is
retained as unchecked data. The preview checks that reachable universe
parameters are listed by each declaration, but does not type-check the result.

Universe records use sequential table indices: zero is implicit, and `succ`
refers to an earlier table entry. Concrete `max` and `imax` refer to two earlier
entries; for concrete levels `imax(a, 0)` is zero, and otherwise it is
`max(a, b)`. Sorts refer to a table index; the preview preserves this index and
the level-expression graph. Concrete values are resolved where all operands
are concrete. A symbolic expression remains `null`, even when simplification
could determine its value. Different table indices may resolve to the same level.
`make test-level-differential` compares the preview and experimental Forth
evaluator on 76 concrete and nested cases with pinned Lean's level normalization;
it is finite test evidence, not a proof.

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
independent human review. The concrete pipeline covers composition, identity,
and a theorem quantified over `Type`. A fourth, universe-polymorphic Lean export
is also decoded. The ordinary concrete test transport rejects previews
containing symbolic levels or level parameters;
it recomputes concrete level values and checks sort references. Its flag and
mutable input are untrusted metadata; a consistently altered input is a
different declaration, not proof of provenance or validity. The general
test-only byte protocol uses
little-endian nonnegative 32-bit fields up to 2,147,483,647, carrying declaration
indices and node records. A synthetic test stages and reads back level 256;
this is not a production serialization. An older, composition-specific test
still uses one-byte fields.
Altered values return non-success, and truncated or extended streams
fail. These examples do not demonstrate general Lean or Mathlib compatibility.
The polymorphic fixture's universe graph and parameter ID also reach an
experimental Forth structural scope check in a separate test-only byte stream.
That check uses opaque IDs and does not resolve structured Lean names or check
the polymorphic theorem. The stream checks only the final level root: unrelated
nodes printed in its table are not thereby shown to be in scope.
Another test-only stream interns selected previewed structured names in Forth
and checks alias mapping, including aliases used as prefixes. It uses one-byte
indices, lengths and numeric components and is limited to 63 exported names;
it is not a general Lean name transport and does not apply the map to the
universe or declaration checker.

A separate test-only stream specializes the polymorphic fixture under explicit
numeric assignments and feeds the resulting concrete expression nodes to the
untrusted Forth declaration probe. It checks four assignments against pinned
Lean's kernel and compares canonical type and value syntax for all four with
Lean's instantiated expressions. It also compares the complete `u = 1` node
table with a separately exported concrete theorem. Missing, invalid or
duplicate assignments fail;
the test uses bounded host integers, opaque name IDs, and untrusted mutable
storage. This exercises four instances, not the polymorphic theorem. No checked
declaration is registered, and no supported runtime or interchange API exists.
Run `make test-poly-specialization-differential` with pinned Lean and Gforth.
