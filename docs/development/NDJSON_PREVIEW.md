# Development preview of Lean NDJSON

**Forth now reads Lean exports itself:** see
[NDJSON_READER.md](NDJSON_READER.md). Under the owner's product rule (end
users need only a Forth system and an NDJSON file) and decision OQ-4, the
Python preview described here is a development tool and a test oracle, not
part of the user's path.

`tests/support/ndjson_preview.py` is an untrusted Python 3 development tool,
not a supported runtime importer. It reads an export on standard input and
prints deterministic JSON with `checked: false`; malformed or unsupported
input yields a structured error on standard error, a nonzero exit status, and
no partial result. For example:

```sh
python3 tests/support/ndjson_preview.py < tests/reference/composition.ndjson
make test-composition-fixture
```

## Outcomes and error contract

Every input ends in exactly one outcome, following the owner's three-outcome
policy plus a resource outcome. No failure is ever reported as success.

| Outcome | Exit | `code` on standard error | Meaning |
| --- | --- | --- | --- |
| accepted | 0 | none | One JSON line on standard output: **unchecked** data, never a checked theorem |
| rejected | 1 | `LF_PREVIEW_MALFORMED` | Not a well-formed pinned lean4export 3.1.0 stream |
| unsupported | 2 | `LF_PREVIEW_UNSUPPORTED` | A well-formed record or version this preview does not handle yet |
| limit | 3 | `LF_PREVIEW_LIMIT` | A prototype bound was exceeded; the input may be valid Lean |
| internal fault | 4 | `LF_PREVIEW_INTERNAL` | An unexpected error in the preview itself; still a failure |

A failure writes nothing to standard output and one JSON object to standard
error with the keys `code`, `message` and `line`: the 1-based NDJSON line of the
failing record, the last line read when the stream ends without metadata or a
declaration, or `null` for empty input. Messages are diagnostic text and may change; tests pin
codes and lines. Output is byte-identical across runs and `PYTHONHASHSEED`
values.

**Framing is strict and fails closed.** The pinned exporter writes plain UTF-8
with one JSON object per line, each terminated by a line feed. The preview
therefore rejects, as malformed: invalid UTF-8 (including encoded surrogates and
overlong forms), a byte order mark, any carriage return (so CRLF line endings
too), a final line without its line feed, blank lines, and strings holding lone
surrogate escapes. Spaces between JSON tokens are accepted.

**Malformed versus unsupported.** Record kinds not defined by export format
3.1.0 are malformed: unknown name, level, expression or top-level record kinds
(including level `mvar` and expression `fvar`), records mixing kinds, a second
metadata record, and enumeration values outside the format (`binderInfo`,
`hints`, `safety`, quotient `kind`). Metadata fields that are not strings are
malformed; well-typed metadata naming another exporter, format, Lean version or
revision is unsupported. A declaration's `all` list must be nonempty, hold
distinct names and contain the declaration itself; a longer, well-formed list is
an unsupported mutual block. Format kinds the preview does not handle (`letE`,
`proj`, `natVal`, `strVal`, `mdata`, `axiom`, `opaque`, `quot` and `inductive`)
are unsupported once their shape matches the records observed in pinned Lean
4.35.0 exports: exact field sets, earlier references for their direct name and
expression fields, booleans, canonical decimal `natVal` text, and the nested
field sets of inductive types, constructors, recursors and recursor rules. A
malformed payload of one of these kinds is rejected. No pinned export has yet
produced `mdata`, so its payload is **not** validated and any `mdata` record is
reported as unsupported. Nested values inside inductive records are not
reference-checked. The stream stops at its first failing record, so an
unsupported report names only the first unsupported kind.

**Numbers.** Integer fields accept JSON integers only: booleans, floats, strings
and negative values are malformed. Record indices must be sequential, so an
index far beyond a table, such as name index 300, is malformed rather than a
limit. Lean natural numbers that are valid but exceed the preview's signed
32-bit bound (name `num` components, `bvar` indices and `hints.regular` up to
the `UInt32` maximum) are a limit; a reducibility height beyond `UInt32` is
malformed.

The preview supports the pinned Lean 4.35.0 and export format 3.1.0 metadata,
sequential string and numeric names, successor, `max`, `imax`, and parameter
universe expressions, bound variables, constant references with ordered universe
arguments, applications, lambdas, Pi expressions and singleton definition and theorem
records. Child and name references must refer to existing records. It preserves
binder metadata in its output, but does not check term-variable scope, types or proof terms.
Definitions and their safety/reducibility fields are returned as **unchecked
data**, not registered or unfolded; even a `safe` field is just exported input.
Axioms, inductives, recursors, quotients and mutual declarations are unsupported,
never assumed. Polymorphic declaration metadata is retained as unchecked data.
The preview checks that reachable universe
parameters are listed by each declaration, but does not type-check the result.
For constants, it validates name and level-table indices and preserves the
ordered `us` list; it does not resolve referenced declarations, check universe
arity as a validity judgment, authorize axioms or establish dependencies.
The preview reports bounded **observations** for constants reachable from each
declaration's type or value: the expression and name indices, whether the
referenced name appears earlier, later, on the same declaration, or nowhere in
the stream, and whether locally observed universe-argument counts match. It
matches full structured names, not rendered names or raw name indices. Missing
means only absent from this stream. `targetRecord` is a zero-based index in the
returned `declarations` list, not an NDJSON line number. `arityMatches` compares
only the two observed counts; it does not validate a declaration or type.
Cycle analysis, external environments,
declaration validity and completeness are not checked; the output explicitly
has `cyclesChecked: false`, `dependenciesChecked: false` and `checked: false`.
The provisional output is version `0.4` (0.4 introduced the strict framing,
reclassified outcomes, distinct exit codes and error lines described above;
the success payload is otherwise unchanged from 0.3); observations are ordered by declaration
and expression index. Shared occurrences use `inType` and `inValue` flags.
These are diagnostics for planning an import, not authorization to use a
declaration or an axiom.

The pinned `constant-fixture.ndjson` contains two definitions and a theorem
with symbolic and concrete universe instances of a referenced constant.
`make reference-export` reproduces it with Lean's exporter. This preview can
read those records, but neither existing Forth transport accepts constants or
definitions, and the fixture cannot yet be independently checked by LeanForth.
At this checkpoint the source SHA-256 is
`e09e14555a4faad4874a96ed9fc76374ef5d4f326ab37f2c85ce23dc79b7b710` and
the export SHA-256 is
`b6444346ee56d77f6936fb1bdca389b25bc76330b146fb7612fb6fc5c1be0249`.

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

It bounds each input line to 4096 bytes including its line feed, the stream to
1 MiB (1,048,576 bytes), names and explicit universe entries to 256 each,
expression nodes to 64, declarations to 64 and a constant's universe arguments
to 256. Tests check each bound both at the limit (accepted) and one step beyond
it (`LF_PREVIEW_LIMIT`). Overlong JSON nesting is rejected as malformed. These limits are prototype constraints, not a
Mathlib-scale design. The output format is not yet a versioned production API
or a stable serialization. No Python code is part of the trusted kernel.

`tests/core/test_preview_contract.py` holds the outcome-contract tests (framing,
classification, limits, numeric edges and the command-line contract); `make
test` runs it directly (target `test-composition-fixture`), and
`tests/core/test_ndjson_preview.py` pins the SHA-256 of all five
`tests/reference/*.ndjson` fixtures.

The fixture test independently compares preview nodes against the existing
fixture inspector and feeds the resulting fields as test-only binary data to
the untrusted Forth staging (`src/import/load.fs`), which must give back the
same nodes. The current checker accepts symbolic Sorts only, so
`tests/core/test_export_definitions.py` stages the same exports as handle
terms with symbolic levels (`tests/core/export-definition-stream.fs`) and runs
`lf-mixed-definition-probe` on each claim and value. Neither the preview nor
the probe registers a theorem; declaration import and the trusted boundary
require independent human review. The pipeline covers composition, identity,
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
it is not a general Lean name transport. A separate integration test applies
Forth's interned IDs to a level context and comparison, including equal aliases
with different export indices. It does not register a declaration or establish
the identity of names across mutable table lifetimes. Only the selected level
roots are scope-checked; disconnected staged levels do not inherit that result.

The same stream can replace the polymorphic fixture's universe parameter by
`succ^k zero` (`lf-mixed-level-substitute`) before the definition probe. It
checks four instances against pinned Lean's kernel and compares canonical type
and value syntax for all four with Lean's instantiated expressions
(`make test-export-specialization-differential`); `test_export_definitions.py`
also compares the `u = 1` instance with the separately exported concrete
theorem. `tests/core/export-signature-stream.fs` puts the fixture's claim into
the candidate signature index and compares its `lf-msp-specialize` results with
Lean's `instantiateLevelParams` (`make test-export-signature-differential`).
Missing or extra replacements fail; the test uses bounded host integers,
opaque name IDs, and untrusted mutable storage. This exercises four instances,
not the polymorphic theorem. No checked declaration is registered, and no
supported runtime or interchange API exists.

`tests/core/test_export_definitions.py` stages the pinned polymorphic
identity's expressions with symbolic Sorts and its single opaque universe
parameter, and the untrusted definition probe checks the unspecialized
proposition and proof without specializing the parameter; the proposition
given as its own proof does not check. This is a single fixture and a
restricted byte protocol; binder names, binder information and declaration
names are not preserved. A zero diagnostic does not register or accept a
theorem. Full NDJSON import, trusted checking and Mathlib remain unavailable.
(An earlier test of the same pair through the superseded `tagged-*`
declaration diagnostic was retired with that code on 2026-11-02.)
