# ADR 0005: structured names — proposal

Status: **draft for human review; not approved for trusted use**. Lean names
are needed for universe parameters, constants and declaration identities.
This proposal does not authorize any declaration or axiom.

## Candidate representation

Represent anonymous names and chains of `str(prefix, component)` and
`num(prefix, component)`. Name equality depends on the full structured prefix,
the component kind and the exact string or natural-number component. Do not
merge numeric components with digit strings or normalize visually similar
Unicode spellings. A future importer must interpret Lean strings correctly,
validate its input encoding, handle Lean's natural-number range or report a
resource limit, and never equate names merely because their export indices match.

Interning is a candidate optimization: within one immutable table and lifetime,
the same structured name may receive the same ID. This depends on correctly
canonicalizing prefixes, protecting the storage and preventing ID reuse across
resets. A numeric ID alone does not establish Lean name identity across imports,
tables or lifetimes. Any serialization must encode structure and bytes, not a
host pointer or cell layout.

## Experimental evidence and limitations

`src/experimental/names.fs` uses global mutable bounded storage, byte strings
and nonnegative host-cell numeric components. It interns equivalent components
under the same prefix and checks basic storage bounds before reading strings.
It does not validate UTF-8, protect raw memory, authenticate stale IDs or prove
canonical uniqueness after corruption. Caller-supplied input addresses must be
readable. A test-only stream maps interned IDs into an experimental level
context; the IDs are not connected to trusted declaration or level checking.
`make test-name-differential` compares nine hand-selected cases with Lean
4.35.0; this is finite evidence, not proof of general name compatibility.

Before using name identity in trusted conversion or declaration lookup, a human
reviewer must examine encoding semantics, canonicalization, overflow, table
ownership and lifetimes, corruption handling, resource limits and integration
with Lean import. The existing symbolic-level comparison still depends on an
external opaque-ID identity assumption and is not made trusted by this arena.
