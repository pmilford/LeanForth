# Inductive blocks: the first data types LeanForth checks

Status: implemented 2026-11-04 as plan task 5.2.1a of
[ADR 0015](../adr/0015-inductive-types.md) (design accepted by the owner
on 2026-11-03). **Experimental [kernel] and [import] code, not through
its review gate and not independently audited.** Every accepted result is
*accepted (experimental, not independently audited)*. Source:
`src/kernel/check-block.fs` (the check, in Lean's order),
`src/kernel/inductive-block.fs` (the block, its shape and the checks
that need no typing), `src/kernel/inductive-recursor.fs` (the recursor
LeanForth builds), `src/kernel/level-geq.fs` (Lean's `is_geq`), with
small changes to `src/core/input.fs` and `src/import/feed.fs` (the data
the check reads), `src/kernel/env-publish.fs` and `environment.fs` (a
block published together), `src/kernel/env-signature.fs` (the block's
own type visible to inference) and `src/kernel/mixed-infer.fs` (a
guard for structures like `PUnit`).

## In plain words

A data type in Lean is given by its constructors, the ways of building an
element; Lean's kernel then derives the type's **recursor**, the
principle of induction and of definition by cases, together with
computation rules. An export file holds the type, its constructors and a
recursor, but the file's recursor is never trusted: LeanForth runs the
checks Lean's kernel runs on the type and its constructors, in Lean's
order, **builds the recursor itself** exactly as Lean's kernel builds it,
and compares it, field by field, with the one in the file. If the file's
recursor is not the one Lean's kernel would have built, the file is
rejected, as Lean's own checker of exports rejects it. Only then do the
type, its constructors and its recursor become usable by later
declarations, all at the same moment.

Task 5.2.1a covers a block of **one type that is not recursive**: no
constructor takes an argument of the type being defined. That includes
`Bool`, `True`, `And`, `Or`, `Exists`, `Eq`, `PUnit`, `PProd` and
structures such as `Add`. Recursive types (`Nat`, `List`), mutual and
nested blocks are later tasks and are answered *unsupported*, and so is
everything that uses them.

## Example in three forms

Conjunction, the structure `And` (ADR 0015, §1).

- **Mathematics.** A proof of $a \wedge b$ is a pair of proofs. Its
  recursor: from $f : \forall (x : a)(y : b),\ C\,(x, y)$ we get $C\,t$
  for every $t : a \wedge b$, with $\mathrm{rec}\,f\,(x, y) = f\,x\,y$.
- **LeanForth words** (ADR 0017 §15 *sketch syntax, not implemented*:
  LeanForth reads data types from Lean exports only):

  ```text
  structure MyAnd
    Prop explicit: a
    Prop explicit: b
    Prop
  where
    a explicit: left
    b explicit: right
    MyAnd a $ b $  constructor: intro
  end MyAnd
  ```

- **Lean.** `structure And (a b : Prop) : Prop where intro :: left : a;
  right : b`. The kernel generates

  ```text
  And.rec.{u} : {a b : Prop} → {motive : a ∧ b → Sort u} →
    ((left : a) → (right : b) → motive ⟨left, right⟩) → (t : a ∧ b) → motive t
  k = false; rule And.intro, 2 fields: fun a b motive intro left right => intro left right
  ```

What LeanForth does with Lean's export of it
(`tests/core/check-block-cases/ind.and.ndjson`, the row `ind.and` of the
inductive table): it reads the one-line block record
`{"inductive":{"types":[…],"ctors":[…],"recs":[…]}}`, checks the type
`Prop → Prop → Prop` and the constructor, finds that the result is a
proposition with one constructor whose two fields are proofs (so the
recursor may eliminate into every universe, rule E3, and gets its own
universe `u`), builds `And.rec`'s type and rule as above, finds them equal
to the file's, and publishes `And`, `And.intro` and `And.rec` together:
`make test-check-block` prints nothing for it but checks *accepted* at
step 15. Change the file's rule to `fun a b motive intro left right =>
intro right left`, and the same check rejects the block at step 13 (rule
B3, Lean's replay: "Invalid recursor").

## What is checked, and in which order

The check runs when the checked environment reaches a block's first
member (`check-declaration.fs` sends every block member to
`lf-block-check`). Its steps, each ended by the first failure; the step
reached is `lf-block-step@` (15 when every step succeeded); every
rejection names Lean's reason through a diagnostic
([codes 62–75](DIAGNOSTICS.md#catalogue)):

| Step | Rule (ADR 0015) | What | Lean (`inductive.cpp`, 4.35.0) | LeanForth's outcome on failure |
| ---: | --- | --- | --- | --- |
| 1 | B0, U1 (audit), U2, V1, scope | the block as lean4export writes it; no unsafe member; no `let`, literal, projection or metadata; no loose variable; one type, mentioned by each constructor only as the head of its result | replay's reading; 1237–1247 | invalid (shape, V1); unsupported (unsafe, U2, mutual, recursive, the type in a result index) |
| 2 | T0 | no constant named under `_nested` | 1222–1233 | rejected |
| 3 | C1 | each occurrence of the type applied to the block's universe parameters and parameters | 134–164 | rejected |
| 4 | T1 | at least `numParams` binders | 1138–1146 | rejected |
| 5 | T5 | universe parameters distinct | 869 | rejected |
| 6 | N2 | the type's name and `T.rec` unused | 258–259 | rejected; unknown or unsupported when an earlier declaration of that name is undecided or unsupported (K5) |
| 7 | — | the type's type inferred | 261 | inference's outcome |
| 8 | T2 | its telescope (parameters, indices) and a `Sort` at the end | 263–287 | rejected (typeExpected); unknown where Lean's `whnf` might unfold a definition |
| 9 | C4, N2, C2, U1, C3 | each constructor: name unique, unused, its type inferred, each parameter's domain the type's, each field's universe within the result's (Lean's `is_geq`) unless the type is a proposition, its result `T As is` | 456–497 | rejected; unknown where a comparison needs unfolding |
| 10 | E0–E4, K1 | the elimination level (every universe, or `Prop` only) and `k` | 522–616 | — |
| 11 | N2 | `T.rec` is no constructor's name | 813 | rejected |
| 12 | G1, G2 | the recursor's type and rules built | 632–819 | full when the term store has no room |
| 13 | B3 | every constructor and every exported recursor equal to the one built, by Lean's `==` | `Lean/Replay.lean` 148–164 | rejected (Invalid constructor, Invalid recursor, No such recursor) |
| 14 | B4 | the type's `numIndices`, `isRec`, `isReflexive`, `numNested`, and a recursor missing from the block: never used, never failing | replay ignores them | accepted, with a warning bit (`lf-block-warnings`) |

Not run: positivity (436–452) holds trivially, since the scope leaves no
field mentioning the type and reduction never creates an occurrence; G4,
Lean's defensive check of its own recursors (829–866), is replaced by the
comparison with Lean's recursor (B3), and for a non-recursive block each
rule's result is the minor premise applied to the fields, whose type is
the recursor's result type by construction.

**Lean's local types.** Lean gives each parameter, index and field the
type of its binder with outer `outParam`, `semiOutParam`, `optParam` and
`autoParam` removed (`consume_type_annotations`); LeanForth does the same
when it builds the recursor and when it types the constructors' fields.

**Where Lean might unfold, LeanForth says unknown.** Definitional
unfolding is phase 4. A telescope or a field type headed by a definition
(for example `outParam (Type w)` in `HAdd`), or a parameter domain that is
equal to the type's only after unfolding (`id Type`), leaves the block
*unknown*, never rejected.

**Comparison (B3).** Constructors first, then recursors, as Lean's replay:
a constructor's universe parameters, index, `numParams` and `numFields`
(its name, type and type name are the kernel's own, by B0); a recursor's
name (`T.rec`, else "No such recursor"), universe parameters (the motive's
universe first, `u` or `u_1`, … when taken), type, `all`, `numParams`,
`numIndices`, `numMotives`, `numMinors`, rules (constructor, `nfields`,
right side) and `k`. Terms compare structurally (`mixed-compare.fs`): the
store keeps no binder names or annotations, which Lean's `==` ignores.

**Publication (B5).** The check's candidate covers all the block's
members (`lf-env-span!`, `environment.fs`); the publisher re-checks every
member (kind, safety, no value, its block, distinct universe parameters,
every name unused below the block), writes every slot with the one
outcome, the input declaration and the shared dependencies, and marks them
final last (`env-publish.fs`). The serial run skips the members already
final.

**The block's own type during the check.** Lean adds the type to its
environment before it checks the constructors. LeanForth's inference finds
it through a hook in `env-signature.fs` (`lf-envsig-local`), set by
`check-block.fs` and answering only during a block's step 9, with L1 and L2
as for any constant and no dependency.

**A guard in comparison (P4).** With structures in the environment,
Lean's last comparison route, `is_def_eq_unit_like`, makes any two terms of
a structure like `PUnit` equal. Rules D3 and D5 of
[ADR 0011](../adr/0011-definite-rejection.md) therefore no longer call two
variable-headed terms apart unless the left one's type is visibly no
constant application (`lf-minfer-unit-free?`, `mixed-infer.fs`). Without
it, `fun x y P h => h : ∀ x y : PUnit, ∀ P, P x → P y`, which Lean
accepts, would be rejected (row `unit.punit-variables`).

## Data in the input

The feed (`src/import/feed.fs`) gives each block a header and each member
its exported data in `lf-input-more` (`src/core/input.fs`): a type's
`numParams`, `numIndices`, `numNested`, flags, `all` and `ctors`; a
constructor's `induct`, `cidx`, `numParams`, `numFields`; a recursor's
numbers, `k`, `all` and rules (constructor, `nfields`, right side as a
term). `lf-input-add` checks that every record lies within the data; the
data is in the input's fingerprint. Only the feed path carries blocks;
`import/checker-input.fs` (the command line's reader) still refuses
inductive types.

## Limits

- 512 constructors per block (`lf-ind-ctor-capacity`); parameters plus
  indices, and the fields of one constructor, at most 64 (inference's
  binder context); a check records at most 16 dependencies
  (`lf-env-dep-capacity`). Beyond: *full*.
- A recursor missing from the block is accepted (B4, as Lean's replay),
  but no slot holds it: a later declaration naming it is rejected as an
  unknown constant, where Lean's replay would use the recursor its kernel
  generated (a tampered file only; lean4export always writes it).
- Under the feed's name view, U1's `is_geq` orders two universe
  parameters by their names in the stage (`lf-name-part-ok?`); until the
  review rvKC's finding H1 was fixed (2026-11-04) it read the plain name
  store, which left levels such as `max u v` *unknown* (blocks such as
  `PProd`).

## Evidence

- `make test-inductive-table` (part of `make check`): every one of the 120
  cases of `tests/reference/inductive-expected.lean` as the export Lean
  prints for it, checked by LeanForth. Task 5.2.1a's 44 rows: 38 give
  Lean's verdict (19 accepted, 19 rejected, each with Lean's reason), and
  six are pending, each
  named with its reason: four use or redeclare `Nat` (task 5.2.1b), one
  needs unfolding (`id Type`), and an empty block has no declaration to
  check (the reader refuses it). Each pending rule is reached by a twin
  row without the dependency. The 76 rows of later tasks give
  *unsupported* or *unknown*, or Lean's own verdict (`ind.eq`, an indexed
  family; two universe rows with indices; none differs), except two
  whose files name a constant they never declare, which the importer
  refuses as *invalid*.
- `make test-check-block` (part of `make test`): 41 of those files
  committed in `tests/core/check-block-cases/` (the table test checks they
  are still Lean's), every outcome with its rule's diagnostic and step,
  Lean's replay of the `Bool` block with twelve mutations, `blocks.ndjson`
  published block by block and tampered one field at a time (recursor
  numbers, rules, `k`, constructor fields; B4 fields; B0, unsafe, U2, V1),
  a fuel bisection (exhausted below the least budget, ok from it), and a
  full term store.
- Eighteen planted faults (`ind-*` in `tests/mutants/faults.toml`), each
  caught by `tests/core/check-block.fs`.
- Lean's `Init` checked whole (2026-11-04, a probe, 896 s with
  `gforth-fast`; details in ADR 0015, *Implementation (plan task
  5.2.1a)*): of its 604 blocks, 551 are in this task's scope; 142 are
  accepted, their recursors generated equal to Lean's; 144 are unknown
  (unfolding, undecided dependencies, and 30 by the name-view defect);
  265 are unsupported (a dependency such as `Nat`, or a U2 form); none is
  rejected or invalid.

## Measured (2026-11-04, this machine, other agents running)

| What | Size | Time |
| --- | --- | --- |
| `make test-check-block` (41 files, 20 tampered runs, about 40 fuel runs) | — | 0.3 s (`gforth`) |
| `make test-inductive-table` (120 files; one Lean run) | 50,000 lines of Lean output | 38 s |
| Lean's `Init`, every declaration checked | 345 MB export, 59,349 declarations, 604 blocks | 896 s (`gforth-fast`): stage 26 s, feed 126 s, checks 744 s |
