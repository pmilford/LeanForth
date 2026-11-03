# First checker: expected results

**Status: reference table for the first checker (plan tasks 2.1.4 and
2.2.1); Lean's column was checked on 2026-11-02; "LeanForth must answer" is
the requirement, and "Measured" is what LeanForth's code answers today**
(2026-11-02, plan task 2.2.1, [kernel] code not yet through its review
gate; see [Measured](#measured-2026-11-02)). The rules behind the columns
are in [ADR 0011](../adr/0011-definite-rejection.md) (rules accepted by the
owner); the owner's summary is [the gate draft](FIRST_CHECKER_GATE.md).

## How to read it

Each row is one declaration: one of the five pinned fixtures, a deliberately
broken copy, or a declaration outside the first checker's scope.

- **Lean 4.35.0 kernel** — what pinned Lean's kernel said when the exact
  declaration was added to an environment holding only the rows named in
  *Earlier*: *accepted*, or the kind of error it raised. Checked by
  `tests/reference/first-checker-expected.lean`.
- **LeanForth must answer** — the outcome the first checker must give.
  *rejected* only where Lean certainly rejects (and with the same kind of
  error); *unknown* where Lean decides by a rule the first checker does not
  have yet; *unsupported* for a feature not built yet; *invalid* for
  malformed input. For the owner, *unknown* and *unsupported* together are
  the outcome "unsupported/unknown".
- **Rule** — the ADR 0011 rule that decides LeanForth's answer.
- **Source copy** — "yes" when the same mistake is also written as ordinary
  Lean source in `tests/reference/first-checker-invalid.lean`, where Lean
  must reject it with a fixed message (Lean's front end usually finds the
  mistake before the kernel, so the message differs from this table).
- **Measured** — LeanForth's answer from today's code, with the rule its
  diagnostic names: for D rules, every D rule used from the compared pair
  down to the pair that decided (`D3+D4`: the claim and the proof's type
  are Πs, D4, whose bodies are different variables, D3). "Stand-in audit"
  marks the rows the declaration audit of plan task 2.2.3 will decide; a
  test driver stands in for it today.

Lean error kinds: `appTypeMismatch` (an argument of the wrong type),
`declTypeMismatch` (the proof proves something other than the claim),
`typeExpected` (a type was needed), `funExpected` (a function was needed),
`thmTypeIsNotProp` (a theorem's statement is not a proposition),
`unknownConstant`, `alreadyDeclared`, `levelCount` (wrong number of universe
arguments), `undefinedLevelParam`, `duplicateLevelParam`, `looseBVar` (a
variable without a binder). The last four are Lean's `other` errors,
recognised by their fixed message.

## Summary

| | Lean accepted | Lean rejected | Total |
| --- | ---: | ---: | ---: |
| LeanForth **accepted** | 14 | 0 | 14 |
| LeanForth **rejected** | 0 | 28 | 28 |
| LeanForth **invalid** | 0 | 1 | 1 |
| LeanForth **unknown** | 10 | 1 | 11 |
| LeanForth **unsupported** | 8 | 0 | 8 |
| Total | 32 | 30 | 62 |

Every fixture group reaches *accepted*, a failure (*rejected* or *invalid*)
and *unknown* or *unsupported*. 27 broken copies also exist as Lean source,
and Lean rejects each with the expected message.

The LeanForth differential (task 2.2.1) must show, for every row:
LeanForth's answer equals this table; *accepted* only where Lean accepted;
*rejected* only where Lean rejected, with the same error kind; *invalid* only
where Lean rejected. An *unknown* row may change only through a reviewed rule
and an updated table.

## Measured 2026-11-02

`make test-first-checker-differential` (part of `make check`) runs every
row through the code that exists before the declaration check (plan task
2.2.3): `tests/reference/first-checker-terms.lean` prints each case's
declarations from the very terms the Lean file above checks, and
`tests/support/first-checker-driver.fs` builds them in LeanForth's stores
and checks them in input order, with the checked environment
(`src/kernel/environment.fs`: N1, N2, L1–L3, K5), the definition or
theorem probe (`src/kernel/mixed-definition-probe.fs`: S1, S3, D1–D5 for
the declaration) and inference (`src/kernel/mixed-infer.fs`: S2, F1, D1–D5
at applications). Accepted earlier declarations become the probe's
candidate signatures. The run fails unless every row has the table's
outcome, every *rejected* names a rule whose Lean exception is the row's,
and every D rejection's rules include the row's.

| | Lean accepted | Lean rejected | Total |
| --- | ---: | ---: | ---: |
| LeanForth **accepted** | 14 | 0 | 14 |
| LeanForth **rejected** | 0 | 28 | 28 |
| LeanForth **invalid** | 0 | 1 | 1 |
| LeanForth **unknown** | 9 | 1 | 10 |
| LeanForth **unsupported** | 8 | 0 | 8 |
| LeanForth **full** | 1 | 0 | 1 |
| Total | 32 | 30 | 62 |

Every row equals the table but one: `composition.proof-irrelevance` is
*full*, not *unknown*: LeanForth's 64-node term store fills while the
value's type is inferred, before the comparison that would be undecided
(K2). It was *full* before task 2.2.1 too, and neither answer is accepted.
Seven rows (U1, U2) are decided by the driver's stand-in for the
declaration audit, 55 by kernel code. Before task 2.2.1 the same paths
answered *unknown* for the 15 rows of rules D1–D5, F1, S1 and S2, and had
no theorem mode for the four S3 rows.

## composition

For all propositions A, B, C: if A implies B and B implies C, then A implies
C. Lean: `theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C
:= fun value => g (f value)`. (The LeanForth Forth form is not designed yet,
plan task 8.1.1.)

| Case | What changed | Lean 4.35.0 kernel | LeanForth must answer | Rule | Source copy | Measured |
| --- | --- | --- | --- | --- | --- | --- |
| `original` | the pinned fixture | accepted | **accepted** | A1 |  | accepted |
| `wrong-intermediate` | g : C → C, so g receives a B where it needs a C | appTypeMismatch | **rejected** | D3 | yes | rejected (D3) |
| `wrong-argument` | g value: g receives an A where it needs a B | appTypeMismatch | **rejected** | D3 | yes | rejected (D3) |
| `wrong-declared-type` | claims A → B; the proof gives A → C | declTypeMismatch | **rejected** | D4 | yes | rejected (D3+D4) |
| `theorem-over-types` | A B C : Type, so the statement is a type, not a proposition | thmTypeIsNotProp | **rejected** | S3 | yes | rejected (S3) |
| `definition-over-types` | the same term as a definition is fine | accepted | **accepted** | A1 |  | accepted |
| `applies-a-non-function` | value value: value : A is not a function | funExpected | **rejected** | F1 | yes | rejected (F1) |
| `proof-irrelevance` | Q (f a) used as Q (f' a): f a and f' a are both proofs of B, so Lean equates them | accepted | **unknown** | K2 |  | full (term store) |

## identity

Every proposition P implies itself. Lean: `theorem identity {P : Prop}
(proof : P) : P := proof`.

| Case | What changed | Lean 4.35.0 kernel | LeanForth must answer | Rule | Source copy | Measured |
| --- | --- | --- | --- | --- | --- | --- |
| `original` | the pinned fixture | accepted | **accepted** | A1 |  | accepted |
| `wrong-binder` | returns the proof of P where Q is claimed | declTypeMismatch | **rejected** | D4 | yes | rejected (D3+D4) |
| `returns-the-proposition` | returns P itself, whose type is Prop, not P | declTypeMismatch | **rejected** | D2 | yes | rejected (D2+D4) |
| `type-is-not-a-type` | the declared type is a function, not a type | typeExpected | **rejected** | S1 | yes | rejected (S1) |
| `theorem-over-types` | P : Type, so the statement is a type, not a proposition | thmTypeIsNotProp | **rejected** | S3 | yes | rejected (S3) |
| `definition-over-types` | the same term as a definition is fine | accepted | **accepted** | A1 |  | accepted |
| `loose-bound-variable` | the body refers to a binder that does not exist | looseBVar | **invalid** | V1 |  | invalid |
| `unknown-constant` | uses a name that was never declared | unknownConstant | **rejected** | N1 | yes | rejected (N1) |
| `let` | the proof is let copy := proof; copy (a let expression) | accepted | **unsupported** | U2 |  | unsupported (stand-in audit) |
| `binder-annotation-differs` | explicit binder in the proof, implicit in the statement | accepted | **accepted** | A1 |  | accepted |

## type-identity

For any type A, predicate P on A and x in A, a proof of P x proves P x.
Lean: `theorem type_identity {A : Type} {P : A → Prop} {x : A} (proof : P x)
: P x := proof`.

| Case | What changed | Lean 4.35.0 kernel | LeanForth must answer | Rule | Source copy | Measured |
| --- | --- | --- | --- | --- | --- | --- |
| `original` | the pinned fixture | accepted | **accepted** | A1 |  | accepted |
| `wrong-universe` | the proof takes A : Prop where the statement says A : Type | declTypeMismatch | **rejected** | D1 | yes | rejected (D1+D4) |
| `wrong-argument` | claims P y from a proof of P x, with x y : A and A : Type | declTypeMismatch | **rejected** | D5 | yes | rejected (D3+D4+D5) |
| `proof-irrelevance-twin` | the same with A : Prop: x and y are proofs, so Lean equates them | accepted | **unknown** | K2 |  | unknown |
| `eta-twin` | k P versus k (fun y => P y): equal only by eta | accepted | **unknown** | K3 |  | unknown |
| `beta` | claims (fun y => P y) x, which beta-reduces to P x | accepted | **accepted** | A1 |  | accepted |
| `binder-is-not-a-type` | proof : x, but x : A is a value, not a type | typeExpected | **rejected** | S2 | yes | rejected (S2) |
| `applies-a-non-function` | P : A is not a function, so P x is meaningless | funExpected | **rejected** | F1 | yes | rejected (F1) |
| `theorem-over-types` | P : A → Type, so the statement is a type, not a proposition | thmTypeIsNotProp | **rejected** | S3 | yes | rejected (S3) |
| `definition-over-types` | the same term as a definition is fine | accepted | **accepted** | A1 |  | accepted |

The `wrong-argument` and `proof-irrelevance-twin` rows differ only in
whether A is a type of data or a proposition; Lean rejects the first and
accepts the second. They are the test that LeanForth's rejection rule D5
does not overreach.

## poly-identity

The same for a type A in any universe u. Lean: `universe u` then
`theorem poly_identity {A : Sort u} {P : A → Prop} {x : A} (proof : P x) :
P x := proof`.

| Case | What changed | Lean 4.35.0 kernel | LeanForth must answer | Rule | Source copy | Measured |
| --- | --- | --- | --- | --- | --- | --- |
| `original` | the pinned fixture | accepted | **accepted** | A1 |  | accepted |
| `undeclared-universe` | uses universe u without declaring it | undefinedLevelParam | **rejected** | L2 | yes | rejected (L2) |
| `repeated-universe` | declares universe u twice | duplicateLevelParam | **rejected** | L3 | yes | rejected (L3) |
| `wrong-universe` | the proof takes A : Sort (u+1) where the statement says Sort u | declTypeMismatch | **rejected** | D1 | yes | rejected (D1+D4) |
| `swapped-universe` | the proof takes A : Sort v where the statement says Sort u | declTypeMismatch | **rejected** | D1 | yes | rejected (D1+D4) |
| `theorem-over-sort-u` | P : A → Sort u: a proposition only when u = 0, so not for every u | thmTypeIsNotProp | **rejected** | S3 | yes | rejected (S3) |
| `definition-over-sort-u` | the same term as a definition is fine | accepted | **accepted** | A1 |  | accepted |
| `equal-universe-other-spelling` | the proof writes Sort (max u u); Lean's level normalisation equates it with Sort u | accepted | **unknown** | K4 |  | unknown |
| `proof-irrelevance-imax` | P y from a proof of P x, A : Sort (imax u 0), which is Prop for every u: x and y are proofs | accepted | **unknown** | K2 |  | unknown |
| `proof-irrelevance-max-zero` | the same with A : Sort (max 0 0), which is Prop | accepted | **unknown** | K2 |  | unknown |

The last two rows are `type-identity.proof-irrelevance-twin` with `Prop`
spelled so that only Lean's level normalisation (`normalizes_to_zero`)
sees it. They were added after the independent review of task 2.2.1 (its
finding M1, the probes `pi-imaxu0` and `pi-maxzero`): LeanForth may call
x and y apart only when it knows they are not proofs, and a check that
read the level's spelling instead of normalising it would reject these
rows, which Lean accepts. With that fault planted, both rows give
*rejected* (D3+D4+D5) and the differential fails.

## constant fixture

`fixtureId` is the identity function at any universe; `fixturePoly` is
defined through it; `fixtureUse` proves "P implies P" with it. Lean:
`def fixtureId {α : Sort u} (x : α) : α := x`,
`def fixturePoly {α : Sort u} (x : α) : α := fixtureId x`,
`theorem fixtureUse {P : Prop} (h : P) : P := fixtureId h`. *Earlier*
declarations: none for `fixtureId` and `forward-reference`; `fixtureId`
for every other row; also `fixtureUnfold` (the `needs-unfolding` row) for
`uses-an-undecided-declaration`, and `fixtureUse` for
`theorem-cites-theorem` and `over-application`.

| Case | What changed | Lean 4.35.0 kernel | LeanForth must answer | Rule | Source copy | Measured |
| --- | --- | --- | --- | --- | --- | --- |
| `fixtureId` | the pinned polymorphic identity definition | accepted | **accepted** | A1 |  | accepted |
| `fixturePoly` | the pinned definition that uses fixtureId.{u} | accepted | **accepted** | A1 |  | accepted |
| `fixtureUse` | the pinned theorem that uses fixtureId.{0} | accepted | **accepted** | A1 |  | accepted |
| `forward-reference` | fixturePoly checked before fixtureId exists | unknownConstant | **rejected** | N1 | yes | rejected (N1) |
| `self-reference` | fixturePoly uses itself, which a non-recursive definition cannot | unknownConstant | **rejected** | N1 |  | rejected (N1) |
| `duplicate-name` | fixtureId declared a second time | alreadyDeclared | **rejected** | N2 | yes | rejected (N2) |
| `too-few-universes` | fixtureId used with no universe argument; it takes one | levelCount | **rejected** | L1 |  | rejected (L1) |
| `too-many-universes` | fixtureId used with two universe arguments; it takes one | levelCount | **rejected** | L1 | yes | rejected (L1) |
| `wrong-universe-argument` | fixtureId.{1} expects a Type; P is a Prop | appTypeMismatch | **rejected** | D1 | yes | rejected (D1) |
| `wrong-argument` | passes P (a proposition) where a proof of P is needed | appTypeMismatch | **rejected** | D2 | yes | rejected (D2) |
| `needs-unfolding` | claims fixtureId Prop P from a proof of P: true by unfolding fixtureId | accepted | **unknown** | K1 |  | unknown |
| `needs-unfolding-wrong` | claims fixtureId Prop Q from a proof of P: false, but only unfolding shows it | declTypeMismatch | **unknown** | K1 | yes | unknown |
| `uses-an-undecided-declaration` | cites fixtureUnfold, which LeanForth could not decide | accepted | **unknown** | K5 |  | unknown |
| `theorem-cites-theorem` | a theorem whose proof cites the earlier theorem fixtureUse | accepted | **accepted** | A1 |  | accepted |
| `over-application` | fixtureUse h is a proof of P, not a function, but is applied to h | funExpected | **rejected** | F1 | yes | rejected (F1) |
| `function-type-behind-definition` | f's type is fixtureId Prop (P → P); it is a function type only after unfolding | accepted | **unknown** | K1 |  | unknown |
| `sort-behind-definition` | Q : fixtureId Type Prop; Q is a proposition only after unfolding | accepted | **unknown** | K1 |  | unknown |

`needs-unfolding-wrong` is the one row where Lean rejects and LeanForth must
still say *unknown*: the claim is false, but seeing that requires unfolding
`fixtureId`, which the first checker does not do (owner decision 3).

## scope

Declarations Lean accepts but the first checker must not: features planned
for phases 4 and 5, and a statement assumed without proof (an axiom; the
first checker's allowlist is empty, owner decision 4). *Earlier*: the
assumed statement, for `uses-postulate`.

| Case | What changed | Lean 4.35.0 kernel | LeanForth must answer | Rule | Source copy | Measured |
| --- | --- | --- | --- | --- | --- | --- |
| `metadata` | a metadata node in the proof | accepted | **unsupported** | U2 |  | unsupported (stand-in audit) |
| `number-literal` | the number 3, a literal of the data type Nat | accepted | **unsupported** | U2 |  | unsupported (stand-in audit) |
| `postulate` | a statement assumed without proof; the allowlist is empty | accepted | **unsupported** | U1 |  | unsupported (stand-in audit) |
| `uses-postulate` | a proof that cites the assumed statement | accepted | **unsupported** | K5 |  | unsupported |
| `opaque` | an opaque declaration (never unfolds) | accepted | **unsupported** | U1 |  | unsupported (stand-in audit) |
| `unsafe-definition` | a definition marked unsafe | accepted | **unsupported** | U1 |  | unsupported (stand-in audit) |
| `partial-definition` | a definition marked partial | accepted | **unsupported** | U1 |  | unsupported (stand-in audit) |

## Cases with no Lean counterpart

These belong to the failure-path suite (plan task 2.2.4) and are tested in
LeanForth only, because Lean has no matching input or limit.

| Case | LeanForth must answer |
| --- | --- |
| A malformed or truncated NDJSON record, an out-of-range reference, a cycle | **invalid** |
| The processing budget (fuel) runs out during a check | **exhausted** |
| A store, stack or depth limit is reached | **full** |
| A stale or cross-snapshot handle is used | **invalid** |
| The k-th allocation fails, for every k (task 1.4.6) | **exhausted** or **full** |
| After any outcome other than *accepted* | nothing published; the environment unchanged |
| The same input checked twice | byte-identical verdicts (task 2.2.5) |

## Broken copies as Lean source

`tests/reference/first-checker-invalid.lean` holds the 27 rows marked "yes",
one declaration per line, each ending in `-- expect <case>: <message>`.
`first-checker-check.sh` requires Lean to reject the file, to report each
marked line with its message ("Lean rejected this, as expected") and to
report no error on any other line. Some kernel rows cannot be written as
source: a variable without a binder, a non-recursive self-reference (Lean
compiles recursion away), a constant with too few universe arguments, and
the out-of-scope rows.

## Reproduction

```sh
LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
  bash tests/reference/first-checker-check.sh
```

Run on 2026-11-02 with Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`);
it took about two seconds and printed "Lean kernel verdicts match
first-checker-expected.tsv (60 cases)" and "Lean rejected all 27 broken
source copies, each for the expected reason". The script is part of `make
check`, as `make reference-first-checker`. Run again on 2026-11-02 after
the two `proof-irrelevance-imax` and `-max-zero` rows were added: "(62
cases)", and the same 27 source copies. SHA-256 at that run:
`first-checker-expected.lean`
`4d0d4f5e3ed70d786e93fc5334170e8d055e733f8268b5b58d8dd6bd93e84c5d`,
`first-checker-expected.tsv`
`b2a299e13151f1ef2847845471e7038874afa55a090961b36cf3073793473031`,
`first-checker-invalid.lean`
`62f94c7cbd31548fbb6b90808d54da9b88b6c1197701cfa44f583bf472d6ec9e`
(unchanged).

The measured column:

```sh
make test-first-checker-differential
```

Run on 2026-11-02 with Lean 4.35.0 and Gforth 1.0.0, in about two
seconds, with the 62 rows: "first checker: 14 accepted, 1 full, 1
invalid, 28 rejected, 10 unknown, 8 unsupported; 55 decided by kernel
code, 7 by the stand-in audit (U1, U2); known differences:
composition.proof-irrelevance". The two files
it adds have SHA-256 `first-checker-terms.lean`
`98df70061b4bca7f93a4c9c4bc55acae242e57691c9aff7e840a02e7bc1f1c96` and
`first-checker-driver.fs`
`7b2746b10e171ba51e7180e9db64c92e10acb729f649598def1690131943a821`.
