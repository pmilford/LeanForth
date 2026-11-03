# First checker: expected results

**Status: reference table for the first checker (plan tasks 2.1.4, 2.2.1
and 2.2.3); Lean's column was checked on 2026-11-02; "LeanForth must
answer" is the requirement, and "Measured" is what the first checker
answers end to end today** (2026-11-02, plan task 2.2.3: check-declaration
through the checked environment; [kernel] code not yet through its review
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
- **Measured** — the first checker's answer (check-declaration, plan task
  2.2.3, through the checked environment), with the rule its diagnostic
  names: for D rules, every D rule used from the compared pair down to the
  pair that decided (`D3+D4`: the claim and the proof's type are Πs, D4,
  whose bodies are different variables, D3). An *unknown* row names its
  rule only when the diagnostic does (K5); K1–K4 leave the record of the
  undecided step. Every *accepted* row prints *accepted (experimental, not
  independently audited); axioms: none*.

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
| LeanForth **unknown** | 8 | 1 | 9 |
| LeanForth **unsupported** | 8 | 0 | 8 |
| Total | 30 | 30 | 60 |

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
row end to end through the first checker (plan task 2.2.3):
`tests/reference/first-checker-terms.lean` prints each case's declarations
from the very terms the Lean file above checks;
`tests/support/first-checker-driver.fs` builds them in LeanForth's stores
(an unsupported form as its own leaf, `src/core/unsupported-forms.fs`) and
checks them in input order with check-declaration
(`src/kernel/check-declaration.fs`) through the checked environment's
serial publisher (`src/kernel/env-publish.fs`). check-declaration audits
the declaration (U1, U2, V1), then checks its name (N2) and universe
parameters (L3), infers the declared type in environment mode (constants
looked up in the environment in Lean's order: N1, K5, L1, L2,
`src/kernel/env-signature.fs`; S2, F1 and D1–D5 inside inference), its
Sort (S1), the proposition test of a theorem (S3), the value's type, and
the final comparison (D1–D5). The run fails unless every row has the
table's outcome, every *rejected* names a rule whose Lean exception is the
row's and ends at a step where that rule acts in Lean's order, every D
rejection's rules include the row's, every *accepted* row prints *accepted
(experimental, not independently audited); axioms: none* and gets a valid
handle, and no other slot gives a handle.

| | Lean accepted | Lean rejected | Total |
| --- | ---: | ---: | ---: |
| LeanForth **accepted** | 14 | 0 | 14 |
| LeanForth **rejected** | 0 | 28 | 28 |
| LeanForth **invalid** | 0 | 1 | 1 |
| LeanForth **unknown** | 8 | 1 | 9 |
| LeanForth **unsupported** | 8 | 0 | 8 |
| Total | 30 | 30 | 60 |

Every row equals the table. `composition.proof-irrelevance`, *full* before
task 2.2.3 (LeanForth's 64-node term store filled while the value's type
was inferred), is now *unknown* (K2) as the table requires: check-declaration
discards the declared type's scratch before it infers the value, so the
value's inference has the room. Eight rows (U1, U2, V1) are decided by the
declaration audit, 52 by typing in Lean's order. Before task 2.2.1 the same
paths answered *unknown* for the 15 rows of rules D1–D5, F1, S1 and S2, and
had no theorem mode for the four S3 rows.

Two more tables run the same way. The binder-domain table of
[ADR 0003, Amendment 1](../adr/0003-conversion.md) (`make
test-binder-domains-differential`): its 12 declarations, and its 10
comparisons, each as a theorem whose check makes exactly that comparison
(`tests/reference/binder-domains-terms.lean`, which checks Lean's verdict
on each): 8 accepted, 6 rejected, 7 unknown, 1 full. 19 rows equal the
amended column; three meet the 64-node term store (ADR 0016 is to lift it)
and answer a failure instead: `compare.lambda-beta-domain-different-body`
and `decl.lambda-in-argument-wrong-body` stay *unknown* where the table says
*rejected* (the rejection analysis runs out of room), and
`compare.eta-under-beta-domain` is *full* where it says *unknown*. With
`lf-term-capacity` 160 in a scratch copy all 22 equal the table (measured
2026-11-02). The universe-scope rows of ADR 0012's test matrix, row 4
(`tests/reference/universe-scope-terms.lean`, `make
test-universe-scope-differential`): 17 cases, every one as expected —
6 accepted, 10 rejected (L1, L2, L3, D1), 1 unknown (K4).

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
| `proof-irrelevance` | Q (f a) used as Q (f' a): f a and f' a are both proofs of B, so Lean equates them | accepted | **unknown** | K2 |  | unknown |

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
| `loose-bound-variable` | the body refers to a binder that does not exist | looseBVar | **invalid** | V1 |  | invalid (V1) |
| `unknown-constant` | uses a name that was never declared | unknownConstant | **rejected** | N1 | yes | rejected (N1) |
| `let` | the proof is let copy := proof; copy (a let expression) | accepted | **unsupported** | U2 |  | unsupported (U2) |
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
| `uses-an-undecided-declaration` | cites fixtureUnfold, which LeanForth could not decide | accepted | **unknown** | K5 |  | unknown (K5) |
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
| `metadata` | a metadata node in the proof | accepted | **unsupported** | U2 |  | unsupported (U2) |
| `number-literal` | the number 3, a literal of the data type Nat | accepted | **unsupported** | U2 |  | unsupported (U2) |
| `postulate` | a statement assumed without proof; the allowlist is empty | accepted | **unsupported** | U1 |  | unsupported (U1) |
| `uses-postulate` | a proof that cites the assumed statement | accepted | **unsupported** | K5 |  | unsupported (K5) |
| `opaque` | an opaque declaration (never unfolds) | accepted | **unsupported** | U1 |  | unsupported (U1) |
| `unsafe-definition` | a definition marked unsafe | accepted | **unsupported** | U1 |  | unsupported (U1) |
| `partial-definition` | a definition marked partial | accepted | **unsupported** | U1 |  | unsupported (U1) |

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
source copies, each for the expected reason". The script is not yet part of
`make check`. SHA-256 at that run: `first-checker-expected.lean`
`7a861ced6724395c3d1151d4df851c6ab33fdcb2558760e52d1b1df6ebe171e3`,
`first-checker-expected.tsv`
`ae154a1ac50a887eb2a13f810ec4b59f94ba11922b0b59d5057545c6a1a0263a`,
`first-checker-invalid.lean`
`62f94c7cbd31548fbb6b90808d54da9b88b6c1197701cfa44f583bf472d6ec9e`.
(It is part of `make check` now, as `make reference-first-checker`.)

The measured column:

```sh
make test-first-checker-differential
make test-binder-domains-differential
make test-universe-scope-differential
```

Run on 2026-11-02 (plan task 2.2.3) with Lean 4.35.0 and Gforth 1.0.0 and
again with Gforth 0.7.3, each in well under a minute: "first checker: 14
accepted, 1 invalid, 28 rejected, 9 unknown, 8 unsupported; 8 decided by
the declaration audit; known differences: none"; "binder domains: 8
accepted, 1 full, 6 rejected, 7 unknown; …; known differences:
compare.lambda-beta-domain-different-body, compare.eta-under-beta-domain,
decl.lambda-in-argument-wrong-body"; "universe scope: 6 accepted, 10
rejected, 1 unknown; …; known differences: none". SHA-256 at that run:
`first-checker-terms.lean`
`98df70061b4bca7f93a4c9c4bc55acae242e57691c9aff7e840a02e7bc1f1c96`,
`first-checker-driver.fs`
`6c27472085bed6876a78acb4464a24de9dfe14e4669027d830516608a9f823ce`,
`binder-domains-terms.lean`
`4d3e7650860f8cf51ee94da61161ae21b4e5c8574090fb550fc604c788fb6f0c`,
`universe-scope-terms.lean`
`07e68cd94788ec9df270ae88f0cdbe78b12505d7fd6cc0a10258d822aeb54c75`,
`src/kernel/check-declaration.fs`
`0673fd437379360509926b96ade88f0271c34e0cac0255af6f370beae2cead90`,
`src/kernel/env-signature.fs`
`d4b560d37dd93360a475bda8b666dde21fd1198aac6171411d0d65628f359427`.
(Before task 2.2.3, with a test stand-in for the audit: "14 accepted, 1
full, 1 invalid, 28 rejected, 8 unknown, 8 unsupported".)
