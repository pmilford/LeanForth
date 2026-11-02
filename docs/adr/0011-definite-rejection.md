# ADR 0011: definite rejection and the first checker's scope

Status: **proposed**, 2026-11-02 (plan task 2.1.1). A checker rule: it must
pass the review gate in `AGENTS.md` — rules that follow Lean's published
kernel, agreeing pinned-Lean differential tests that reach every outcome, an
independent AI review with no unresolved findings, and the owner's approval
of the plain-language summary in
[the gate draft](../reviews/FIRST_CHECKER_GATE.md). Nothing here is
implemented. It refines ADRs 0002, 0003, 0006 and 0008 for the first checker
and supersedes none of them. The plan reserves ADR 0012 for the
checked-environment implementation (task 2.1.3), so the first checker's scope
is decided here rather than in a separate record.

## Summary in plain words

LeanForth's first checker will answer *accepted*, *rejected* or
*unsupported/unknown* for each definition or theorem. *Rejected* is a claim
about Lean: it may be answered only where Lean 4.35.0's own kernel would
certainly reject the same declaration, and this record lists exactly those
situations, each traced to the Lean source that makes it certain. Lean can
also treat two different-looking expressions as equal by unfolding a
definition, by treating any two proofs of the same statement as equal, by
"eta" (a function `f` equals `fun x => f x`) or by simplifying universe
levels. The first checker does none of these, so wherever one of them could
apply it must answer *unknown*, even when the declaration is in fact wrong.
The expected answers for the five pinned fixtures and 53 broken or
out-of-scope variants are in
[the expected-results table](../reviews/FIRST_CHECKER_EXPECTED.md); Lean's
verdict on every one of them was checked with the pinned Lean binary.

## Problem

Owner decision 2 requires three outcomes and tests that reach each of them.
Today the experiments in `src/kernel/` never reject: a definitely wrong value
returns *unknown* (coverage finding cov-T11; ADR 0008 step 3). Adding
*rejected* is dangerous in one direction: Lean's definitional equality
equates terms that a structural comparison calls different, so "my cautious
comparison failed" must never be reported as "Lean says this is wrong". The
plan names the risky cases — anything unfolding, eta or proof irrelevance
might equate — and asks for a rule list with Lean citations.

## The referee

- **Lean 4.35.0**, tag `v4.35.0`, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (the `lean --githash` of the
  pinned toolchain; `git ls-remote` shows the tag at that commit). The
  installed toolchain has no C++ kernel source (ADR 0006), so the files were
  read from `raw.githubusercontent.com/leanprover/lean4/v4.35.0/` on
  2026-11-02: `src/kernel/type_checker.cpp`, `type_checker.h`,
  `environment.cpp`, `declaration.h`, `declaration.cpp`, `level.cpp`,
  `inductive.h`, `quot.h` and `kernel_exception.h`, and
  `src/Lean/Environment.lean` and `Declaration.lean` (these two match the
  hashes ADR 0006 records). Their SHA-256 hashes are under
  *Reproduction*; line numbers below refer to these files.
- **Lean's verdict** on a declaration is the result of
  `Kernel.Environment.addDeclCore` (C++ `lean_add_decl` →
  `environment::add`, `environment.cpp` 271–295) adding it, with checking,
  to an environment that holds exactly the earlier declarations of the same
  input that Lean accepted. The result is *accepted* or one value of
  `Kernel.Exception` (`Lean/Environment.lean` 260–277): `unknownConstant`,
  `alreadyDeclared`, `declTypeMismatch`, `funExpected`, `typeExpected`,
  `appTypeMismatch`, `thmTypeIsNotProp`, `other` with a message, and others
  outside this fragment. The kernel stops at the first exception. The test
  oracle starts from the environment of a Lean file that imports `Lean`,
  not from an empty one; apart from `Nat` in the `number-literal` row, no
  test declaration uses anything from it, so the verdicts are the same.

## Scope of the first checker

**Declarations.** Theorems, and definitions whose safety is `safe` (any
reducibility hint), each a block of one (`all` is the declaration's own
name), with distinct universe-parameter names. Every other kind is
*unsupported* (rule U1): axioms (the allowlist is empty, owner decision 4),
opaque declarations, quotients, inductive types with their constructors and
recursors, mutual blocks, and `unsafe` or `partial` definitions.

**Terms.** `Sort` with levels built from `zero`, `succ`, `max`, `imax` and
declared parameters; bound variables (de Bruijn indices); application; `λ`
and `Π` with any binder name and annotation (both ignored, as Lean ignores
them); constants with universe arguments that name declarations accepted
earlier in the same run. *Unsupported* (rule U2): `let`, number and string
literals, projections and metadata nodes. Free variables, metavariables and
level metavariables cannot appear in an export and are *invalid* input.

**Environment.** It starts empty and grows only by declarations this run
accepted (ADR 0006; its implementation is ADR 0012). It therefore never
contains an inductive type, constructor, recursor, quotient or literal — the
fact the rules below rely on.

**Outcomes** use ADR 0008's vocabulary. For the owner, *accepted* is ok;
*rejected* is rejected; *unsupported/unknown* is unsupported or unknown;
*invalid* (malformed input), *exhausted* (out of fuel) and *full* (a store or
depth limit) are reported separately. None of them is ever accepted, stored
as accepted or cached as success.

**Accepted results** print *accepted — experimental, not independently
audited; axioms: none*. The axiom set of a declaration is the union of the
sets of the declarations it uses, computed and printed even though it is
always empty in this scope (no axiom can be accepted, rule U1, and nothing
that depends on one can be, rule K5).

## Facts from Lean's kernel that the rules use

1. **Lean checks in a fixed order and stops at the first failure.**
   `add_theorem` (`environment.cpp` 192–209): name not already declared
   (`check_name` 102–105), universe parameters distinct
   (`check_duplicated_univ_params` 111–121), the type is checked and must
   reduce to a `Sort` (`check_constant_val` 127–133), the type must be a
   proposition (`is_prop`, 201–202), the value is checked, and its type must
   be definitionally equal to the declared type (205–206).
   `add_definition` (160–190) is the same without the proposition test.
   Inside a term, `infer_type_core` (`type_checker.cpp` 325–358) visits a
   `λ` or `Π` telescope domain by domain (`infer_lambda` 125–142,
   `infer_pi` 144–166) and an application function first, then argument,
   then the comparison (`infer_app` 173–206).
2. **Only constants unfold, and theorems unfold too.** `whnf` (706–743)
   unfolds only through `unfold_definition` (589–602), which needs a
   constant at the head (`is_delta` 555–563). `is_delta` accepts any constant
   whose `constant_info::has_value()` holds, and `has_value` is true for
   theorems as well as definitions (`declaration.h` 466–468); theorems carry
   `opaque` hints, which only make them unfold last
   (`constant_info::get_hints`, `declaration.cpp` 294–299). ADR 0006 and
   the checked-environment review packet propose that theorems never
   unfold, and plan task 4.1.1 describes Lean's procedure that way; Lean
   4.35.0's kernel differs. Not unfolding theorems is cautious for
   acceptance and changes nothing in this record's scope (nothing unfolds),
   but a rule that treated a theorem at the head of a term as fixed could
   reject what Lean accepts. Phase 4 must decide with this fact in view.
3. **For a term whose head is not a constant, `whnf` is beta reduction.** In
   this scope `whnf_core` (468–551) only beta-reduces: `let` and projections
   are unsupported, there are no `let` variables, and recursor and quotient
   reduction need a recursor or `Quot` constant at the head
   (`inductive_reduce_rec` in `inductive.h` 77–83, `quot_reduce_rec` in
   `quot.h` 39–42). `reduce_nat` (672–703) needs a `Nat` constant at the
   head and `unfold_definition` a constant. So when the head of the
   beta-reduced term is a `Sort`, `Π`, `λ` or bound variable, Lean's `whnf`
   returns exactly LeanForth's weak-head beta normal form (ADR 0003, step 1).
4. **Without data types, Lean's equality test has exactly three ways past
   structure and beta:** unfolding constants (`lazy_delta_reduction`
   1055–1075), proof irrelevance (`is_def_eq_proof_irrel` 899–906: any two
   terms whose type is a proposition are equal when their types are) and eta
   (`try_eta_expansion`, `type_checker.h` 94–96, core 841–853: a `λ` against
   a non-`λ`). The remaining routes of `is_def_eq_core` (1132–1207) need an
   inductive declaration in the environment — a constructor
   (`try_eta_struct_core` 856–872) or a structure (`is_def_eq_unit_like`
   1120–1130), which rule U1 keeps out — a literal (1104–1117,
   `is_def_eq_offset` 1043–1052), which rule U2 keeps out, or one of the
   constants `Nat.zero`, `Nat.succ`, a `Nat` operation (`reduce_nat`) or
   `Bool.true` (1142–1146) at the head of a compared term, which
   precondition P1 below excludes, as it excludes every constant head.
   These routes are matched by name, so a user declaration with such a name
   would trigger them; P1 makes that harmless here.
5. **Two `Sort`s, two `Π`s and two `λ`s are decided at once.**
   `quick_is_def_eq` (802–826) compares two `Sort`s by level equivalence and
   two binders by `is_def_eq_binding` (752–779), and `is_def_eq_core`
   returns that answer immediately (1135–1136) — no unfolding, proof
   irrelevance or eta is tried for the pair itself.
6. **The proposition test is exact.** `is_prop` (383–389) asks whether the
   level of the type's sort satisfies `normalizes_to_zero` (`level.cpp`
   174–187): true for `zero`, false for `succ` and parameters, both sides
   for `max`, the right side for `imax`. That is precisely "zero under every
   assignment of the parameters", since `imax a b` is zero exactly when `b`
   is. LeanForth can compute it exactly.
7. **Different values prove different levels.** Level equality is
   `is_equivalent` (`level.cpp` 518–521): structurally equal, or equal after
   `normalize` (454–516). Every step of `normalize` (`mk_max` 81–104,
   `mk_imax` 112–123, sorting and the subsumption of explicit levels)
   preserves a level's value under every assignment. So if one assignment
   gives two levels different values, Lean's `is_equivalent` is false.
   Lean also equates some levels that are not structurally identical
   (`max u u` and `u`), so where neither structure, concrete values nor a
   witness decides, LeanForth answers *unknown* (rule K4).

## Decision (proposed)

### Order

LeanForth first audits the whole declaration — representation, closedness
and supported forms (rules V1, U1, U2) — before any typing. It then checks in
Lean's order (fact 1): name, universe parameters, the declared type and its
sort, the proposition test for a theorem, the value, and the final
comparison; inside terms, binder domains left to right, then bodies;
functions before arguments; for a constant, the lookup, then the number of
universe arguments, then the parameters those arguments use. The first step
that does not succeed ends the check and decides the outcome. Every step LeanForth calls a success is a
success for Lean as well, so a *rejected* outcome names the same failing
step and the same kernel exception as Lean. Audit failures (invalid,
unsupported) may be found before a failure Lean would report first; both
are failures, and neither claims Lean's reason.

### Terms the rules talk about

- `whnfβ(t)`: the weak-head beta normal form of ADR 0003, step 1.
- *Rigid*: `whnfβ(t)` has a `Sort`, `Π`, `λ` or bound variable at its head;
  *flexible*: a constant (definition or theorem) at its head.
- *Known not to be a proof*: LeanForth infers `t`'s type `T` and `T`'s type,
  and the latter's `whnfβ` is `Sort l` where `l` fails `normalizes_to_zero`
  (it is nonzero for some assignment), so Lean's `is_prop(T)` is false
  (fact 6). Every type qualifies, since a `Sort` has type `Sort (l+1)`.
- *Equal*: ADR 0003's cautious comparison — structural after beta, binder
  names and annotations ignored, binder domains identical, levels identical
  or both concrete with the same value, constants with the same name and
  equal levels. Every *equal* answer is also equal for Lean
  (`quick_is_def_eq`, `is_def_eq_binding`, `is_def_eq_app`, and the
  constant and variable cases at 1170–1175).
- *Witness assignments* for levels: all parameters 0; and, for each
  parameter, that parameter 1 and all others 0.

### Rejection rules (LeanForth answers *rejected*)

| Rule | When | Lean source | Lean's exception |
| --- | --- | --- | --- |
| N1 | A constant names no accepted declaration and no earlier declaration of the input whose check was undecided (rule K5). Covers unknown, forward and self references. | `infer_constant` 101–102 → `environment::get` (`environment.cpp` 78–85) | `unknownConstant` |
| N2 | The declaration's name is the name of an accepted declaration. | `check_name` (`environment.cpp` 102–105) via `check_constant_val` 128 | `alreadyDeclared` |
| L1 | A constant gets a different number of universe arguments than it has parameters. | `infer_constant` 103–108 | `other`: "incorrect number of universe levels parameters" |
| L2 | A `Sort` or constant uses a universe parameter the declaration does not declare. | `check_level` 85–91 from `infer_type_core` 345–347 and `infer_constant` 118–120; `get_undef_param` (`level.cpp` 289–298) | `other`: "invalid reference to undefined universe level parameter" |
| L3 | The declaration lists a universe parameter twice. | `check_duplicated_univ_params` (`environment.cpp` 111–121) | `other`: "duplicate universe level parameter" |
| S1 | The declared type's type, after `whnfβ`, is rigid and not a `Sort`. | `check_constant_val` 131–132 → `ensure_sort_core` 62–71; fact 3 | `typeExpected` |
| S2 | A binder domain's type, after `whnfβ`, is rigid and not a `Sort`. | `infer_lambda` 131–133, `infer_pi` 151 → `ensure_sort_core` | `typeExpected` |
| S3 | A theorem's type has sort `Sort l` (syntactically, after S1) where `l` fails `normalizes_to_zero`, i.e. is nonzero for some assignment. Exact both ways (fact 6). | `add_theorem` 201–202 → `is_prop` 383–389 → `normalizes_to_zero` | `thmTypeIsNotProp` |
| F1 | A function's type, after `whnfβ`, is rigid and not a `Π`. | `infer_app` 175 → `ensure_pi_core` 74–83; fact 3 | `funExpected` |
| D1–D5 | An argument's type and the expected domain (application), or the value's type and the declared type (declaration), are *apart* (below). | `infer_app` 181–186; `add_theorem` 205–206, `add_definition` 185–186 | `appTypeMismatch` or `declTypeMismatch` |

**Apart** (Lean's `is_def_eq` is certainly false). Let `t' = whnfβ(t)` and
`s' = whnfβ(s)`.

- **D1** — both are `Sort`s and some witness assignment gives their levels
  different values (facts 5 and 7).

Otherwise the pair must satisfy three preconditions — **P1** both rigid (no
unfolding, fact 2); **P2** both known not to be proofs (no proof
irrelevance); **P3** not exactly one of them a `λ` (no eta) — and one of:

- **D2** — they have different shapes among `Sort`, `Π` and a bound variable
  with or without arguments (`x a₁ … aₙ`). With P1–P3 every route of
  `is_def_eq_core` fails (facts 3–5): `quick_is_def_eq` gives no answer for
  different kinds, `lazy_delta_reduction` finds nothing to unfold, the
  constant, variable and application cases do not match, and eta,
  structure eta and unit-like need a `λ`, a constructor or a structure.
- **D3** — both are bound-variable applications, with different head
  variables (each head known not to be a proof) or with different numbers of
  arguments: `is_def_eq_app` (878–895) needs equal heads and equal counts.
- **D4** — both are `Π`s, or both `λ`s: walking the two binder telescopes
  together as `is_def_eq_binding` does, the first pair of domains that are
  not identical is apart, or all domains are identical and the remaining
  bodies are apart. A domain pair that is neither identical nor apart makes
  the result *unknown*. Bodies are entered only under identical domains, the
  case ADR 0003 already allows, so this adds no new context-conversion
  obligation (plan task 2.1.2 is unaffected).
- **D5** — both apply the same head variable to the same number of
  arguments, and some argument pair is apart (recursively, with P1–P3 for
  that pair): `is_def_eq_app` then fails, and fact 4 leaves no other route.

In the fixtures, D1 catches wrong universes, D2 a proposition passed where a
proof is needed, D3 a wrong variable (`B` where `C` is needed), D4 a wrong
result type, and D5 `P y` claimed from `P x`.

### Invalid input (*invalid*)

- **V1** — a bound variable that no binder covers, a free variable or
  metavariable, a level metavariable, or any other malformed record. Lean's
  kernel rejects the first case ("type checker does not support loose bound
  variables", `infer_type_core` 326–327) and the second
  (`check_no_metavar_no_fvar`, `environment.cpp` 87–100); the export format
  cannot express them. LeanForth finds them in its audit.

### Must stay unknown (*unknown*)

- **K1 unfolding** — a flexible term where LeanForth needs a `Sort` (S1,
  S2, S3), a `Π` (F1) or a comparison (P1). Lean may unfold it (fact 2).
- **K2 proof irrelevance** — a compared pair in which either side is not
  known not to be a proof.
- **K3 eta** — a `λ` compared with a non-`λ`.
- **K4 levels** — two levels that are not identical, not both concrete and
  equal, and have no witness (fact 7).
- **K5 undecided dependency** — a constant naming an earlier declaration of
  the input whose check ended *unknown*, *exhausted*, *full* or *invalid*;
  the dependent ends *unknown*, or *unsupported* if the dependency was
  *unsupported*. Lean may have accepted the dependency. A dependency that
  ended *rejected* is absent for Lean too, so its use is N1. The same
  applies to N2: reusing the name of an undecided declaration is *unknown*,
  of a rejected one is no conflict.
- **Everything else** that is neither accepted nor covered by a rule above.

The table pins pairs that differ only in what Lean's extra rules can see:
`type-identity.wrong-argument` (rejected, D5) against
`proof-irrelevance-twin` (Lean accepts, unknown, K2); `constant.needs-unfolding`
(Lean accepts) and `needs-unfolding-wrong` (Lean rejects), both unknown (K1).

### Unsupported (*unsupported*)

- **U1** — declaration kinds outside the scope above.
- **U2** — term forms outside the scope above.

Lean accepts every unsupported case in the table; *unsupported* says only
that LeanForth has not built the feature.

### Acceptance (*accepted*)

- **A1** — every step succeeded, each comparison by *equal*, and every
  constant named an accepted declaration with the right number of universe
  arguments. Publication follows ADR 0006 (ADR 0012 to come); a failed check
  publishes nothing.

Running out of fuel gives *exhausted* and a full store or depth limit gives
*full* at whatever step it happens. Lean's own limits
(`deterministicTimeout`, `deepRecursion`, `excessiveMemory`) are not
comparable and are not part of the differential.

## Evidence

Run on 2026-11-02 with `.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`
(Lean 4.35.0, `eb6cafb7…`):

- `tests/reference/first-checker-expected.lean` builds 60 kernel
  declarations — the five fixtures' seven declarations and 53 variants — and
  adds each with `addDeclCore` to a scratch environment. It first checks that
  its hand-built originals equal the terms Lean elaborates from the fixture
  sources (up to binder names and annotations, which the kernel ignores), so
  they match the pinned exports. Lean gave
  the recorded verdict in all 60: 30 accepted, 30 rejected (every exception
  kind above appears). The expected LeanForth outcomes are 14 accepted,
  28 rejected, 1 invalid, 9 unknown and 8 unsupported; each of the five
  fixtures reaches accepted, a failure and unknown or unsupported. Every
  *rejected* row has the Lean exception its rule names, and no *accepted*
  row is rejected by Lean.
- `tests/reference/first-checker-invalid.lean` writes 27 of the broken
  copies as Lean source; Lean rejects each on its marked line with the
  expected front-end message and reports nothing else.
- `tests/reference/first-checker-check.sh` runs both and compares the
  kernel rows with `first-checker-expected.tsv` byte for byte. Planted
  faults in a scratch copy — a changed expected verdict, a hand-built
  original that differs from the fixture, a changed table row, an unmarked
  error, a wrong message and a broken copy made valid — each made it fail.

This is evidence about Lean, not about LeanForth: no LeanForth code returns
*rejected* yet. The LeanForth differential against this table is plan task
2.2.1. It must check that accepted, rejected and invalid rows agree with the
table and Lean, that every *rejected* carries the row's exception kind, and
that no *unknown* row becomes *rejected* without a rule.

## Consequences

- ADR 0008 step 3 gets its rule list. ADR 0003's "unknown is never
  inequality" stays true; this record adds the cases where inequality is
  certain.
- The first checker needs two small exact computations it lacks today:
  `normalizes_to_zero` (S3) and evaluation of levels under the witness
  assignments (D1), and a "known not to be a proof" test built on its own
  inference (P2).
- The rules assume LeanForth's inferred types agree with Lean's `infer_type`
  up to beta reduction on this fragment; the mixed-inference differential
  and task 2.2.1 test that assumption.
- Phase 4 (unfolding, ADR 0014 in the plan) must revisit P1 and K1, and
  decide theorem unfolding knowing that Lean's kernel does it (fact 2).

## Open questions for the gate

1. Statements assumed without proof are *unsupported* here (Lean accepts
   them; LeanForth's allowlist is empty). The alternative is *rejected* by
   policy, which would make *rejected* no longer mean "Lean rejects".
2. D5 looks inside arguments and depends on the proof test P2; it could be
   deferred, leaving `P y` from `P x` *unknown*.
3. Whether to widen the witness assignments (D1) now or wait for Lean's
   level normalisation (plan task 4.1.2).

## Rejected alternatives

- **Any failed comparison is *rejected*.** Calls valid proofs wrong whenever
  unfolding, proof irrelevance, eta or level normalisation is needed (the
  K rows of the table).
- **Never reject.** Simplest and safe against false acceptance, but the owner
  asked for the failure paths, and users need to tell "wrong" from "not yet
  decidable".
- **Reject on a cautious-unequal comparison unless a constant is present.**
  Misses proof irrelevance and eta, which need no constant
  (`proof-irrelevance-twin`, `eta-twin`).
- **Port Lean's `normalize` now.** Exact level equality is plan task 4.1.2;
  witnesses are sound, small and enough for the fixtures.
- **Report axioms as *rejected* by policy.** See open question 1.
- **A separate scope ADR 0012.** The plan already gives 0012 to the
  checked-environment implementation.

## Reproduction

```sh
LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
  bash tests/reference/first-checker-check.sh
git ls-remote https://github.com/leanprover/lean4 refs/tags/v4.35.0
curl -sSfLO https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/kernel/type_checker.cpp
```

Full SHA-256 of the Lean files read: `src/kernel/type_checker.cpp`
`26eae5ebb88f6f7da2c0a91f470aae4b74d370569dc5ca81b44b2d5c24c8df4e`,
`src/kernel/type_checker.h`
`251e5910586972445d0ebd317a056e27d8f124515f19ae7865560526fa7935b0`,
`src/kernel/environment.cpp`
`0930ff37576a02240dcc16a2089d3280dcc58898ccbc772b620be031089c30b2`,
`src/kernel/declaration.cpp`
`1d4751c0a2a1e0663cc08dfb00941164c7fb61b16f885c2722cf24422b2ca454`,
`src/kernel/level.cpp`
`7cb927c6fabd9fb843f548443494d3673a08074e26fe32b679e80f4664fc7f25`,
`src/kernel/kernel_exception.h`
`58facd4e272a08b5b646fe1af1d26c60a9fad3185928326fa53479068dd1e24c`,
`src/Lean/Environment.lean`
`6c90105aecc4d28efe94cc9aef1704c284e7a748b28270b5f8513d2562331e43`,
`src/Lean/Declaration.lean`
`1cf2f06d848086f165b3df0afe494924ae26aaea248d5e0135d5efc2d588948f`,
`src/kernel/declaration.h`
`eb9c497bb19dab26550cbb5196a13e0a925896c6d357a8faa2f3794c1e798a51`,
`src/kernel/inductive.h`
`61bd41532dc7bd3c0632130c3bf718975094be36740cd1189f1885e6656d398a`,
`src/kernel/quot.h`
`17105c835e79ccb397194e9663dba71b5515edbc89c9698b0d58a95dc30a8243`.
