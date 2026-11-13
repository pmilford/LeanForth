# ADR 0011: definite rejection and the first checker's scope

Status: **rules D1–D5 and K1 retired** by plan task 4.2.2d (2026-11-04, [ADR 0014](0014-definitional-equality.md#progress)): Lean's `is_def_eq`, ported, decides the rejections they approximated, after a cross-check in which the port rejected every pair they showed apart; the rest of this ADR (S3, K4–K6, the order) stands. Before: **rules accepted** by the owner on 2026-11-02 (gate questions G1–G4 in [the gate summary](../reviews/FIRST_CHECKER_GATE.md#owners-answer)); the implementation still needs its own gate approval with test results. **Implemented** for comparison and inference on 2026-11-02 (plan task 2.2.1; see [Implementation](#implementation-plan-task-221)); its [kernel] gate was **approved by the owner on 2026-11-03** ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)), with Lean's rule for a "for all" whose body is not a type to follow as an amendment. **[Amendment 1](#amendment-1-proposed-2026-11-03-universe-levels-are-built-and-compared-as-lean-builds-and-compares-them)** (proposed, 2026-11-03, after the independent review of the declaration check found four wrong *accepted* answers): universe levels are built and compared exactly as Lean's kernel builds and compares them; it corrects fact 7, *Equal*, D1 and K4 below and adds rule K6. **[Amendment 2](#amendment-2-proposed-2026-11-03-a-for-all-whose-body-is-not-a-type-rule-s4)** (proposed, 2026-11-03, plan task 2.1.5): Lean's rejection of a "for all" whose body is not a type, rule S4. Previously: **proposed**, 2026-11-02 (plan task 2.1.1). A checker rule: it must
pass the review gate in `AGENTS.md` — rules that follow Lean's published
kernel, agreeing pinned-Lean differential tests that reach every outcome, an
independent AI review with no unresolved findings, and the owner's approval
of the plain-language summary in
[the gate draft](../reviews/FIRST_CHECKER_GATE.md). When proposed, nothing
here was implemented; the rules of comparison and inference now are (see
[Implementation](#implementation-plan-task-221)), the environment's (N1,
N2, L1–L3) by [ADR 0012](0012-checked-environment.md), and the declaration
audit (U1, U2) and the whole check in Lean's order by check-declaration
(plan task 2.2.3; see [its implementation](#implementation-plan-task-223)). It refines ADRs 0002, 0003, 0006 and 0008 for the first checker
and supersedes none of them. The plan reserves ADR 0012 for the
checked-environment implementation (task 2.1.3), so the first checker's scope
is decided here rather than in a separate record.

Approval status: accepted 2026-11-02, gate: first-checker rules (G1-G4), [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Legacy retirement and the first checker's rules (2026-11-02, evening)"; kernel gate 2026-11-03, section "Gate answers and working guidelines (2026-11-03)"; rules D1-D5 and K1 were later retired by plan task 4.2.2d (see the Status paragraph above)

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
literals, projections and metadata nodes (projections are checked since plan
task 5.2.2, ADR 0015 J1 and J2, when an export is staged and fed). Free variables, metavariables and
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
   *Corrected by Amendment 1 (2026-11-03):* the converse fails —
   `is_equivalent` also calls some levels with equal values *different*
   (`imax 1 (u+1)` and `max 1 (u+1)`), because `normalize` leaves the
   arguments of a `max` that `mk_imax` produced unsorted. LeanForth now
   computes `is_equivalent` itself, exactly as Lean does, and builds every
   level the way Lean's kernel builds it.

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
  *Corrected by Amendment 1 (2026-11-03):* that last sentence was false
  for universe levels. LeanForth typed a `Π` with a raw `imax` and
  specialized a constant's type without simplifying, where Lean's kernel
  builds simplified levels (`mk_imax`, `mk_max`); and its level comparison
  removed `max … 0` and `imax … 0` at any depth, which Lean's `normalize`
  does not always do. Both made LeanForth call levels equal that Lean calls
  different, so it accepted four declarations Lean rejects (and a fifth
  found since). Levels are now *equal* exactly when Lean's
  `is_equivalent` holds for the levels Lean itself would have built
  ([Amendment 1](#amendment-1-proposed-2026-11-03-universe-levels-are-built-and-compared-as-lean-builds-and-compares-them)).
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
| S4 | *Amendment 2:* a `Π`'s body's type, after `whnfβ`, is rigid and not a `Sort`. | `infer_pi` 158 → `ensure_sort_core` 62–71; fact 3 | `typeExpected` |
| F1 | A function's type, after `whnfβ`, is rigid and not a `Π`. | `infer_app` 175 → `ensure_pi_core` 74–83; fact 3 | `funExpected` |
| D1–D5 | An argument's type and the expected domain (application), or the value's type and the declared type (declaration), are *apart* (below). | `infer_app` 181–186; `add_theorem` 205–206, `add_definition` 185–186 | `appTypeMismatch` or `declTypeMismatch` |

**Apart** (Lean's `is_def_eq` is certainly false). Let `t' = whnfβ(t)` and
`s' = whnfβ(s)`.

- **D1** — both are `Sort`s and some witness assignment gives their levels
  different values (facts 5 and 7). *Amended 2026-11-03 (Amendment 1):*
  both are `Sort`s and Lean's `is_equivalent` is false for their levels —
  exactly `quick_is_def_eq`'s answer (fact 5). A witness that tells the
  levels apart implies this, so every earlier D1 rejection stays.

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
  *Amended 2026-11-02 (owner answer G7):* with ADR 0003 Amendment 1 (G6),
  "identical" above reads "equal by the cautious comparison": the bodies
  are entered, under the expected side's domain, whenever the domains are
  shown equal, so a body pair that is apart rejects there too.
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
  equal, and have no witness (fact 7). *Amended 2026-11-03 (Amendment 1):*
  only when Lean's `is_equivalent` cannot be computed — a parameter whose
  name is not in the name store (never in a declaration's check), or too
  little fuel or room.
- **K6 shared universe objects** (Amendment 1) — specializing a constant's
  type meets a `max` or `imax` that contains a parameter, whose children
  come out structurally unchanged, and that Lean's `mk_max` or `mk_imax`
  would simplify. Lean keeps such a node only when the universe arguments
  are the very objects in memory that the stored type holds, so Lean's
  verdict depends on memory sharing that no input format records.
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

This was evidence about Lean, not about LeanForth: when proposed, no
LeanForth code returned *rejected*. The LeanForth differential against this
table is plan task 2.2.1. It must check that accepted, rejected and invalid
rows agree with the table and Lean, that every *rejected* carries the row's
exception kind, and that no *unknown* row becomes *rejected* without a rule.
It does: see [Implementation](#implementation-plan-task-221).

## Implementation (plan task 2.2.1)

Written 2026-11-02; [kernel] code, experimental, not through the review
gate. Each place that returns *rejected* names its rule in a comment and
records a diagnostic naming it
([codes 55–60](../programming/DIAGNOSTICS.md#catalogue)).

| Rule | Where | What it computes |
| --- | --- | --- |
| S1 | `mixed-definition-probe` `lf-mdefinition-claim-level` → `mixed-infer` `lf-minfer-sort-rule` | the claim's type is not a visible Sort, and its whnfβ is rigid and not a Sort (`mixed-head` `lf-mhead-not-sort?`) |
| S2 | `mixed-infer` `lf-minfer-domain` → `lf-minfer-sort-rule` | the same for a λ's or Π's domain; a Π's *body* that is no type stays unknown (no rule). *Since Amendment 2:* rule S4, `lf-minfer-body-sort` |
| S3 | `mixed-definition-probe` `lf-mdefinition-prop`, in the new `lf-mixed-theorem-probe` | `level-value` `lf-level-zero?`: Lean's `normalizes_to_zero`, computed as "zero when every parameter is 1" (equivalent, by induction on the level) |
| F1 | `mixed-infer` `lf-minfer-not-pi` | a function's type is not a visible Pi, and its whnfβ is rigid and not a Pi |
| D1 | `mixed-infer` `lf-minfer-sorts-apart` | `level-value` `lf-level-apart?`: the witness assignments of *Terms the rules talk about*. *Since Amendment 1:* `level-compare` `lf-level-inequivalent?`, Lean's `is_equivalent` false |
| D2–D5 | `mixed-infer` `lf-minfer-apart` and the words before it; at an application (`lf-minfer-argument`) and for the declaration (`lf-mdefinition-value-type`) | P1 and P3 on head kinds (`mixed-head`), P2 by `lf-minfer-proof-free?`, then the shapes; D4 enters bodies under the right (expected) side's domain (ADR 0003 Amendment 1, B2) |

Decisions of the implementation, none of which adds or widens a rule:

- **The analysis only turns *unknown* into *rejected*.** It runs after the
  step it decides was undecided; if it cannot decide, or runs out of fuel,
  room or frames, the step stays *unknown*. A rejection replaces the
  undecided step's diagnostic with the rule's.
- **P2 runs inference "aside"**: with every rule off, on the analysis's own
  nodes (whnfβ results and inferred types, made by the checker's passes
  from the audited input), in the current binder context, discarding what
  it allocates. A failure of that inference means "not known".
- **Fuel.** Inference's comparisons keep the fuel an undecided level
  comparison leaves (`lf-mixed-convert-keeping`; the direct
  `lf-mixed-convert` still leaves none), so that the analysis can run
  after it. Each level of the analysis costs one unit of fuel and one of
  inference's frames.
- **P2 is checked for every compared pair, including two Πs or two λs**,
  although Lean decides those at once (fact 5): stricter than needed, and
  equally sound.
- The D diagnostic records the set of D rules used from the compared pair
  down to the pair that decided (1 D1, 2 D2, 4 D3, 8 D4, 16 D5).

Evidence: `make test-first-checker-differential` runs all 62 table cases
through these paths and the checked environment (with a test stand-in for
the U1/U2 audit) and checks every row against Lean (see
[the expected results](../reviews/FIRST_CHECKER_EXPECTED.md#measured-2026-11-02));
`tests/core/definite-rejection.fs` tests each rule and its K boundary; the
randomized differentials against the code before the change show only
*unknown* → *rejected* changes, each with its rule.

## Implementation (plan task 2.2.3)

Written 2026-11-02; [kernel] and [bypass] code, experimental, not through
the review gate. `src/kernel/check-declaration.fs` is the check the
publisher of [ADR 0012](0012-checked-environment.md) runs for each
declaration, in the order of *Order* above, step by step: the audit (U1,
U2, V1), N2, L3, the declared type's inference, S1, S3 for a theorem, the
value's inference and the final comparison (D1–D5). Decisions, none of
which adds or widens a rule:

- **Lookups where Lean makes them.** N1, K5, L1 and L2 are not checked in
  a pass before typing: inference runs in an *environment mode*
  (`lf-minfer-start-env`, `src/kernel/mixed-infer.fs`) in which a constant
  is looked up in the check's snapshot when inference visits it, as
  `infer_constant` does (lookup, number of levels, each level in the
  declaration's scope, then the stored type instantiated), and a `Sort`'s
  level is checked when it is visited, as `infer_type_core` does
  (`src/kernel/env-signature.fs`). So when a declaration has two faults,
  the one Lean meets first decides, with Lean's reason. While inference
  runs aside (test P2), as in Lean's `infer_only` mode, L2 is skipped and
  no dependency is recorded; aside runs happen only inside the rejection
  analysis, after the step has already failed.
- **The stored type is the accepted declaration's own input term**,
  specialized by the existing simultaneous level substitution; no
  candidate signature is involved. The dependencies are the accepted
  declarations the type and value name, recorded as inference meets them.
- **The audit's forms.** An importer stages `let`, a literal, metadata or
  a projection as a leaf of its own tag that records only which form it
  was (`src/core/unsupported-forms.fs`), so U2 is a walk of the
  declaration's terms, not a flag an importer sets. A concrete `Sort` in
  the symbolic term graph is the wrong representation (ADR 0007) and is
  *invalid* (V1), as are free and meta variables (the importer refuses
  them) and a definition or theorem without a value. Inference itself
  still reports an unknown constructor as *unknown*; in a declaration's
  check none reaches it.
- **Scratch between the type and the value.** After step 6 nothing built
  for the type is needed, so the scratch is rolled back to the input marks
  before the value is inferred. With the 64-node term store this turns
  `composition.proof-irrelevance` from *full* into the table's *unknown*.
- **Fuel.** One budget per check (`lf-check-budget`, 0 in a new context:
  every check *exhausted*) covers the audit and inference; a lookup and
  the arity test cost none, L2 one unit per level node.
- **Label.** `lf-check-verdict.` prints an accepted slot as *accepted
  (experimental, not independently audited); axioms: none*, the axiom set
  read from the slot.

Evidence: the 62 table rows end to end through the environment, all
equal to the table (`make test-first-checker-differential`); the 22
binder-domain rows (ADR 0003, Amendment 1), 19 equal and three that meet
the 64-node store answering a failure (`test-binder-domains-differential`);
17 universe-scope rows (`test-universe-scope-differential`);
`tests/core/check-declaration.fs` (every outcome, Lean's order, fuel
sweeps) and `check-declaration-ndjson.fs` (the pinned exports); planted
faults; randomized differentials of the paths that existed before, with no
difference ([expected results](../reviews/FIRST_CHECKER_EXPECTED.md)).

## Amendment 1 (proposed, 2026-11-03): universe levels are built and compared as Lean builds and compares them

Approval status: accepted 2026-11-03, gate: kernel and bypass, [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Gate answers and working guidelines (2026-11-03)"; the entry names the declaration check with the universe-level fix (rules S4 and K6); the word proposed in the heading or Status line below was true when written

Status: **proposed**; [kernel] change, for the gate in `AGENTS.md`.
Written by agent LV after the independent review of the declaration check
(`.claude/work/LV/REVIEW-CD.md`, finding 1, category 1: four wrong
*accepted* answers).

### Summary for the owner

A universe level is a small expression such as `u`, `u+1`, `max u v` or
`imax u v` that says how "big" a type is. Lean's kernel tidies these
expressions whenever it makes one (for example it writes `max 1 (u+1)`
where LeanForth wrote `imax 1 (u+1)`), and then compares levels by a fixed
procedure that is deliberately incomplete: it sometimes calls two levels
different even though they always have the same value. LeanForth made the
untidied expressions and compared them with its own rule, so in four
review cases (and two more found since) it said "equal" where Lean says
"different" — it **accepted declarations that Lean rejects**, the worst
kind of mismatch. It was not a logical error (the levels really are equal
in value), but it broke the rule that LeanForth gives Lean's verdict.

The fix copies Lean exactly: LeanForth now tidies levels with exact copies
of Lean's `mk_max` and `mk_imax` wherever Lean's kernel does, and compares
levels with an exact copy of Lean's `is_equivalent` (including its
incomplete `normalize` step and Lean's ordering of names). The six review
cases, 26 further declarations checked with the pinned Lean, and 1,800
random pairs of levels now all give Lean's own answer. Levels never need
*unknown* in a declaration's check any more, except in one odd situation
where Lean itself gives two different answers to the very same input
(rule K6, below): there LeanForth now says *unknown*. Where Lean's
comparison misses a true equality, LeanForth now misses it too, as the
owner's rule requires; those cases are recorded in
`docs/project/BEYOND_LEAN.md` (rows BL-1 and BL-3) for a later improved
mode.

### Lean's source

Read at the pinned commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (the
`lean --githash` of the toolchain) from
`raw.githubusercontent.com/leanprover/lean4/<commit>/src/…` on 2026-11-03;
SHA-256 under *Reproduction* below (`level.cpp` and `type_checker.cpp`
have the hashes recorded above for `v4.35.0`).

| Lean function | Where | What it does |
| --- | --- | --- |
| `mk_succ`, `mk_max_core`, `mk_imax_core` | `level.cpp` 33–35 → `Level.succ`, `.max`, `.imax` (`Lean/Level.lean` 142–149, 157–161) | the raw constructors: no simplification |
| `is_explicit`, `to_offset`, `get_depth` | `level.cpp` 54–64, 67–74, 40 | `succ`ⁿ `zero`; strip successors; an explicit level's depth is n |
| `mk_max` | `level.cpp` 81–104 | both explicit: the deeper (the first on a tie); equal: the first; a `zero` argument: the other; one argument of a `max` that is the other: that `max`; same base: the larger offset; otherwise a raw `max` |
| `mk_imax` | `level.cpp` 112–123 (`is_one` 110) | right side never zero (`is_not_zero`, 160–172): `mk_max`; right side `zero`: `zero`; left side `zero` or `1`: the right side; equal: the left; otherwise a raw `imax` |
| `operator==` | `level.cpp` 125–150 | structural equality (hash, depth and pointer tests only shortcut it); parameters by name |
| `instantiate` with `replace` | `level.cpp` 317–340, 261–277 | a level without parameters is kept; a parameter becomes its argument; others are rebuilt from their rebuilt children |
| `update_succ`, `update_max` | `level.cpp` 301–306, 308–315 | rebuild with `mk_succ`, or `mk_max`/`mk_imax`, **unless every child is the very same object** (`is_eqp`, pointer identity), when the node is kept |
| `instantiate_lparams`, `instantiate_type_lparams` | `instantiate.cpp` 232–246, 248–254 (`update_sort`, `update_const`: `expr.cpp` 342–347, 349) | a constant's type specialized: `instantiate` on every `Sort` level and constant level |
| `infer_constant` | `type_checker.cpp` 101–123 | the constant's type is `instantiate_type_lparams` (122) |
| `infer_pi` | `type_checker.cpp` 144–166 | the type of `Π`s is `Sort` of `mk_imax(u₁, mk_imax(u₂, … s))` (163), innermost first |
| `infer_type_core`, `Sort` case | `type_checker.cpp` 345–348 | the type of `Sort l` is `Sort (mk_succ l)` (347): raw |
| `is_def_eq(level)`, `quick_is_def_eq` | `type_checker.cpp` 781–787, 810–811 | two `Sort`s, and two constants' levels, are compared by `is_equivalent` |
| `is_equivalent` | `level.cpp` 518–521 | structurally equal, or structurally equal after `normalize` |
| `normalize` | `level.cpp` 454–516 (with `push_max_args` 420–427, `mk_max` of a list 429–444, `mk_succ(l, k)` 446–452) | strip successors; `imax`: `mk_imax` of the normalized sides, **not normalized again**; `max`: flatten, normalize each argument and flatten again, sort by `is_norm_lt`, drop an explicit level that a later argument's offset covers, keep the largest offset per base, add the successors back to each, and fold with `mk_max` from the right |
| `is_norm_lt` | `level.cpp` 395–418, kinds in `level.h` 30 | by base, then offset; bases by kind (`zero` < `succ` < `max` < `imax` < `param`), parameters by name, `max`/`imax` by left then right side |
| name order | `name.h` 114, `name.cpp` 191–220 (`string_ref` `<`: `object.cpp` 2210–2215) | component by component from the root; a string component after a number; strings by bytes, then length; numbers by value; a prefix first |

### Where LeanForth builds levels

| Site | Lean's counterpart | Before | Now |
| --- | --- | --- | --- |
| `mixed-infer` `lf-minfer-pi-sort` (the type of a `Π`) | `infer_pi` 163 | raw `imax`, or `0` for a `0` body | `lf-level-mk-imax` (`level-make`) |
| `mixed-infer` `lf-minfer-sort-type` (the type of a `Sort`) | `infer_type_core` 347 | raw `succ` | unchanged: `mk_succ` is raw |
| `level-substitute` `lf-lsubst` (specializing a constant's type, through `mixed-level-substitute` and `env-signature`; also the signature probe) | `instantiate` with `update_succ`/`update_max` | rebuilt nodes kept their kind, unsimplified | each `max`/`imax` with a parameter whose children changed is rebuilt with `mk_max`/`mk_imax`; one without a parameter is kept |
| `level-normalize` (temporary levels of one comparison, rolled back after it) | `normalize` | none (a zero rewrite instead) | exact port |

Every other place that makes a level stores one as written in the input
(the importers, `author/build.fs`, `lf-hlevel-succ`): the input is what
Lean's elaborator or exporter wrote, which the kernel takes as it is.
Every site where Lean's kernel builds a level must build exactly Lean's
level; a new site needs the same port.

### Comparison

`level-compare` decides two levels by Lean's `is_equivalent`: structural
equality (parameters by their name IDs), or structural equality of the two
`normalize` results, with Lean's name order for parameters. *Equal* is
exactly Lean's *true*; a *false* answer is *unknown* to conversion (as
before) and is rule D1's rejection. The old rewrite of `max … 0` and
`imax … 0` at any depth is gone: it equated `succ (max 0 (imax 1 (u+1)))`
with `succ (imax 1 (u+1))`, which Lean does not (row
`universe.zero-rewrite-gone`). Concrete levels need no separate evaluation:
`normalize` turns a level without parameters into its value.

### The shared-object case (rule K6)

`update_max` keeps a `max` or `imax` node unchanged when both rebuilt
children are the same objects in memory as before. So when a constant's
stored type holds a node that `mk_max`/`mk_imax` would simplify, such as
`imax 1 (u+1)`, and a reference passes back exactly the parameter objects
the type holds, Lean keeps the node; with equal but separately allocated
arguments, it simplifies it. Measured with pinned Lean
(`tests/reference/universe-scope-terms.lean`, rows
`universe.shared-object` and `universe.fresh-object`): the same
declaration is accepted with the shared object and rejected
(`declTypeMismatch`) with a fresh one. No export or text format records
sharing, so LeanForth cannot know which Lean would see; it answers
*unknown* (diagnostic 36), and only there: a node without parameters is
kept (as `replace` keeps it), a node whose children changed in structure
is certainly rebuilt, and a node that `mk_max`/`mk_imax` would not change
is the same either way.

### Rules changed

- **D1** — Lean's `is_equivalent` false (was: a witness assignment). Fact
  5: `quick_is_def_eq` decides two `Sort`s by it at once.
- **K4** — only when `is_equivalent` cannot be computed.
- **K6** — new, above.
- **A1** — unchanged in wording; *equal* levels now mean Lean's
  `is_equivalent` on Lean's own levels.

### Rejected alternatives

- **Unknown for every comparison with a `max` or `imax`** (the review's
  stopgap). Safe, but weaker than Lean: the declarations Lean accepts
  (`T2`, `T3`, `N2`, …) would be *unknown*, against the owner's rule.
- **A complete level comparison** (equal for all parameter values). It
  would accept what Lean rejects (`T1`, `T4`, …); recorded as BL-1 in
  `docs/project/BEYOND_LEAN.md` for a later, labelled improved mode.
- **Choosing one sharing model** (always keep, or always rebuild). Each
  accepts a declaration Lean rejects in the other model.

### Evidence

Measured 2026-11-03 with Lean 4.35.0 and Gforth 1.0.0 (rows and commands
in [the expected results](../reviews/FIRST_CHECKER_EXPECTED.md#universe-levels-amendment-1)):

- **Universe-scope table**, 49 rows (17 before, 32 new), each with Lean's
  verdict checked by the Lean file: LeanForth gives Lean's verdict on all
  45 rows outside K6 (25 accepted, 20 rejected) and *unknown* on the four
  K6 rows. On `main` before the fix, the review's four and the two
  zero-rewrite rows were *accepted*, and T3 *unknown*.
- **The 62-row table**: unchanged but for `equal-universe-other-spelling`,
  now *accepted* as by Lean (was *unknown*, K4). Binder domains unchanged.
- **Random levels against Lean's kernel**: 1,800 seeded pairs over `u`,
  `v`, `w` agree with `Kernel.isDefEq` on `Sort`s (`is_equivalent`: 708
  equal, 1,092 not), with `mk_max` (through `instantiate`) and with
  `mk_imax` (through `infer_pi`), byte for byte
  (`tests/core/level-kernel-differential.py`).
- **Against an independent model** (`tests/core/level-compare.fs`, make
  test): 18,000 `mk_max`, `mk_imax` and `operator==` checks on random level
  DAGs against a plain recursive port of `level.cpp`, every rule reached;
  855 equivalent pairs, each equal in value under the witness assignments
  and symmetric.
- **Planted faults** (`tests/mutants/faults.toml`): each fix reverted in
  turn (raw `imax` for a Π, raw rebuild in substitution, witness D1, the
  sharing rule kept or dropped) and each of Lean's rules broken one by
  one: all 16 caught by `make test`'s files; the raw `imax`, the raw
  rebuild and a reversed name order also fail the pinned-Lean tables.

## Amendment 2 (proposed, 2026-11-03): a for-all whose body is not a type (rule S4)

Approval status: accepted 2026-11-03, gate: kernel, [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Gate answers and working guidelines (2026-11-03)"; the entry adds Lean's rejection of a for-all whose body is not a type through the same gate; the word proposed in the heading or Status line below was true when written

Status: **proposed**; [kernel] change, for the gate in `AGENTS.md`. Plan
task 2.1.5, which the owner asked for when approving the rejection rules
("identical to Lean").

**In plain words.** "For all x, B" is only a statement or a type when B
itself is a type. Lean's kernel checks that and rejects the declaration
otherwise; LeanForth answered *unknown* there. It now rejects in the same
situations, by the same test it already uses for the type of a variable
(rule S2), and stays *unknown* only where Lean might first have to unfold
a definition to decide.

**Lean's source.** `infer_pi` (`type_checker.cpp` 144–166) infers the
body's type after the binders and calls `ensure_sort_core` on it (158):
when the type is not a `Sort`, it reduces it with `whnf` and, if that is
still not a `Sort`, throws `type_expected_exception` (62–71):
`typeExpected`. For a term whose `whnfβ` is rigid (fact 3: a `Sort`, `Π`,
`λ` or bound variable at its head), Lean's `whnf` is exactly `whnfβ`, so
"rigid and not a `Sort`" is exactly Lean's failure; a constant at the head
might unfold either way (fact 2, K1).

**Rule S4.** A `Π`'s body's type, after `whnfβ`, is rigid and not a
`Sort`: *rejected*, `typeExpected`, diagnostic 61, at the place and in the
order Lean checks it (domains first, then the body, innermost `Π` first).
Otherwise the step stays as before (*unknown* when the type is no visible
`Sort`). Implemented as `lf-minfer-body-sort` in `src/kernel/mixed-infer.fs`
(the same `lf-minfer-sort-rule` as S2).

**Evidence** (Lean 4.35.0, Gforth 1.0.0, 2026-11-03). Seven Lean-checked
rows in the expected table (`pi-body.*`): three Lean rejects
(`typeExpected`: a variable, a λ, and the same in a theorem's claim),
LeanForth *rejected* by S4; two neighbours Lean accepts, *accepted*; and
two whose body's type is a constant, one Lean accepts and one it rejects
after unfolding, both *unknown* (K1). All 69 rows agree end to end. Unit
tests: `tests/core/check-declaration.fs` (value, claim, K1),
`mixed-infer.fs` and `mixed-definition-probe.fs`; planted faults
`lv-s4-off` and `lv-s4-reads-flexible` are caught.

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

Amendment 1 read these at commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (2026-11-03,
`curl -fsSL https://raw.githubusercontent.com/leanprover/lean4/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/<path>`):
`src/kernel/level.cpp`
`7cb927c6fabd9fb843f548443494d3673a08074e26fe32b679e80f4664fc7f25`,
`src/kernel/level.h`
`c8bd15369a7defcde87a5e0b750ab46512c28ce0a4de30f9be3eff8e3069c483`,
`src/kernel/type_checker.cpp`
`26eae5ebb88f6f7da2c0a91f470aae4b74d370569dc5ca81b44b2d5c24c8df4e`,
`src/kernel/instantiate.cpp`
`42527c96f4053fb3cbf4c26fbd544b1c4e0399e5c41b0fd792935d1d42f8916a`,
`src/kernel/expr.cpp`
`cb02c18964aca67289b8c1d64864355bb5c10fc93d55bd3c3c9646776af9c592`,
`src/util/name.cpp`
`644d615eb92757c3b5c92987ba0e0485eff988d32c3d22fad1607a03d83291fe`,
`src/util/name.h`
`604f5351cfcd65019f8a30c4c09b917204bc1b9dc53d123d6f530627d75cfd98`,
`src/runtime/string_ref.h`
`a970beded7021919ba0b5be211941c42e67ad0f6cd212e1d9fd6ad557d1c9f5e`,
`src/runtime/object.cpp`
`1dba3476a698ab05f8f0a56c323487755790675046e90219218cb9727658ead4`.
`level.cpp` and `type_checker.cpp` are byte for byte the files read for
`v4.35.0` above. The Lean-side constructors are in the toolchain's own
`src/lean/Lean/Level.lean`.
