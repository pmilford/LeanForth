# ADR 0003: candidate conservative conversion

Status: base text superseded by ADR 0014 (see the approval status below); Amendment 1 stays accepted. No theorem may be accepted using
this design until the rules, implementation and tests have been reviewed.
This describes a deliberately incomplete step toward Lean 4.35.0, not Lean's
complete definitional-equality algorithm. [Amendment 1](#amendment-1-proposed-comparing-under-binders-whose-domains-differ)
(proposed, 2026-11-02) answers the binder-domain question this record left
open.

Approval status: superseded by ADR 0014 (the base text; owner approved 2026-11-12, night, [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Approval round of 2026-11-12, night (approval pack)"); Amendment 1 below stays accepted and unchanged

## Purpose and inputs

The type checker needs to establish that two types agree. The candidate
procedure operates only on previously validated terms in a well-formed
context and the concrete-sort, variable, application, lambda and Pi fragment
of ADR 0002. Open subterms are interpreted under their current binder context;
the outer declaration type and value must be closed. Inputs, context,
allocation and result handles must be protected from concurrent mutation.

"Validated" here must mean more than syntactically scoped: before a comparison
can authorize a type-checking step, both compared expressions must be known to
be well typed in the same well-formed context. The type checker and conversion
procedure are mutually dependent; their ordering and termination argument are
still a review obligation, not established by the current prototype. In
particular, do not treat a successful untrusted scope scan as this precondition.
The reference oracle demonstrates why: Lean's `Kernel.isDefEq` reports an
ill-typed application equal to itself, while `Kernel.check` rejects it. Equality
alone is not evidence that either operand is well typed.

It returns `equal`, `unknown` or `resource-exhausted`. `equal` is intended to
be a sound sufficient condition for Lean definitional equality. `unknown` is
not inequality: the terms may be equal in Lean. A caller must never translate
`unknown`, a crash, a resource limit, or a failed check into `equal` or a
checked theorem. Malformed data and unsupported expression forms are handled
before this procedure, with their own diagnostics.

## Candidate algorithm

1. `whnf(t)` leaves a sort, variable, lambda or Pi at the head unchanged. For
   `App(f, a)`, first compute `whnf(f)`. If its result is `Lam(A, body)`,
   instantiate `body` with `a` using the capture-avoiding operation in ADR
   0002 and continue with the result. Otherwise retain `App(whnf(f), a)`.
   Subterms need not be normalized until comparison requires them.
2. `compare(t, u)` computes `whnf` on both. For two `Sort` nodes, return
   `equal` only if their concrete levels are identical. For two `Var` nodes,
   return `equal` only if their de Bruijn indices are identical. For two
   applications, recursively compare functions and arguments. For two lambdas
   or two Pi nodes, first require the domains to be structurally identical
   without reduction, ignoring binder names and annotations. If they are not,
   return `unknown` even if Lean could establish equality. Otherwise compare
   the bodies under the shared context extended by that domain. Return `equal`
   for these compound forms only when the required comparisons succeed.
3. Every other result, including different constructors, different indices,
   different levels or an inconclusive child comparison, is `unknown`. Propagate
   `resource-exhausted` when a required operation cannot finish within budget.
   Binder names and binder annotations do not affect this structural comparison.

The stricter binder rule avoids attempting body comparison when domains differ
syntactically, even if they are beta-convertible. For domains identical after
erasing binder names and annotations, the proposed representative is the left
domain; the equivalence of those contexts and preservation of body typing still
require human review. This is not a proof of soundness or a resolution of the
type-checking/conversion ordering obligation. A future extension to compare
merely convertible domains needs a separately reviewed context-conversion
argument. This change is newer than the owner's recorded review.

This intentionally does not return a general `not equal` verdict. Lean's
function eta and proof irrelevance can equate expressions that are not equal by
these structural and beta rules. Unfolding definitions, lets, recursors,
quotients, projections and symbolic universes is also outside this fragment.
Those require their own reviewed extensions. A type mismatch may only be
reported as Lean-invalid when independently justified by a reviewed rule;
otherwise a non-match is `unsupported`.

## Limits and state

All recursive traversal, beta steps, substitution, shifts and allocations draw
from explicit finite per-check budgets. Detect overflow before incrementing
indices or depths, and roll back or isolate temporary allocations on any
failure. Do not use the host call stack without a documented bound. The result
must be deterministic for a fixed term, context, limits and version. Any cache
must include the terms, binder context, relevant environment and resource
policy, and cannot turn an incomplete or exhausted result into `equal`.

The untrusted scope prototype and its raw mutable arena do not supply these
guarantees. They cannot be promoted to the trusted boundary without separate
review. No importer, Forth word, tactic or explanation can manufacture an
accepted theorem handle.

## Evidence and review

`tests/reference/core-oracle.lean` asks the pinned Lean kernel about beta,
dependent beta, binder names and annotations, function eta and proof
irrelevance. `tests/reference/substitution-oracle.lean` exercises open-term
shifts and instantiation. These tests characterize examples of Lean behavior;
they do not prove the candidate algorithm sound or test a LeanForth checker.

Before implementation, review the soundness of every `equal` case, binder
context handling, substitution and overflow, conversion callers, resource
limits and error propagation. Add positive and negative Lean comparisons and
tests that force each resource failure. In particular, confirm that the
candidate cannot make an ill-typed term or an unsupported Lean feature into an
accepted theorem. An expert human review is required by the project gate.

## Amendment 1 (proposed): comparing under binders whose domains differ

Approval status: accepted 2026-11-02, gate: first-checker rules (G6, G7); implementation needs its own gate, [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Legacy retirement and the first checker's rules (2026-11-02, evening)"; the word proposed in the heading or Status line below was true when written

Status: **rule accepted** by the owner on 2026-11-02 (G6, with G7 extending ADR 0011's D4; [gate](../reviews/FIRST_CHECKER_GATE.md#owners-answer-second-set)); the implementation still needs its own gate approval. Previously: proposed, 2026-11-02 (plan task 2.1.2). A checker rule: it
passes the [kernel] gate in `AGENTS.md` only with the owner's approval of
the plain-language summary in
[the gate document](../reviews/FIRST_CHECKER_GATE.md#second-set-of-questions)
(questions G6 and G7). Until then the identical-domain rule above stands.
When proposed, nothing here was implemented; plan task 2.2.1 (2026-11-02)
implements D4 read with *equal* domains and B2 in the rejection analysis
of `src/kernel/mixed-infer.fs` (ADR 0011, *Implementation*), and
`mixed-convert.fs` already compared domains up to beta (B1). The amendment is recorded here rather than in a
new ADR because it settles a question this record left open; the plan gives
ADR 0014 to Lean's full definitional-equality procedure (task 4.1.1).

### The open question

The owner's review of 2026-10-30
([record](../reviews/2026-10-30-human-review.md)) approved continuing but
noted "an unresolved conversion-context soundness question". In plain
words: when LeanForth compares two functions, or two "for all" statements,
whose argument types are *written* differently but *mean* the same thing —
`fun (x : (fun T => T) A) => x` against `fun (x : A) => x` — may it go on
to compare the two bodies, and which of the two argument types does `x`
have while it does? The independent AI reviews asked for a
"context-conversion" argument
([finding 2](../reviews/2026-10-30-ai-kernel-review.md),
[follow-up finding 1](../reviews/2026-10-30-ai-followup.md)); this record
avoided the question by demanding identical domains and answering *unknown*
otherwise.

### The answer in plain words

Lean answers both parts. It first checks that the two argument types are
equal, with its full equality test. Only if they are does it compare the
bodies, and while doing so the variable has the argument type of the
*second* thing compared — which, at every step of checking, is the
*expected* side: the declared type of a declaration, or the function's
argument type at an application. Because the two argument types are equal,
the choice cannot change the answer, and Lean's published type theory states
exactly this rule. LeanForth can do the same: compare the argument types
with its cautious comparison and, when they are equal, compare the bodies,
giving the variable the expected side's argument type. Some valid proofs
that the first checker would call *unknown* become *accepted*, as in Lean;
none can become wrongly accepted.

The same example in three forms. Lean 4.35.0 accepts the Lean source below
(tried 2026-11-02; `#print` shows that the statement keeps
`(fun T => T) A`), and the same declaration built directly for the kernel is
test row `decl.beta-domain-in-statement`:

- Mathematics: for every proposition A, "(the identity function on
  propositions, applied to A) implies A" — that is, A implies A.
- Lean: `theorem bdStatement : ∀ (A : Prop), (fun T : Prop => T) A → A :=
  fun (A : Prop) (h : A) => h`. The claim's argument type is
  `(fun T => T) A`; the proof's is `A`; they are equal after one beta step.
- LeanForth Forth — *illustrative sketch only; the syntax is designed in
  plan task 8.1.1 and nothing here runs*:

  ```forth
  s" bdStatement" theorem
    s" A" prop explicit
    s" T" prop  T fun  A apply   A arrow     statement
    s" h" A  h fun                            proof
  end-theorem
  ```

### Lean 4.35.0 evidence

Read from tag `v4.35.0` (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
at `raw.githubusercontent.com/leanprover/lean4/v4.35.0/` on 2026-11-02.
`type_checker.cpp`, `environment.cpp` and `level.cpp` have the SHA-256
hashes ADR 0011 records; the other files are listed under *Reproduction*.
Line numbers refer to these files.

1. **`is_def_eq_binding`** (`src/kernel/type_checker.cpp` 745–779) compares
   two `λ`s or two `Π`s. It walks both binder telescopes together while both
   are binders of the same kind (758, 776). For each pair, if the domains
   are not structurally equal (760) it instantiates both with the local
   variables made so far and returns *false* unless `is_def_eq` holds for
   them (761–764). If either body uses the variable, it makes one new local
   variable whose type is the domain of `s`, the *second* operand, with
   `s`'s name and annotation (766–770); otherwise it substitutes a
   placeholder constant `dontcare` (771–773, 1286), since no body can look
   at it. Finally it compares the instantiated bodies (777–778). The test
   on line 760 is `operator!=`, structural equality that ignores binder
   names and annotations (`src/kernel/expr_eq_fn.h` 13–16,
   `expr_eq_fn.cpp` 98–103 and 123–125).
2. **It decides at once.** `quick_is_def_eq` (801–826) sends two `λ`s or
   two `Π`s straight to it (808–809), and `is_def_eq_core` returns that
   answer immediately (1135–1136, and again after `whnf_core`, 1155–1161):
   no unfolding, proof irrelevance or eta is tried for such a pair.
3. **The second operand is the expected side.** `infer_app` calls
   `is_def_eq(a_type, d_type)`: the argument's inferred type first, the
   function's domain second (176–186). `add_definition` and `add_theorem`
   call `is_def_eq(val_type, type)`: the value's inferred type first, the
   declared type second (`src/kernel/environment.cpp` 184–186, 204–206).
4. **Both sides are already checked.** `infer_lambda` and `infer_pi` check
   that each domain is a type before adding its local variable (125–166);
   `infer_app` checks the function, then the argument, then compares
   (173–187); a declaration's type is checked to be a `Sort` before its
   value is checked (`environment.cpp` 127–133, 180–186, 196–206).
   `is_def_eq` itself checks no types (see *Purpose and inputs* above).
5. **Lean's type theory has this rule.** M. Carneiro, *The Type Theory of
   Lean* (2019), §2.2: from `Γ ⊢ α ≡ α′` and `Γ, x : α ⊢ e ≡ e′` follows
   `Γ ⊢ λx : α. e ≡ λx : α′. e′`, and likewise for `∀`; §2.3 gives the same
   congruence rules for the algorithmic equality Lean checks. The bodies are
   compared under *one* of the two domains, and with the symmetry rule of
   §2.2 either may be used, so Lean's use of the second operand's domain is
   an instance of the published rule. No separate context-conversion
   argument is needed beyond it. (A secondary source written for Lean 3;
   the Lean 4.35.0 code above is the primary evidence.)

### Decision (proposed)

- **B1 — walk.** To compare two `λ`s or two `Π`s, walk both telescopes
  together while both are binders of the same kind, as `is_def_eq_binding`
  does, comparing each pair of domains (each under the binders before it)
  with this record's comparison. A pair that is *equal* lets the walk go on;
  otherwise the pair's answer is the binder comparison's answer: *unknown*,
  or *apart* where ADR 0011 rule D4 applies. After the last pair, compare
  the bodies.
- **B2 — the variable's type.** While the bodies are compared, each bound
  variable has the domain of the *right-hand* operand. Every caller keeps
  Lean's operand order — inferred type on the left, expected type on the
  right (an argument's type against the function's domain; a value's type
  against the declared type) — so the variable has the expected side's
  domain, exactly as in Lean (evidence item 3).
- **B3 — preconditions unchanged.** Both operands are well typed in the same
  context, established by LeanForth's own checking in Lean's order before
  any comparison (ADR 0011, *Order*; evidence item 4).

B1–B3 replace, in step 2 of the candidate algorithm, the sentences from
"first require the domains to be structurally identical" to "under the
shared context extended by that domain", and the paragraph that begins
"The stricter binder rule". In ADR 0011's definition of *Equal*, "binder
domains identical" becomes "binder domains *equal* (B1)".

**Why no wrong acceptance can follow.** By induction on the comparison: if
LeanForth finds every domain pair *equal*, Lean finds them equal (ADR 0011,
*Equal*), so Lean reaches the body comparison with the context B2 gives
LeanForth; if LeanForth finds the bodies *equal*, so does Lean, and
`is_def_eq_binding` returns true. The cautious comparison never reads a
bound variable's type — it has no eta, proof irrelevance or unfolding — so
in the first checker B2 cannot change an *equal* answer. B2 matters where a
rule infers a type under a binder: ADR 0011's "known not to be a proof"
test (P2, used by rules D2, D3 and D5 inside bodies), and eta and proof
irrelevance in phase 4. There it keeps LeanForth's context identical to
Lean's.

**Consequence for ADR 0011 rule D4 (owner question G7).** D4 enters bodies
only under identical domains. The consistent change is to read D4 with
*equal* domains: walking the two telescopes as `is_def_eq_binding` does,
D4 applies when the first pair of domains that is not *equal* is apart, or
when every pair is *equal* and the remaining bodies, with the variables
typed as B2 says, are apart. It is sound for the same reason: Lean then
compares those bodies under the same context, finds them unequal,
`is_def_eq_binding` returns false (evidence item 1, lines 777–778) and
`is_def_eq_core` returns that at once (evidence item 2). Keeping D4 as
approved leaves five rows of the table *unknown* that Lean rejects. If G7
is approved, ADR 0011's D4 text is updated with the approval.

### Tests

`tests/reference/binder-domains.lean`, with its table
`binder-domains.tsv` and script `binder-domains-check.sh`, run by
`make reference-binder-domains` (part of `make check`). It has 22 rows:

- **10 comparisons** of two closed `λ`s or `Π`s whose domains differ: by one
  beta step (in a non-dependent arrow, in a body that uses the variable, deep
  in a telescope), apart, equal only by unfolding a definition, only by
  proof irrelevance, and equal domains followed by eta. Lean's kernel checks
  both terms, then compares them **in both orders**; the run fails if the
  two orders disagree. Lean: 6 equal, 4 different; both orders agreed on
  all ten, the observable side of "the choice cannot change the answer".
- **12 declarations** whose value's type differs from the declared type, or
  whose argument's type differs from the function's domain, only in binder
  domains. Each row names that inner comparison; the run checks that its two
  types are structurally different binders and that Lean's answer on them,
  in both orders, explains the verdict. Lean: 6 accepted, 4
  `declTypeMismatch`, 2 `appTypeMismatch`.

Each row also gives LeanForth's required answer now and after the
amendment; the run fails if either contradicts Lean (*equal*/*accepted*
where Lean says no, *apart*/*rejected* where Lean says yes).

| Change from now to amended | Rows |
| --- | --- |
| *unknown* → *equal* or *accepted* (B1) | 8: three comparisons, five declarations (`decl.beta-domain-in-statement`, `-in-proof`, `-used-by-body`, `decl.argument-beta-domain`, `decl.lambda-in-argument`) |
| *unknown* → *apart* or *rejected* (D4 read with *equal* domains, G7) | 5: two comparisons, `decl.beta-domain-wrong-claim`, `decl.argument-beta-domain-wrong-body`, `decl.lambda-in-argument-wrong-body` |
| unchanged | 9: domains apart (*apart*/*rejected*, 3 rows), domains equal only by unfolding (*unknown*, K1, 4 rows), proof irrelevance (K2) and eta (K3) |

Run on 2026-11-02 with the pinned Lean 4.35.0: all 22 answers as recorded,
about one second. Thirteen planted faults in scratch copies were each
caught: a changed Lean verdict or LeanForth column in the table, a changed
expected verdict, a wrong claim made valid, structurally equal operands, the
reversed comparison disabled, a dropped row, a domain made identical in a
statement, an argument and a `λ` row, a misstated inner comparison, and a
LeanForth column that would accept what Lean rejects or reject what Lean
accepts. By inspection, no row of
[the first checker's table](../reviews/FIRST_CHECKER_EXPECTED.md) changes:
none of its 60 cases compares two binders whose domains are equal without
being identical.

This is evidence about Lean, not LeanForth: when this was written no
LeanForth code implemented B1–B3 (since plan task 2.2.1, the rejection
analysis does, for D4; the 22 rows' LeanForth columns are not yet run
against LeanForth code). The untrusted experiment `src/kernel/mixed-convert.fs` already
compares binder domains up to beta and then the bodies, unlike the
identical-domain text above: in `make test-mixed-convert-differential`, row
2 (`∀ x : (fun x => x) C, C` against `∀ x : C, C`) is *equal* in Forth and
in Lean. `tests/reference/type-model.lean`, a Lean model of the old rule,
asserts that beta-equal domains stay inconclusive; that assertion changes
when the amendment is implemented.

### Rejected alternatives

- **Keep identical domains only.** Safe, but leaves Lean-valid proofs
  *unknown* (8 rows) for no gain in safety, and disagrees with the existing
  experiment.
- **Give the variable the left-hand domain** (this record's earlier
  wording). Equally sound by symmetry, but differs from Lean's code; with
  Lean's choice, every type inferred under a binder is inferred in Lean's
  own context.
- **Go on to the bodies when a domain pair is undecided.** If the bodies are
  apart under the right-hand domain, Lean says *false* whether or not the
  domains are equal, so this would add rejections (rows
  `compare.domain-needs-unfolding-different-body` and
  `decl.domain-needs-unfolding-wrong-claim`). But it reasons in a context
  Lean may never build, and is not needed before unfolding (phase 4).
- **Compare the bodies without the domains.** Unsound: `fun (x : A) => x`
  and `fun (x : B) => x` have the same body.

### Reproduction

```sh
make reference-binder-domains
curl -sSfLO https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/kernel/type_checker.cpp
```

SHA-256 of the files read beyond ADR 0011's list:
`src/kernel/expr_eq_fn.h`
`ad010ccbc56f48abb3b94c3009e7c2d04ac0455f5d12a6ad7b7a797e39f65f3b`,
`src/kernel/expr_eq_fn.cpp`
`7feb30ca81d90d8dc585f79fc1e9cc64d84bd2f0c458a2e50922a92a4740a07c`;
Carneiro's thesis, release v1.0 of `github.com/digama0/lean-type-theory`
(`main.pdf`), `cd631ba59850370692a13151b7c9f58d40f094ecbefb72cd1c7950486afea4ec`.
