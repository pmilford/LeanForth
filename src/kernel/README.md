# Kernel — the proof checker, under development

This folder holds the checker as it is developed: universe substitution,
value and comparison; candidate signatures; shift, instantiate, beta
reduction, definitional comparison, conversion and type inference over
free variables (`mixed-open.fs`: Lean's `instantiate_rev`, `abstract` and
`mk_pi`; see *Free variables* below); the
definition and theorem probe that drives them; the checked environment and
its publisher; and the first checker, `check-declaration.fs` (plan task
2.2.3), which the publisher runs for each declaration: the audit (U1, U2,
V1), then the name, the universe parameters, inference in environment mode
(constants and universe arguments looked up in the environment in Lean's
order, `env-signature.fs`) and the final comparison. Inference and the
probe answer *rejected* by the rules of
[ADR 0011](../../docs/adr/0011-definite-rejection.md) (S1–S3, F1, D1–D5;
the head kinds those rules read are in `mixed-head.fs`, the level tests in
`level-value.fs`), the environment by N1, N2 and L1–L3, the declaration
audit *unsupported* by U1 and U2; every other failure stays *unknown*,
*invalid*, *exhausted* or *full*. Universe levels are built and compared
exactly as Lean's kernel does (ADR 0011, Amendment 1): `level-make.fs`
ports Lean's `mk_max`, `mk_imax` and structural level equality,
`level-normalize.fs` its `normalize`, name order and `is_equivalent`,
which `level-compare.fs` (conversion, rule D1) uses; `mixed-infer.fs`
types a Π with `mk_imax`, and `level-substitute.fs` specializes a
constant's type as Lean's `instantiate` does. A new place that builds a
level where Lean's kernel builds one must use the same ports.

Inductive blocks (plan task 5.2.1a, [ADR 0015](../../docs/adr/0015-inductive-types.md);
[developer notes](../../docs/programming/INDUCTIVE_BLOCKS.md)):
check-declaration sends a block's first member to `check-block.fs`, which
runs Lean's `add_inductive` for a block of one non-recursive type in
Lean's order -- the audit and the checks that need no typing in
`inductive-block.fs`, the typed steps itself, Lean's `is_geq` in
`level-geq.fs` -- builds the recursor (`inductive-recursor.fs`), compares
the constructors and the file's recursors with what it built (B3), and
the publisher (`env-publish.fs`) makes every member's slot final
together. Any other block is *unsupported*.

## Free variables (plan task 4.2.2a, ADR 0014 Q2)

Inference meets only closed terms, as Lean's kernel does. When it enters
a binder it names the bound variable with a *free variable*: a term node
of tag `lf-tag-fvar` whose number is an entry of the check's *local
context* (`src/core/local-context.fs`), which holds the variable's type
(and, for a `let`, its value). `mixed-open.fs` ports the four functions
that move between the two forms: `instantiate` and `instantiate_rev` put
terms (free variables) for a body's loose bound variables, `abstract` turns
free variables back into bound ones, and `mk_pi` wraps a type in the Πs of
free variables. `mixed-infer.fs` enters the binders of a telescope of λs
or Πs one at a time, each checked as Lean's `infer_lambda` and `infer_pi`
check it, and keeps the opened binders' free variables on its *scope* (at
most `lf-depth-limit`). It reads source terms under the scope (a loose
bound variable `k` is the scope's free variable `k` places from the top),
which infers Lean's opened body without copying it, so that each binder
stays one step with its source node in the derivation log; a chain of λs
gets the type `mk_pi` gives it, built once from the inside out
(`lf-minfer-lam`).

Rules a new kernel module must keep:

- A free variable is valid only while its own entry names it
  (`lf-fvar-live?`): the local context is emptied when an inference job
  starts and only appended to during it, and a rollback of the term store
  leaves the entries of discarded variables dead. So never keep a free
  variable across a job, and audit any term that may hold one with
  `lf-cterm-check`, which accepts live free variables only. Inputs never
  hold them.
- Terms given to inference, conversion's callers and the substitutions are
  closed; `lf-instantiate` and `lf-instantiate-rev` rely on it (Lean's
  `lift_loose_bvars` is then the identity) and do not check it. Inside
  inference, a λ chain's inner types are over the scope's bound variables
  until the chain's top closes them; nothing but the enclosing λ sees them.
- The derivation log copies a free variable as the bound variable it
  stands for at the step's depth (`lf-fvar-depth`, set when inference
  opens the binder): a module that opens binders for logged steps must
  record that depth too.
- A node's address can move when a store grows: keep node and entry
  numbers, never addresses, across an allocation.
- ADR 0011's rejection analysis is the one place with open terms: it keeps
  the binders it enters (D4) as bound variables, each with a free
  variable on the scope, and closes a term with the scope's free
  variables (`lf-minfer-closed`) before P2 infers it. It is retired by plan task 4.2.2d.
- A caller that walks a telescope itself (`check-block.fs`, as Lean's
  `check_constructors`) opens each binder with `lf-minfer-push` (the
  domain closed with the scope's free variables, then a new free
  variable) and compares two terms read under the scope with
  `lf-minfer-agree`: structurally on equal depths, and the analysis
  closes what it infers with the whole scope. So the derivation log's
  comparison steps there, written at the block step's depth, hold bound
  variables only.
- What 4.2.2b–e need is in place: `lf-lctx-local` and `lf-lctx-let`
  (Lean's `mk_local_decl`, for `is_def_eq_binding`, eta and `infer_let`),
  `lf-fvar-value` (for `whnf_fvar`'s zeta), `lf-instantiate` (for beta) and
  the scope. Not yet: `cheap_beta_reduce` of a λ body's type (with
  `whnf_core`, 4.2.2c), `mk_pi` of a `let` variable (4.2.3), and the
  loose-variable range that lets Lean skip closed subterms (Q12).

**Nothing here is verified yet.** The code is in progress, and it becomes
trusted only when the owner declares it so, after the review gate in
`AGENTS.md`:

1. its rules follow Lean's published kernel behavior;
2. pinned-Lean differential tests agree and reach every outcome (accepted,
   rejected, unsupported/unknown), including deliberately invalid proofs;
3. an independent AI review of the exact change has no unresolved findings;
4. the owner approves a plain-language summary of the change.

Until an outside Lean expert has audited it, every accepted result is
labelled *experimental — not independently audited*. Axiom policy:
`docs/project/OWNER_DECISIONS.md`.

Kernel modules may use `lib/` and `core/`, never `import/`.
