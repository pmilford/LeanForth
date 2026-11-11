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
probe answer *rejected* where Lean's `whnf` shows a type is no Sort or
no Π (`ensure_sort`, `ensure_pi`, below), where Lean's `is_def_eq` says
no (`defeq.fs`, below; ADR 0011's rules D1–D5 approximated it until plan
task 4.2.2d) and by rule S3 of
[ADR 0011](../../docs/adr/0011-definite-rejection.md) (its level tests in
`level-value.fs`), the environment by N1, N2 and L1–L3, the declaration
audit *unsupported* by U1 and U2; every other failure stays *unknown*,
*invalid*, *exhausted* or *full*. Universe levels are built and compared
exactly as Lean's kernel does (ADR 0011, Amendment 1): `level-make.fs`
ports Lean's `mk_max`, `mk_imax` and structural level equality,
`level-normalize.fs` its `normalize`, name order and `is_equivalent`,
which `level-compare.fs` (conversion) uses; `mixed-infer.fs`
types a Π with `mk_imax`, and `level-substitute.fs` specializes a
constant's type as Lean's `instantiate` does. A new place that builds a
level where Lean's kernel builds one must use the same ports.

Definitional unfolding and equality (plan tasks 4.2.2b–d, [ADR 0014](../../docs/adr/0014-definitional-equality.md)),
ports of Lean's own functions as frame steps on the caller's frames:
`whnf.fs` (`whnf_core`, `whnf`, `is_delta`, `unfold_definition`,
`reduce_nat`'s test, `cheap_beta_reduce`; definitions and theorems
unfold, opaque declarations never; the **iota hook** `lf-whnf-iota`,
which `iota.fs` sets) and `defeq.fs` (`is_def_eq_core` in Lean's order,
with `quick_is_def_eq`, `is_def_eq_binding`, `is_def_eq_app`,
`is_def_eq_args`, lazy delta reduction, `is_def_eq_offset`, proof
irrelevance and eta, tasks 4.2.5 and 4.2.4; structure eta and
unit-like types answer *unknown* where they may decide, task 5.2.2; Lean's names
matched by name are K7 only where `reduce_nat` computes a literal).
Lean's `==` is `lf-expr-equal` (`mixed-compare.fs`). Lean's caches
(`caches.fs`, plan task 4.2.7, ADR 0014 Amendment 1): inferred types per
mode, `whnf_core`, `whnf`, unfolded values, success and failure pairs,
keyed by skeletons that stand for `==`, and Lean's cached node data
(loose bound variables, free variables), set into the passes through
hooks; off with the derivation log on. Conversion
(`mixed-convert.fs`) is `defeq.fs` after its audits, its no
*rejected*; inference lends it a typer (`lf-minfer-typed`, Lean's
infer-only `infer_type`), and its `ensure_sort` and `ensure_pi` put a
type in Lean's `whnf`, replacing rules S1, S2, S4 and F1, whose
diagnostic codes they keep.

Inductive blocks (plan tasks 5.2.1a and 5.2.1b, [ADR 0015](../../docs/adr/0015-inductive-types.md);
[developer notes](../../docs/programming/INDUCTIVE_BLOCKS.md)):
check-declaration sends a block's first member to `check-block.fs`, which
runs Lean's `add_inductive` for a block of one type or a mutual block,
recursive or not, in Lean's order -- the audit and the checks that need
no typing in `inductive-block.fs`, the typed steps itself with
positivity (in Lean's `whnf`, `whnf.fs`), Lean's `is_geq` in
`level-geq.fs` -- builds the recursors with their induction hypotheses
(`inductive-recursor.fs`), compares the constructors and the file's
recursors with what it built (B3), and the publisher (`env-publish.fs`)
makes every member's slot final together. A nested block is
*unsupported*. `iota.fs` ports Lean's iota reduction (`inductive_reduce_rec`)
behind `whnf.fs`'s hook. When no slot holds `T.rec`
(the file left it out, or the block was rejected by B3), a later
declaration's inference builds Lean's generated recursor again from the
recipe the block check left (`generated-recursor.fs`, called by
`env-signature.fs`; ADR 0015 decision 12).

## Free variables (plan task 4.2.2a, ADR 0014 Q2)

The types inference gives back are closed, as in Lean's kernel; the
source terms it reads are not (see below). When it enters
a binder it names the bound variable with a *free variable*: a term node
of tag `lf-tag-fvar` whose number is an entry of the check's *local
context* (`src/core/local-context.fs`), which holds the variable's type
(and, for a `let`, its value). `mixed-open.fs` ports the four functions
that move between the two forms: `instantiate` and `instantiate_rev` put
terms (free variables) for a body's loose bound variables, `abstract` turns
free variables back into bound ones, and `mk_pi` wraps a type in the Πs of
free variables. `mixed-infer.fs` enters the binders of a telescope of λs
or Πs one at a time, each checked as Lean's `infer_lambda` and `infer_pi`
check it, and keeps the opened binders' free variables on its *scope* (a
growable array: no fixed depth, plan task 6.2.0). It reads source terms under the scope (a loose
bound variable `k` is the scope's free variable `k` places from the top),
which infers Lean's opened body without copying it, so that each binder
stays one step with its source node in the derivation log; a chain of λs
gets the type `mk_pi` gives it, built once from the inside out
(`lf-minfer-lam`). The substitutions (`mixed-open.fs`, `mixed-shift.fs`,
`mixed-instantiate.fs`) are Lean's `replace` (plan task 6.5.5, ADR 0014
Amendment 3): a node whose data word shows it unchanged is kept unvisited,
and each result is kept per node and offset for the call in the replace
memo (`replace-memo.fs`); a closing with the scope's free variables keeps
its results for the job, and inference keys an inferred type by the node
closed with its scope, as Lean keys the opened term.

Rules a new kernel module must keep:

- A free variable is valid only while its own entry names it
  (`lf-fvar-live?`): the local context is emptied when an inference job
  starts, and when inference discards scratch it drops the entries whose
  nodes went with it (`lf-lctx-drop`), so a number may be taken again by a
  new node; a discarded node never names the new entry (identities never
  repeat). So never keep a free variable across a job or a discard, and
  audit any term that may hold one with `lf-cterm-check`, which accepts
  live free variables only. Inputs never hold them.
- Source terms are read under the scope, so one source node can mean
  different terms: a hash-consed `#0` shared by two depths stands for
  different free variables. A cache of inferred types (ADR 0014 Q10, plan
  task 4.2.7) must be keyed by the opened term (a closed copy) or by the
  pair (node, scope), never by the source node alone; only closed scratch
  terms may be cached by node. P2 closes its term before inferring it for
  that reason too.
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
- The comparison's typer (`lf-minfer-typed`) closes the term it infers
  with the scope's free variables (`lf-minfer-close`) first, as terms
  read under the scope need (ADR 0011's rejection analysis, which did the
  same, was retired by plan task 4.2.2d).
- A caller that walks a telescope itself (`check-block.fs`, as Lean's
  `check_constructors`) opens each binder with `lf-minfer-push` (the
  domain closed with the scope's free variables, then a new free
  variable) and compares two terms read under the scope with
  `lf-minfer-agree`: structurally on equal depths, and the typer
  closes what it infers with the whole scope. So the derivation log's
  comparison steps there, written at the block step's depth, hold bound
  variables only.
- `lf-lctx-local` and `lf-lctx-let` (Lean's `mk_local_decl`) serve
  `is_def_eq_binding` (`defeq.fs`, 4.2.2b), eta and `infer_let`
  (`mixed-infer.fs`, 4.2.3, which also closes a `let` chain's type as
  `mk_pi` with `remove_dead_let` does); `lf-fvar-value` serves
  `whnf_fvar`'s zeta, and `whnf.fs` reduces a `let` term by zeta
  (`core/let-terms.fs`, 4.2.3) and beta with `lf-instantiate` (4.2.2c);
  `cheap_beta_reduce` of a λ body's type is in place (4.2.2c). Not yet:
  the loose-variable range that lets Lean skip closed subterms (Q12):
  `whnf.fs` scans for loose bound variables instead.

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
