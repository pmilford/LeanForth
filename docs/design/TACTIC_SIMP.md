# Simp: Lean's simplifier and its family (simp, simp only, simp at, simp_rw, simpa, simp_all, dsimp)

Status (2026-11-24): **second version, after the independent review**
([report](../development/design-reviews/2026-11-24-tactic-simp.md), "approve with changes"; every change applied, listed at the
end); the owner approved the plan on 2026-11-24 (OWNER_DECISIONS.md, "simp: the plan and its spellings"). Slice
SD-a written and tested on branch `simp-sd-a` (2026-11-25; not reviewed, not merged, not done): format 4's `congr`
records and `defeq` tags, `simp-data.fs`, the test export `tests/front/simp-slice` (decide's slice lacks four
congruence lemmas of its functions, so it stays at format 3); the check's count line waits for `src/cli`'s branch.
Nothing else is built. The design builds on two designs the owner approved on 2026-11-18: [SIMP_DATA.md](SIMP_DATA.md)
(elaboration data format 4) and [LF_LIBRARIES.md](LF_LIBRARIES.md) §3 (library 2). Their slices SP1a to SP3 are
re-cut here as SD-a, SD-b and SL1a to SL6 (section 6); SP4, MF, S7 and S8 stay as they are. Plan rows: FE9, and TB2's
simp family. LeanForth paths are relative to `src/front/`, Lean's to the pinned toolchain's `src/lean/`. All of it is
untrusted front-end code: simp builds a term, and only the kernel accepts a proof. Lean's behaviour was settled by the
author's probes (p1-p3) and the reviewer's (r1-r5) on pinned Lean 4.35.0 (appendix C).

## 0. One page for the owner

**What simp does.** `simp` rewrites a goal or a hypothesis with equations, again and again and inside every part of the
term, until none applies; a goal that has become `True` is closed. `simp only [a, b]` uses only the equations named;
plain `simp` every lemma marked `@[simp]` (10,296 in Init, 101,283 in Mathlib), found through an index on each lemma's
left side. A lemma with a condition is used only when a nested simp proves the condition; built-in programs
("simprocs") compute with literals (`2 + 3` becomes `5`). In Forth terms: a term walker with a memo table, whose visit
word tries a table of rules before and after visiting the children and builds, beside the new term, a proof that old
equals new, glued from the children's proofs. The kernel checks that proof; the port must still give Lean's proof
node for node: the same rule order, congruence lemma and helper-theorem names.

| After | Lean | LeanForth |
|---|---|---|
| SD-a, SL1a | `simp only [h]`, `simp only [Nat.add_zero] at h` (no binders, no conditions) | `by-simp-only[ ' h ]`, `by-simp-only[ ' Nat.add_zero ] at[ h ]` |
| SL1b | the same under `∀`, `→`, `fun`, `let`, `match`; `↔`, `¬` hypotheses; `at *` | `... at[ * ]` |
| SL2 | through `if` and dependent arguments; conditional lemmas | the same words |
| SL3a-c | `simp`, `simp [foo, -bar, *]`, `simp at h`; literal arithmetic | `by-simp`, `by-simp[ ' foo -' bar '* ]`, `by-simp at[ h ]` |
| SL3d | `simp only [← foo, Nat.add_comm, iff_lemma]`, `simp_rw [foo]` | `by-simp-only[ ' foo <- ... ]`, `by-simp-rw[ ' foo ]` |
| SL4-SL6 | `simpa using h`, `simp_all`, `dsimp only [f]`, `simp +contextual`, `simp?` | `' h by-simpa-using`, `by-simp-all`, `by-dsimp-only[ ' f ]`, `by-simp config[ +contextual ]`, `by-simp?` |

**(a) Reuse.** simp calls 31 existing files (12,157 lines) unchanged: unification, normal forms, inference, instance
search, the index's insertion and keys, telescopes, term builders, goal words, locations, the data reader, the
hand-over. About 1,200 lines are missing below simp (settings switches in the shared Meta files, index queries, nine
proof builders, a rebuild walk under binders, helper theorems, an in-place hypothesis change). Reused code is about
half of what a simp call runs (12,200 of about 23,700 lines).

**(b) New library.** About 11,500 lines in about 30 new files and 10 changed ones. The simp core (about 5,200) is
called by `norm_num`, `field_simp`, `ring_nf`, `norm_cast`, `split`, `unfold`, `conv`, `acyclic` (pattern slice E5),
the equation theorems of recursive definitions (FE8), `aesop`, `linarith`'s preprocessing, and `trivial`'s last rule
(so `exists`). Simproc families about 2,000, arithmetic about 1,100, the data reader about 1,050; about 1,900 are
shared Meta words other tactics need: congruence theorems (`congr`, `convert`: 4,516 Mathlib uses), the rebuild walk
(`decide`, coercions, `delta`), the term order (`ac_rfl`), index queries (`norm_num`'s table, `positivity`), helper
theorems (`omega`, FE8).

**Size.** About 11,500 Forth lines (tests about as many) in 12 slices: **16-19M tokens**, a quarter to a third of a
week's 60-70M shared with other work. The time is set by the chain: ten slices in sequence at about one a day (as
TB2's ran), so two to three weeks.

**Your questions** (my recommendation in each):
1. **Spellings:** `by-simp`, `by-simp[ ]`, `by-simp-only[ ]` and the same for simpa, simp_all, dsimp; in the list `<-`
   after a rule, `-' foo` to erase, `'*` for all hypotheses, `' foo !pre` for Lean's `↓`; `' h by-simpa-using`;
   options as a trailing `config[ +contextual ]` (Lean writes them first). *Yes*: Lean's `*` and `-` are LeanForth's
   multiplication and subtraction in a term list, and `!pre` can be no Lean name (`pre` would forbid a hypothesis so
   named).
2. **The order** of section 6: `simp only`, then plain `simp` as soon as it can be faithful, then the wrappers. *Yes*;
   SL1b first measures what Init's 898 `simp` proofs need, and the later order follows that.
3. **[format] additions to format 4:** the `refl` and `symm` lemma sets (for `by-rfl`, `by-symm`), and the list of
   helper theorems Lean already made in the library (`Foo._simp_N`, `f.congr_simp`: name and statement). *Yes*: hints
   checked like the rest. In your file LeanForth makes exactly the helpers Lean makes there (`THM._simp_1_k` for a
   theorem, `NAME._simp_k` for a definition, also for bracket lemmas that end up unused).
4. **A cross-cutting change:** Lean's unfolding switches (match reduction, projections, `let`) in the Meta settings,
   honoured by `whnf.fs`, `defeq.fs` and the key maker, the most shared front-end files, today's behaviour the
   default. *Yes*: simp needs three settings from its first step; no other branch edits those files during SL1a.
5. **The depth limit:** Lean stops at 512 nested calls, two per simp visit plus unification's. Count at every ported
   place, refuse past 512 with Lean's message, document the rest. *Yes*: otherwise a proof Lean refuses for depth alone
   could pass.

## 1. The machinery: Lean's layers, what LeanForth has, what is new

Basis for every Forth figure: Lean code lines (no comments or blanks) times the ratio measured on ported files.
- **2.1** for simp's own code, like `meta-tactic/rewrite.fs` (178 file lines for 86 Lean code lines);
- **1.6** for Meta ports, like `meta-tactic/meta-induction.fs` (1.5);
- **1.3** for simproc tables (one Lean `builtin_simproc` line is one row).

New design work, such as the settings layer, is counted directly.

| Lean (file:line) | What it does | LeanForth today | New (slice) | Lean | Forth |
|---|---|---|---|---:|---:|
| `simpGlobalConfig` (SimpTheorems.lean:282), `mkIndexConfig`, `mkMetaConfig` (Types.lean:141, 162) | whnfCore switches: iota, proj kind, zeta, zetaDelta, beta | `meta-config.fs` holds defeq flags and transparency only; `whnf.fs` runs Lean's defaults | fields in `meta-config.fs`, honoured in `whnf.fs`, `defeq.fs`, `discr-keys.fs` (SL1a) | — | 280 |
| `mkPath` with `noIndexAtArgs` (DiscrTree/Main.lean:258-265); `getMatch`, `getMatchWithExtra` (:393-500) | head-only keys; candidates of a term | `lf-dt-path` full keys; `lf-dtree-unify` | flag and match mode (`discr-keys.fs`), queries (`discr-tree.fs`) (SL1a) | 110 | 220 |
| `Result`, `State`, `Step`, `Methods`, result builders, `simpAppUsingCongr` (Types.lean:25-61, 248-452, 560-765, 919-962) | the records; proofs by `congrArg`, `congrFun'`, `congr` | `lf-mk-congr-arg`, `lf-mk-eq-trans` | `simp/types.fs` (SL1a) | 220 | 460 |
| `simpLoop`, `simpStep`, `visitFn`, `congr`, `congrDefault`, `reduceStep` (Main.lean:70-255, 531-720) | the walk: cache, steps, depth, pre, children, post | `whnf.fs` steps | `simp/main.fs` (SL1a; `match` SL1b; unfold SL3a) | 230 | 480 |
| `tryTheoremCore`, `tryTheoremWithExtraArgs?`, `tryTheorem?`, `rewrite?`, `synthesizeArgs`, defaults (Rewrite.lean:58-240, 389-420, 536-547) | trying a lemma | `lf-meta-defeq`, `lf-try-synth` | `simp/rewrite.fs` (SL1a) | 190 | 400 |
| `SimpTheorem`, `Origin`, `isRflProof`, intake; `inferDefEqAttr` (DefEqAttrib.lean:159) | lemmas, origins, the rfl flag | `lf-dtree-insert` | `simp/theorems.fs` (SL1a; local preprocessing SL1b; global SL3d) | 200 | 420 |
| `getCongrSimpKinds` (CongrTheorems.lean:178-212), `congrCache` | which arguments may be rewritten | `fun-info.fs` (part of `ParamInfo`) | `congr-thms.fs`, `fun-info.fs` fields (SL1a) | 70 | 200 |
| `simpTarget`, `applySimpResult*`, `simpGoal` (Main.lean:780-911; Types.lean:1008); `replaceLocalDeclDefEq` (Replace.lean:110) | replacing goal and hypotheses | `lf-goal-replace-target-eq`, `-defeq`, `lf-goal-assert`, `lf-goal-try-clear` | `simp/goal.fs`, `assert.fs` (SL1a) | 130 | 300 |
| `simpLambda`, `simpForall`, `simpArrow`, `simpLet`, `simpMatch` (Main.lean:257-467; Rewrite.lean:336-387) | binders and `match` | `telescope.fs` | `main.fs` (SL1b) | 230 | 480 |
| `dsimpImpl` (Main.lean:469-530) on `transformWithCache` (Meta/Transform.lean) | rewriting without proofs (every argument with forward dependencies) | none: S3 built no transform; `dag-walk.fs` (176 lines) does not open binders | `transform.fs`, `main.fs` (SL1b; guard in SL1a) | 230 | 400 |
| `@[congr]` use, `tryAutoCongrTheorem?`, `mkCongrSimpCore?`, `.congr_simp` (Main.lean:552-635; Types.lean:773-917; CongrTheorems.lean:296-482) | congruence with dependent and instance arguments | none | `congr-thms.fs`, `simp/congr.fs` (SL2) | 320 | 620 |
| discharging (Rewrite.lean:21-57, 568-648) | side conditions, depth 2 | E3's `unifyEq?` (planned) | `rewrite.fs` (SL2) | 110 | 230 |
| default set, unfolding, `elabSimpArgs` items (Elab/Tactic/Simp.lean:336-370, 411-488) | the data's sets; names that are simprocs, sets or definitions | `elab-data.fs` reader | `simp/args.fs`, `theorems.fs` (SL3a) | 250 | 520 |
| simprocs (`Simproc.lean`, `BuiltinSimprocs/`: 1,451 code lines) | literals, `if` on known conditions, constructor equations | `reduce-nat.fs`, `nat-offset.fs`, `lib/bigint.fs` | `simp/simprocs.fs`, `simp/simprocs/*.fs` (SL3a-c) | 1,580 | 2,000 |
| `preprocess` (SimpTheorems.lean:319-390), `mkAuxLemma` (AuxLemma.lean:43), `mkUniqueName` (CoreM.lean:95-147), `isPerm`, `acLt` (ACLt.lean) | helpers for bracket lemmas, `←`, perm | `handover.fs` hands one theorem | `theorems.fs`, `handover.fs`, `ac-lt.fs` (SL3d) | 310 | 580 |
| `evalSimpaCore`, `SimpAll`, `dsimpGoal`, Mathlib `SimpRw.lean` | the wrappers | none | `simp/simpa.fs`, `simp/simp-all.fs`, `tactics/*` (SL3d, SL4) | 290 | 560 |
| options, `simpUsingDecide`, `simp?`; `simpArith`, `seval` (Arith/ 599) | options | `lf-mk-decide` | SL5, SL6 | 900 | 1,720 |
| format 4 reader and the realized constants list (SIMP_DATA §3-5) | the simp data | `elab-data.fs`'s reader | `simp-data.fs` (SD-a, SD-b) | — | 1,050 |

Total: about 11,500 Forth lines, with the tactic words (about 250). SIMP_DATA's figures were about half of this and
LF_LIBRARIES' about two thirds. The difference is the settings layer, `dsimp` from the start, congruence kinds, and the
2.1 ratio. Simp.Config's fields and their 4.35.0 defaults are in appendix E. SL1a ports the record whole, and a field
whose behaviour is not yet ported answers unsupported.

## 2. Words and forms

The owner's rules: values before a word are postfix; a list of any length sits between a bracket word and `]`; a
location is a trailing `at[ ]` (`|-` the goal, `*` everything).

| Lean | LeanForth | Slice |
|---|---|---|
| `simp only [h, foo, bar a]` ; `simp only` | `by-simp-only[ ' h ' foo ' bar ' a $ ]` ; `by-simp-only[ ]` | SL1a |
| `simp only [..] at h ⊢` ; `at *` | `by-simp-only[ .. ] at[ h \|- ]` (SL1a) ; `at[ * ]` (SL1b) | SL1a, SL1b |
| `simp` ; `simp []` ; `simp [foo]` ; `simp at h` | `by-simp` ; `by-simp[ ]` ; `by-simp[ ' foo ]` ; `by-simp at[ h ]` | SL3a |
| `simp [-foo]` ; `simp [*]` ; `simp [↓ foo]` | `by-simp[ -' foo ]` ; `by-simp[ '* ]` ; `by-simp[ ' foo !pre ]` | SL3a |
| `simp [f]` (unfold) ; `simp [Nat.reduceAdd]` ; `simp [push_cast]` (a set) | `by-simp[ ' f ]` ; `by-simp[ ' Nat.reduceAdd ]` ; `by-simp[ ' push_cast ]` | SL3a |
| `simp only [← foo]` ; `simp_rw [foo, ← bar] at h` | `by-simp-only[ ' foo <- ]` ; `by-simp-rw[ ' foo ' bar <- ] at[ h ]` | SL3d |
| `simpa` ; `simpa [..]` ; `simpa only [..]` | `by-simpa` ; `by-simpa[ .. ]` ; `by-simpa-only[ .. ]` | SL4 |
| `simpa using e` ; `simpa [..] using e` ; `simpa only [..] using e` | `e by-simpa-using` ; `e by-simpa-using[ .. ]` ; `e by-simpa-only-using[ .. ]` | SL4 |
| `simp_all` ; `simp_all [..]` ; `simp_all only [..]` ; `dsimp` ; `dsimp [..]` ; `dsimp only [..]` | `by-simp-all` ; `by-simp-all[ ]` ; `by-simp-all-only[ ]` ; `by-dsimp` ; `by-dsimp[ ]` ; `by-dsimp-only[ ]` | SL4 |
| `simp +contextual -zeta [..]` ; `(config := {..})` ; `(maxSteps := 500)` | `by-simp[ .. ] config[ +contextual -zeta ]` ; the same ; `config[ maxSteps 500 ]` | SL5 |
| `simp?` | `by-simp?`: prints `Try this: simp only [Nat.add_zero]` and `Try this: by-simp-only[ ' Nat.add_zero ]` | SL5 |
| `+arith`, `simp_arith`, `+ground` ; `(disch := ..)`, `simp!`, `simp_all?` | `config[ +arith ]`, `config[ +ground ]` (SL6) ; no form, unsupported | SL6 |

**Reader.** Every list word uses `tac-shape-rules` (`tactic-syntax.fs:357`), so an empty list is accepted as
Lean accepts `simp []` (`tac-shape-list+` refuses it, 460); SL1a changes no reader. SL3a adds three item words: `-'`
(a parsing word like `'`: the next name is erased; 83 outside a simp list), `'*`, and `!pre` after a rule as `<-`
(no Lean identifier begins with `!`); `'*` and `!pre` are refused in `by-rw[`. **Items are not plain terms**
(`elabSimpArgs`, Elab/Tactic/Simp.lean:336-370, 488): an item `' NAME` is resolved in Lean's order: a simproc (by
format 4's `simproc` records: `Nat.reduceMul` is in Lean's own package, not an Init export, so as a plain term it is
error 1), a simp set (its `simp_set` record), a definition to unfold, a theorem, a hypothesis, else a term; until
SL3a the first three answer unsupported. SL5's `config[` is a parsing list of `+NAME`, `-NAME`, `NAME N`, read like
`at[` and placed before it; Lean writes options before the list, a difference of spelling only.

**Errors** keep Lean's texts (appendix D), each a new code. SL1a takes 500-539 for the family: the reviewer confirmed
that no code at 310 or above is used on main or the 25 most recent branches; TACTIC_BLOCKS uses 468.
TACTIC_PLUGINS' reservation 300-339 collided with the runner's faults (300-309): see "Changes after review".

## 3. Lean fidelity

Each word ports the Lean function named and is compared with pinned Lean node for node (the theorem's term and every
helper declaration) and goal for goal (the step log). What must match:

- **Settings**, each set at its entry and restored on every exit, a throw included: lemma keys `simpGlobalConfig`
  (iota off, proj `.no`, zetaDelta off; SimpTheorems.lean:282); term keys `mkIndexConfig` (proj `.no`; Types.lean:141);
  unification `mkMetaConfig` (proj `.yesWithDelta`, zetaDelta from the config; :162).
- **Keys by origin.** A global constant gets full keys (`noIndexAtArgs := false`, SimpTheorems.lean:470, 473); a
  hypothesis or other term the head only (:502, 509; DiscrTree/Main.lean:258-265). So `h : f 6 = 0` rewrites
  `f (2 * 3)` with no simproc (r1 a1), and a head-only hypothesis wins over a full-keyed global lemma (r4 o4).
- **Origins.** A bracket term is `.stx` (Elab/Tactic/Simp.lean:363, 370), a hypothesis from `*` is `.fvar` (:400-401),
  and `simpGoal` erases only `.fvar h` (Main.lean:884): `simp only [h] at h h2` leaves `h : True` (r5 x3).
- **Order.** At a term (Rewrite.lean:536-547): pre is `rewritePre`, `simpMatch`, user pre-simprocs,
  `simpUsingDecide`; post is `rewritePost`, user post-simprocs, `simpGround`, `simpArith`, `simpUsingDecide`; the first
  answer wins (`andThen`, Types.lean:374). Lemmas (Rewrite.lean:214-240): the tree's result (star branch before the
  key whatever the bracket order, r4 o1/o2; one leaf's lemmas in insertion order, bracket order for brackets, r1 n1-n4;
  an equal value replaced in place; a metavariable in the term is the key `other`), then a stable sort by priority,
  highest first; erased origins skipped. `simp only` starts from `eq_self`, `iff_self` (:512), with no simprocs (:568)
  and with `@[congr]` (:569).
- **Trying a lemma.** `rewrite?` calls `tryTheoremWithExtraArgs?` with the tree's extra-argument count
  (Rewrite.lean:178-185, 234); the retry without them belongs to `tryTheorem?` (:187-202), which other callers use. In
  a new metavariable depth: unify at the meta setting; synthesize still-unassigned instances, `isDefEq` at
  reducible-and-instances; a still-unassigned Prop to the discharger; a result structurally equal to the term
  refused; a perm lemma kept only if `acLt` allows; `resolveBinderNameHint` (:152; Main.lean:600).
- **Congruence kinds** (CongrTheorems.lean:178-212). `congrDefault` asks for the automatic theorem first on every
  application (Main.lean:545-549); the plain builders only when every kind is `fixed` or `eq` (result dependencies,
  Prop to `cast`, instance to `subsingletonInst` or `fixed`, the class subobject mask, `fixKindsForDependencies`;
  matchers always plain; cached per function). Until SL2 another kind, or a head with a `@[congr]` record, is
  unsupported.
- **dsimp of dependent arguments.** Every argument with forward dependencies, every type argument included, is
  `dsimp`ed (Types.lean:668-677, 757-764, 831): with `x : Fin (n + 0)`, `p (n + 0) x` becomes `p n x` and the term is
  `id hp` (r4 o6). In SL1a such an argument holding a beta-redex, a projection or a node a rfl lemma could rewrite is
  unsupported (a scan with `lf-term-holds-node?`, `term-find.fs:61`); SL1b ports `dsimpImpl`.
- **Proof shapes.** A rfl lemma gives no step (`of_eq_true (eq_self n)`). `simpAppUsingCongr` uses `congrArg`,
  `congrFun'`, `congr` with explicit levels (Types.lean:682-726); `congrArgs` and `addExtraArgs` use AppBuilder's
  `congrFun`, `congrArg`, `congr` (:598-614). Shortcuts (AppBuilder.lean:630-660): `mkOfEqTrue (eq_true h)`,
  `mkEqTrue (of_eq_true h)` and `mkEqFalse (of_eq_false h)` are `h`, so `p` by `simp only [h]` with `h : p` is `h`
  (r5 x1). `simp only []` on `True` is `True.intro` with no "no progress" (x2). A changed target goes through
  `replaceTargetEq`; a hypothesis is `Eq.mp p h`, asserted, the old one try-cleared; one that becomes `False` closes
  by `False.elim`, one that becomes `True` is kept (r1 a5, r4 o9).
- **Hypotheses without a proof step** change in place by Lean's `replaceLocalDeclDefEq` (Replace.lean:110):
  `Expr.equal` (binder names and info compared, stricter than `lf-meta-eqv`), dependents allowed, no node left; "no
  progress" relies on it giving back the same goal (Main.lean:908). `assert.fs:189-211`'s `lf-goal-change-local-decl`
  is `changeLocalDecl` (revert, `id` hint) and is not used.
- **Local hypotheses** become proofs inline (SL1b): `propext h`, `eq_true h`, `eq_false h`, and
  `(fun x => propext (h x)) 0`, a beta-redex Lean keeps (p3 v4).
- **Helper names** (DeclNameGenerator.mkUniqueName, CoreM.lean:95-147). A theorem's proof runs in an async child:
  `THM._simp_1_k`; a definition: `NAME._simp_k` (r3 `d2._simp_1`); an `example` keeps none; a taken name is skipped.
  Every bracket lemma that needs preprocessing gets its helper when the list is read, used or not (r2 v1: the unused
  `Nat.add_eq_zero_iff` took `_simp_1_2`, the used helper is `_simp_1_3`). Nested `have` blocks share the counter and
  the cache by statement. The helper's rfl flag: `inferRfl := true`, `defeq := inv && tag` (SimpTheorems.lean:465-469).
- **Realized constants.** Init's `.olean` files hold 256 `.congr_simp` and 7,537 `._simp_` constants
  (`Decidable.decide.congr_simp` comes from Init.SimpLemmas, r3); Lean's user file declares none of them. LeanForth
  builds each listed one (SD-b) as a library constant, checked against the listed statement, and declares in the
  user's file, handed to the kernel before the theorem, only what Lean realizes there.
- **The user's rfl flag.** Lean sets it at declaration (`inferDefEqAttr`, DefEqAttrib.lean:159): the proof written
  `:= rfl` and a check at instances transparency (r5: `myrfl` leaves no step, `:= (rfl)` leaves `myrfl2 n`). LeanForth
  ports the rule for the spelling that elaborates exactly Lean's `:= rfl`; another user lemma used by simp is
  unsupported.
- **Equality tests**: Lean's `==` is `lf-meta-eqv`, `Expr.equal` a new `lf-meta-equal?` (`term-eqv.fs`), never a term
  identity alone (hash-consing can be off, `core/terms.fs:30`). **The cache** is keyed structurally as Lean's
  `ExprMap`; the congruence and dsimp caches, fresh caches for new local lemmas and the cache kept across a discharge
  are ported as they are, in one state shared by nested calls.
- **Limits** (Main.lean:677-687, 714): a cache hit first, then the step check (a strict `numSteps > maxSteps`) before
  the increment: exact. Depth rises twice per visit (`simpLoop`, `simpImpl`); the rest is question 5. Not visited:
  instance-implicit arguments (unless `instances`), proofs, `OfNat` and `Char` literals.

**Not node for node.** Which dsimprocs ran leaves no trace in the term (the step log's goals catch a different normal
form); Lean's heartbeats fall elsewhere than LeanForth's fuel (a run-out is "exhausted", never success);
unused-argument warnings (Elab/Tactic/Simp.lean:705) change no verdict. No term comparison is weakened.

## 4. The data

**What simp reads** is SIMP_DATA §1-3 under the [import]/[format] gate approved 2026-11-18 (with lazy loading and
"Lean's on-demand theorems at the next library export"): the simp sets' lemma and left-out records, definitions to
unfold, simprocs and their entries, `@[congr]` lemmas with rank, the `defeq` and `backward_defeq` tags. Measured: Init
10,296 default lemmas (4.5 MB), 341 default simprocs, 59 congruence lemmas; Mathlib 101,283 (63 MB), 346, 111. Init's
default set has no `←` and no perm lemma (SIMP_DATA appendix A).

**State.** The writer is on branch `simp-data-tool` (6 commits, 2026-11-17, with tests; not merged; 847 commits
behind main, which has since changed `export_elab.py` by 192 lines and `export_elab.lean` by 40). It writes keys,
simprocs and congruence lemmas, not realized constants. No reader exists.

- **SD-a** rebases the writer for two kinds, `congr` records and the tag's `defeq` flags, and reads them in a new
  `simp-data.fs` registered by kind with `elab-data.fs`'s reader, so later kinds need not edit that file (1,637 lines,
  where data branches meet).
- **SD-b**: the rest of SIMP_DATA §3, the `coe_decl` tag (owner, 2026-11-18), the `refl` and `symm` kinds if question
  3 is approved, and `realized` records (each realized constant of the library: name, statement, kind `congr_simp` or
  `simp_helper`); and **EX**, which writes the on-demand theorems into Init's export (today it lacks 1,009 of the
  helpers Init's default lemmas use, SIMP_DATA §2). Every refusal of SIMP_DATA §4 is a planted fault, plus one for a
  realized record whose statement differs from the constant LeanForth builds.

**Test exports.** SL1a to SL2 run on a new `tests/front/simp-slice` (a roots file, built as `decide-slice`):
the lemmas tested, the proof constants simp builds with (`eq_self`, `iff_self`, `of_eq_true`, `eq_true`, `eq_false`,
`congrArg`, `congrFun'`, `congr`, `congrFun`, `funext`, `implies_congr`, `forall_congr`, `propext`, `Eq.mpr`,
`Eq.mp`, `id`, `True.intro`, `False.elim`), every realized constant the tests reach, and every `@[congr]` lemma
whose function the slice holds (a unit test checks the rule: with `ite` but not `ite_congr`, LeanForth would
silently take another route). From SL3a the tests run on the whole Init export and its format-4 data, as
`make reference-elab-data` builds them, because a slice's default set is not Lean's.

## 5. Reuse, new words, consumers, sizes

**Reused**, all on main:
- Meta core: `lf-meta-defeq`, `lf-meta-whnf-r`, `lf-meta-whnf-d`, `lf-whnf-core`, `lf-infer`, `lf-instantiate!`,
  `lf-meta-eqv`, `lf-meta-at`, `lf-commit-when`, `lf-must`, `lf-meta-fun-info`;
- instances: `lf-try-synth`, `lf-synth-instance?`;
- index: `lf-dtree-insert`, `lf-dtree-builder!`, `lf-dt-path`;
- telescopes: `lf-forall-meta-telescope-reducing`, `lf-mk-lambda-fvars`, `lf-mk-forall-fvars`, `lf-with-local-decl`;
- term builders: `lf-mk-eq-refl`, `-eq-symm`, `-eq-trans`, `-congr-arg` (with Lean's fusion of nested `congrArg`),
  `-eq-mp`, `-eq-mpr`, `-expected-type-hint`, `-false-elim`, `-app-m`, `-decide`;
- goal words: `lf-goal-replace-target-eq`, `-defeq`, `lf-goal-assert`, `lf-goal-try-clear`, `lf-goal-intro-n`;
- tactic layer: `lf-with-location`, `lf-tac-elab-term`, `tac-shape-rules`, `lf-handover`;
- term scans: `lf-term-holds-node?` (`term-find.fs:61`); `dag-walk.fs` as the base of `transform.fs`;
- `lib/`: `memo.fs` (caches, per-lemma checks), `htab.fs`, `frame.fs` (the walk, no host recursion), `sort.fs` (the
  stable priority sort), `slab.fs`, `runs.fs`, `xt-table.fs` (simprocs by name), `bigint.fs`.

**New words**, with their stack effects, homes and slices: appendix F.

**Copies replaced.**
- `abm-deeper` (`app-builder.fs:309`) is rebuilt on `lf-with-new-depth`.
- `getUnify` and `getMatch` share one node visitor.
- `meta-tactic/delta.fs`'s walk (`dag-walk.fs`, Lean's `Core.transform`) moves onto `transform.fs` where binders
  allow.
- No sort, table or walk is written anew.

**Consumers** (who else calls these layers, with the evidence): appendix G; summary in section 0.

## 6. Slices

Every slice ends in `bin/leanforth check --env ENV --elab-data DATA FILE.lf` on its `.lf` files, run beside a
pinned-Lean twin (`NAME.lean`) and wrong twins (`NAME-wrong.lean`, which Lean rejects). The folder
`tests/front/tactics/simp-X/` holds `test.fs`, `check.py`, `steps.golden` and `faults.d/simp-X.toml`. A slice also
brings its TACTIC_STATUS.md rows and LANGUAGE_REFERENCE.md entries, passes `make cover-changed`, and sweeps each new
word.

Tokens come from measured history: a slice costs 1.0-1.65M all in. A slice that opens a library layer has twice run
over its implementer ceiling, and E1 was under-estimated by 25%, so such slices are priced above the range.

| Slice | Command at the end, node for node with its twin | Contains | Forth | Tokens | Needs |
|---|---|---|---:|---:|---|
| **SD-a** | the check reads format 4's `congr` records and `defeq` tags from Init's data and refuses each planted fault | writer rebased for two kinds; `simp-data.fs` | 350 | 0.9-1.1M | `elab-data.fs` claim |
| **SL1a** | `by-simp-only[ ' h ]` and `[ ' Nat.add_zero ]` on first-order goals and `at[ h ]`: `h : f 6 = 0` rewriting `f (2 * 3)`; `n + 0 + 0 = n`; `p` from `h : p` is `h`; `True` by `True.intro`; no progress refused | the settings layer; keys by origin; `getMatch` with extra arguments; loop, cache, steps and depth; rewriting with Eq lemmas and hypotheses (instances, no conditions); congruence kinds; the dsimp guard; target words; `at[ h ]` with `replaceLocalDeclDefEq`; the user's rfl rule; builders | 2,300 | 2.0-2.4M | SD-a; sole claim on `meta-config.fs`, `whnf.fs`, `defeq.fs`, `discr-keys.fs`, `discr-tree.fs`, `app-builder.fs`, `meta-must.fs`, `fun-info.fs`, `assert.fs` |
| **SD-b** | `scripts/export-elab.sh` writes full format 4 with realized records; EX's export holds the helpers; the check refuses each fault | the rest of SIMP_DATA's SP1a; `refl`, `symm` (Q3) | 700 | 1.2-1.5M | runs beside SL1a-SL2 |
| **SL1b** | first a report: what Init's 898 `simp`/`simp [..]` proofs use; then `by-simp-only[ ]` under `∀`, `→`, `fun`, `let`, `match`, `x : Fin (n + 0)` as `id hp`, `↔`/`¬`/`∀` hypotheses, `at[ * ]` | the measurement (pinned Lean's simp traces over those proofs); binders; `simpMatch`; `dsimpImpl` on `transform.fs`; local preprocessing | 1,100 | 1.4-1.7M | SL1a |
| **SL2** | `decide p = decide q` from `' h` (library `Decidable.decide.congr_simp`); through `if` (`ite_congr` with `fun a => h`); conditional lemmas | `@[congr]`, automatic congruence, realized constants, the default discharger (equation hypotheses on E3's `unifyEq?`, else unsupported) | 1,250 | 1.5-1.8M | SL1b, SD-b |
| **SL3a** | `by-simp` on Init's one-liners: K of 898, node for node; `-' foo`, `'*`, `' foo !pre` | the default set (lazy branches, per-lemma checks, `simp_left_out`), unfolding, item kinds, simproc interface, the 5 root simprocs | 1,150 | 1.5-1.8M | SL2, SD-b, EX |
| **SL3b** | K of 898 rises: Nat, Int, Fin literals | three families, table-driven | 850 | 1.1-1.3M | SL3a |
| **SL3c** | UInt, SInt, Char, String, BitVec, List, Array literals | seven families | 1,000 | 1.1-1.3M | SL3a |
| **SL3d** | `simp only [Nat.lt_irrefl, ..]` with `THM._simp_1_k`, a def's `NAME._simp_k`; `[← foo]`; `[Nat.add_comm]`; `by-simp-rw[ ]` | bracket preprocessing with helpers made as the list is read, `←`, `isPerm`, `acLt`, Mathlib's `simp_rw` | 700 | 1.2-1.5M | SL3a |
| **SL4** | `' h by-simpa-using`, `by-simp-all`, `by-dsimp-only[ ' f ]`; Init's one-liners of each, K of N | the six simpa words, `simp_all`, the dsimp words | 560 | 1.1-1.3M | SL3a |
| **SL5** | `config[ +contextual ]`, `+decide`, `+instances`, `maxSteps`; `by-simp?` prints both lines | options, `mkSimpOnly` | 590 | 1.0-1.2M | SL4 |
| **SL6** | `config[ +arith ]`, `+ground` | `Arith/`, `seval` | 1,130 | 1.3-1.6M | SL3a |

**Totals: about 11,500 lines of Forth (11,700 by this table, 11,200 by section 1's); 15.3-18.5M tokens, nearer
17-19M if the first slices run as E1 did.** If SL1a
passes 1,600 lines, `at[ h ]` and `replaceLocalDeclDefEq` (about 300) move to SL1b.

**Value per token** (review): Init has 17 `simp only` one-liners and 898 `simp`/`simp [..]` (279 bare, 619 with
brackets).
- **What we know.** Their default lemmas come already preprocessed as library helpers through EX, and the set has no
  `←` or perm lemma, so SL3d is not needed for them. They need the root and Nat simprocs, the congruence kinds and the
  59 `@[congr]` lemmas (`reduceIte` is named 123 times in Init's source).
- **What was not measured.** How many go under binders or use conditional lemmas, and how many bracket items need a
  helper or are perm lemmas.
- **What the measurement decides.** SL1b's first task measures this. If most of the 898 need neither binders nor
  discharging, SL3a moves before SL1b's binder work and SL2's discharger.

**Wrong twins and faults** (a twin is a text pinned Lean rejects that LeanForth must refuse). SL1a: twins
`w-no-progress`, `w-head-only` (a goal only head-only keys close), `w-at-self`, `w-unused-rule-closes`; faults
`head-keys-full`, `at-erases-bracket-h`, `post-before-pre`, `cache-ignored`, `congrfun-for-congrfun'`,
`rfl-step-kept`, `step-check-after-increment`, `settings-not-restored`, `kinds-all-eq`, `dsimp-guard-off`. SL1b:
`w-binder-skipped`, `w-dsimp-arg`; `forall-as-arrow`. SL2: `w-congr-first`, `w-discharge-depth-3`;
`congr-rank-reversed`, `cast-kept`, `realized-in-user-file`. SL3a: `w-erased-used`, `w-left-out-used`;
`priority-ascending`, `star-after-key`, `simproc-skipped`, `item-as-term`. SL3d: `w-perm-loops`, `w-helper-name`, a
def twin (`NAME._simp_k`); `perm-unchecked`, `helper-only-when-used`, `aux-not-deduplicated`. SL4:
`w-simpa-default-defeq`, `w-dsimp-non-rfl`.

**Parallel work.** SL1a holds the most shared Meta files for its whole run: no other branch edits `meta-config.fs`,
`whnf.fs`, `defeq.fs` or `discr-keys.fs` until it merges. SD-b (scripts and `simp-data.fs`) runs beside SL1a to SL2.
SL3b and SL3c touch only new files under `simp/simprocs/` and run beside anything. SL3a and SL5 edit
`tactic-syntax.fs`, which TB2's batches with new shapes also edit, so not at the same time as one of them. E2 and E3
do not meet simp's files; SL2 uses E3's `unifyEq?` once merged.

## 7. Trust and gates

Nothing here changes `src/kernel`, `src/core` or the import path. Every simp result is a term the kernel checks at
`end NAME`; every helper or realized constant is a theorem the kernel checks (as a library constant, or before the
theorem), never an axiom. Gates: [import]/[format] for format 4 approved 2026-11-18, EX under it; the `refl`/`symm`
kinds and realized records are question 3; the settings layer is front-end Meta code (question 4); spellings question
1. Axioms: `propext` (every `↔` rewrite) and, through lemmas, `Classical.choice`, listed by the axiom report.

**Where LeanForth could accept what Lean rejects, and the guard.** (1) Another route than Lean's: wrong keys
(head-only versus full), a bracket hypothesis wrongly erased, a missing `@[congr]` lemma, a skipped simproc or
left-out lemma, a dependent argument not `dsimp`ed. Keys and origins are ported exactly (twins `w-head-only`,
`w-at-self`); unported simprocs that match, left-out records reached, unported congruence kinds, arguments needing
`dsimp` before SL1b and unported Config values answer unsupported. (2) A different normal form a later step accepts:
the step log's goals are compared after each step. (3) A limit Lean hits and LeanForth does not: steps exact, depth
question 5. (4) `dsimp` with a non-rfl lemma: rfl-only by the tags, twin `w-dsimp-non-rfl`. (5) simpa at default
transparency: twin `w-simpa-default-defeq`. (6) A user lemma's rfl flag: Lean's declaration-time rule or unsupported.
Unsupported at first: what each slice lists; `(disch := ..)`, `simp!`, `+suggestions`.

## 8. Risks, performance, what was not verified

- **Cost grows with the library.** A lookup walks the term's keys; the candidates under a busy root (1,304 under `Eq`
  in Init) are each unified, as in Lean. Lazy roots, branches parsed at first use and one check per lemma (SIMP_DATA
  Q4); every branch built would be about 7 MB for Init, 154 MB for Mathlib. SL3a measures `by-simp` per call against
  pinned Lean on the 898; the nightly run keeps the figure.
- **Re-entrancy.** simp calls itself; its state is on frames in the checker context, no module variable. Under `--jobs`
  each context builds its own lazy branches unless a shared read-only Init tree is made (plan 9.4.8p decides).
- **The settings layer** touches the files every front-end branch reaches; its defaults must keep every existing dump
  byte-identical (the whole tier with every pinned-Lean comparison).
- **Not verified:** which realized constants LeanForth's own Init export holds (the reviewer counted `.olean` files);
  the share of the 898 needing binders, conditions or congruence (SL1b's first task); the cost of loading the whole
  Init export with format 4; which LeanForth spelling elaborates exactly Lean's `:= rfl`; the Mathlib form counts are
  a text count (comment blocks excluded, strings not).

## Changes after review

1. Must-change items 1-9: keys by origin; dsimp's guard in SL1a and the port in SL1b; the settings layer in SL1a; the
   congruence kinds in SL1a; origins exact with `w-at-self`; a real `replaceLocalDeclDefEq`; the helper-name rule; the
   library's realized constants from data, declared in the user's file only when Lean does so; the user's rfl rule.
2. Should-change items: the builder shortcuts tested (r5 x1, x2); `tryTheoremWithExtraArgs?` and
   `resolveBinderNameHint`; exact limits; list items resolved by kind; sizes at 2.1 and 16-19M; value per token
   (measure first, SL3d after SL3a); `abm-deeper` at `app-builder.fs:309`; 500-539 confirmed free.
3. Coordinator's decisions A-F: SD-a and SL1a cut as the review proposed, with my count (2,300, not 1,400, and a cut
   line); the rest of SD (SD-b, with EX) beside SL1a-SL2; slices after SL1a ordered by value per token; realized
   constants from data; `!pre`; `by-simp[ ]` on the rules shape; sizes re-estimated; a one-page section 0; the new
   words and consumers moved to appendices F and G.
4. Not applied here: the 300-339 range at SIMP_DATA.md:229 is outside this file, so the commit that adds this design
   corrects it.

## Appendix A. Counts

**Mathlib's simp forms** (2026-11-24, a script over `Mathlib/**/*.lean`). It counts the keyword at a line start or
after `by`, `;`, `<;>`, `(`, `=>`, `·`, `try` or `|`, with comments dropped.

| Form | Uses | Form | Uses |
|---|---:|---|---:|
| `simp [..]` | 32,778 | `simpa using e` | 7,332 |
| `simp only [..]` | 23,915 | `simpa [..] using e` | 5,737 |
| `simp` | 21,710 | `simpa only [..] using e` | 3,561 |
| `simp only [..] at` | 3,688 | `simpa`, `simpa [..]`, `simpa only [..]` | 1,483, 1,469, 818 |
| `simp at`, `simp [..] at` | 566, 490 | `dsimp`, `dsimp [..]`, `dsimp only [..]` | 2,828, 1,792, 778 |
| options (any form) | about 880 | `simp_all`, `[..]`, `only [..]` | 1,177, 667, 257 |
| `simp_rw` | 8,975 | totals `simp`/`simpa`/`dsimp`/`simp_all` | 84,265/20,530/6,531/2,115 |

`simp only` in all its forms is 27,970 uses (23% of the family's 122,416), and plain `simp` about 56,200 (46%). Inside
the lists: `←` appears in 8,712 lines, `*` in 1,003, `-lemma` in 484 and `↓` in 251. Options: `+contextual` 613,
`+instances` 171, `+unfoldPartialApp` 67, `+decide` 24, `+arith` 14; `(disch := ..)` 52; `simp?` 18.

**Init's one-line simp proofs** (`:= by simp...` at a line's end): 915. Of these, 279 are bare `simp`, 619 are
`simp [..]` and 17 are `simp only [..]`.

**Lean code lines:**

| File | Lines | File | Lines |
|---|---:|---|---:|
| Types | 650 | Simpa | 136 |
| Main | 709 | SimpAll | 109 |
| Rewrite | 503 | Simproc | 333 |
| SimpTheorems | 522 | simproc families | 1,451 |
| CongrTheorems | 350 | Arith | 599 |
| ACLt | 141 | SimpTrace | 151 |
| Transform | 183 | DiscrTree/Main | 367 |
| Elab Simp | 632 | | |

## Appendix B. Lean source notes (Lean 4.35.0, `src/lean/Lean/`)

**Meta/Tactic/Simp/Main.lean**

| Function | Line |
|---|---:|
| `simpLambda`, `simpArrow`, `simpForall`, `simpLet` | 328, 333, 365, 436 |
| `dsimpImpl` | 517 |
| `visitFn`, `congrDefault` | 531, 545 |
| `trySimpCongrTheorem?`, `congr` | 586, 637 |
| `simpStep`, `simpLoop` (limits 679-687), `simpImpl` | 657, 677, 714 |
| `simpTargetCore`, `applySimpResult` | 781, 807 |
| `simpGoal` (erase 884, no progress 908-910), `dsimpGoal` | 874, 929 |

**Meta/Tactic/Simp/Types.lean**

| Function | Line |
|---|---:|
| `mkIndexConfig`, `mkMetaConfig` | 141, 162 |
| `andThen` | 374 |
| builders | 598-620 |
| `congrArgs` | 649 |
| primed builders | 682-726 |
| `simpAppUsingCongr` | 732 |
| `mkCongrSimp?`, `tryAutoCongrTheorem?` | 773, 807 |

**Meta/Tactic/Simp/Rewrite.lean**

| Function | Line |
|---|---:|
| `synthesizeArgs` | 58 |
| `tryTheoremCore` (binder-name hint 152) | 115 |
| `tryTheoremWithExtraArgs?`, `tryTheorem?` | 178, 187 |
| `rewrite?` | 207 |
| `simpMatch` | 376 |
| defaults | 536-547 |
| `dischargeDefault?` | 637 |

**Other files**

| File | Function | Line |
|---|---|---:|
| SimpTheorems.lean | `simpGlobalConfig` | 282 |
| | `preprocess` | 319 |
| | `mkSimpTheoremFromConst` (helper, rfl flag) | 453 (465-469) |
| | `noIndexAtArgs` | 470, 473, 502, 509 |
| CongrTheorems.lean | `getCongrSimpKinds` | 178 |
| | `mkCongrSimpCore?` | 296 |
| | reserved names | 405-446 |
| AppBuilder.lean | shortcuts | 630-660 |
| Replace.lean | `replaceLocalDeclDefEq` | 110 |
| CoreM.lean | `mkUniqueName` | 95-147 |
| DefEqAttrib.lean | `inferDefEqAttr` | 159 |
| Elab/Tactic/Simp.lean | items | 336-370, 488 |
| | origins | 363, 370, 400-401 |
| | `simpOnlyBuiltins` | 512 |
| | `mkSimpContext` | 554 |
| Init/Tactics.lean | `trivial`'s `simp` rule | 1197 |

## Appendix C. Probes (pinned Lean 4.35.0)

The author's probes p1-p3 are in the scratch folder `simp-probes/`; the reviewer's r1-r5 are in `review-simp/`.

| Probe | Lean's result |
|---|---|
| p1 `n + 0 + 0 = n` by `simp only [Nat.add_zero]` | `of_eq_true (eq_self n)` |
| p1 `f a = f b` by `simp only [h]` | `of_eq_true (Eq.trans (congrFun' (congrArg Eq (congrArg f h)) (f b)) (eq_self (f b)))` |
| p1 `a + b = b + a` by `simp only [Nat.add_comm]` | `.. (congrArg (Eq (a + b)) (Nat.add_comm b a)) ..` |
| p1 `decide p = decide q` by `simp only [h]` | `.. (Decidable.decide.congr_simp p q (propext h)) ..` (a library constant, r3) |
| p3 `p 0` by `simp only [h]`, `h : ∀ x, p x ↔ x = 0` | `of_eq_true (Eq.trans ((fun x => propext (h x)) 0) (eq_self 0))` |
| p2 `3 < 5` by `simp` | `of_eq_true (eq_true_of_decide (Eq.refl true))` |
| r1 a1 `f (2 * 3) = 0` by `simp only [h]`, `h : f 6 = 0` | `of_eq_true (Eq.trans (congrFun' (congrArg Eq h) 0) (eq_self 0))` |
| r4 o6 `p (n + 0) x`, `x : Fin (n + 0)`, by `simp only [Nat.add_zero]` | `id hp` |
| r5 x1 `p` by `simp only [h]`, `h : p` ; x2 `True` by `simp only []` | `h` ; `True.intro` |
| r5 x3 `simp only [h] at h h2; exact h` | `h : True`; Lean refuses (type mismatch) |
| r2 v1 helpers with an unused bracket lemma; r3 a def | used helper `_simp_1_3`; `d2._simp_1` |
| r5 `myrfl := rfl` ; `myrfl2 := (rfl)` | no step ; step `myrfl2 n` |
| p1 `simp only []` on `n = n + 1` ; `simp?` | `` `simp` made no progress `` ; `Try this: [apply] simp only [Nat.add_zero]` |

## Appendix D. Errors kept (Lean's text; codes 500-539)

| Lean (file:line) | Text |
|---|---|
| Main.lean:684 | `` `simp` failed: maximum number of steps exceeded `` |
| Main.lean:910 | `` `simp` made no progress `` |
| Main.lean:959 | `` `dsimp` made no progress `` |
| SimpAll.lean:156 | `simp_all made no progress` |
| SimpTheorems.lean:309-564 | invalid simp theorem: an equivalent equation; `←` on `≠`, `¬` or a rule to `True`; not a proposition; an unexpected kind; no exposed body |
| Elab/Tactic/Simp.lean:278-294 | `←` on a definition or let variable; a variable that is not a proposition |
| Elab/Tactic/Simp.lean:559-561 | `simp_all` or `dsimp` with a discharger |
| Simpa.lean:99, and after simplification | `Occurs check failed`; `Type mismatch: After simplification, term` |
| Types.lean:692 | `failed to build congruence proof, function expected` |
| (depth) | Lean's maximum recursion depth message |

## Appendix E. Simp.Config in 4.35.0 (Init/MetaTypes.lean:252-417)

| Setting | Default |
|---|---|
| `memoize`, `zeta`, `beta`, `eta`, `iota`, `proj`, `dsimp`, `failIfUnchanged`, `index`, `implicitDefEqProofs`, `zetaUnused`, `catchRuntime`, `zetaHave`, `letToHave`, `congrConsts`, `bitVecOfNat`, `warnExponents` | on |
| `etaStruct` | `.all` |
| `contextual`, `singlePass`, `decide`, `arith`, `autoUnfold`, `ground`, `unfoldPartialApp`, `zetaDelta`, `suggestions`, `locals`, `instances` | off |
| `maxSteps` | 100000 |
| `maxDischargeDepth` | 2 |

`DSimp.Config` (:154) has the dsimp subset with the same defaults.

## Appendix F. New words

**New words** (public, documented in the file header, tested in the file's unit test with a refusal sweep):

| Word | Home | Slice |
|---|---|---|
| `lf-meta-iota!`, `lf-meta-proj!` (`.no`, `.yes`, `.yesWithDelta`), `lf-meta-zeta!`, `lf-meta-zeta-delta!`, `lf-meta-beta!` ( flag -- ), saved and restored with `lf-meta-config`; `lf-with-simp-keys`, `lf-with-simp-index`, `lf-with-simp-meta` ( i*x xt -- j*x ) | `meta-config.fs` (honoured in `whnf.fs`, `defeq.fs`, `discr-keys.fs`) | SL1a |
| `lf-dt-path` gains `( type head-only? -- k n outcome )`; `lf-dtree-match`, `lf-dtree-match-extra ( e tree out -- outcome )`; throwing faces `lf-dt-get-match`, `-match-extra` | `discr-keys.fs`, `discr-tree.fs` | SL1a |
| `lf-with-new-depth ( i*x xt -- j*x )` (throw-safe; `abm-deeper`, `app-builder.fs:309`, on it) | `meta-must.fs` | SL1a |
| `lf-param-fwd-deps? ( m i -- flag )`, `lf-param-back-deps ( m i -- run )`, `lf-param-inst? ( m i -- flag )`; `lf-congr-simp-kinds ( f n -- kinds )` | `fun-info.fs`, new `congr-thms.fs` | SL1a |
| `lf-mk-congr-fun ( h a -- h' )`, `lf-mk-congr ( h1 h2 -- h )`, `lf-mk-of-eq-true`, `lf-mk-eq-true`, `lf-mk-eq-false`, `lf-mk-prop-ext ( h -- h' )` with Lean's shortcuts (SL1a); `lf-mk-funext`, `lf-mk-imp-congr`, `lf-mk-forall-congr`, `lf-mk-iff-of-eq` (SL1b) | `app-builder.fs` | SL1a, SL1b |
| `lf-meta-equal? ( a b -- flag )` (Expr.equal); `lf-goal-replace-local-decl-defeq ( goal fvar type -- goal' )` | `term-eqv.fs`, `meta-tactic/assert.fs` | SL1a |
| `/simp-result`; `lf-simp-trans ( r1 r2 -- r )`, `lf-simp-proof ( r -- h )`, `lf-simp-congr-fun ( r a -- r' )`, `lf-simp-congr-arg ( f r -- r' )`, `lf-simp-congr ( r1 r2 -- r )`, `lf-simp-extra-args ( r args -- r' )` | `simp/types.fs` | SL1a |
| `lf-simp-methods ( pre post dpre dpost disch -- m )`, `lf-simp ( e ctx m -- r )`, `lf-simp-visit ( e -- r )` (the nested `simp`); `lf-dsimp ( e ctx m -- e' )` (SL1b) | `simp/main.fs` | SL1a |
| `lf-simp-try-theorem ( e thm n -- r true \| false )`, `lf-simp-rewrite? ( e tree rfl-only -- r true \| false )`, `lf-simp-discharge-default ( p -- h true \| false )` (SL2) | `simp/rewrite.fs` | SL1a |
| `lf-simp-set-new ( -- set )`, `lf-simp-set-add ( set e origin post inv prio -- set )`, `lf-simp-set-erase`, `lf-simp-rfl? ( h -- flag )`; `lf-simp-preprocess ( h type inv global? -- pairs )` (SL1b, SL3d) | `simp/theorems.fs` | SL1a |
| `lf-goal-simp-target ( goal ctx m -- goal' \| 0 )`, `lf-goal-simp ( goal ctx m fvars target? -- fvars' goal' \| 0 )`; `lf-goal-dsimp`, `lf-goal-simp-all` (SL4) | `simp/goal.fs` | SL1a |
| `lf-transform ( e pre post flags -- e' )` (opens binders) | new `transform.fs` | SL1b |
| `lf-mk-congr-simp ( f -- thm true \| false )`, `lf-congr-simp-for-const ( d levels -- thm true \| false )`; `lf-simp-try-congr-thm`, `lf-simp-auto-congr ( e -- r true \| false )` | `congr-thms.fs`, `simp/congr.fs` | SL2 |
| `lf-simp-args ( i kind -- ctx m )` (items by kind); `lf-simproc: ( "name" pre? dsimproc? -- )` | `simp/args.fs`, `simp/simprocs.fs` | SL3a |
| `lf-aux-lemma ( kind type value levels -- name )` (mkAuxLemma with mkUniqueName); `lf-ac-lt ( a b mode -- flag )` | `handover.fs`, new `ac-lt.fs` | SL3d |

## Appendix G. Consumers

**Consumers.** The evidence is a grep of Lean's modules that call `Simp.main`, `simpTarget` or `Simp.Context` outside
`Simp/`.

| Later work | Calls |
|---|---|
| Lean's `split`, `unfold`, `split_ifs` (Mathlib, 1,416 uses) | `lf-simp` with custom pre; `simpMatch` |
| `acyclic` (E5), equation theorems and wf preprocessing (FE8) | `lf-simp`, `lf-aux-lemma` |
| `norm_cast`, `push_cast` (883 + 372); `conv => simp` | `lf-simp` with a named set |
| `norm_num`, `field_simp` (S8), `ring_nf` (S7) | `lf-simp-methods`, `lf-dt-get-match` |
| `congr`, `convert`, `congr!` (2,999 + 1,517) | `congr-thms.fs` |
| `rw` with `↔` rules, `omega`'s helper (S4); `decide`, coercions (FE4a), `delta` | `lf-mk-prop-ext`, `lf-aux-lemma`; `lf-transform` |
| `by-trivial`'s last rule `simp` (Init/Tactics.lean:1197; unsupported today, TACTIC_STATUS.md:52), so `by-exists[ ]` | plain simp (SL3a) |
| `aesop`, `linarith`'s preprocessing, `grind` | the simp core, later |
