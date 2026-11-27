# Tactic inventory: which Lean tactics Mathlib uses, and how often

Measured 2026-11-21 on the Mathlib source in `.tools/mathlib/mathlib4` (commit `56a0058`,
2026-10-13, Lean 4.35.0; 8,624 files), read only. Purpose: order the tactic work by real
use, and size it (owner, 2026-11-21: "complete most of them this week").

## How it was counted

`.claude/work/tactics/count.py` (untracked working script) collects every keyword that Lean,
Mathlib and Mathlib's packages declare as a tactic (540), then counts each keyword where a
tactic can start: at the start of a line (after bullets), after `by`, `;`, `<;>`, `(` or `=>`.
It is a text count, not a parse: `have`, `let`, `show` and `calc` also count where they are
terms, and a tactic inside a macro is counted once. Read the shares as good to a few points.
592,556 uses were counted; 564,299 after removing six keywords that are not proof steps
(`_`, `match`, `if`, `module`, `tactic`, `trace`).

## Result by class

| Class | What it means | Keywords | Uses | Share |
|---|---|---:|---:|---:|
| have | LeanForth has a word today (`by-exact`, `by-apply`, `by-intro`, `by-intros`, `by-rfl`, `by-rw`, `by-induction`, `by-constructor`, `by-left`, `by-right`, `by-assumption`, `by-clear`, `by-exfalso`, `by-decide`, `by-case`) | 15 | 208,319 | 36.9% |
| small | A structural tactic: in Lean a macro or a short function over the same goal operations we already port (`have`, `refine`, `obtain`, `rcases`, `rintro`, `cases`, `by_cases`, `use`, `subst`, `calc`, the goal combinators, ...) | 84 | 184,079 | 32.6% |
| simp | `simp` and what is built on it (`simpa`, `simp_rw`, `dsimp`, `simp_all`, `norm_cast`, `norm_num`, `split_ifs`, ...); LeanForth has `by-simp-only[ ]`, `by-simp` and `by-simp[ ]` with `at[ ]` since 2026-11-26 (57 of Init's 640 one-line simp proofs node for node, `make reference-simp-init`) | 15 | 114,872 | 20.4% |
| engine | A decision procedure or search of its own (`ext`, `grind`, `congr`/`convert`/`gcongr`, `lia`/`omega`, `aesop`, `ring`, `linarith`, `fun_prop`, `positivity`, ...) | 43 | 53,891 | 9.6% |
| unclassed | 162 rarely used keywords, none above 140 uses | 162 | 3,138 | 0.6% |

What follows from it:

1. **About 100 keywords carry 69% of all uses and need no engine** (have + small). They are the
   week's target: 84 small tactics, in batches.
2. **`simp` is the one engine that matters most**: one fifth of all uses, and `simpa`, `simp_rw`
   and `dsimp` come with it. `ring` is 0.3%, `linarith` 0.1%, `omega` under 0.1% (Mathlib now
   writes `lia` and `grind` where it once wrote `omega` and `norm_num`).
3. **37 keywords are 90% of uses, 59 are 95%, 115 are 99%.** The other 400 keywords do not
   matter for a first pass.
4. **A keyword is not the whole tactic.** "have" means the word exists on the forms tested
   today (Init slices). On Mathlib every tactic that takes a term (`exact e`, `rw [h]`,
   `refine e`) is only as strong as the term elaborator: implicit arguments, instance search,
   coercions, notation. That is slices MF and FE of the plan, and it limits real coverage more
   than the tactic count does.
5. **`simp` needs data the export does not carry**: which lemmas are marked `@[simp]`, with
   their priorities. It must come from Lean with the elaboration data, as instances do.

## What one small tactic costs today, and the change

`by-exfalso` (commit 9c9b8389) is 3 lines of Forth over one library word, yet its commit
touched 13 files and 251 lines: its own test directory (`check.py`, `test.fs`, four `.lf`
files, `steps.golden`), a fault file, the registry golden, the quality baseline; and it paid
an architect step, a Forth review, a tier and a done check. Tactic files are 19 to 92 lines
(16 files, 607 lines in all): the library works, the cost is everything around it.

Process for the batches (plan row TB2 and after):

1. **One branch, 8 to 12 tactics of one family**, one word list, one Forth review, one tactic
   tier, one done check with one checklist. Target cost: what one tactic cost before.
2. **A table of cases, not a directory per tactic**: one row is a theorem, its proof script
   and the expected outcome (accepted, or Lean's error); the `.lf` file, the Lean twin, the
   wrong twin and the unit test's goal counts are generated from the row and compared with
   pinned Lean by one command. Built once, before the first batch.
3. **Standard planted faults per tactic from a template** (action skipped, wrong goal kept,
   tag lost), generated with the row, plus hand-written ones only for a word with logic.
4. **Macros as macros**: a tactic that is a macro in Lean (`exfalso`, `rwa`, `exacts`,
   `by_contra`, `use` ...) is a colon definition over existing tactic words, with Lean's
   source line cited, and needs no new library word.
5. **Families, in order of use**: (a) `have`, `suffices`, `show`, `change`, `replace`, `refine`,
   `let`, `specialize`, `exacts`, `rwa`; (b) `cases`, `rcases`, `obtain`, `rintro`, `by_cases`,
   `subst`, `injection`, `contradiction`, `absurd`, `by_contra`; (c) combinators: `try`,
   `first`, `repeat`, `all_goals`, `any_goals`, `swap`, `<;>`, `case`, `next`; (d) `symm`,
   `trans`, `funext`, `use`, `exists`, `unfold`, `delta`, `revert`, `generalize`, `rename`,
   `trivial`, `calc`; then `simp` (designed in parallel), `ext`, `congr`, `ring`.

Small tactics 1 (2026-11-26, branch `small-tactics-1`; tests in
`tests/front/tactics/batch-small-1/`, each term node for node pinned Lean's): `funext`
(`by-funext`, `by-funext[ x .. ]`; 989 uses), `infer_instance` (`by-infer-instance`; 2,842),
`rename` (`T by-rename: h`; 197), `generalize` (`e by-generalize: x`, `e by-generalize-eq: h x`,
each with `at[ ]`; 209), `skip` (`by-skip`), `done` (`by-done`) and `iterate n`
(`n by-iterate ... by-end`, `batch-small-1b/`); their limits are in the language reference's
section D.11. Looked at and left for later: `with_reducible` (a scope over a block, which the
runner's block loop cannot put back when an error leaves the block), `subst_eqs` (`cases` on
each `Eq` hypothesis, an indexed family's case split, slice E4), `haveI`/`letI` (the term
elaborator's zeta let, not ported).

Small tactics 2 (2026-11-26, branch `small-tactics-2`; tests in
`tests/front/tactics/batch-small-2/`, each term node for node pinned Lean's, on the patterns
slice, which gained Nat's `Trans` instances): `calc` (`by-calc[ T1 e1 T2 e2 .. ]`: `=`, `≤`,
`<` chains mixed, a later step's first `_` ascribed the type before it, `?_` proofs as new
goals, the last step extended by a `calc.step` goal) and `with_reducible`,
`with_reducible_and_instances`, `with_unfolding_all` (`by-with-reducible ... by-end` and its
two siblings: blocks whose steps run at their transparency, put back however a step ends).
Left: `subst_eqs` and `haveI`/`letI` (as above), and calc's `throwCalcFailure` messages
(131 after a coercion is not found); limits in the language reference's section D.13.

## The table (keywords with 100 uses or more)

| # | Tactic | Uses | Running share | Class | Declared in |
|---:|---|---:|---:|---|---|
| 1 | `rw` | 84,918 | 15.0% | have | Lean |
| 2 | `simp` | 76,280 | 28.6% | simp | Lean |
| 3 | `exact` | 55,677 | 38.4% | have | Lean |
| 4 | `have` | 42,429 | 46.0% | small | Mathlib |
| 5 | `refine` | 26,506 | 50.6% | small | Lean |
| 6 | `let` | 21,323 | 54.4% | small | Mathlib |
| 7 | `rfl` | 20,489 | 58.1% | have | Lean |
| 8 | `apply` | 19,838 | 61.6% | have | Mathlib |
| 9 | `obtain` | 19,348 | 65.0% | small | Lean |
| 10 | `simpa` | 18,082 | 68.2% | simp | Lean |
| 11 | `ext` | 15,709 | 71.0% | engine | Lean |
| 12 | `intro` | 15,315 | 73.7% | have | Lean |
| 13 | `simp_rw` | 8,812 | 75.3% | simp | Mathlib |
| 14 | `rcases` | 8,764 | 76.8% | small | Lean |
| 15 | `rintro` | 8,616 | 78.3% | small | Lean |
| 16 | `dsimp` | 6,284 | 79.5% | simp | Lean |
| 17 | `induction` | 4,926 | 80.3% | have | Lean |
| 18 | `by_cases` | 4,910 | 81.2% | small | Lean |
| 19 | `rwa` | 4,774 | 82.0% | small | Lean |
| 20 | `grind` | 4,620 | 82.9% | engine | Lean |
| 21 | `cases` | 4,532 | 83.7% | small | Lean |
| 22 | `congr` | 4,325 | 84.4% | engine | Lean |
| 23 | `constructor` | 3,564 | 85.1% | have | Lean |
| 24 | `suffices` | 3,536 | 85.7% | small | Mathlib |
| 25 | `calc` | 3,039 | 86.2% | small | Lean |
| 26 | `convert` | 2,999 | 86.8% | engine | Mathlib |
| 27 | `infer_instance` | 2,842 | 87.3% | engine | Lean |
| 28 | `classical` | 2,800 | 87.8% | small | Lean |
| 29 | `use` | 2,799 | 88.3% | small | Mathlib |
| 30 | `filter_upwards` | 2,326 | 88.7% | engine | Mathlib |
| 31 | `change` | 2,227 | 89.1% | small | Lean |
| 32 | `gcongr` | 2,092 | 89.4% | engine | Mathlib |
| 33 | `lia` | 2,012 | 89.8% | engine | Lean |
| 34 | `simp_all` | 1,938 | 90.1% | simp | Lean |
| 35 | `replace` | 1,924 | 90.5% | small | Mathlib |
| 36 | `cat_disch` | 1,840 | 90.8% | engine | Mathlib |
| 37 | `lift` | 1,663 | 91.1% | small | Mathlib |
| 38 | `show` | 1,659 | 91.4% | small | Mathlib |
| 39 | `aesop` | 1,649 | 91.7% | engine | aesop |
| 40 | `letI` | 1,619 | 92.0% | small | Mathlib |
| 41 | `convert!` | 1,517 | 92.2% | engine | Mathlib |
| 42 | `ring` | 1,451 | 92.5% | engine | Mathlib |
| 43 | `split_ifs` | 1,416 | 92.8% | simp | Mathlib |
| 44 | `set` | 1,359 | 93.0% | small | Mathlib |
| 45 | `subst` | 1,353 | 93.2% | small | Lean |
| 46 | `grw` | 1,105 | 93.4% | engine | Mathlib |
| 47 | `haveI` | 1,071 | 93.6% | small | Mathlib |
| 48 | `unfold` | 1,002 | 93.8% | small | Lean |
| 49 | `fun_prop` | 1,000 | 94.0% | engine | Mathlib |
| 50 | `funext` | 989 | 94.1% | small | Lean |
| 51 | `ext1` | 943 | 94.3% | engine | Lean |
| 52 | `positivity` | 903 | 94.5% | engine | Mathlib |
| 53 | `swap` | 901 | 94.6% | small | batteries |
| 54 | `norm_cast` | 883 | 94.8% | simp | Lean |
| 55 | `contrapose!` | 879 | 94.9% | small | Mathlib |
| 56 | `linarith` | 816 | 95.1% | engine | Mathlib |
| 57 | `choose` | 802 | 95.2% | small | Mathlib |
| 58 | `intros` | 756 | 95.4% | have | Lean |
| 59 | `symm` | 697 | 95.5% | small | Lean |
| 60 | `all_goals` | 673 | 95.6% | small | Lean |
| 61 | `specialize` | 636 | 95.7% | small | Lean |
| 62 | `congrm` | 633 | 95.8% | engine | Mathlib |
| 63 | `exacts` | 630 | 95.9% | small | batteries |
| 64 | `by_contra` | 628 | 96.1% | small | batteries |
| 65 | `trans` | 612 | 96.2% | small | batteries |
| 66 | `conv_rhs` | 598 | 96.3% | small | Mathlib |
| 67 | `case` | 559 | 96.4% | have | Lean |
| 68 | `nth_rw` | 555 | 96.5% | small | Mathlib |
| 69 | `conv_lhs` | 522 | 96.6% | small | Mathlib |
| 70 | `right` | 511 | 96.7% | have | Lean |
| 71 | `contrapose` | 507 | 96.7% | small | Mathlib |
| 72 | `by_contra!` | 492 | 96.8% | small | Mathlib |
| 73 | `erw` | 484 | 96.9% | small | Lean |
| 74 | `tauto` | 474 | 97.0% | engine | Mathlib |
| 75 | `by_cases!` | 473 | 97.1% | small | Mathlib |
| 76 | `congr!` | 463 | 97.2% | engine | Mathlib |
| 77 | `left` | 441 | 97.2% | have | Lean |
| 78 | `assumption` | 426 | 97.3% | have | Lean |
| 79 | `abel` | 415 | 97.4% | engine | Mathlib |
| 80 | `decide` | 411 | 97.5% | have | Lean |
| 81 | `tfae_have` | 408 | 97.5% | small | Mathlib |
| 82 | `cfc_tac` | 401 | 97.6% | engine | Mathlib |
| 83 | `push_cast` | 372 | 97.7% | simp | Lean |
| 84 | `wlog` | 358 | 97.7% | small | Mathlib |
| 85 | `nontriviality` | 356 | 97.8% | small | Mathlib |
| 86 | `clear` | 352 | 97.9% | have | Mathlib |
| 87 | `conv` | 344 | 97.9% | small | Lean |
| 88 | `fin_cases` | 340 | 98.0% | small | Mathlib |
| 89 | `apply_fun` | 330 | 98.0% | small | Mathlib |
| 90 | `linear_combination` | 317 | 98.1% | engine | Mathlib |
| 91 | `try` | 313 | 98.2% | small | Lean |
| 92 | `norm_num` | 310 | 98.2% | simp | Mathlib |
| 93 | `ring_nf` | 301 | 98.3% | engine | Mathlib |
| 94 | `revert` | 294 | 98.3% | small | Lean |
| 95 | `slice_lhs` | 278 | 98.4% | engine | Mathlib |
| 96 | `inclusion` | 268 | 98.4% | engine | Mathlib |
| 97 | `delta` | 260 | 98.5% | small | Lean |
| 98 | `contradiction` | 244 | 98.5% | small | Lean |
| 99 | `push` | 242 | 98.5% | simp | Mathlib |
| 100 | `trivial` | 242 | 98.6% | small | Lean |
| 101 | `ring1` | 232 | 98.6% | engine | Mathlib |
| 102 | `exact_mod_cast` | 225 | 98.7% | small | Lean |
| 103 | `field_simp` | 218 | 98.7% | simp | Mathlib |
| 104 | `generalize` | 209 | 98.7% | small | Lean |
| 105 | `field` | 205 | 98.8% | engine | Mathlib |
| 106 | `finiteness` | 202 | 98.8% | engine | Mathlib |
| 107 | `rename` | 197 | 98.8% | small | Lean |
| 108 | `cfc_cont_tac` | 173 | 98.9% | engine | Mathlib |
| 109 | `algebraize` | 169 | 98.9% | engine | Mathlib |
| 110 | `isBoundedDefault` | 162 | 98.9% | engine | Mathlib |
| 111 | `slice_rhs` | 149 | 99.0% | engine | Mathlib |
| 112 | `absurd` | 147 | 99.0% | small | batteries |
| 113 | `subsingleton` | 146 | 99.0% | engine | Mathlib |
| 114 | `bicategory` | 143 | 99.0% | engine | Mathlib |
| 115 | `introv` | 140 | 99.1% | unclassed | Mathlib |
| 116 | `bound` | 140 | 99.1% | engine | Mathlib |
| 117 | `exfalso` | 136 | 99.1% | have | Lean |
| 118 | `split` | 134 | 99.1% | small | Lean |
| 119 | `choose!` | 131 | 99.2% | unclassed | Mathlib |
| 120 | `omega` | 130 | 99.2% | engine | Lean |
| 121 | `nth_rewrite` | 129 | 99.2% | unclassed | Mathlib |
| 122 | `first` | 117 | 99.2% | small | Lean |
| 123 | `repeat` | 115 | 99.3% | small | Lean |
| 124 | `volume_tac` | 113 | 99.3% | unclassed | Mathlib |
| 125 | `subst_vars` | 112 | 99.3% | small | Lean |
| 126 | `nlinarith` | 108 | 99.3% | engine | Mathlib |
| 127 | `inhabit` | 104 | 99.3% | small | Mathlib |
| 128 | `aesop_mat` | 104 | 99.3% | unclassed | Mathlib |
| 129 | `hint` | 100 | 99.4% | unclassed | Mathlib |
| 130 | `borelize` | 100 | 99.4% | unclassed | Mathlib |
