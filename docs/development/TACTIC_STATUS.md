# Tactic status: what each tactic word covers, and what it still lacks

Owner, 2026-11-22: "There are a number of partly complete tactics, with more features that come
with other work, be sure to track those carefully." This is that ledger. One row per LeanForth
tactic word of plan row TB2 (and the older words where a gap is known): the Lean tactic and where
it is defined, what is not covered yet, what LeanForth answers there, and which piece of work
removes the gap. **A gap never accepts a proof**: it answers unsupported (exit 2) unless the row
says otherwise. Update this file in the branch that changes a row; when a piece in the last
column lands, every row naming it is revisited in that branch.

Sources: **Lean** is core Lean 4.35.0; **Batteries** and **Mathlib** are the libraries at the
pinned Mathlib commit `56a0058` (`.tools/mathlib/mathlib4`, Batteries under `.lake/packages`).
Their tactics are ported from their source; nothing of them is loaded at run time. Pinned core
Lean cannot run a Batteries or Mathlib tactic, so those rows are compared against an equivalent
core-Lean proof (column "Compared with").

Pieces named in the last column: **A** shapes (done), **B** holes `?_` `_` (done for refine, exact,
apply and have where unification fills them, batch 3b; the rows say what is left), **C** anonymous
constructor, **D** locations (done for hypotheses and the goal; written `at[ ]` since batch 3b), **E**
cases and patterns, **F** blocks, **G** macro word (done), **NL** name lists (done for intro, revert,
clear and rename_i, batch 3b; a list sits between its bracket word and `]` on one line), **FE2** `→`, `∀`, `fun` in statements
and terms, **REFL** Lean's `@[refl]` lemma set brought over with the elaboration data,
**NR** names resolved as Lean does everywhere (unknown identifier messages), **LC** a local
context that can hold one variable at two types (replaceLocalDeclDefEq).

| Word | Lean tactic (source) | Compared with | Not covered yet | Answer | Removed by |
|---|---|---|---|---|---|
| `by-change`, `by-show` | `change`, `show` (Lean) | Lean | a pattern left with an open metavariable (holes are read since batch 3b; change's own treatment of them is not ported) | 93 | change's holes |
| `by-change at[ ]` | `change … at h` (Lean) | Lean | another hypothesis depends on `h` | 93 | LC |
| `by-swap` | `swap` (Batteries) | `rotate_left`-style core twin | `pick_goal n`, `rotate_left/right` not built | no word | small batch |
| `by-specialize` | `specialize` (Lean) | Lean | holes are collected as goals (allowNaturalHoles, batch 3b), but a hypothesis applied to a term cannot be written yet (136) and a function hypothesis cannot be stated | 136 / untestable end to end | FE2 |
| `by-revert`, `by-revert[ ]` | `revert` (Lean) | Lean | a `let` variable (several names: `by-revert[ ]`, batch 3b) | 93 | LC |
| `by-delta` | `delta` (Lean) | Lean | several constants; a theorem's name; a let between the value's lambdas | 93 / 99 | small batch |
| `by-delta at[ ]` | `delta … at h` (Lean) | Lean | a hypothesis it would change | 99 | LC |
| `by-contradiction` | `contradiction` (Lean) | Lean | an empty or indexed-family hypothesis (any `≤` met first); two different constructors equated; `Nat.hasNotBit` | 99 | E |
| `by-trivial` | `trivial` (Lean) | Lean | whatever `by-contradiction` lacks; rules added by Mathlib | 99 | E; Mathlib's rules with the elaboration data |
| `by-absurd` | `absurd` (Batteries) | core twin | none known | | |
| `by-have:`, `by-have`, `by-let:`, `by-suffices:`, `by-replace:` | `have`, `let`, `suffices`, `replace` (Lean) | Lean | one name only; `_` as the name; binders and patterns; a `:= by` block; suffices' `from`/`by` forms; a `?_` or a `_` unification leaves in the value or type (Lean's refine makes it a goal; a `_` it fills works, batch 3b); a dependent let past the first variable | 99 / 93 / no form | F, E, refine_lift over by-refine |
| the same | | | a value naming a cleared or unknown hypothesis: refused, with error 76/99 where Lean says "Unknown identifier" | exit 4 or 2, message differs | NR |
| `by-have-goal:` | `have h : T` (Mathlib's `have` without a value) | core `refine` twin | as `by-have:` | | |
| `' r <-` in `by-rw[ ]` | `rw [← r]` (Lean) | Lean | `<-` on an `↔` rule | 99 | small batch |
| `by-rw[ ]`, `by-rewrite[ ]` | `rw`, `rewrite` (Lean) | Lean | a rule that leaves new goals or metavariables; a rule naming a definition (equation lemmas); `occs`/config; rw leaving `R x x` for a relation other than `=`, `↔` (Lean leaves the goal) | 99 / 93 | B, FE8, REFL |
| `at[ ]` | location (Lean) | Lean | `at[ * ]`; a constant's name among the names (Lean: error); a list across lines (458: owner's rule) | 99 / 458 | small batch |
| `by-rwa[ ]` | `rwa` (Lean) | Lean | what `by-rw[ ]` and `by-rfl` lack | 93 | REFL |
| `by-rfl` | `rfl` (Lean) | Lean | `x R x` for a relation other than `=`, `↔` (`@[refl]` lemmas); the `HEq` branch | 93 | REFL |
| `by-exacts[ ]` | `exacts` (Batteries) | core `exact` steps | none known beyond `by-exact`'s terms | | FE2, C |
| `by-cases:` | `by_cases` (Lean) | Lean | the unnamed form; instance priorities tied with the classical one; a decidable instance the data left out | no form / 93 | small batch; data |
| `by-contra:`, `by-contra` | `by_contra` (Batteries) | core twin | the pattern form; `by_contra!` (Mathlib, over `push_neg`) | no form | E; simp family |
| `by-symm` | `symm` (Lean) | Lean | relations other than `=`, `↔`, `≠`, `HEq`, `∧`, `∨` (`@[symm]` lemmas) | 99 | `@[symm]` set with the data (as REFL) |
| `by-and-intros` | `and_intros` (Lean) | Lean | none known | | |
| `by-next`, `by-case: _` | `next`, `case _` (Lean) | Lean | names after `next`; `case a \| b`; `@tag` | no form | NL, F |
| `by-intro:`, `by-intro[ ]` | `intro` (Lean) | Lean | patterns; type ascriptions `(h : T)` (several names and bare `intro`: `by-intro[ ]`, batch 3b) | no form | E |
| `by-intros`, `by-clear`, `by-clear[ ]` | `intros`, `clear` (Lean) | Lean | names for intros (several names for clear: `by-clear[ ]`, batch 3b) | no form | small batch |
| `by-rename-i[ ]` | `rename_i` (Lean) | Lean | Lean logs "too many variable names provided" and goes on; LeanForth stops (211; both refuse the proof) | 211 | none needed |
| `by-exact`, `by-apply` | `exact`, `apply` (Lean) | Lean | terms with `fun`, `⟨ ⟩`, nested `by`, coercions; an expected type that unfolds to a function (a negation): 133/136; apply with a hole it leaves open (Lean: a new goal, otherMVarIds); a hole that is an argument left open (Lean's message names the argument); an implicit argument left open (LeanForth's 95, Lean's "don't know how to synthesize implicit argument") | 93 / 133 / 136 / 99 / 95 (message differs) | FE2, C; otherMVarIds; mvarArgNames |
| `by-induction` | `induction` (Lean) | Lean | several targets; `generalizing`, `using`; a hypothesis depending on the target | 99 | E |
| bullets, `<;>`, `try`, `first`, `all_goals`, `repeat` | (Lean) | | not built | no word | F |
| `by-refine` | `refine` (Lean) | Lean | a `?: NAME` some metavariable has (findUserName? reuse, 139); a hole argument left open (99) and an implicit argument left open (95, message differs) as exact's; `refine'` not built | 139 / 99 / 95 | mvarArgNames; small batch |
| `exists`, `use`, `constructor` forms | (Lean; `use` Mathlib) | | not built | no word | C |
| `cases`, `rcases`, `obtain`, `rintro`, `subst`, `injection` | (Lean) | | not built | no word | E |
| `simp` and its family | (Lean; Mathlib extends) | | not built; needs the `@[simp]` set with the data | no word | own design |

Other tracked loose ends of these batches: the printer writes a binder whose Lean name is a
reserved LeanForth word (possible only through `«»`) in a spelling the reader then refuses (78):
fix in the printer; `tac-shape-at` is not sealed after load; the step log prints `@id Prop (a = a)`
where Lean shows `id (a = a)`.

Staying compatible when the pins move: every tactic file cites the Lean, Batteries or Mathlib
source lines it ports, and every batch has Lean twins that pinned Lean runs. On a new pin the
twins are run again; a tool that lists the tactic files whose cited source changed between two
pins is a plan task (not started). Twins of Batteries and Mathlib tactics run on core Lean in an
equivalent form today; running them inside the Mathlib checkout, on the tactic itself, is a plan
task (not started).
