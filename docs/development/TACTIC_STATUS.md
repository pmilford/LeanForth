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
constructor (done, `<< >>`, batch 3c), **D** locations (done for hypotheses and the goal; written `at[ ]` since batch 3b), **E**
cases and patterns, **F** blocks (slice 1 done: braces, `by-focus`, `by-have-by:`; slice 2 done: `<;>`, `by-all-goals`; slice 3 tested on its branch `tb2-blocks3`, not merged: `by-try`, `by-first`, `by-repeat`, `by-any-goals`), **G** macro word (done), **NL** name lists (done for intro, revert,
clear and rename_i, batch 3b; a list sits between its bracket word and `]`, over lines since batch 3c), **FE2** `→`, `∀`, `fun` in statements
and terms, **REFL** Lean's `@[refl]` lemma set brought over with the elaboration data,
**NR** names resolved as Lean does everywhere (unknown identifier messages), **LC** a local
context that can hold one variable at two types (replaceLocalDeclDefEq).

Column **Logged under recover** (blocks slice 1, docs/design/TACTIC_BLOCKS.md 1): the word's
errors Lean logs and goes on from, instead of throwing them, while its `recover` flag is true
(`throwOrLogError`, Elab/Tactic/Basic.lean:422-434; the term elaborator's errToSorry,
Elab/Tactic/ElabTerm.lean:31-39; `closeUsingOrAdmit`, Basic.lean:351-361). LeanForth makes them
final there (`tactic-run.fs`'s `lf-tac-log-fail`, `lf-tac-logged`, the loop's admitting
frames): no try or first may take one back, and the run stops at it, the same verdict. With
recover false (a try's or first's alternative that is not the last) they are thrown, as Lean's,
with Lean's term-elaborator flag errToSorry modelled since blocks slice 3 (the frame field
`tfr-sorry`, on branch `tb2-blocks3`): withoutRecover clears it and a have-by's fresh
Tactic.run does not set it again, so a term error, or the unsolved goals, of a have-by inside a
block that does not recover are thrown, as Lean's (the review's Q8 is accepted). A logged error
while a handler's save is open answers 490, unsupported (the coordinator's rule).
The pinned-Lean twins of these classes inside `any_goals` come with blocks slice 3, which builds
the handlers that can tell them apart; slice 1's unit tests pin them with probe handlers
(`tests/front/tactics/blocks-1/test.fs`).

| Word | Lean tactic (source) | Compared with | Logged under recover | Not covered yet | Answer | Removed by |
|---|---|---|---|---|---|---|
| `by-change`, `by-show` | `change`, `show` (Lean) | Lean | its terms' elaboration errors | a pattern left with an open metavariable (holes are read since batch 3b; change's own treatment of them is not ported) | 93 | change's holes |
| `by-change at[ ]` | `change … at h` (Lean) | Lean | its terms' elaboration errors | another hypothesis depends on `h` | 93 | LC |
| `by-swap` | `swap` (Batteries) | `rotate_left`-style core twin | none | `pick_goal n`, `rotate_left/right` not built | no word | small batch |
| `by-specialize` | `specialize` (Lean) | Lean | its terms' elaboration errors | holes are collected as goals (allowNaturalHoles, batch 3b), but a hypothesis applied to a term cannot be written yet (136) and a function hypothesis cannot be stated | 136 / untestable end to end | FE2 |
| `by-revert`, `by-revert[ ]` | `revert` (Lean) | Lean | `by-revert`'s term's | a `let` variable (several names: `by-revert[ ]`, batch 3b); an unknown name in the list (455) reported at `by-revert[`, where Lean reports it at the name (its own place is recorded, and shown by `--steps`) | 93 / 455 (place differs) | LC; place: small batch |
| `by-delta` | `delta` (Lean) | Lean | none | several constants; a theorem's name; a let between the value's lambdas | 93 / 99 | small batch |
| `by-delta at[ ]` | `delta … at h` (Lean) | Lean | none | a hypothesis it would change | 99 | LC |
| `by-contradiction` | `contradiction` (Lean) | Lean | none | an indexed-family hypothesis (any `≤` met first; the empty type without index, `Empty`, `False`, closes since E2b, tested on branch `tb2-patterns-e2b`: rule 6, Contradiction.lean:45-87, batch-h2's empty.lf node for node, wrong twins True and False ∧ a = a with Lean's 449); two different constructors equated; `Nat.hasNotBit` | 99 | E (E4: indices, noConfusion) |
| `by-trivial` | `trivial` (Lean) | Lean | none | whatever `by-contradiction` lacks; rules added by Mathlib | 99 | E; Mathlib's rules with the elaboration data |
| `by-absurd` | `absurd` (Batteries) | core twin | its terms' elaboration errors | none known | | |
| `by-have:`, `by-have`, `by-let:`, `by-suffices:`, `by-replace:` | `have`, `let`, `suffices`, `replace` (Lean) | Lean | its terms' elaboration errors | one name only; `_` as the name; binders and patterns (the `:= by` block is `by-have-by:`, blocks slice 1); suffices' `from`/`by` forms; a `?_` or a `_` unification leaves in the value or type (Lean's refine makes it a goal; a `_` it fills works, batch 3b); a dependent let past the first variable | 99 / 93 / no form | E, refine_lift over by-refine |
| the same | | | a value naming a cleared or unknown hypothesis: refused, with error 76/99 where Lean says "Unknown identifier" | its terms' elaboration errors | exit 4 or 2, message differs | NR |
| `by-have-goal:` | `have h : T` (Mathlib's `have` without a value) | core `refine` twin | its terms' elaboration errors | as `by-have:` | | |
| `' r <-` in `by-rw[ ]` | `rw [← r]` (Lean) | Lean | its terms' elaboration errors | `<-` on an `↔` rule | 99 | small batch |
| `by-rw[ ]`, `by-rewrite[ ]` | `rw`, `rewrite` (Lean) | Lean | its terms' elaboration errors | a rule that leaves new goals or metavariables; a rule naming a definition (equation lemmas); `occs`/config; rw leaving `R x x` for a relation other than `=`, `↔` (Lean leaves the goal) | 99 / 93 | B, FE8, REFL |
| `at[ ]` | location (Lean) | Lean | none | `at[ * ]`; a constant's name among the names (Lean: error); an unknown name (455) reported at the tactic's word, where Lean reports it at the name | 99 / 455 (place differs) | small batch |
| `by-rwa[ ]` | `rwa` (Lean) | Lean | its terms' elaboration errors | what `by-rw[ ]` and `by-rfl` lack | 93 | REFL |
| `by-rfl` | `rfl` (Lean) | Lean | none | `x R x` for a relation other than `=`, `↔` (`@[refl]` lemmas); the `HEq` branch | 93 | REFL |
| `by-exacts[ ]` | `exacts` (Batteries) | core `exact` steps | its terms' elaboration errors | none known beyond `by-exact`'s terms | | FE2 |
| `by-cases:` | `by_cases` (Lean) | Lean | its terms' elaboration errors | the unnamed form; instance priorities tied with the classical one; a decidable instance the data left out | no form / 93 | small batch; data |
| `by-contra:`, `by-contra`, `by-contra[ ]` (the pattern form E2b, tested on branch `tb2-patterns-e2b`, not merged) | `by_contra` (Batteries, Init.lean:43-60: by_contra_core; rintro (pat)) | core twin (batch-c; batch-h2: 7 theorems node for node, the pattern read by rcases.fs's lf-rintro) | 474 for two patterns or none | `by_contra h : T` (E5); `by_contra!` (Mathlib, over `push_neg`) | no form | E5; simp family |
| `by-symm` | `symm` (Lean) | Lean | none | relations other than `=`, `↔`, `≠`, `HEq`, `∧`, `∨` (`@[symm]` lemmas) | 99 | `@[symm]` set with the data (as REFL) |
| `by-and-intros` | `and_intros` (Lean) | Lean | none | none known | | |
| `by-next`, `by-case: _` | `next`, `case _` (Lean) | Lean | any error leaving its block (closeUsingOrAdmit) | names after `next`; `case a \| b`; `@tag` | no form | NL, F |
| `by-intro:`, `by-intro[ ]` | `intro` (Lean) | Lean | none | patterns; type ascriptions `(h : T)` (several names and bare `intro`: `by-intro[ ]`, batch 3b); a goal `¬a = b` with another negation such as `k : ¬a = a` in the context, also through `by-rintro[ ]` (intro's whnf path, older than slice E2a: the Forth review of E2a, probes p26-p26c; Lean accepts) | no form / 93 | E / 9.4.8t |
| `by-intros`, `by-clear`, `by-clear[ ]` | `intros`, `clear` (Lean) | Lean | `by-clear`'s term's | names for intros (several names for clear: `by-clear[ ]`, batch 3b); an unknown name in `by-clear[ ]` (455) reported at `by-clear[`, where Lean reports it at the name | no form / 455 (place differs) | small batch |
| `by-rename-i[ ]` | `rename_i` (Lean) | Lean | none | Lean logs "too many variable names provided" and goes on; LeanForth stops (211; both refuse the proof) | 211 | none needed |
| `by-exact`, `by-apply` | `exact`, `apply` (Lean) | Lean | its terms' elaboration errors | terms with `fun`, nested `by`, coercions; an expected type that unfolds to a function (a negation): 133/136; apply with a hole it leaves open (Lean: a new goal, otherMVarIds); a hole that is an argument left open (Lean's message names the argument); an implicit argument left open (LeanForth's 95, Lean's "don't know how to synthesize implicit argument"); a hole left open in exact (461, Lean's message) reported at the step's word, where Lean reports it at the hole | 93 / 133 / 136 / 99 / 95 (message differs) / 461 (place differs) | FE2; otherMVarIds; mvarArgNames |
| `by-induction` | `induction` (Lean) | Lean | its term's; with alternatives 206, 207, 208, 213 (throwOrLogError) and any error leaving an alternative | several targets; `generalizing`, `using`; a hypothesis depending on the target | 99 | E |
| `{ }` | `·`, `{ }` (Lean, Elab/Tactic/BuiltinTactic.lean:167-185) | Lean | any error leaving it (closeUsingOrAdmit) | where Lean logs an error inside it, admits the goal and goes on (closeUsingOrAdmit), LeanForth stops at that first error (the same verdict); 90 told at `{`, Lean at `}` | rejected / place differs | log and carry on (plan row) |
| `by-focus` | `focus` (Lean, BuiltinTactic.lean:187; Basic.lean:332-338) | Lean | none | none known | | |
| `by-have-by:` | `have h : T := by tacs` (Lean, Init/Tactics.lean:942; Term.runTactic, Elab/SyntheticMVars.lean:474-537) | Lean | T's elaboration errors; its unsolved goals (always); an error leaving its block when the block around recovers | as `by-have:`'s name, binders and patterns (`_`: 99); its unsolved goals told at `by-have-by:`, Lean's at `by` | 99 / place differs | as `by-have:`'s |
| `<;>` | `t1 <;> t2`, the macro `focus (t1; all_goals t2)` (Lean, Init/Tactics.lean:451-456) | Lean | any error of t2 (all_goals logs it, admits that goal, aborts at the end) | where Lean logs t2's error on a goal and runs the others, LeanForth stops at the first (the same verdict and first error); final where the block recovers, so inside slice 3's `any_goals` it will reject where Lean may roll the logged error back; a name t1 gave used on a goal that lacks it: 76 where Lean says unknown identifier (row NR) | rejected / 76 (message differs) | log and carry on (plan row); slice 3 |
| `by-all-goals` | `all_goals` (Lean, BuiltinTactic.lean:229-253) | Lean | any error of its block (logged, the goal admitted, aborts at the end) | as `<;>`'s | rejected | as `<;>`'s |
| `by-try` | `try` (Lean, Init/Tactics.lean:445: `first \| tacs \| skip`) | Lean | none: its block runs without recover (a have-by inside it recovers again, its errToSorry false: its term errors and unsolved goals are thrown, as pinned Lean's) | an error Lean logs in a block inside it that recovers again (a brace in a have-by) while its save is open: 490 | unsupported | log and carry on (plan row) |
| `by-first` | `first` (Lean, BuiltinTactic.lean:631-641) | Lean | the last alternative's, as the block around it; the others none (withoutRecover) | as `by-try`'s | unsupported | log and carry on |
| `by-repeat` | `repeat` (Lean, Elab/Tactic/Repeat.lean:17-26) | Lean | none (withoutRecover) | a block that never fails ends in step fuel (91), where Lean ends in maxHeartbeats | exhausted | — |
| `by-any-goals` | `any_goals` (Lean, BuiltinTactic.lean:256-270) | Lean | its block's (recover kept): a term error, a failing brace, a have-by's unsolved goals in a pass | an error Lean logs in a pass: 490, since a later failure of the pass would take it back (`u-any-gap.lf`: Lean accepts); Lean prints the block's text after 469's message, LeanForth does not | unsupported / message shorter | log and carry on |
| `by-refine` | `refine` (Lean) | Lean | its terms' elaboration errors | a `?: NAME` some metavariable has (findUserName? reuse, 139); a hole argument left open (99) and an implicit argument left open (95, message differs) as exact's; the place of error 461 (a `_` left open, Lean's message and context): LeanForth reports it at the step's word, Lean at the hole; `refine'` not built | 139 / 99 / 95 / 461 (place differs) | mvarArgNames; small batch |
| `<< >>`, `⟨ ⟩` | anonymous constructor `⟨ ⟩` (Lean, Elab/BuiltinNotation.lean:43) | Lean | its elaboration errors (the term's) | where Lean postpones it (no expected type, an expected metavariable application, an operand of `+`); an expected pi (Lean: "not an inductive type"); an item of another type (Lean: application type mismatch); a private constructor; a type over 30 characters in the message (Lean indents it); the error's place: LeanForth's step word with `<<` second, Lean's `⟨` | 132 / 133 / 131 / 139 / message differs / place differs | FE2 postponing; coercions FE4; small batch |
| `by-exists[ ]` | `exists` (Lean, Init/Tactics.lean:1293) | Lean | its terms' elaboration errors | what `<< >>`, `by-refine` and `by-trivial` lack (trivial's unsupported rules make it unsupported) | as those | as those |
| constructor forms | `refine ⟨?_, ?_⟩`, `exact ⟨a, b⟩` (Lean) | Lean | its terms' elaboration errors | none: `<< ?_ ?_ >> by-refine` and `<< a b >> by-exact` (batch 3c) | | |
| `use` | `use` (Mathlib, Tactic/Use.lean) | | not built: left out of batch 3c (its loop over constructors, the discharger `use_discharger` and `use!`, `(discharger := ...)` together are more than the batch's budget for an exact port) |  | no word | its own batch |
| `' h by-obtain[ pat ]`, `' h by-rcases[ pat ]` (E1, on main; `rfl` since E2a, on its branch) | `obtain pat := e`, `rcases e with pat` (Lean, Elab/Tactic/RCases.lean:520-552; Meta/Tactic/Cases.lean, Induction.lean) | Lean (tests/front/tactics/batch-g: 21 theorems node for node) | names, `_`, `-`, tuples `<< >>` and `⟨ ⟩` nested, alternatives `\|` (a bar binds tighter than a space; `<< a \| b >> \| c` is Lean's `(a \| b) \| c`), more and fewer patterns than fields, Nat through Nat.casesAuxOn, a term generalized; Lean's errors 470, 471; tags and hidden names as Lean's | an indexed family (Eq, Nat.le: Meta cases' generalizeIndices); Quot; typed pieces `(h : T)`, `@pat`, several targets, `obtain pat : T`; a recursor whose parameters are not the major type's first arguments; a hypothesis or statement variable named where its goal's context lacks it (cleared by a split or `-`) says LeanForth's 76 (Lean's "Unknown identifier"); 471's message on a pi needs binder kinds (136) | 99 (indexed, Quot), no form (typed, `@`), 76/136 refusals | E4 (indexed), E5 (typed, `@`, Quot, several targets), NR (76), FE2 (136) |
| `rfl` in a pattern (E2a, tested on branch `tb2-patterns-e2a`, not merged) | rcases' `rfl` (Elab/Tactic/RCases.lean:279-284: substEq) | Lean (batch-h: 5 theorems node for node) | substEq's errors (478) | as `by-obtain[ ]`'s; a pending instance problem is synthesized at the walk's end, where Lean synthesizes it before the rfl | rejected / none met | — |
| `' h by-subst`, `by-subst[ ]`, `by-subst-vars` (E2a, tested on branch `tb2-patterns-e2a`, not merged) | `subst`, `subst_vars` (Lean, Elab/Tactic/BuiltinTactic.lean:494-520; Meta/Tactic/Subst.lean) | Lean (batch-h: 15 theorems node for node: both sides, dependents before and after, Eq.rec both ways, HEq, the reduced path both sides, variables, several names, skip, a hidden dependent, subst_vars' order) | its getFVarId's (389, 455) | a let variable, which Lean unfolds (99); a have, or a let or have among the reverted (revert.fs's lets: 93, Lean accepts); an unknown name in `by-subst[ ]` is 455 at `by-subst[` | 99 / 93 / 455 (place differs) | LC (let revert) |
| `by-rintro[ ]` (E2a, tested on branch `tb2-patterns-e2a`, not merged) | `rintro` (Lean, Elab/Tactic/RCases.lean:483-558) | Lean (batch-h: 5 theorems node for node; the grouping twin) | as `by-rcases[ ]`'s | rintro's typed group `(x y : T)` and `: T`; whatever `by-rcases[ ]` lacks | no form / as by-rcases[ | E5 |
| `cases`, `injection`, `by-contra[ ]` | (Lean) | | not built |  | no word | E2b-E4 |
| `simp` and its family | (Lean; Mathlib extends) | | not built; needs the `@[simp]` set with the data |  | no word | own design |

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
