# Adding a tactic

How to add a LeanForth tactic word as a plug-in (design
[TACTIC_PLUGINS.md](../design/TACTIC_PLUGINS.md) section 3; slices a2-ii and
a2-iii, 2026-11-18). The template is `src/front/tactics/assumption.fs`
(a plain word on one goal operation); `src/front/tactics/apply.fs` shows a
word that takes a term.

## The rule: a port of Lean's tactic

A tactic is a port of what Lean 4.35.0's tactic does: the same choices, in
the same order, building the same proof term, written as Forth on the
tactic library, never a line-by-line transcription (owner, 2026-11-17).

1. **Lean call list first.** Read the tactic in pinned Lean's source
   (`.tools/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`): its
   elaborator (`Elab/Tactic/*.lean`) and its goal operation
   (`Meta/Tactic/*.lean`). List every Lean function it calls one level
   down and, for each, the Forth word that ports it: one that exists
   (file and word), or one you add. Put the list in the file's header.
2. **Search before writing.** Look in `src/lib/`
   ([FORTH_LIBRARY.md](FORTH_LIBRARY.md)), the tactic library
   (`src/front/meta-must.fs`, `app-builder.fs`, `telescope.fs`), the goal
   layer (`src/front/meta-tactic/`) and `src/front/` for each word.
3. **Library words in their layer.** A Lean function of `Meta` or
   `Meta/Tactic` that no word ports goes into the library file of its
   layer (`meta-tactic/NAME.fs` for an `MVarId` operation), never into the
   tactic file. The tactic file holds only the elaborator's part.
4. **Not ported is not supported.** Every case you do not port answers
   "not supported yet" (error 99, or the library's unsupported, exit 2),
   never a silent success or a different term.

## The file

```forth
require ../tactic-api.fs
tac-shape-plain lf-tactic: by-assumption constant tac-k-assumption
s" assumption" tac-k-assumption lf-tactic-lean!
: tas-tac ( goal -- goals ) lf-goal-assumption 0 ;
: tas-run ( i -- ) ['] tas-tac lf-lift-meta-tactic ;
' tas-run tac-k-assumption lf-tactic-action!
```

- `lf-tactic:` ( shape "spelling" -- kind ) registers the word: a new kind
  and row, the spelling reserved for the printer and added to LF-WORDS,
  its reader made for the shape. A spelling reserved already, or one not
  spelt `by-` and at least one more character, aborts the load.
- Shapes are data (`src/front/tactic-syntax.fs`, plan row TB2), the same
  ones the built-in words are read by: `tac-shape-plain` (no value,
  by-rfl's), `tac-shape-term` (one term, by-exact's), `n tac-shape-terms`
  (n values), `n k tac-shape-term-names` (n values before the word, then
  k names after it on its line, each a hypothesis word until the block
  ends; `tac-shape-name`, `0 1`, is by-intro:'s, `tac-shape-decl`, `2 1`,
  by-have:'s, by-let:'s, by-suffices:'s and by-replace:'s), `n tac-shape-term-this`
  (n values and the hypothesis `this`, Lean's name when none is given),
  `tac-shape-rules` (`by-x[ ... ]`: the values up to `]` are the rules,
  by-rw['s; a rule followed by `<-` is right to left, which
  `lf-tac-arg-symm? ( i k -- flag )` tells), `tac-shape-list` (the same
  bracket of terms, no `<-`: by-exacts['s), and the lists of names
  (plan row TB2, batch 3b): `tac-shape-binders` (`by-x[ a _ b ]`: new
  hypotheses, `_` an inaccessible one, none allowed: by-intro['s),
  `tac-shape-binders+` (the same, one at least: by-rename-i['s) and
  `tac-shape-hyps` (names of hypotheses the goal has, one at least, `_`
  refused: by-revert['s, by-clear['s); `tac-shape-list+` is
  `tac-shape-list` with one term at least (by-exists['s, batch 3c);
  `tac-shape-pattern` (`src/front/pattern-syntax.fs`, plan row TB2 piece
  E) one value, then a case pattern up to `]`, its items postfix in the
  step's arguments with their spans (`lf-tac-arg-span`), by-obtain['s
  and by-rcases['s; `tac-shape-rintro` (the same file, slice E2a) no
  value, one pattern or more under a `pat-seq` node, by-rintro['s;
  `tac-shape-contra` (slice E2b) the same with exactly one pattern (474),
  and `tac-shape-contra-name` and `tac-shape-contra-this` one name (or
  `this`) read as such a pattern, by-contra['s, by-contra:'s and
  by-contra's, whose second row is by-rintro['s; a Meta word refuses a
  case it does not port with `outcome-unsupported lf-must`, and a tactic
  that calls it maps that to 99 with `tactic-run.fs`'s `lf-tac-ported (
  i*x xt -- j*x )`; Lean's `try ... catch _ =>` is `meta-must.fs`'s
  `lf-meta-try ( i*x xt in out -- j*x true | false )`; a
  goal operation that substitutes an equation is `meta-tactic/subst.fs`'s
  (`lf-goal-subst`, `lf-goal-subst-eq`, `lf-goal-subst-core`, errors
  475-480); a reader of its own is a shape made with
  `tac-shape-new ( n k build-xt -- shape )`. A
  list sits between its bracket word and `]`, on as many lines as it
  needs (the owner's rules of 2026-11-22; batch 3c: the shared reader
  `author/runner.fs`'s `lfa-token-on` reads on, and every list is an
  author bracket, `author/scopes.fs`); a word that is never its item,
  `end NAME`, `:=` or the text's end is 458 at the list's word (459,
  460); what follows `]` is the next step. The
  step's arguments are the values, then the names (`lf-tac-arg`; a name
  is 0 for `_`; `lf-tac-arg-names ( i -- names )` all of them as a run,
  `lf-tac-arg-fvars ( i -- fvars )` getFVarIds of them in the main goal's
  context, `lf-tac-name-fvar ( name -- fvar )` one). Lean's `have k : T
  := e` is `T e by-have: k`, Lean's `revert h k` is `by-revert[ h k ]`:
  ```forth
  tac-shape-decl lf-tactic: by-have: constant tac-k-have
  tac-shape-hyps lf-tactic: by-revert[ constant tac-k-revert-list
  ```
- Holes (mechanism B, batch 3b): `_`, `?_` and `?: NAME` are term nodes
  (`syntax.fs`'s `syn-k-hole`, `syn-k-synthetic`) that `elab-term.fs`
  elaborates as Lean's elabHole and elabSyntheticHole. A tactic that
  takes a term with holes elaborates it with `lf-tac-elab-holes ( node
  expected allow? -- e goals )` and then tags the goals with
  `lf-tac-tag-new ( goals suffix -- goals )` (`tactic-core.fs`, the two
  together Lean's elabTermWithHoles: expected -1 for none; goals the
  term's new open metavariables, with allow? false a natural hole left
  open being Lean's placeholder error, 461; suffix a counted string,
  `c" refine"`, the anonymous goals tagged as Lean's tagUntaggedGoals):
  `tactics/refine.fs`, `specialize.fs`. Lean's refineCore is
  `lf-tac-refine ( node goal -- goals )` (tactic-core.fs, batch 3c), for a
  tactic Lean writes as a macro over refine: `tactics/exists.fs` builds
  the syntax `⟨e1, .., en, ?_⟩` (syntax.fs's `syn-node-new`, `syn-arg!`,
  `syn-last!`) at its step's word and refines with it.
  The goal words under it are `new-goals.fs`'s `lf-fresh-mvars`,
  `lf-natural-mvars`, `lf-tac-log-unassigned` and `lf-tag-untagged`.
- Blocks (plan row TB2, blocks slice 1; design
  [TACTIC_BLOCKS.md](../design/TACTIC_BLOCKS.md)): a word whose steps
  after it form its block is registered with `n k flags tac-shape-block
  ( -- shape )` (n values, k names, then the block up to `by-end`;
  `tac-block-cuts`: the names given inside it go at its end;
  `tac-block-self`: it closes itself at `}`), its run word opens the
  runner's frame with `lf-tac-block ( i rest -- )` or, over the main goal
  alone, `lf-tac-focused ( i -- )` (Lean's focus: 90 with no goal, before
  the frame is pushed; a brace's `lf-tac-bracketed ( i -- )` tells that 90
  at its `}`, as Lean's), and its row names the frame's mode with
  `lf-tactic-mode! ( mode kind -- )`: `lf-mode-done` (the default: Lean's
  closeUsingOrAdmit, no goal left at its end, 89), `lf-mode-nested`
  (Term.runTactic: a fresh recover, its unsolved goals always reported)
  or `lf-mode-focus` (the goals left before the others), or, over every
  goal with `lf-tac-all ( i -- )`, `lf-mode-per-goal` (Lean's all_goals:
  the block once on each goal not solved when reached, the goals left in
  order; blocks slice 2); a new mode is
  `lf-block-mode ( open-xt end-xt fail-xt|0 flags -- mode )` with the
  flags `lfr-admits`, `lfr-no-recover`, `lfr-fresh-recover`; a mode's end
  may run the block's steps again with `lf-tac-again ( frame -- )`
  (`tactics/blocks.fs`; `tactics/have.fs`'s `by-have-by:`). A tactic Lean
  writes as a sign, not a `by-` word, registers with `lf-tactic-sign:`
  (`{`, `<;>`: its shape `tac-shape-then`, the reader's then-step). An error of Lean's logged class (throwOrLogError, a term that
  does not elaborate) is raised with `lf-tac-log-fail ( code -- )` or
  `lf-tac-logged ( i*x xt -- j*x )`: final while the block recovers
  (`lf-tac-recover? ( -- flag )`), else thrown; `lf-tac-no-recover ( i*x
  xt -- j*x )` runs xt as Lean's withoutRecover (try's and first's
  alternatives but the last).
- A tactic that takes Lean's location (`at h ⊢`) is registered with a
  located shape (`tac-shape-at ( shape -- shape )`: `tac-shape-plain-at`,
  `tac-shape-term-at`, and `tac-shape-rules` takes one already); a trailing
  `at[ h1 h2 |- ]` then amends its step, and any other tactic refuses `at[`
  (453). Its run word passes its two actions to `lf-with-location ( i*x i
  xt-local xt-target -- i*x )` (Lean's withLocation): xt-local ( i*x fvar
  -- i*x ) for each hypothesis named, resolved by name in the main goal's
  context, then xt-target ( i*x -- i*x ) when the goal is named or no
  `at[ ]` was written (`tactics/symm.fs`); `lf-at-location ( i xt-local
  xt-target -- )` is the same for actions of step i alone, which
  `lf-lift-target1 ( i xt -- i )` and `lf-lift-local1 ( i fvar xt -- i )`
  make from a goal operation, xt ( i goal -- goal' ) and ( i fvar goal --
  goal' ) (`tactics/change.fs`, `delta.fs`); `lf-tac-located?`,
  `lf-tac-loc#`, `lf-tac-loc-fvar` read the location directly (rwa's
  single hypothesis). A hypothesis's new type goes in with
  `lf-goal-replace-local-decl` (replaceLocalDecl, an equality proof),
  `lf-goal-change-local-decl` (changeLocalDecl, defeq) or
  `lf-goal-replace` (MVarId.replace, a new proof), all in
  `meta-tactic/assert.fs`.
- A tactic that Lean writes as another tactic run first runs that row on
  its own step with `lf-tac-eval ( i kind -- )`: `tactics/replace.fs`
  runs by-have:'s row, then clears the old hypothesis (Lean's
  evalReplace); `lf-tac-row ( kind -- )` is the same on the step running
  (an alternative of `lf-tac-first-of`: `tactics/rwa.fs`).
- A tactic Lean writes as a macro of other tactics run one after the other
  (`t1; t2`), each reading the step's own arguments, is one line:
  `lf-tactic-seq: ( kind1 .. kindn n shape "spelling" -- kind )` registers
  the word as `lf-tactic:` does and gives it a run word that runs kind1's
  row, then kind2's, .. kindn's, on its step (`tactics/by-contra.fs`,
  Batteries' `by_contra h`, the macro `by_contra_core; rintro h`):
  ```forth
  tac-k-by-contra-core tac-k-intro 2 tac-shape-name
    lf-tactic-seq: by-contra: constant tac-k-by-contra
  ```
  by-intro:'s row reads the step's argument 0, the name after the word. A
  macro of alternatives (`first | t1 | t2`, `t1 <|> t2`) is
  `lf-tac-first-of` in a run word (the alternatives before the last run
  withoutRecover, as Lean's orElse); an extensible macro's rules (several
  `macro_rules`, Lean's expandEval: `rfl`, `trivial`) are
  `lf-tac-macro-alts`, the same loop with the block's recover kept; one
  whose parts take other arguments is a run word of its own.
- `lf-tactic-lean!` gives Lean's name for the step log; `lf-tactic-action!`
  the run word ( i -- ), step i of the record; `lf-tactic-plan!` a plan
  step to name while the word is not ported (error 80).
- `lfa-code:` ( n outcome c-addr u "name" -- ) adds an error code and its
  message (Lean's first line), in the file that raises it (assumption's
  381 is in `meta-tactic/assumption.fs`, where Lean's throwTacticEx is); a
  code registered anywhere aborts the load. Plan the number by the ranges
  of the design's appendix C. A code that is Lean's own error, raised
  where Lean raises it, takes the outcome `lfa-lean` (invalid, with the
  code's "Lean's error" bit set): only such a code is caught by try and
  first (`lf-tac-try-lean`, `lf-tac-first-of`, `lf-tac-macro-alts`,
  tactic-run.fs's `lf-tac-lean-error?`; plan row TB2, blocks slice 1).
  Every other code,
  `outcome-invalid` included, is LeanForth's own refusal and passes every
  try, so a gap or a malformed state never becomes another alternative.
- `lf-lift-meta-tactic` (Lean's liftMetaTactic): xt ( i*x goal -- goals )
  gets the main goal in its context; its goals (a run) take its place.
  `lf-lift-meta-tactic1` (liftMetaTactic1): the same for a goal operation
  that gives one goal, xt ( i*x goal -- goal' ) (`tactics/exfalso.fs`:
  `' lf-goal-exfalso lf-lift-meta-tactic1`).
- A goal operation's error with the goal below it (Lean's throwTacticEx) is
  `lf-tac-ex ( goal code -- )` (`tactic-msg.fs`); a part of the message on
  its own first line is `lf-tac-inline` before it (clear's `'h'`).
- A tactic that takes a hypothesis by name gets its free variable with
  `lf-tac-get-fvar ( node -- fvar )` (Lean's getFVarId: error 389 for any
  other term).
- Add the file to `src/front/tactics/all.fs`, sorted.

What a tactic file may not do (`scripts/check-tactic-plugins.py`): write a
hook (`is`, `defer!`), store into another file's data word, or set a row of
another file's kind.

## Tests

In `tests/front/tactics/NAME/` (the Makefile finds them; their class is a
pattern row of `tests/test-classes.txt`):

- `check.py`: calls `tests/front/tactics/tactic_check.py`'s `main` with the
  accepted `.lf` files, the wrong twins (exit 4, Lean's first line and
  detail) and the files not supported yet (exit 2). Each accepted
  theorem's type and value must equal pinned Lean's node for node: add its
  Lean twin to a `.lean` file whose output is the golden (see
  `goal-layer.lean`), and its step logs go to `NAME/steps.golden`
  (`--write-steps` after a review). `--lean` checks the Lean side.
- `test.fs`: unit tests of the goal operation for what text cannot reach,
  in every class of [TEST_COVERAGE_REVIEW.md](TEST_COVERAGE_REVIEW.md).
- `tests/mutants/faults.d/NAME.toml`: a planted fault per risky word, each
  caught by a test (`python3 scripts/mutants.py --only ID`).
- `tests/front/check_registry.py --write` after a review: the registry's
  dump gains the new word's lines only.

Run `scripts/pre-tier.sh` and `make cover-changed` early and again as the
words land, not only before the tier: they take seconds to a minute and
find the class-table row, the duplicate, the style count or the block no
unit test runs while it is cheap to fix (tactic batch 1 found two such
only in its tier and its review).

A batch of tactics (plan row TB2) keeps one test directory,
`tests/front/tactics/batch-NAME/`, for all of them: one `check.py` passing
`main` its own Lean twins and golden (`lean=`, `lean_wrong=`, `golden=`,
`tests/front/tactics/batch-a/check.py`), one `test.fs`, one `steps.golden`,
and one fault file `tests/mutants/faults.d/batch-NAME.toml`. Its goal
operations go into `src/front/meta-tactic/` as new files, or as new colon
definitions between an existing one's definitions: such a branch stays
confined (the tactic tier) when every definition of an existing goal
operation stays token for token the same and in order, and no new word is
defined elsewhere or already used by a Forth file, a Gforth host word such
as `bounds` included (`scripts/check-tactic-plugins.py`).

## Documentation

A row and a paragraph in [LANGUAGE_REFERENCE.md](../user/LANGUAGE_REFERENCE.md)
(plain sentences, two examples from checked files), the codes in
[LEANFORTH_WORDS.md](../programming/LEANFORTH_WORDS.md)'s error table (in
the order `lf-author-each-message` gives them), and the word's own
[parser] question to the owner before it merges.
