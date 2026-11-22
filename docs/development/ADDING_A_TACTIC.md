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
  its reader made for the shape (`tac-shape-plain`: no value;
  `tac-shape-term`: one term). A spelling reserved already, or one not
  spelt `by-` and at least one more character, aborts the load.
- `lf-tactic-lean!` gives Lean's name for the step log; `lf-tactic-action!`
  the run word ( i -- ), step i of the record; `lf-tactic-plan!` a plan
  step to name while the word is not ported (error 80).
- `lfa-code:` ( n outcome c-addr u "name" -- ) adds an error code and its
  message (Lean's first line), in the file that raises it (assumption's
  381 is in `meta-tactic/assumption.fs`, where Lean's throwTacticEx is); a
  code registered anywhere aborts the load. Plan the number by the ranges
  of the design's appendix C.
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

A batch of tactics (plan row TB2) keeps one test directory,
`tests/front/tactics/batch-NAME/`, for all of them: one `check.py` passing
`main` its own Lean twins and golden (`lean=`, `lean_wrong=`, `golden=`,
`tests/front/tactics/batch-a/check.py`), one `test.fs`, one `steps.golden`,
and one fault file `tests/mutants/faults.d/batch-NAME.toml`. Its goal
operations go into `src/front/meta-tactic/` as new files, or as lines added
to an existing one: such a branch stays confined (the tactic tier) when no
line of an existing goal operation changes or goes and no word is defined
again (`scripts/check-tactic-plugins.py`).

## Documentation

A row and a paragraph in [LANGUAGE_REFERENCE.md](../user/LANGUAGE_REFERENCE.md)
(plain sentences, two examples from checked files), the codes in
[LEANFORTH_WORDS.md](../programming/LEANFORTH_WORDS.md)'s error table (in
the order `lf-author-each-message` gives them), and the word's own
[parser] question to the owner before it merges.
