# LeanForth Forth style guide

Forth is its own language. Good Forth is a vocabulary of small words, each
doing one thing, that pass data on the stack and read almost like prose. This
guide states the project's rules for writing it. Authors follow it; the
[Forth reviewer](FORTH_REVIEWER.md) enforces it. Trust-boundary and
correctness rules in `AGENTS.md` always take precedence: never shorten code
by dropping validation, bounds checks or rollback.

`python3 scripts/forth-metrics.py --words 20 <files>` (or `make forth-metrics`)
reports the measurable signals below: word length, globals, locals, deep
stack shuffling and return-stack use. Treat them as prompts for review, not
as automatic verdicts.

## 1. Words are short

- **Aim for one or two lines per colon definition.** Three to five lines needs
  a reason; more than five is a refactoring candidate the reviewer must raise;
  more than ten needs an explicit justification in a comment.
- A word does one thing that its name says. If you need "and" to describe it,
  factor it.
- Factor repeated phrases into named words, even two-word phrases, when the
  name explains intent (for example `fail-invalid ( -- 0 status )` instead of
  repeating `-1 lf-x-invalid lf-x-leave exit` 17 times).
- Long `IF ... THEN` chains that dispatch on a tag are a table: use `CASE` for
  a few values, or a `CREATE`d table of execution tokens indexed by the tag
  (`tag cells table + @ execute`) for walkers, with the tag range validated
  first.
- Nesting deeper than two levels of `IF`/`BEGIN`/`DO` means a helper word is
  missing.

## 2. Use the stack

- **Values flow on the data stack.** Each word should consume and produce few
  items — normally at most three in and two out. Needing more means the data
  belongs in a record whose address is passed, or the word should be split.
- Prefer `DUP`, `SWAP`, `OVER`, `DROP`, `NIP`, `TUCK`. Use `ROT`/`-ROT`
  sparingly. Avoid `PICK` and `ROLL`; they signal that too much is on the
  stack.
- The return stack is for short, local parking: every `>R` has its `R>` in the
  same word on every path, never across `EXIT` without `R>`/`RDROP` first, and
  never across `DO ... LOOP` boundaries unless the loop is entirely inside.
- Every colon definition has a stack comment immediately after its name,
  `( in -- out )`, using meaningful names (`( node -- type status )`), and
  documents flags (`f`) versus status codes.

## 3. Globals are the exception

- **Never use a `VARIABLE` as a register to pass values between words or
  across a few lines of one word.** Storing three values in globals only to
  fetch them for the next call hides the data flow, breaks re-entrancy and
  invites stale-value bugs. Keep them on the stack, or pass the address of a
  record.
- Legitimate module state is long-lived data with an invariant: arena storage
  and counts, a session's generation, an index. Document each global's owner,
  invariant, reset behaviour and re-entrancy.
- Group related state into one record (`BEGIN-STRUCTURE` ... `END-STRUCTURE`)
  rather than a cluster of loose variables, so that a later re-entrant design
  can allocate one record per job. A table made by a defining word such as
  `store:` or `walk:` is still a global and counts as one; per-check state
  belongs in records reached through the worker's context
  ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)), never in
  another module's scratch.
- Constants (`CONSTANT`) are not globals; use them for every magic number,
  field offset and capacity.

## 4. Locals only when they clearly help

- Prefer factoring to locals. A word that needs locals is usually too long.
- Where locals genuinely make a short word clearer than stack juggling, use the
  Forth-2012 form `{: a b -- :}` and say why in the review. Never emulate
  locals with a global frame array indexed by magic slot numbers
  (`3 frame@`); name the fields.

## 5. Data structures are defined, not computed

- Use Forth-2012 `BEGIN-STRUCTURE`, `FIELD:`, `CFIELD:` and `+FIELD` for
  record layouts. Never write raw offsets such as `3 cells +` or
  `4 cells + swap 3 cells + @` in algorithm code; give each field a named
  accessor.
- Use `CREATE ... DOES>` defining words for repeated patterns (bounded arenas,
  tables, status sets) instead of copying the same array-plus-count code into
  each module.
- Bounds are checked in the accessor or constructor, once, not re-derived at
  every use.
- Name a record's fields `record-field` with hyphens (`node-tag`,
  `walk-fuel`, `lf-entry-prefix`) and its size `/record`. Do not use `>` in
  field names: in Forth `>x` reads as a conversion. Choose a record name that
  cannot be confused with its module's own prefix (the name table's entries
  are `lf-entry-…`, because `lf-name-…` are the module's words).

## 6. One error convention

- Use one project-wide outcome vocabulary — *ok, rejected, unknown, invalid
  input, exhausted* — shared by all modules, instead of per-module status
  constants plus translation words. The owner's three outcomes (accepted,
  rejected, unsupported/unknown) must be distinguishable at every interface.
- Keep status codes and flags distinct: a status is never consumed by `IF` as
  a truth value. Zero must not mean both "success" and "false".
- Whether exceptional failures (malformed input, exhaustion) should use
  `CATCH`/`THROW` with rollback in the handler is an open design decision; it
  needs an ADR before trusted code depends on it.

## 7. Names and modules

- Names say what, not how. Follow Forth conventions: `@` fetch, `!` store,
  `?` predicate or conditional, `>x` conversion to x, `#` count, `+!`
  accumulate, `x,` compile or append.
- Group a module's words in a wordlist (`WORDLIST`, `GET-ORDER`,
  `SET-ORDER`), as the handoff's `LF.CORE`, `LF.KERNEL` plan intends, rather
  than relying only on long `lf-module-` prefixes. Adopting wordlists is an
  open design decision for the trusted kernel.
- A module header states purpose, trust status, load dependencies, global
  state and re-entrancy.

## 8. Portability and tests

- Use Forth-2012 words. Isolate Gforth-specific words behind a named adapter;
  CI also runs on Gforth 0.7.3.
- Every public word has `T{ ... -> ... }T` tests for success and each failure
  outcome, with data-stack depth and return-stack balance checked. Library
  words also get randomized tests against a simple independent model
  (`tests/lib/lib-model.fs`).
- **Byte order and cell size never leak.** Memory is read the way it was
  written: cells with `@`/`!`, pairs with `2@`/`2!` (whose cell order the
  standard fixes), characters with `C@`/`C!`. Never read a cell's bytes, or
  bytes as a cell. No literal may assume a cell size: write `cell`, `cells`
  and `max-n`, not 8 or 9223372036854775807. Anything written to a file or
  read from one (exports, saved results, hashes that are compared across
  machines) is defined byte by byte — text, or fixed-width integers with an
  explicit byte order built with shifts — never a memory image.
  `scripts/check-portable-forth.py` (part of `make test`) enforces the
  checkable part: byte-access words only in listed text modules, and no
  numeric literal beyond 32 bits.

## Where the code stands

**After the refactor (measured 2026-11-02, evening, main `398b76b`).**
`src/core/` and `src/kernel/` hold 671 colon definitions: 73% of one or two
lines, 27% of three to five, 3 of six to eight, none longer (the longest is
`lf-minfer-dispatch`, a six-arm `CASE`). Their mutable state is in 37 named
records (`store:`, `walk:`, `walk2:`, `frames:`, or one structure instance
per module), down from 225 globals, plus 7 remaining `VARIABLE`s. Four
narrowing status words remain, under review. No module borrows another's
work stack. `src/legacy/` (28 files) is unchanged and awaits retirement.

**Before the refactor (measured 2026-11-02, morning).**
`scripts/forth-metrics.py src` reported 436 colon definitions:

| Signal | Value |
| --- | --- |
| 1–2 lines / 3–5 / 6–10 / over 10 | 37% / 20% / 19% / 22% |
| Longest word | 59 lines (`lf-minfer-walk`, `src/kernel/mixed-infer.fs`) |
| `VARIABLE`s / `CREATE`d arrays | 378 / 81, in 56 files |
| Locals | 0 |
| `ROT`, `-ROT`, `PICK`, `ROLL`, `2SWAP`, `2OVER` | 40 |
| Status-translation words (`lf-*-status`) | 34 |
| `BEGIN-STRUCTURE`, `DOES>`, execution-token dispatch, `CATCH`/`THROW`, wordlists | none |

Stack comments are nearly universal and deep shuffling is rare, but much of
that is because values are parked in globals. The largest improvements are
sections 3 (globals), 5 (structures), 6 (one error convention) and 1
(dispatch tables and factored exits). These are code-quality tasks for the
experimental modules that will become the checker; see
[the Forth library inventory](FORTH_LIBRARY.md).
