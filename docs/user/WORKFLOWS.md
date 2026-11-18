# Workflows: checking a theorem, verifying a program

Two diagrams of how LeanForth is meant to be used, as of 2026-11-12. **Solid boxes exist and are tested; dashed boxes are
planned and do not exist yet.** Thick boxes are the parts that are to be
trusted once they pass the review gate of `AGENTS.md`; nothing is trusted
today. The internal structure behind them is in
[the architecture page](../development/ARCHITECTURE.md).

## Checking a theorem

Today there is one way in that works end to end, and a second that is only
partly built; both are meant to end at the same checker:

- **From Lean** (works today): you write and prove the theorem in
  Lean, as usual. Lean's exporter writes the checked declarations as an
  NDJSON file; LeanForth reads that file and checks every declaration
  again, on its own, in the file's order.
- **In LeanForth itself** (checked since 2026-11-12 by `leanforth check [--env EXPORT]
  FILE.lf`, plan 8.2.1c-d, gates pending): you write the theorem and its proof with Forth words
  ([LeanForth syntax](LEANFORTH_SYNTAX.md), [ADR 0017](../adr/0017-leanforth-syntax.md),
  approved by the owner). The authoring words (`src/author/`, plan task
  8.1.2) run a file line by line through Forth's own interpreter, build
  the terms, report mistakes with line and column, and print a declaration
  back as words. They are untrusted: `check FILE.lf` loads them in its own process,
  and the kernel checks the terms they build, so a wrong proof is rejected.
  In natural LeanForth, the default, an untrusted elaborator fills in
  implicit arguments, instances, numerals and `+`, and the tactics
  `by-rfl`, `by-exact`, `by-induction-with` and `by-rw[ ]` build the proofs
  (plans S1 and S2, with the library's elaboration data;
  [the elaborator](ELABORATION.md)); in the kernel form proofs are kernel
  terms written by hand. Either way `Init` comes from Lean's export, and
  the same checker decides; a
  LeanForth-written theorem is to be printable as Lean source for Lean
  to check as a second opinion (not built).

```mermaid
flowchart TD
  src["Lean source file (.lean)"]
  lfsrc["LeanForth source file (.lf)<br/>theorem and proof written with Forth words<br/>syntax: ADR 0017"]
  author["Authoring words, src/author<br/>run by Forth's interpreter, line by line;<br/>errors with line and column; printed back as words<br/>untrusted; task 8.1.2"]
  proc["Records written by the words (src/author/export.fs)<br/>no elaborator or tactics yet (8.3)<br/>untrusted; task 8.2.1"]
  lean["Lean 4.35.0 elaborates and checks it"]
  exp["leanexport (lean4export 3.1.0)<br/>writes the declarations"]
  nd["NDJSON export file<br/>one JSON record per line"]
  rd["Forth NDJSON reader<br/>src/import/ndjson.fs<br/>checks every record whole, fails closed"]
  stage["Staging into the input stores<br/>names, levels, terms<br/>task 3.2.1"]
  probe["Today: inference and definition probe<br/>src/kernel/mixed-*.fs<br/>diagnostics only, never accepted"]
  chk["First checker<br/>ADR 0011 rules approved; rejection rules in progress (2.2.1),<br/>declaration check next (2.2.3)"]
  pub["Publisher<br/>writes each slot once, ok only<br/>ADR 0012, v0 written, under review"]
  env["Checked environment<br/>library of accepted declarations<br/>v0 written, under review"]
  out["One verdict per declaration<br/>accepted / rejected / unsupported / unknown<br/>invalid / exhausted / full"]
  print["Term printer, src/present<br/>statement and proof in Lean notation, ASCII or LaTeX"]
  more["Axiom list, receipt, proof outline<br/>tasks 2.2.5, 2.4.4, 3.4"]
  ref["Lean's verdicts on the same cases<br/>differential tests in make check"]

  src --> lean --> exp --> nd --> rd
  lfsrc --> author --> proc
  rd --> stage
  proc -- "export records, same format" --> stage
  stage --> chk
  chk -- "ok only" --> pub --> env
  env -- "earlier accepted declarations" --> chk
  chk --> out --> more
  stage -- "terms and binder names" --> print
  print --> more
  rd -. "today: decoded records only" .-> probe
  ref -. "compared with" .-> out

  classDef planned stroke-dasharray: 6 4
  classDef gate stroke-width: 3px
  class more,proc planned
  class chk,pub,env gate
```

What each step means for you:

1. **Lean and its exporter** are outside LeanForth. Lean has already
   checked the file; LeanForth checks it again independently. Users who
   check an existing library (such as Mathlib) need only its export file.
2. **The reader** exists. It decodes every record kind of the pinned
   format and refuses anything malformed, any other exporter or Lean
   version, and any record kind its caller did not ask for. It decides
   nothing about proofs. It decodes the whole pinned Mathlib export in
   under two minutes ([reader guide](../development/NDJSON_READER.md)).
3. **Staging** keeps the decoded names, levels, expressions and
   declarations in the importer's compact store (`src/import/stage.fs`; a loading stage,
   the checker does not read it in place), and the **feed** (`src/import/feed.fs`) gives them to the checker in
   file order, its stores grown to fit; `bin/leanforth check` runs both, on
   exports of any size ([the command line](COMMAND_LINE.md)). `check
   --record`, `replay` and `print` still copy an export straight into the
   checker's stores at their default sizes (`src/import/checker-input.fs`,
   version 0), so only exports the size of the test fixtures fit there.
4. **The checker** gives each declaration exactly one outcome
   ([outcomes](CONCEPTS.md#outcomes)). Its rules are approved; the checker
   runs from the shell on Lean's exports (all of `Init` on this build), but has
   not passed its review gate ([first check](FIRST_CHECK.md)).
5. **The publisher and the checked environment** keep the accepted
   declarations; a later declaration may use only earlier accepted ones,
   and a failed check changes nothing
   ([ADR 0012](../adr/0012-checked-environment.md)). Version 0 is written
   and tested ([checked environment](../programming/CHECKED_ENVIRONMENT.md))
   and the checker publishes its accepted declarations into it; it
   awaits its review gate.
6. **The term printer** exists: it prints a statement and its proof in
   Lean's notation, ASCII or LaTeX, with the binder names the export
   recorded ([printing terms](TERM_PRINTER.md)). Printing the checked
   statement lets a person see what was actually checked — the defence
   against a reader that decoded a different claim. `leanforth print` also prints a proof outline
   from the checker's derivation log (task 2.4.4; untrusted presentation).
7. **Lean as referee.** `make check` compares LeanForth's
   passes and the printer with Lean on finite tables, and Lean's own
   verdicts on the first checker's
   [expected results](../reviews/FIRST_CHECKER_EXPECTED.md).

## Verifying a Forth program

Today, for the committed example words, the program words write the
program IR (a small intermediate language whose meaning is defined in
Lean), a Python generator writes the proof obligations from the contract,
Lean writes and checks the proofs, and, for clamp, LeanForth's checker
re-checks Lean's export and a Python script writes a receipt that keeps
three answers apart: was a proof *checked*, are the obligations *proved*,
and did the word *run* correctly in tests. No command does this for your
own word: `leanforth verify` (plan 8.4.1) is not started and does not
exist. The box drawn with a dashed outline below is that missing command.

```mermaid
flowchart TD
  fs["Forth source<br/>src/program/clamp.fs, examples.fs"]
  contract["Contract: what the word needs and guarantees<br/>a contract file, e.g. tests/program/contracts/lf-clamp.contract"]
  rdr["Program words<br/>src/program/verify.fs<br/>untrusted, named in receipts as trusted-reader"]
  ir["Program IR 0.1, text form<br/>tests/program/ir/"]
  model["IR semantics in Lean<br/>tests/reference/program-ir.lean<br/>proves each word's IR equals its reference model"]
  interp["IR interpreter vs host word vs Lean model<br/>src/program/ir-run.fs, task 2.5.4"]
  vc["Verification-condition generator v0<br/>obligations from IR and contract<br/>scripts/program_vc.py, untrusted, task 2.5.5"]
  leanchk["Proofs written and checked by Lean<br/>tactic scripts from the generator"]
  lfchk["Lean's proofs exported with their closure<br/>re-checked by the LeanForth checker<br/>bin/leanforth check, task 5.5.1, clamp"]
  run["RUN: tests on Gforth<br/>make test-program<br/>testing is not proof"]
  receipt["Receipt, schema 0.3<br/>check, verify and run kept apart<br/>clamp: LeanForth's verdict, task 5.5.1"]

  fs --> rdr --> ir
  ir --> model --> leanchk
  ir --> interp
  ir --> vc
  contract --> vc
  vc --> leanchk
  leanchk --> lfchk
  fs --> run
  lfchk --> receipt
  interp --> receipt
  run --> receipt

  cmd["leanforth verify<br/>plan 8.4.1, not started"]
  cmd -.-> fs

  classDef gate stroke-width: 3px
  class lfchk gate
  classDef missing stroke-dasharray: 5 5
  class cmd missing
```

What exists today, for the six example words (clamp, checked add, checked
abs, in-range, factorial, gcd):

- The **program words** (`src/program/verify.fs`; the earlier `src/program/ir-reader.fs` is kept for comparison) translate their source into IR 0.1 with the source
  location of every token, and refuses anything outside IR 0.1 with a
  diagnostic ([program IR](../programming/PROGRAM_IR.md)).
- **Lean proves**, for every cell width, that each word's IR returns
  exactly what its reference model returns, and refutes two deliberately
  wrong programs. These proofs are written and checked by Lean, not by LeanForth.
- **Runtime tests** compare the host words with Lean models on finite
  input tables.
- The **IR interpreter** runs IR as the Lean model does and agrees with
  the host words and with Lean on 5,152 cases and 300 random programs
  ([IR interpreter](../programming/PROGRAM_IR_RUN.md)).
- The **verification-condition generator** v0 turns IR plus a contract
  into Lean obligations; Lean proves them for clamp, checked add, checked
  abs and in-range, and refutes three wrong contracts
  ([verification conditions](../programming/PROGRAM_VC.md)).
- For **clamp**, Lean's exporter writes the contract theorem and its two
  obligations with every declaration they use (4,277), and **LeanForth's
  checker re-checks that export** and accepts it; an export whose program IR
  term, postcondition or proof term was changed after Lean proved it is
  rejected (plan 5.5.1). Lean wrote the proofs; LeanForth wrote none of
  them.
- The **receipt format** exists as a JSON Schema, version 0.3
  ([program receipts](../programming/PROGRAM_RECEIPTS.md)), and the first
  receipt, for clamp, is generated: `accepted-by-leanforth` (LeanForth's
  verdict on Lean's proofs), obligations discharged, 986 runs passed.

Not established: that Gforth runs the words as the IR semantics says (the
interpreter comparison tests it; testing is not proof), that the reader's
translation is faithful (it is tested, not proved), and anything about stack overflow, other hosts or
compiled code. The program track's destination is most of the Forth-2012
Core word set, in five stages (plan, "Program-track goal").
