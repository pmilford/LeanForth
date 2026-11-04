# Owner decisions in plain language

**Status: decided by the project owner on 2026-11-02; answers are recorded
at the end.** This document restates the open review
questions from [the kernel review packet](../reviews/KERNEL_REVIEW.md) and
[the checked environment review](../reviews/CHECKED_ENVIRONMENT_REVIEW.md) for a reader
who does not know Lean, theorem proving or program verification. Each
question gives the background, the options, a recommendation and the reasons.

## A few words first

- **Proof checker ("kernel").** A small program that reads a proof and says
  *accepted* or *not accepted*. Everything LeanForth promises rests on it: if
  it wrongly accepts a bad proof, every result built on it becomes worthless.
  That is why the project rules treat it so carefully.
- **Lean.** An existing, widely used proof system. **Mathlib** is Lean's huge
  shared library of mathematics (well over 100,000 results). LeanForth aims to
  check the same proofs Lean checks, independently, written in Forth.
- **Declaration.** One named item in the library: a *definition* (a named
  value or function) or a *theorem* (a statement plus its proof).
- **Axiom.** A statement accepted *without* proof. Each one is a trusted
  assumption, so the list of allowed axioms must be short and deliberate.
- **Differential test.** Give the same input to LeanForth and to Lean and
  check that they agree. Lean is the reference.

## Why these questions block progress

The project rules say a *human expert* must review the checker's rules before
they are trusted. The only human review so far (2026-10-30) said "continue",
but explicitly left one technical soundness question open. Since then Codex
kept building experiments *around* that gate instead of through it: 51
experimental modules exist, but no checker. Without these decisions the
project cannot reach its next step, the first independently checked
declaration.

## Decision 1 — How do we trust the checker without an in-house expert?

**Background.** The review gate assumes someone who can read typing rules and
judge whether they are correct. If nobody on the project can, the gate can
never be passed, and work stalls or drifts.

**Options.**

1. **Lean is the referee (recommended).** Copy Lean's own published checking
   rules as closely as possible rather than inventing new ones. Accept a
   checker change only when all of these hold:
   - it agrees with Lean on a large and growing set of tests, including
     deliberately broken proofs that must be rejected;
   - an independent AI review of that change finds no unresolved problem;
   - you approve a short plain-language summary of what changed.
   Until an outside Lean expert has audited the checker, every result is
   labelled *"experimental — not independently audited"*. Plan to find or pay
   such an expert before any public claim that LeanForth is trustworthy.
2. **Expert first.** Stop checker work until an outside expert has reviewed
   the rules. Safest, but could stall the project for months and costs money.
3. **AI review is enough.** Fastest, but AI reviewers can share blind spots
   and be confidently wrong. Not recommended for the one component everything
   depends on.

**Recommendation: option 1.** The project's goal is to agree with Lean, so
"agrees with Lean" is the right test of correctness. Test results are
objective; you can read pass and fail counts without understanding the
mathematics. It unblocks the work without pretending an expert has checked
it, and keeps the label honest until one has.

Under option 1, the purely technical designs still awaiting review — how
checked results are stored, how stale references are prevented, and the
internal representations in ADRs 0004, 0005 and 0007 — would be decided by
the same process. My recommendation for storage is the simplest safe design:
the library only ever grows, one check runs at a time, a new entry is added
only after it fully passes, and nothing saved to disk is trusted without being
checked again.

## Decision 2 — What should the first checker accept?

**Background.** Lean has many kinds of declarations: simple definitions,
theorems, recursive functions, data types, and more. The proposal starts
with only simple, non-recursive definitions and theorems. Everything else is
reported as not yet supported.

**Options.**

1. **Narrow start with three outcomes (recommended).** Accept only simple
   definitions and theorems at first. Every check ends in exactly one of:
   *accepted*; *rejected* (definitely wrong); or *unsupported / unknown*
   (could not decide). Only *accepted* ever counts.
2. **Include data types from the start.** More useful sooner, but a much
   bigger first step with more room for mistakes.

**Recommendation: option 1.** It is the smallest step that can be built and
tested properly. Keeping "could not decide" separate from "wrong" stops a
limitation from being mistaken for a disproof, or for success. Data types
should come soon after, because nearly all of Mathlib depends on them.

## Decision 3 — What happens when the checker cannot tell if two things are equal?

**Background.** Checking a proof often means deciding whether two
expressions mean the same thing — for example, a name and the definition it
stands for, or `2 + 2` and `4` after computing. Lean decides this by
"unfolding" definitions and computing. The proposed first checker handles
only the simplest cases and answers *unknown* otherwise. *Unknown* is never
treated as success. The technical question left open on 2026-10-30 concerns
exactly this comparison; the cautious version avoids it, but the next step
must answer it.

**Options.**

1. **Cautious first, unfolding next (recommended).** Ship the cautious
   version, then make unfolding definitions — following Lean's own method
   and tested against Lean — the very next step.
2. **Full Lean equality now.** Fewer *unknown* answers, but a much larger and
   riskier first version.

**Recommendation: option 1.** Being cautious can only make the checker fail
to accept some true proofs; it can never make it accept a false one. But
almost every real Lean proof needs unfolding, so it cannot be postponed long.

## Decision 4 — Which axioms are allowed?

**Background.** Lean and Mathlib rely on three standard axioms that nearly
all mathematicians accept:

- **Propositional extensionality** (`propext`): two statements that each imply
  the other are equal.
- **Choice** (`Classical.choice`): from any non-empty collection you can pick
  an element. Proof by contradiction relies on it.
- **Quotient soundness** (`Quot.sound`): needed to build things like
  fractions from pairs of numbers.

Mathlib cannot be used without them. Lean also has two "trust the compiler"
axioms (`Lean.ofReduceBool`, `Lean.trustCompiler`) that accept whatever
Lean's compiled code computes. They are not mathematical assumptions, and
Mathlib largely avoids them.

**Options.**

1. **None now; the standard three later; never compiler trust
   (recommended).** The first checker allows no axioms; it does not need
   any. When importing Lean's library starts, allow exactly the three
   standard axioms, each with its exact Lean statement. Never allow the
   compiler-trust axioms. Every accepted theorem lists the axioms it depends
   on, and you approve any future change to the list, recorded in a
   versioned file.
2. **No axioms ever.** Purer, but most of Mathlib could then never be
   accepted, which contradicts the project goal.
3. **Allow whatever Lean allows.** Simplest, but quietly trusts Lean's
   compiler, which LeanForth exists to check independently.

**Recommendation: option 1.** It matches what mathematicians and the Lean
community accept, keeps the full-Mathlib goal reachable, refuses the
non-mathematical shortcut, and keeps every assumption visible.

## Recorded answers

On 2026-11-02 the project owner, who states they are not an expert in Lean,
theorem proving or program correctness, answered these four questions in a
Claude Code session. The question text above had SHA-256
`c03d2d6eed88015d069dc4b1260577c0434deeaab9dd75c54411a2be2c743196` before
this section and the status line were filled in.

1. **Trust model: option 1, Lean is the referee.** A checker change requires
   agreement with pinned Lean on positive and negative tests, an independent
   AI review with no unresolved findings, and owner approval of a
   plain-language summary. Results are labelled *experimental — not
   independently audited* until an outside Lean expert audits the checker.
   Technical designs (storage of checked results, stale-reference handling,
   ADRs 0004, 0005, 0006 and 0007) are decided by this same process.
2. **First scope: option 1, narrow start with three outcomes**, with the
   owner's addition: *"should also test the failure paths. unknown/rejected"*.
   Every check therefore needs tests that reach each of *accepted*,
   *rejected* and *unsupported/unknown*, and tests showing that neither
   failure outcome is ever reported or stored as accepted.
3. **Equality: option 1, cautious first, unfolding next.** Unfolding
   definitions, following Lean's method and tested against Lean, is the next
   checker step after the first checked declaration. It must settle the
   conversion question left open on 2026-10-30.
4. **Axioms: option 1.** No axioms for the first checker. When library import
   begins, exactly `propext`, `Classical.choice` and `Quot.sound`, each with
   its exact Lean 4.35.0 statement, may be added to a versioned allowlist.
   `Lean.ofReduceBool` and `Lean.trustCompiler` are never allowed. Every
   accepted theorem reports the axioms it depends on, and the owner approves
   any change to the allowlist.

These answers are policy decisions. They do not approve any implementation,
and they are not an expert review of the checker's rules; that is why
decision 1 keeps the *not independently audited* label.

## Planning answers (2026-11-02, later the same day)

The owner answered the planning questions of
[the draft plan](PLAN_DRAFT.md#8-questions-for-the-owner) and two design
records in the same Claude Code session. Quoted words are the owner's own.

- **Re-entrancy, [ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md):
  approved, build it now** during the remaining refactor. Parallel checking
  uses Forth's own multitasking design rather than separate operating-system
  processes: *"I'd prefer a forth compatible solution, not a linux
  multiprocessing solution."*
- **Gforth-only features (OQ-7):** Forth-style tasks (`USER` variables,
  tasks, `PAUSE`, semaphores) may be used, behind a small adapter, with a
  serial path that CI tests. The C interface, timers and command-line
  arguments were not discussed; ask when one is needed.
- **Outcome vocabulary, [ADR 0008](../adr/0008-outcome-vocabulary.md):
  approved**, with the owner's question *"is it worthwhile to split exhausted
  into ran out of processing and ran out of memory?"* Answer adopted: yes —
  *exhausted* (2) now means out of fuel, and a new *full* (6) means a store,
  stack or depth limit was reached. Neither is ever accepted.
- **Legacy (OQ-8): approved** deletion of `src/legacy/` once the current code
  has at least the same test coverage; the owner does not need to see the
  list first (the paths are still listed in the commit). Tests of legacy
  code move to `tests/legacy/` beside it: *"I'm surprised the tests were not
  already moved to legacy themselves."*
- **Checker isolation (OQ-1): separate program.** The checker runs as its own
  program and receives proofs only as data.
- **Saved results (OQ-3): two modes.** *"Most of the time we are running in
  development or research mode, so don't need high levels of trust. a 'final
  run' would be in full trust mode."* Development and research runs may reuse
  saved results, labelled as not re-checked in this run; a final run
  re-checks everything and reads no saved results. Only a final run's results
  support a claim.
- **Lean reader (OQ-4): a Forth reader** on the checking path; Python stays
  as an independent second reader for tests.
- **Big numbers (OQ-6): our own Forth module**, *"but it should be able to be
  very fast too."*
- **Program track (OQ-5): the honest order** — the first program proof
  checked by LeanForth itself arrives with data types (phase 5).
- **Mathlib download (OQ-9): approved**, after the owner freed disk space
  (160 GB free); into `.tools/` with hashes recorded.
- **Outside Lean expert (OQ-10): only before a public trust claim.**
- **Proof explanations (OQ-11): templates first**, *"but make very easy from
  the start for ai written - and also human written that can stick with the
  proof as it evolves."*
- **Parallel publishing (OQ-2):** treated as answered by approving ADR 0009
  (one publisher, append-only library, parallel verdicts identical to serial
  ones), keeping the recommended condition that a feature is checked in
  parallel only after its serial version has passed its gate.
- **Tooling (OQ-12):** not asked; the default that installs nothing applies
  (Mermaid checked on GitHub, standard-library JSON checks).

## Product dependencies and module loading (2026-11-02)

- **End users need only a Forth system and an NDJSON file.** *"overall I'd
  like not [to] have any python dependency, and hopefully not any lean
  dependency, except a ndjson file ... during development it doesn't matter,
  but keeping end user downloads and installs and updating to a minimum is a
  good thing."* Everything on the user's path — reading Lean exports,
  checking, the command-line tool, printing proofs and receipts — is Forth.
  Python and Lean remain development tools (tests, oracles, metrics,
  producing exports). Users who check existing Lean or Mathlib developments
  use a published export; only users who write new Lean source need Lean, to
  produce its export.
- **Each file loads what it uses, and only that.** Every module `require`s
  its direct dependencies; *"main should only require its direct
  requirements, not the ones needed by the modules."*

## Legacy retirement and the first checker's rules (2026-11-02, evening)

- **Retiring `src/legacy/`:** the four capabilities only legacy code had are
  not ported first. Theorem mode (statement must be a proposition) is
  rebuilt in phase 2; the old loader (`src/import/load.fs`) stays with its
  round-trip tests until the Forth NDJSON reader replaces it; open terms
  under a supplied context wait for a Lean-style local context; the stricter
  universe rule stays, and the checked environment needs a per-declaration
  universe scope. All four answers were the recommended options.
- **First checker gate, rules only** ([gate summary](../reviews/FIRST_CHECKER_GATE.md#owners-answer),
  [ADR 0011](../adr/0011-definite-rejection.md)): the rule list is approved
  before coding (G1); *rejected* means Lean would reject it too (G2); axioms
  are *unsupported* in the first checker (G3); rule D5 is included (G4). The
  checker code still needs its own approval with test results.
- **Second set of first-checker gate questions (G6–G11), same evening:**
  compare under differing argument types as Lean does (ADR 0003 Amendment
  1); rule D4 rejects through equal argument types (ADR 0011 amended); ADR
  0012's library design approved; no speculative checking for now; the
  library points at the checked imported records; development mode
  labels saved results and their dependents. All recommended options; the
  checker code still needs its own approval with test results.

## Program-track goal: most of Forth-2012 Core (2026-11-02, night)

The owner approved an explicit destination for the verified-program track,
comparable to "all of Mathlib" for theorems: verify words written in most of
the Forth-2012 Core word set, in stages — (1) core arithmetic and stack
words, double-cell and unsigned arithmetic, `DO`/`LOOP`; (2) a memory model
for cells, characters and buffers with explicit ownership and no-overlap
contracts; (3) execution tokens with known targets, `DEFER`, `CATCH`/
`THROW`; (4) `CREATE`/`DOES>`/`VALUE` data treated as declared data; (5)
strings and I/O as effects with stated assumptions. Compile-time
metaprogramming (`IMMEDIATE`, `POSTPONE`, `EVALUATE`, run-time dictionary
changes) stays *unsupported* inside verified words; only the words it
produces can be verified.

## Progress marks and program-reader names (2026-11-02, night)

- **Done marks.** The owner kept the five tasks the progress report marks
  done: T1.3 (CI on Gforth 0.7.3 and the pinned tools), T4.1 and T5.1 (the
  approved conversion and rejection rules and the checked-environment
  design) and P3.1 and P3.2 (IR 0.1 and its Lean semantics). Design and
  specification tasks count as done when they meet their own acceptance
  text; the report says which ones are designs only.
- **Names in Forth source are case-independent.** Prompted by the owner
  ("Forth is case independent"): the program reader finds names ignoring
  ASCII case, as Gforth 0.7.3 and 1.0 do and as Forth-2012 3.4.2 allows
  (standard words must be found in upper case). A definition whose name
  equals an existing one apart from case is a redefinition and refused;
  names with bytes outside printable ASCII are refused, because how a
  system folds them is implementation-defined. This replaces the review's
  first suggestion of refusing upper-case names.
- **LeanForth theorem syntax is words, not parsed strings** (2026-11-02,
  night). The owner: "I was hoping we can encode the theorems and proofs
  in leanforth words, not strings that are parsed." Theorems and proofs
  written in LeanForth are ordinary Forth word sequences run by Forth's
  own interpreter; there is no separate expression grammar. Defining and
  token-reading words (as `:` reads a name) are allowed; mathematical
  notation stays in the printer and rendering layer. Applies to ADR 0017
  (plan task 8.1.1).
- **ADR 0017, LeanForth syntax: approved as the basis for building it**
  (2026-11-02, night; plan 8.1.2 may start). The owner's answers to the
  ADR's decisions, each as recommended: (1) the overall shape, Forth
  words run by Forth's own interpreter, postfix, binder words that read
  their name, `theorem NAME … := … end NAME`; (2) proof files use only
  LeanForth's fixed vocabulary for now: no helper words defined inside
  proof files, and Forth's `+` keeps its machine meaning (libraries of
  user words may come later in the authoring program); (3) names in
  theorem files are case-sensitive, as in Lean and Mathlib, unlike Forth
  program files; (4) labels and `note"`/`ai-note"` notes beside each step,
  kept through edits and never checked, are what the owner meant by notes
  that stay with an evolving proof. The implementation still passes the
  [parser] gate before it is relied on.

## Gate answers and working guidelines (2026-11-03)

- **Rejection rules, [kernel] gate: approved** (plan task 2.2.1, ADR 0011
  as implemented), as recommended: when the extra rejection analysis runs
  out of fuel or room the answer stays *unknown*; Lean's rejection of a
  "for all" whose body is not a type (`infer_pi`'s `ensure_sort` on the
  body) is added as an ADR 0011 amendment through the same gate. Every
  accepted result keeps the label *experimental — not independently
  audited*.
- **Behave identically to Lean.** The owner, with that approval: "In
  general we should behave identical to Lean. Too soon to 'improve' lean.
  leave that for later. Working worse than Lean is of no use." LeanForth's
  target is Lean 4.35.0's exact verdicts; an *unknown* where Lean decides
  is a gap to close, not a design choice, and no rule may differ from
  Lean's even where it would be "better". Resource limits (*exhausted*,
  *full*) are reported as such.
- **ADR 0016, the compact store: accepted**, with its three
  recommendations: the basis for plan tasks 6.2.0–6.2.3; every theorem's
  proof stays in memory for now; equal terms are stored once even though
  the exporter already shares them.
- **NDJSON reader, [import] gate: approved** (second round of questions,
  the same day), with a new task: LeanForth's export script writes a
  manifest beside each export (SHA-256 of the file, line and record
  counts, Lean version, Mathlib commit), and import checks it by default,
  computing SHA-256 in Forth during its single read; a missing or wrong
  manifest is *invalid* unless the user asks to skip it. The owner had
  asked whether Lean's export carries a signature or checksum: it does not
  (its first line names only the exporter, format and Lean versions, which
  the reader already requires to be the pinned ones), and a file cut off
  cleanly between two lines would otherwise read as a shorter library.
  Also: keep adding reader checks, and add an upgrade test that compares
  the Forth reader with the independent Python reader record by record on
  each new Lean or Mathlib. The owner: "maintaining full compatibility with
  Mathlib is of highest importance." The owner also asked about
  re-exporting Mathlib from LeanForth and comparing it byte for byte with
  Lean's file (answered in the progress report).
- **ADR 0013, the derivation log: accepted** with D1–D5 as recommended
  (off unless asked; "log incomplete at step N" when full, verdict
  unchanged; intermediate formulas kept; short readable proof by default
  with `--detail`; the checker's usual gate with "nothing changed" as the
  evidence). The owner: "the ability to pretty print is also important,
  latex and unicode I assume." Printing is Unicode first, through the term
  printer that matches Lean's `#print`; LaTeX becomes a second output mode
  of the same (untrusted) printer.
- **ADR 0018, exceptions: accepted** as recommended: inside one
  operation *invalid*, *exhausted* and *full* may be thrown and are turned
  back into outcomes at its entry; adoption module by module (the job-pool
  prerequisite is already merged). The owner asked about the clean-up
  when jumping straight out (allocated memory, processes, other): the ADR's
  decisions 3, 4 and 6 cover it — store marks roll every store back,
  files and heap buffers are held only by "resource owner" words that
  release them on every path, context records hold no heap memory, and a
  `THROW` never crosses a job boundary (each job catches its own and its
  context is replaced).
- **ADR 0010, word lists: accepted** as recommended: a public and a
  private word list per part of the program, a check that no name is
  defined twice, one-line switches before each group, the library first
  and then the checked environment.
- **Speed goal.** One-thread performance as close to Lean's kernel as
  possible, or better; parallel checking then exceeds it.
- **Machine use.** At most about 10 processes or workers for
  compute-heavy parallel LeanForth runs (for example checking a big
  theorem in parallel), so the rest of the computer stays fast; full
  parallelism only for specific tests. Corrected by the owner the same day:
  this does not limit how many development agents run, as long as they do
  not take too much CPU ("continue with more agents in parallel").
- **Local Gforth 0.7.3 runs only for major changes** (owner, the same
  day, to speed work up: "I believe it has been very very compatible").
  CI still runs `make test` on Gforth 0.7.3 for every push; locally it runs
  only for host-sensitive changes (the job pool, contexts, portability and
  32-bit access words, byte reading, exceptions, `BASE`, cell width) and
  before gate decisions.
- **Program correctness is equally important, without slowing the Lean
  track.** The owner: "the forth program correctness is equally important,
  but, lets not slow down the lean for it. I don't have a good test in mind
  for the program correctness, but perhaps SHA-256 should be a good one?"
  Recorded as the program track's flagship target: prove LeanForth's own
  SHA-256 (`src/lib/sha256.fs`) equal to FIPS 180-4 in five stages
  ([plan](PLAN_DRAFT.md#program-track-goal-most-of-forth-2012-core-owner-2026-11-02)),
  in the program-track lane.
- **Record every Lean limitation; an improved mode later.** The owner:
  "there are a number of issues that come, like the universe one just now
  … some are just what lean does, but, perhaps some lead to theorems that
  could be solved without the limitations. make sure to take careful note
  of anything that could lead to better theorem solving. we need 100%
  compatibility with lean, but, also, if we can have an improved solver
  mode, that would be great!" Kept in [BEYOND_LEAN.md](BEYOND_LEAN.md); the
  improved mode is opt-in, labelled and designed after phase 6 (plan W8).
- **General-purpose code is written as reusable libraries.** The owner:
  "functionality like the bignum library should, in general, be well
  factored so it can be used by other users and programs, not tightly
  coupled to LeanForth … They can be LeanForth specific if we gain a lot
  from that, but otherwise should be more general." Added to `AGENTS.md`;
  audit and plan task 1.1.8 in
  [FORTH_LIBRARY.md](../development/FORTH_LIBRARY.md#reusability-the-libraries-as-standalone-forth-code).
- **Program correctness the Forth way: words in two modes** (owner, the
  same day, on the program reader's [parser] gate, which is therefore
  **not approved** and paused). The owner asked whether the reader is
  "1) an ascii file read and translation … or 2) a set of LeanForth words
  with the same names, that, instead of running, output the IR (in
  correctness mode) and execute in run mode", and: "I much prefer 2 and
  your description is vague", "this is important and may need more
  design", and "option 1 for program correctness isn't a very Forth like
  way to operate." Today's reader is option 1 (it splits the file into
  tokens itself and looks them up in its own table; nothing in the file
  runs). A design record for option 2 — the same source loaded with a
  LeanForth vocabulary whose words emit IR, and with ordinary Forth to
  run — comes first, with a prototype, before any gate question.
- **ADR 0019, program words in two modes: adopted in direction**
  (2026-11-03). The owner's answers: (1) adopt option 2, "but also
  consider if there is a way to do it with a mode shift rather than an
  alias. Either case probably needs special handling of defining words and
  looping" — a study of a mode shift (one set of words switching between
  writing IR and running, like Forth's interpret and compile states)
  against the separate vocabulary, and the design of defining words and
  loops, come before building it; (2) IR first, symbolic execution later;
  (3) today's text reader stays only as a cross-check until the new design
  passes its [parser] gate, then retires, keeping its tests; (4) names that
  read as numbers are refused in correctness mode.
- **Checked environment v0, [kernel] gate: approved** (2026-11-03, plan
  task 2.2.2, ADR 0012 with Amendment 1), as recommended, after six
  independent review rounds (the last found nothing blocking; its three
  small items merged) and the failure-path suite (4,493 injected runs,
  nothing failed ever stored, published or printed as accepted). Every
  accepted result stays labelled *experimental — not independently
  audited*.
- **Program receipt format 0.2, [format] gate: approved** (2026-11-03,
  plan task 2.5.1), as recommended, after three review rounds. The
  approved schema file is `schemas/program-receipt-0.2.schema.json`,
  SHA-256 `bb76793e1cba339d…` (pinned by a test); any later change, even
  an encoding fix, becomes a new version. A receipt that validates is well
  formed, not proved true: it cannot show that its axiom list is complete,
  which only replaying the check can (plan 5.5.2). The two-mode program
  design (ADR 0019) will add an assumption kind for its vocabulary in a
  later version. Schema 0.1 was never approved and is refused.
- **Later: investigate offloading part of the work to a GPU.** Under the
  design rules in `AGENTS.md` a GPU never belongs to the trusted kernel and
  a CPU path is always kept; candidates are untrusted bulk work such as
  hashing, decoding or pre-filtering.
- **Working practice.** Agent notes, reviews and probes are kept in a
  folder that survives a restart (`.claude/work/`), and agents commit work
  in progress on their own branches, after a restart wiped `/tmp` and a
  usage limit cut agents off on 2026-11-03. Progress reports should say
  plainly what each part can do today, for example what LeanForth can do
  with an imported Mathlib.
