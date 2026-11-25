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
- **ADR 0019, mode shift or separate vocabulary: both, mode shift
  first** (2026-11-03). The owner: "If we have both already prototyped,
  Keep working in both. With precidence on mode shift." The portable mode
  shift (Forth's own words, each with a verification meaning in a table
  keyed by the word's identity, run by a short loop over `PARSE-NAME` and
  `SEARCH-WORDLIST`) is built first and is the primary design; the
  separate vocabulary is kept working beside it, sharing the words'
  actions, and both are tested to give the same IR.
- **LeanForth syntax words, [parser] gate: approved** (2026-11-03, plan
  task 8.1.2, ADR 0017), as recommended, after two clean review rounds:
  67 declarations (111 terms) equal Lean's own term for term, binder names
  and kinds and the protected flag included. Limits recorded: untrusted
  authoring code until the separate authoring program (8.2.1); where Lean
  picks between constants by type the words ask for the full name; field
  notation and `export` are not supported yet; Lean's exporter does not
  record `protected`, so real imports need it from elsewhere (8.2.1).
- **Declaration check, [kernel] and [bypass] gates: approved**
  (2026-11-03, plan task 2.2.3), with the universe-level fix that ports
  Lean's level code exactly (ADR 0011 Amendment 1, rules S4 and K6), as
  recommended: 69 table rows and 49 universe rows give Lean's answers, and
  1,800 random level pairs and 800 random declarations match Lean. Every
  acceptance stays labelled *experimental — not independently audited*.
- **ADR 0014, definitional equality (phase 4): accepted** (2026-11-03) with
  G5 and Q-A to Q-D as recommended: unfold theorems exactly as Lean does
  and keep proofs in memory; replace the cautious rules by a line-by-line
  copy of Lean's procedure once it passes its gate (the old rules stay as
  a cross-check during the switch); Lean's free-variable naming inside a
  check; Lean's caches copied exactly, per declaration; *unknown* for
  Lean's specially named constants until phase 5.
- **Speed target (ADR 0014 Q-E):** measure time per distinct node and
  cache hits from the start; within twice Lean's one-thread time before
  phase 6, then close the gap. The owner: "I'm unclear how close we can
  get, even if 2x is possible, so don't spend too much time optimizing
  yet. I'm thinking it will mostly using smarter algorithms. there is a
  chance we will end up using a machine code (assember) version of a few
  words to speed up, but we lose so much portability doing that, i'd much
  prefer avoid." Rule: algorithms first; no machine code without the
  owner's decision.
- **Lean's built-in arithmetic trusted by name (ADR 0015 Q1): copy Lean by
  default, with a toggle.** The owner: "lets default to the same way as
  Lean, but have an easy toggle to make more secure." By default LeanForth
  computes `Nat.add` and the other built-in operations by name exactly as
  Lean does; a documented option (for example `--strict-builtins`) answers
  *unsupported* unless `Nat` and its operations are exactly Lean 4.35.0's
  own. Answer to the owner's question: other arithmetic (clock arithmetic
  `Fin n`, `ZMod n`, integers) uses its own types and operations in Lean
  and never redefines `Nat.add`; an ordinary Lean file cannot redefine it
  at all (the name exists, and a second declaration is refused); only files
  that start with `prelude`, such as Lean's own core library and kernel
  tests, can. Recorded in BEYOND_LEAN.
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

## Data types, axioms and imports (2026-11-03, late night)

Answers to ADR 0015's questions Q2–Q5 and to the importer gate, given in a
Claude Code session after the questions were asked in plain words.

- **ADR 0015 Q2, exported fields Lean's checker ignores: as Lean, with a
  warning.** LeanForth accepts an export whose recorded numbers (for
  example "is recursive") or missing recursor Lean's own checker ignores,
  uses only its own computed values and prints a warning. The owner added:
  "but also consider if there is a better design that we can make an option
  in the future" — recorded as a later option, a *strict import* that
  refuses any field disagreeing with the rebuilt type (plan W8).
- **ADR 0015 Q3 and Q4: the design is approved as a whole, one gate per
  implementation task, and task 5.2.1a starts now** (non-recursive blocks,
  *unknown* wherever Lean would unfold), before phase 4 is finished.
- **ADR 0015 Q5 and an amendment to decision 4: Lean's verdict, marked.**
  The owner first answered "We should be lean compatible. if lean accepts
  sorryAx with a warning, so should we. we can add a flag to disable this."
  After it was explained that `sorryAx` is false (it proves `0 = 1`) and
  stands for a missing proof, the owner chose: by default LeanForth gives
  Lean's kernel verdict, so a declaration using `sorryAx` or any other
  axiom outside `propext`, `Classical.choice` and `Quot.sound` (or one of
  those with a different statement) is *accepted* as Lean accepts it, but
  labelled **NOT PROVED: depends on** the axiom, as is everything that uses
  it; it has its own exit code and never counts as proved in receipts or
  reports. A flag (for example `--standard-axioms-only`) answers
  *unsupported* instead. Decision 4 becomes: only the three standard
  axioms, with their exact Lean 4.35.0 statements, count as *proved*; the
  versioned allowlist and the owner's approval of changes to it stay.
  `Lean.ofReduceBool` and `Lean.trustCompiler` are never on the list; a
  declaration that needs Lean's compiled code to run in the kernel stays
  *unsupported*.
- **Importer stage approved [import]** (ADR 0016 C9 steps 1, 2 and 5;
  `src/import/stage.fs`, `stage-records.fs`; independent re-review clean,
  minor limits documented). Asked a third time, the owner chose *Approve*.
  Earlier the owner added: "add to the future todo for soon to test several
  other libraries, a few small ones and the biggest one perhaps. - but not
  yet." Recorded as plan task 6.1.6 (import other Lean libraries built with
  Lean 4.35.0: a few small ones and the largest available).
- **Default is always Lean.** The owner: "for the flags we are adding...
  the default with no flags should always be 100% lean compatible." Every
  option that differs from Lean 4.35.0 (`--strict-builtins`,
  `--standard-axioms-only`, a strict import, a later improved mode) is
  opt-in; with no options LeanForth's verdicts are Lean's.

## Program words and run records approved (2026-11-04)

- **Two-mode program words approved [parser]** (ADR 0019, mode shift with
  the alias vocabulary beside it; merges ce25b28, afcb4cf, 1b08f1f;
  independent review rvPW, three rounds, every finding closed). Approved
  with its stated limits: the step from source text to IR is tested, not
  proved (receipt assumption A3); a standard word redefined before the
  program words load is not noticed, nor a compile-only word redefined
  after they load on Gforth 0.7.3; run mode trusts its Forth's standard
  words. The owner added: "reconsider the refusal of redefinintions - for
  example sometimes adding a dup . into a word definition for debugging
  helps - surely they can nest the names?" Recorded as the next program-IR
  design step (IR 0.2, ADR 0019 amendment): redefinition with Forth's own
  early binding, each version of a name its own IR name, and output words
  such as `.` as effects that leave the stack proof unchanged.
- **Run-record format 0.1 approved [format]** (`docs/programming/RUN_RECORDS.md`;
  independent review rvRP3, three rounds, every finding closed). The
  in-progress tie of the importer's two passes for reads without the
  manifest changes no field and gets its own review before merging.
- **Cause of the 2026-11-04 crashes.** Both the WSL crash and the Claude
  Code crash were the new test wrapper `scripts/gforth-strict.sh` calling
  itself (about a thousand copies exhausted 39 GB of memory and 16 GB of
  swap); fixed in e6a0a74 with self-reference and depth guards. No work
  was lost: agents' uncommitted changes were saved as WIP commits.

## IR 0.2 design approved (2026-11-04)

ADR 0019 Amendment 1 (agent IR2; probes in
`docs/development/measurements/ir-0.2-probes-2026-11-04/`):

- **Own words may be redefined, Forth's way:** each use binds to the
  version visible where it is compiled; each version has its own IR name
  (`clamp`, `clamp'1`, …). The owner asked: "is this able to be done in a
  forth friendly native approach - not like the previous program to read
  ascii and process it?" Answer recorded in the ADR: yes, it extends the
  approved mode-shift program words, in which Forth's own interpreter reads
  the file and the words' verification semantics write the IR.
- **Standard words stay refused** for now (recommended option).
- **Output words allowed as effects** (`.`, `U.`, `CR`, `EMIT`, `SPACE`,
  `SPACES`, `."`, `S" … " TYPE`, `.S`); stack proofs unchanged.
- **SHA-2 additions approved:** `LSHIFT`, `-rot`, Forth-2012 number
  prefixes and 32-bit literals. The owner: "the non-standard words should
  have portability implementations" — `-rot` and any other non-standard
  word used gets a portable Forth-2012 definition for hosts that lack it.
- Receipt schema 0.3 comes to the [format] gate with the first receipt
  that needs it.

## Import read approved; fixed limits to become dynamic (2026-11-04)

- **Run-record reading change approved [import]** (`src/import/checker-input.fs`:
  both passes of a read, and the recorded SHA-256, must agree, with or
  without the manifest; independent review rvRP3, four rounds, clean).
- **Checker on the large store: held.** The owner asked: "I;m unclear if
  there is a hardcoded limit of universe parameter lists, 64, does Lean have
  this? I think it probably should be dynamic. we haven't tried out other
  large imports." Answer: Lean has no such limit (universe parameters are a
  list); Mathlib uses up to 30. LeanForth's fixed limits of 64 — universe
  arguments per reference and parameters per declaration, the level
  context's parameter names (Init already uses 62) and the walk, frame and
  binder depths (Mathlib terms nest up to 1,221 deep) — become dynamic,
  bounded only by memory (*full*), before the [kernel] gate is asked again
  (plan 6.2.0 brought forward).

## Readable proofs approved (2026-11-04)

- **Derivation log and proof outlines approved (ADR 0013 gate D5; plan
  2.4.1, 2.4.4; `bin/leanforth print`).** Independent review rvRB, three
  rounds, every finding fixed: the whole suite passes with the log on in
  three settings, the printer prints only what the checker accepted, and
  an isolation check refuses other code touching the log. The owner
  accepted the measured memory: about 218 KB per context while the log is
  on (D3 had estimated about 150 KB), under 1 KB while off.

## Free variables approved (2026-11-04)

- **Plan task 4.2.2a approved [kernel]** (ADR 0014 Q2: free variables, the
  local context, `instantiate_rev`/`abstract`; inference enters binders one
  at a time). Independent review rvD2A, two rounds, every finding closed;
  the chain typing proved equal to Lean's `mk_pi`; a well-typed random
  trial (now in `make test`) agrees with the old code and an independent
  typing model. Accepted cost: checking is 10–25% slower until the
  loose-variable range of ADR 0014 Q12 is built.

## Data types, first step, approved with a condition (2026-11-04)

- **Plan task 5.2.1a approved [kernel][import]** (non-recursive inductive
  blocks; independent review rvI21, three rounds, the last clean). The
  owner: "I think approve, but I am concerned about the difference with
  Lean - do we have to be different? if this is better, it should be with
  a flag, I'd like 100% compatible." None of the differences is better
  than Lean; each is a cautious gap (refused or unknown where Lean
  accepts). Condition recorded: close them so the default is 100% Lean —
  (1) a file that uses `T.rec` without declaring it: use LeanForth's own
  generated recursor, as Lean's kernel does; (2) a block rejected at the
  final comparison (B3): its type and constructors stay usable afterwards,
  as in Lean's environment; (3) the P4 guard on unit-like structures:
  closed by task 5.2.2's port of Lean's rules. Any stricter behaviour only
  behind an opt-in flag.

## How progress is described (2026-11-04)

- The owner: "be a bit more clear that we are working on an in progress
  design that will be completed and compatible at a later step!" Every
  report and gate question presents a step as part of an unfinished design
  and names, for each temporary gap from Lean (an *unknown* or a refusal
  where Lean decides), the plan task that makes it identical to Lean.

## Data types, first step: condition met (2026-11-04, late)

- **Plan task 5.2.1a: the owner's 100%-Lean condition is met** (answer
  "Condition met"). Independent review rvI21 rounds 4–6 (the last with
  nothing blocking) checked the closing work of agent I21: a file that
  leaves out `T.rec` gets LeanForth's own recursor, built at the use's
  universes exactly as Lean's `instantiate_type_lparams` of the
  recursor's type; a block rejected at B3 keeps its type and constructors
  usable; an empty block is rejected at Lean's step. Evidence: the
  inductive table, 176 cases against pinned Lean 4.35.0; task 5.2.1a's 94
  rows give Lean's verdict on 88 and are pending on 6, each naming its
  task (5.2.1b, 4.2.2). LeanForth accepts nothing Lean refuses.
- Every remaining difference is temporary and cautious (*unknown*,
  *unsupported*, *full* or *invalid* where Lean decides), closed by a
  later step of the design: recursive types 5.2.1b; unfolding 4.2.2
  (including a type that is a Sort only after reduction); the unit-like
  guard and projections 5.2.2; K-like reduction 5.2.1c; literals 5.2.3;
  quotients 5.2.4; mutual and nested blocks 5.2.5; capacities 6.2.0; a
  file naming a constant it never declares, refused whole where Lean
  rejects only the declaration concerned, 5.2.6 (new); the command line's
  reader moving to the importer's stage and feed (agent CLI2, plan 3.4).

## IR 0.2 implementation approved (2026-11-04, late)

- **ADR 0019 Amendment 1, IR 0.2 [parser] implementation gate: approved**
  (owner, "Approve"). Agent IR3's implementation (merged `cc3afaf`, review
  fixes `71f31b4`): redefinition by Forth's early binding, output words as
  `out` effects (Lean's `runOut_result`: printing never changes the
  computation), `LSHIFT` and `-rot` (portable definition), `#` `$` `%`
  `'c'` numbers; a file using nothing new still gives `lf-ir 0.1` byte for
  byte; Lean proves `sha-rotr`, `sha-ch`, `sha-maj` and `sha-big-sigma0`
  equal FIPS 180-4's ROTR, Ch, Maj and Σ0 for all 32-bit inputs.
  Independent review rvIR3: nothing blocking; its fixes merged. Approved
  with the four additions beyond the design: reason 32 for an unclosed
  text; a run that ends *full* sends only its diagnostic; `TYPE` after
  `S"` checked to be Forth's own; a portable `.S`.
- Named follow-ups: L6 (Lean's printed bytes against the interpreter's),
  L7 (tie `clampDebugProgram` to program-word IR), L10 (narrow the
  portability exemption of `sha-words.fs`), L11 (a receipt for an earlier
  version runs that version's execution token). Next on the track:
  `src/lib/sha256.fs` runs the proved words; receipt schema 0.3 at the
  [format] gate with the first receipt that needs it.

## Checker on the large store approved; resource settings (2026-11-04, late)

- **The checker on the large store, with no depth limit, [kernel] gate:
  approved** (owner, "Approve"; held since the morning until the fixed
  limits became dynamic). ADR 0016's heap stores and the importer's stage
  feed; plan 6.2.0 part (a), universe lists of any length, and part (b),
  every pass on explicit growable stacks (agent KC, merged `215a406`).
  Evidence: Lean's whole `Init` checked from the command line (1,618
  accepted, 0 rejected); random-test answers identical before and after;
  the 2,000- and 10,000-deep Lean differentials agree on every row;
  independent re-review rvKC (REVIEW-B): nothing blocking, five low
  findings being fixed. Temporary gaps, each with its task: time quadratic
  in a term's depth (6.5.5); the remaining fixed capacities (6.2.0, 6.2.2,
  6.2.4).
- **Resource settings are not verdicts** (owner, "Yes, a resource"): the
  100%-Lean rule means Lean's verdict when Lean has enough of its resource
  settings. Lean's `maxRecDepth` refusals (`deepRecursion`, BL-9) and
  `maxHeartbeats` timeouts are resource refusals, as LeanForth's fuel
  (*exhausted*) and memory (*full*) are; LeanForth does not copy Lean's
  counters. An option that emulates `maxRecDepth` would be a later opt-in
  flag, never the default.

## Command line: NOT PROVED exit status and the default engine (2026-11-04, late)

- **NOT PROVED keeps Lean's exit status by default** (owner, "0 like Lean,
  flag for 6"; this replaces "its own exit code" in "Data types, axioms and
  imports"). A declaration that depends on an axiom outside `propext`,
  `Classical.choice` and `Quot.sound` (such as `sorryAx`, or an axiom the
  file declares) gets Lean's verdict, marked NOT PROVED with the axiom
  named, as a warning line and in the JSON report; the exit status is
  Lean's (0 when everything is accepted). An opt-in flag
  (`--strict-axioms`) makes such a run exit 6, below every real failure.
  The owner, on the report format: "Note that if Lean accepts other
  axioms, we will have to be 100% compatible" — LeanForth gives Lean's
  verdict on declarations using any axiom Lean accepts (plan 5.3.1); the
  mark is presentation, never a different verdict.
- **Default engine: Gforth's checking engine** (owner, "Checking default,
  --fast"): `leanforth check` runs on the engine that stops at a stack or
  memory fault where it happens; `--fast` selects gforth-fast (2.4 times
  quicker, identical verdicts in every test). Revisit after the outside
  audit. *Replaced 2026-11-11: gforth-fast is the default (see "Later
  decisions of 2026-11-11").*

## Native LeanForth: where theorems run, inline use, library vocabularies (2026-11-04, late)

ADR 0017 Amendment 1 (agent AU2), the owner's answers:

- **OQ-1 revised: yes.** With LeanForth loaded, Gforth's own interpreter
  runs theorem text — from a file, typed at the prompt, or from a Forth
  program that passes values in; each word builds part of the term and
  `end NAME` checks it. A file run by `leanforth check` in a fresh Gforth
  can use only LeanForth's sealed words and gets the normal label; results
  in a session where other Forth ran say "checked in this session" until
  saved and re-checked by `leanforth check`. This replaces the 2026-11-02
  answer (a separate checker program receiving only data).
- **Inline shape: yes.** Theorem text between `lf[` and `]lf`, values from
  Forth by name with `param:` (a statement, a function, a number, a type),
  the verdict on the stack; prior art: the LCF family's quotation with
  antiquotation.
- **Library names: the library as a vocabulary** (owner: "Lets do 1, but
  carefully document and leave for future consideration 2. Also concerned
  about the case issues."). A library such as `Init` is one word list in
  the search order whose search looks names up in the library's hash index;
  no word is made per name. The alternative (one Forth word per name, made
  at load time) is documented and kept for future consideration. Case: the
  owner is concerned — Lean names are case-sensitive (`Init` has 31 pairs
  such as `id` and `Id`), Forth's usual search is not; the amendment must
  state exactly how case is handled in every layer (library vocabulary,
  LeanForth's own words, binder names, the printer) and test the pairs.
- **A short word for Lean's `+`: not now** — decide with real examples
  once the elaborator (8.3.1) fills hidden arguments.

## Report format approved; memory checker later; fewer tokens (2026-11-04, late)

- **check-report 0.1 [format] gate: approved** (owner: "go with your
  recommendation", which was Approve). The `leanforth check --json` report,
  validated by `schemas/check-report-0.1.schema.json`: deterministic outside
  its `measured` member; names are escaped display text and `index`
  identifies a declaration; NOT PROVED exits 0 as Lean does and 6 under
  `--strict-axioms`; the engine is recorded in `measured.engine`. Two
  independent review rounds (rvCLI2) found nothing blocking.
- **A Forth memory checker, later** (owner: "forth memory checker later is
  good"): a debug allocator wrapping `ALLOCATE`/`RESIZE`/`FREE` with guard
  words, a table of live blocks, poison on free and move, and a guard sweep
  after each declaration, plus a checked mode of the store words; chosen
  over Valgrind (no new dependency). Plan task 6.5.6.
- **Fewer tokens** (owner: "plan for reduced tokens looks good too"):
  focused tests and one `make check` per task, no local Gforth 0.7.3 runs
  unless host-specific, at most one whole-`Init` run, short reports, one
  soundness-focused review round per gate, no new agents while several run.

## Data types, part 2 approved (2026-11-04, late)

- **Plan tasks 5.2.1b (recursive types), 5.2.5a (mutual blocks) and iota
  [kernel][import]: approved** (owner, "Approve"). Agent N1's work, merged
  `13b9a65`, `126a49d`, `55ed9ed`. Evidence: 268 Lean-checked table cases,
  none contradicted; independent review rvN1 round 1 found two wrong
  acceptances on hand-made files (fixed), round 2 found none in 143 more
  probes; `Init`: 261 of 604 blocks accepted (184 before), none rejected.
  Temporary gaps, each with its task: nested blocks 5.2.5b; structures and
  projections 5.2.2 (in progress); literals 5.2.3; proof irrelevance and
  eta 4.2.5, 4.2.4.

## Numbers as parts of names (2026-11-05)

Question (from agent LF's `print --lf` work): Lean names can have parts that are numbers, such as the `0` in
the private helper `_private.Init.Data.Nat.Basic.0.Nat.zero_add.match_1_1`; LeanForth's words refused such
parts in declaration names, so these declarations could not be written as LeanForth text.

Owner: "We must be 100% compatible with lean, if lean has numbers as parts of names, so does leanforth."

Done by agent NN (merged 2026-11-05): any part after the first may be a number, read and written as plain
digits; a text part made of digits is written `«0»`, so the two stay distinct as in Lean; no Forth word is
ever made whose name is a number, so `0`, `1`, `-1` keep reading as numbers. A name whose first part is a
number stays unsupported (the whole token would read as a number); no export seen so far has one. The reader
change is a [parser] item: an independent review is owed.

## Approval round of 2026-11-11

Asked in plain language with a recommendation for each item (the full list with its evidence and reviews:
`.claude/work/APPROVALS-2026-11-11.md`); the owner chose every recommendation ("Approve all", "Strict + official",
"Change the rule"). Every item was already merged and used by `leanforth check`; every accepted result stays
*experimental — not independently audited*.

- **Lean rules [kernel], approved**: unfolding definitions in Lean's lazy order (4.2.2b-d); `let`, function eta and
  proof irrelevance (4.2.3-4.2.5); structures, projections and the comparison's projection steps (5.2.2); K-like
  recursor reduction (5.2.1c); number and string literals (5.2.3); axioms with **allowlist v1** — exactly `propext`,
  `Classical.choice` and `Quot.sound` with Lean's statements, any other axiom reported NOT PROVED — opaque
  declarations and Lean's quotient (5.3.1-5.3.2, 5.2.4, 4.2.6); nested inductive types (5.2.5b); unsafe and partial
  declarations skipped as Lean's official export checker skips them, verdict *skipped*, and any safe declaration
  that uses one rejected (5.2.7).
- **Speed and memory, no Lean rule changed, approved**: result caches (4.2.7); compact-store steps S0-S4 and S6
  (a, c, d, e); the fuel model of ADR 0014 Amendments 3-5 (a unit per distinct node, not per path) and LeanForth's
  own audits once per node per check (Amendment 4). The default fuel of 20,000,000 per declaration follows the
  owner's approval of 2026-11-10 to raise it (raised again to 100,000,000 on 2026-11-11; see "Later decisions of
  2026-11-11").
- **Formats and inputs [import][format], approved**: the importer's index numbering as Lean's reader allows (sparse,
  any order); the opt-in `--any-lean-version`; report format `check-report-0.2` and run records `run-record-0.2`
  (the *skipped* verdict; 0.1 kept unchanged); Lean's JSON number spellings and unknown record members ignored;
  `print --lf` with numeric name parts; print hooks through the safe line sink.
- **Export header (owner's choice)**: kept strict in the default mode (format 3.1.0, Lean 4.35.0); only
  `--any-lean-version` relaxes it. Lean's own checker does not read the header; LeanForth uses it to know the file
  is a Lean 4.35.0 export.
- **Referee for hand-made export files (owner's choice)**: where Lean's kernel order and Lean's official export
  checker (lean4export v4.35.0's replay, which checks in name order) disagree, the official export checker decides.
- **Continuous integration (owner's choice)**: GitHub CI stays off (turned off 2026-11-11 at the owner's request:
  its runs failed for billing, not tests). Before every push both of its jobs run locally — `make check` on the
  pinned tools and `make test` on Gforth 0.7.3 — and their outcomes are recorded; `AGENTS.md` and
  `.claude/CLAUDE.md` say so. GitHub CI is re-enabled only when the owner asks.

Not in this round (no approval asked yet): compact-store step S5 (the checker reading the input in place; parts 1-3
merged) with its follow-up S5B, and step S7 (parallel checking).

## Later decisions of 2026-11-11

- **Default engine: gforth-fast** (owner: "Consider changing default to --fast for everything with just some
  compatibility tests without it"; replaces the 2026-11-04 choice above). `check`, `replay` and `print` run on
  gforth-fast; `--checked` selects Gforth's checking engine; `--fast` stays accepted. Safeguards: `make test` and
  `make check` keep running on the checking engine; `make engine-gate` (all of Init and the arena tests on both
  engines, verdicts and exit codes compared) passes before each approval round and release; first run 2026-11-11
  identical on both engines.
- **Downloads approved** ("All five"): the Lean Kernel Arena's large tests navier-stokes-euler, cslib, cedar,
  reachability and con-leche (git clones at the arena's pinned commits, their Lean toolchains and Mathlib caches) in
  `.claude/work/arena/large/`, untrusted, after the full Mathlib run; Std built locally.
- **Snapshots (ADR 0020)**: layered snapshots (a base plus library layers, loaded together; a name with different
  content in two layers refused); lookup tables rebuilt on load, never stored; an opt-in development flag may load a
  snapshot written by an older verdict version, every result from it labelled stale and never counted in
  compatibility numbers (amends ADR 0020 D3/D6 for that flag only); no Mathlib run only to write a snapshot: every
  full run saves one.
- **Parallel checking**: the workers of `check --jobs N` share one read-only copy of the input, for every export and
  by default ("should be also for other large libraries... or even all").
- **CPU use**: by default up to 10 busy threads (all of WSL); on request a "day" mode of about 6 threads while the
  owner uses the computer.
- **Default fuel 100,000,000 per declaration** (owner, choosing the recommendation): three arena tests do exactly the
  work Lean does but need 20-28 million units, so at 20M LeanForth gave up where Lean accepts. Fuel is LeanForth's
  own limit (Lean has none); a larger budget can only move a verdict toward Lean's, at the cost of a slower give-up
  on a declaration that never finishes. Verdict version 3 (agent PF).
- **Term memory per node** reviewed later (plan 6.5.9; owner: "Do we gain anything? Lose anything?").

## Approval round of 2026-11-12

The owner approved, choosing each recommendation (summary `.claude/work/APPROVALS-2026-11-12.md`; reviews rvKN,
rvRS, rvSS, rvS5B, rvS7, rvIO, rvSN2-rvSN4 all not blocking, their major findings fixed). Every accepted result stays
*experimental — not independently audited*.

- **Lean's methods ported ([kernel] gate):** PF C1 (an argument put into a body without loose variables is not
  closed first, Lean's instantiate); R5 (an application typed from its spine's head as Lean's `infer_app`, ADR 0014
  Amendment 9); NS with FXK (an inductive block's walks visit each shared node once, C1 each (node, depth) pair once,
  the recursor compared by Lean's `==`, ADR 0015 amendment).
- **Speed, memory and repeatability:** S5/S5B (input read in place), S7 (`check --jobs N`), SH (one shared input),
  IO (diagnostic-81 routes), PF task 6 with FXR (a check's fuel independent of the tier, lets included; ADR 0014
  Amendment 7, ADR 0020 Amendment 4), MB with FXR (`--memory-per-check`, exact; ADR 0014 Amendment 8).
- **Snapshots:** SN2-SN5 (ADR 0020 and Amendments 1-3); F2 a library built on Mathlib (Physlib) is checked in exact
  mode first, Lean's import mode later as an option; F3 `replay EXPORT SNAPSHOT` replaces the planned run-record
  format 0.3; F4 no signature on snapshots (hashes detect damage, not forgery; SHA-256 in every report).
- **New plan tasks:** 4.2.7d (K1: reject where Lean's infer-only typing throws) and 6.2.5b (L1: layer lookups; G1:
  a `let` export in the version guard).
- Not in this round: agent MO's nested-pass memo (`2ad871e`, verdict version 8), merged after the round; its review
  and approval come next.

### Second approval round of 2026-11-12 (afternoon)

The owner approved, choosing each recommendation. Every accepted result stays *experimental — not independently
audited*.

- **MO ([kernel] gate):** the nested-inductive passes (translate, lower, restore) keep a replace memo per (node,
  offset), as Lean's `replace_rec_fn` cache (ADR 0015 amendment, verdict version 8). Review rvMO not blocking; its
  finding (no test pinned the offset in the key) fixed by rows `nested.offset-local`/`nested.offset-param` and fault
  `rvmo-nest-no-offset` (83c9bb4).
- **K1, L1, G1 ([kernel] gate; plan 4.2.7d, 6.2.5b):** aside typing follows Lean's infer-only mode and rejects where
  it throws; `defeq.fs` types a Pi as Lean's proof-irrelevance and unit-like steps do. This fixed a soundness gap:
  main had accepted small exports Lean rejects (io-pibad; review rows ck-etapibad, ck-pinat, ck-pilambody). L1 keeps
  a layer's twin whose lookups differ; G1 a `let` export in the version guard (ADR 0014 Amendment 10, ADR 0020
  Amendment 3 corrected, verdict version 9). Review rvCK not blocking; its test-gap finding fixed by part P6 of
  `tests/cli/shared-depths.lean` and two faults (700c4a1).
- **Tonight's run:** all of Mathlib on the final build at full speed (8 workers), saving a version-9 snapshot.

### Third approval round of 2026-11-12

The owner approved both, choosing each recommendation.

- **PERF1 and pf1-fix ([kernel] gate; plan 6.5.8, 6.5.9):** the speed and memory pass of ADR 0014 Amendment 11
  changes how the checker organises its work, never what it decides: every Init declaration keeps its verdict and fuel
  count; Init's check CPU fell about 17%, reachability's peak memory about 40%. Reviews rvPF1, the perf1 Forth review
  and the pf1-fix review (with its re-check) recorded no unresolved finding.
- **review-bugs ([kernel][import][format] gates):** stricter checks that only turn broken or out-of-range input into a
  refusal: a scheduler worker added wholly or not at all, a full snapshot layer kept full, snapshot replay, canon keys
  and slot ranges checked, and Gforth 0.7.3 portability (BOUNDS, U<=, the streams). Init keeps every verdict and fuel
  count (CPU +0.8%). Forth review logged (docs/development/forth-reviews/2026-11-12-no-label-review-bugs.md).

### Front-end syntax (2026-11-12, evening; docs/design/FRONT_END.md §9)

The owner answered the first four front-end questions:

1. **`+`, `=`, `*`, `≤` as words in theorem text: yes.** The owner: "I believe that everything in lf[ ]lf only looks in
   the constrained vocabulary and is using forth compiler and interpreter." That is the design (ADR 0017 §3, Amendment
   1): theorem text runs with only LeanForth's wordlists in the search order (src/author/runner.fs), so there `+` can
   only mean Lean's `+`; Forth's `+` is unchanged in programs. This reverses ADR 0017 decision 4 for theorem text.
2. **`:=` kept, read as "is proved by".** The owner found its place in the sample unclear ("it seemed part of the
   theorem"); the layout is to be explained in the guide and the question of layout stays open.
3. **Tactics with the `by-` prefix** (`n by-induction`, `by-rfl`, `by-exact`).
4. **Natural LeanForth is the default**; the kernel ("assembly") form needs the marker word `kernel-form`.

5. **LeanForth finding a proof by itself comes early** (owner: "Yes bring forward the leanforth finds a proof by
   itself"): new plan row FE1i, `by-decide` and a first slice of `by-omega`, right after FE1.

6. **What "full Lean" means (question 6): anything a Lean user can write can be written in LeanForth, with Lean's
   results**; LeanForth does not read `.lean` files, and Lean libraries come in through Lean's export (FE-L stays not
   planned).
7. **How exact (question 7):** statements identical always; proof terms identical for elaboration and the core tactics
   (FE1-FE8), compared with pinned Lean; for search tactics (`simp`, `omega`, `linarith`, ...) the same goals solved or
   refused and a kernel-accepted proof, identical terms measured but not required.
8. **The elaboration-data exporter (question 8): approved** as a development tool run with pinned Lean when a library
   is exported (ADR 0021 D10); users who only check LeanForth text need no Lean.

9. **Milestone order (question 5), as recommended:** FE1, FE1i, FE2, FE3-FE5, FE6-FE8, FE9, FE12, then FE10 and FE11.
10. **Mathlib's code extensions (question 9):** re-implemented as Forth words, most-used first, each compared with
    Lean; no interpreter for Lean programs in Forth.
11. **Explained proofs** (owner: "Remember we want each line of a pretty printed proof to give the English version
    of how we moved from previous line of a proof"): plan row 8.6.12; FE1g's tactic steps record what 8.6.12 needs.

### LeanForth text checked by the kernel (2026-11-12, evening; [parser][bypass][import] gates)

The owner approved plan tasks 8.2.1a, 8.2.1c and 8.2.1d (ADR 0017 Amendment 2), choosing the recommendation:
`leanforth check [--env EXPORT | --snapshot FILE] FILE.lf` runs LeanForth text with only LeanForth's words visible,
writes each declaration as the records Lean's exporter writes and sends them through the importer stage to the same
kernel; no kernel rule changed. Evidence: the records equal pinned Lean's export for 56 declarations of 19 fixtures;
broken texts refused at their line and column, never accepted; a refused or partial text never reaches the kernel;
Forth reviews of lf-files and lf-files-2 with re-checks, not blocking (LOG.md); done check
(done-checks/2026-11-12-lf-files.md): works end to end. Proofs in `.lf` files are still kernel terms written by hand
(no elaborator or tactics yet).


### Program track: LeanForth re-checks Lean's program proofs (2026-11-12, evening; plan 5.5.1)

The owner approved both gates, choosing each recommendation, after the done check
(done-checks/2026-11-12-program-track.md: works end to end):

- **[bypass]:** the clamp receipt relies on Lean's elaborator and exporter having written the contract and the program
  faithfully (assumption A6, stated in every receipt; supported by Lean printing the program back equal to the IR file).
  Lean wrote and checked the proofs; LeanForth's checker re-checked the export (4,277 declarations) and rejects changed
  program, contract and proof copies; the same for the four SHA helper words' proofs (2,890 declarations).
- **[runtime]:** the receipt's runtime assumptions as stated: one 64-bit two's-complement cell per value, the IR means
  what the Forth source does, Gforth runs the 13 words used as the IR says (tested on 986 cases, not proved), the stacks
  have room.
- Receipt schema 0.3 drops the label (the owner's no-label decision); SHA receipts take 0.4 at its [format] gate.
  Nobody has proved SHA-256 as a whole, and `leanforth verify` (8.4.1) does not exist.

### Kernel refactor edit (2026-11-12, evening; [kernel] gate)

The owner approved, on condition of the re-check, the one src/kernel edit of the FRI refactor: `src/kernel/env-schedule.fs`'s
private `lf-sch-and` replaced by the identical library word `outcome-and` (lib/outcome.fs). The re-check confirmed it
behaviour-identical (same body `over ok? if nip else drop then`, same stack effect, same argument order at every call
site; faults frk-sched-add-pushes-first and frk-sched-outcomes-ored caught). Review: forth-reviews/2026-11-12-refactor-fri.md.

### Order and snapshot stability (2026-11-12, late evening)

- **FE6a early:** the generated definitions of inductive types (casesOn, recOn, noConfusion, below, brecOn), compared
  node for node with Lean's for every inductive type of Init, may start before FE1-FE5 (branch fe6a), because it is
  independent and later steps need it.
- **Snapshot stability first tomorrow:** the owner wants to stop regenerating the Mathlib snapshot so often. Plan
  6.2.5c (read snapshots of the previous one or two format and verdict versions, reusing only results a change cannot
  affect) is the first infrastructure task of 2026-11-13. Any future snapshot addition (such as elaboration data) is
  added as an optional section; refactors must keep snapshot bytes identical.
- **Work tempo (22:00):** "I'm trying to get as much into tonight's build as possible, you will be working after
  mathlib too, without waiting for me. You seem to be delaying work." The coordinator's own 23:45 stop and 01:00
  merge freeze are withdrawn: agents report reviewable ranges early and keep working; work continues overnight,
  during and after the full Mathlib run, without waiting for the owner. Real limits only: owner gates, CPU during the
  run, and no change to the main checkout while the run loads its source.

### Reading older snapshots: design questions answered (2026-11-12, 22:15)

The owner answered the four questions of the 6.2.5c design
([SNAPSHOT_COMPATIBILITY.md](../design/SNAPSHOT_COMPATIBILITY.md), ADR 0020 Amendment 5), each as recommended:
1. **How far back:** two versions, for both the format version and the verdict version. Older ones are refused (exit
   2) and can still be viewed with `--snapshot-stale-ok`, marked stale.
2. **Exact results:** a result carried from an older snapshot must equal this build's fresh check, verdict and fuel; a
   change that may move fuel re-checks everything it can reach.
3. **Automatic re-check:** when an older snapshot needs re-checks, LeanForth does them, first printing how many and
   why; `--save-snapshot NEW` keeps the upgraded snapshot; `--snapshot-stale-ok` gives the quick look instead.
4. **Batching:** changes that move verdicts or fuel are merged together, at most once a day, before the nightly full
   run, which saves the new Mathlib snapshot. Changes that leave verdicts and fuel identical are not held back.

These settle the design's choices. The amendment stays **proposed**: the code (sub-steps 6.2.5c1-c8) still goes
through the [format], [kernel] and [import] gates (Lean comparisons, an independent review, the owner's approval of
the summary) before it is accepted.

### Front-end designs FE1e and FE1g: questions answered (2026-11-12, about 22:40)

Each as recommended ([FE1E_APPLICATIONS.md](../design/FE1E_APPLICATIONS.md) §8,
[FE1G_TACTICS.md](../design/FE1G_TACTICS.md) §10):
1. **Instance-search limits (FE1e):** LeanForth uses its own fuel. Lean stops a search after a count of its own
   allocations or at depth 512, which LeanForth cannot reproduce; where Lean would give up and LeanForth finds an
   answer, the kernel still checks the result and the case is listed in BEYOND_LEAN.md. Nothing unchecked is accepted.
2. **Induction case syntax (FE1g):** Lean's `| tag names =>` lines, one `by-end` closing the group and every
   `by-case:` block (e.g. `n by-induction-with | zero => by-rfl | succ k ih => by-rw[ ' Nat.add_succ ih ] by-end`).
3. **`by-rw` in FE1:** yes; the first native proof uses Lean's own rewrite proof, which is also the proof the
   explained-proofs output (8.6.12) describes line by line.

### Kernel fixes, the kernel refactor and `sorry` (2026-11-12, late night)

1. **KFIX approved [kernel]** (about 23:00): the five stack fixes on out-of-room paths of
   src/kernel/mixed-level-substitute.fs and level-substitute.fs (B1-B5, found by the COV2 tests; in one case a valid
   declaration could have been reported as rejected when memory ran out), and the unused `lf-whnf-ended` removed.
   Evidence: [review](../development/forth-reviews/2026-11-12-kfix-mls.md), not blocking; the crowded test in `make
   test`; planted faults caught. For tonight's build, after its two low follow-ups and CI.
2. **FRK approved [kernel] on condition** that the correctness review finds nothing blocking (met:
   [review](../development/forth-reviews/2026-11-12-refactor-frk.md), every change behaviour-identical by trace) and
   the branch is not slower than main (the implementer's back-to-back CPU pair, pending at the time of the decision;
   the result is recorded below when it arrives). If either fails, FRK waits for the owner.
   **Conditions met (2026-11-13, 00:58):** the implementer's back-to-back Init runs at the same load gave branch
   -5.5% CPU and memory +0.9% (means of both pairs: main 1421.2 s, branch 1419.5 s user), every report and fuel count
   equal; both CI jobs pass on eb9695f. FRK merged into tonight's build.
3. **`sorry` in LeanForth text** (amends ADR 0021 D3; [ADR 0021 Amendment 1](../adr/0021-front-end.md)): allow the
   explicit `sorry` exactly as Lean does, reported NOT PROVED with `sorryAx` named, never counted as proved. The owner
   added: "it needs to report the other parts of a check are good somehow for development, I almost wonder if it is
   better for sorry to be true instead, so proof is called valid if sorry section is true". So the report says that
   everything else was checked, that the statement holds if each open part is true, and lists each open part with its
   statement; it never says "proved". No automatic error recovery.

### No result labels (2026-11-12, evening)

The owner: "I find the constant repetition of experimental and not independently audited, one NOT PROVED not useful.
the code and system is under development and doesn't do anything yet. call it pre-alpha if you have to", then "I
don't really think you need to label anything like that at all, or even pre-alpha." Decision 1's label requirement is
withdrawn: no label on results, in reports, in the JSON report or in documents (task PA removes it; a [format] change
of the check report decided by the owner). Verdicts are unchanged, including NOT PROVED for a declaration that uses an
axiom outside the allowlist. The outside audit (plan 9.2.1) and the review gates stay.


### Approval round of 2026-11-12, night (approval pack)

The owner answered the 18-item approval pack at about 22:25 on 2026-11-12, in four groups, every item as recommended.
The pack is `.claude/work/APPROVALS-2026-11-13.md` (a working file, not tracked; its file name says 11-13, the approval
date is 2026-11-12). Each ADR's "Approval status:" line now cites this section.

- **Items 1-3, superseded (wording only):** ADR 0001 superseded by ADRs 0011, 0012, 0014, 0015, 0016; ADR 0002
  superseded by ADR 0007 item 5, ADR 0011, ADR 0014 and the 2026-11-05 amendment of ADR 0006; ADR 0003's base text
  superseded by ADR 0014, with its Amendment 1 staying accepted. No code change.
- **Items 4-7, accepted under their gates:** ADR 0004 [kernel][format], with levels compared as ADR 0011 Amendment 1
  says and the "experiment" wording marked replaced; ADR 0005 [kernel][import][format]; ADR 0006 [kernel][import], with
  the empty allowlist marked replaced by the 2026-11-05 amendment and "theorems never unfold" by ADR 0012; ADR 0007
  [kernel], with the dead "owner answer O2" reference replaced by the entry "Legacy retirement and the first checker's
  rules (2026-11-02, evening)".
- **Item 8, conditional:** ADR 0009 Amendment 1 (context members may own heap memory; no Lean rule, touches [runtime]
  memory safety) approved on condition that the Forth review of `src/lib/context.fs` finds nothing blocking. The review
  was pending when this was recorded; the ADR line stays "proposed" with the conditional approval noted. **Condition met
  (2026-11-12, 22:50):** the Forth review ([2026-11-12-context.md](../development/forth-reviews/2026-11-12-context.md))
  found nothing blocking (3 low, 4 info), so Amendment 1 is accepted; its findings (missing tests of the first-code
  promise and of freeing grown walks, a usage example, private helpers, one named failure word) are plan work.
- **Item 9:** ADR 0014 Amendment 2 (shared terms cost nodes, not paths), gate [kernel].
- **Item 10:** ADR 0015 FX8 amendment (review rvUNNI), gates [kernel][format]; covered by the 2026-11-11 items A7, A8
  and C3 (gate recorded 2026-11-12 night: [kernel][format]). Its "not through its gate" and "decision pending" text is
  updated.
- **Item 11:** ADR 0021 decisions D1, D2, D3, D5 and D7 approved, gates [bypass][axioms]; the ADR as a whole stays
  proposed until FE1 passes its [parser] gate.
- **Item 12:** ADR 0014 Amendments 1, 3, 4, 5 (caches, node-based fuel, audits once per check): gate [kernel].
- **Item 13:** ADR 0014 Amendments 7, 8 and ADR 0020 Amendment 4 (limits per check): gate [kernel].
- **Item 14:** parallel checking, ADR 0009 Amendment 2, ADR 0012 Amendment 2, ADR 0016 Amendment 2: gates
  [kernel][runtime].
- **Item 15:** snapshots, ADR 0020 Amendments 1-3: gates [format][import][kernel].
- **Item 16:** ADR 0015 Amendment IO (diagnostic-81 routes): gate [kernel].
- **Item 17:** the default engine `gforth-fast` is a [runtime] decision; the default fuel of 100,000,000 per declaration
  is a [kernel] limit; downloads and CPU use: no gate (gate recorded 2026-11-12 night, for "Later decisions of
  2026-11-11").
- **Item 18:** the strict export header and the official export checker as referee for hand-made files (C5, C6): gate
  [import]; the local-CI rule: no gate (process) (gate recorded 2026-11-12 night, for "Approval round of 2026-11-11").

### Less repeated testing (2026-11-13, morning; plan 9.4.6)

The owner asked why small tasks take so long to reach GitHub; the count is in
[TEST_WORKFLOW_REVIEW.md](../development/TEST_WORKFLOW_REVIEW.md) (`lib/sort.fs`: about twelve full-suite runs and two
to three hours of machine time to reach GitHub; six hours of pushes spent 3.6 hours in CI). The owner chose every
recommendation:

1. **Reuse a recorded pass for an identical tree.** When the exact tree (`git rev-parse HEAD^{tree}`) already passed a
   suite with the same Gforth and Lean, a later merge or push reuses that record instead of re-running it. Agents rebase
   on main before their final run so that most merges keep the tested tree.
2. **Tests by change tier, the full suite once a day and before every tag.** Documentation only: the documentation and
   progress checks. Tests only: the changed tests, their faults and the coverage of the files they test. A library
   nothing loads yet: its own tests on both Gforths, its faults and coverage. Front end: the front-end targets and the
   files they load. Kernel, core, import, cli, the Makefile or scripts: the whole of `make check`. A tier never skips a
   test of a file the change can reach. The full suite, Gforth 0.7.3 included, runs once a day (with `LEAN_CACHE=0`)
   and before every tag.
3. **Pushes at checkpoints** (about every two to three hours, at the end of a session, or when a branch someone needs
   lands), with documentation-only commits riding along, instead of after every merge. Every branch stays committed
   locally in the meantime. Work branches are not pushed to GitHub.
4. **Bigger steps.** A new library lands with its first real caller in one branch (libraries the owner asks for on their
   own excepted), and plan steps are sized by a user-visible result, not one layer at a time.

Also adopted with these, as the review proposed: each branch runs its tier's suite once, at the end, on the head it hands
over (focused tests while working, nothing again after a review fix unless the fix reaches a file outside the tier);
reviewers run their own probes and planted faults and do not repeat the implementer's recorded runs; coverage allowances
and small follow-ups go into the branch that caused them. Kept unchanged: planted faults, the Forth style review of every
change to `src/`, both Gforth versions, the daily uncached run and the done checker. Items 1 and 2 at push time need
scripts (plan 9.4.6); until they land, `scripts/push.sh` keeps running both CI jobs in full.


### Gate approvals and omega (2026-11-13, morning)

Asked in plain language with the reviewers' summaries (reports in `docs/development/forth-reviews/`):

- **Snapshot compatibility, plan 6.2.5c steps c1-c5 [format][kernel][import]: approved,** with the relaxed "copied from
  the old file" mark in base snapshots accepted until step c6 adds a record of which files are upgrades (it changes
  labels only, never a verdict). Evidence: every older snapshot is re-checked in full today and equals a fresh check
  (all of Init, 59,349 declarations, 0 differences); the review and its three re-checks are not blocking; 25 planted
  faults caught. Risk accepted: a future rule change with a wrong "reach" note is caught only by the comparison tests on
  the test snapshots, so each such note is reviewed with its change.
- **Elaboration data format 2 (FE1e1) [import][format]: approved;** format 2 replaces format 1. The kernel never reads
  this file.
- **The job pool fails closed when the host refuses threads [runtime]: approved.** The rare hang when a thread dies
  during start-up stays a plan task.
- **FE1i, omega:** "The improvements to omega are good, hide them behind an improved performance flag so we can do both,
  default is full compatibility." So: by default `by-omega` is a port of Lean 4.35.0's omega, succeeding and failing
  exactly where Lean does; improvements beyond Lean's (goals Lean's omega cannot close, or faster search) go behind an
  opt-in flag, reported as such, and never change the default outcome. The flag's name and report wording are settled
  in the FE1i design before FE1i-5 starts.

### Design stage (2026-11-13, morning; plan 9.4.7)

The owner asked to review the design stage ("seems like too many sub tasks and is the design reviewed"); the count is
in [DESIGN_STAGE_REVIEW.md](../development/DESIGN_STAGE_REVIEW.md): eight designs, about 7,000 lines in about 14 hours,
about 95 sub-steps, none independently reviewed before code; six kinds of design problems found late. The owner chose
every recommendation:

1. **A design review before code.** An independent reviewer (not the author) reviews each design once, with a re-check
   if needed, against the checklist of the review note: Lean fidelity of functions and data structures; what the next
   layers need (consumers); work in flight on the same files; slices that each end in a command a user can run, with
   tests and documentation in the slice; trust and gates; size; the owner's questions with recommendations. Then the
   owner approves a one-page summary before code starts. Kernel designs keep AGENTS.md's ADR gate on top.
2. **The plan re-cut into user-visible slices:** S1-S6 (front end), V1-V4 (`leanforth verify`) and one slice for the
   rest of snapshot compatibility, about 11 slices in place of about 50 sub-steps; running work folds into its slice.
3. **A design's main text about 300 lines,** Lean-source notes and long tables in an appendix.
4. **The existing, never-reviewed designs reviewed now:** the front-end designs together before S1 goes further, and
   VERIFY_COMMAND before V1 merges.


### Slice S1 approved (2026-11-13, morning)

The owner approved the S1 design ([S1_INTERFACE.md](../design/S1_INTERFACE.md); the front-end design review and its
re-check in [design-reviews/](../development/design-reviews/LOG.md)) from its one-page summary: the first native proof
`theorem t : 0 + 0 = 0 := by-rfl`, elaborated with Lean's instances and checked by the kernel, built in four branches
(fe1g3, s1-meta, s1-synth, s1-elab), gates [import] when s1-meta and s1-synth merge and [parser] and [bypass] at S1's
end, no kernel change. Also decided: the front end's work limit is `--elab-fuel N` (`--fuel` stays the kernel's); the
midpoint `0 0 + 0 = #check` printing `0 + 0 = 0 : Prop` is accepted as a midpoint, never as "done" (a file of only
`#check` lines then ends with exit 0, as in Lean, instead of error 49); `sorry` is the tactic `by-sorry` now and the term
`sorry` in S5 (the [parser] spelling).

### `leanforth verify`, slice V1 (2026-11-13, morning)

From the design review of [VERIFY_COMMAND.md](../design/VERIFY_COMMAND.md)
([report](../development/design-reviews/2026-11-13-verify.md)) and its questions, the owner chose every recommendation:

1. **V1's trust:** `verify` runs pinned Lean itself to write the proofs and LeanForth's kernel re-checks them; proof
   files a user supplies are accepted only in V2, once LeanForth writes the contract statement itself. For each contract
   a new Lean file is generated (no contract text enters it as code: the hotfix of 2026-11-13) and Lean's own reading of
   the statement, with its hypotheses, is shown back; a short [parser] review of the contract translation is part of V1.
2. **Reports and exit codes:** a missing or failed proof prints "NOT VERIFIED: open" with the list and exits 2, never 0;
   success says "discharged", never the bare word "verified"; LeanForth's kernel rejecting what Lean accepted is exit 5
   "checkers disagree"; a crash of the Python driver is exit 5, never 1 (1 means refuted).
3. **Receipts:** schema 0.3 for V1; 0.4 (the SHA-256 helper words) decided separately; 0.5 later, with V2: paths
   relative to the user's project folder, the proved statement and the tools' hashes.
4. **Python 3 and pinned Lean for V1 only,** a documented exception to the 2026-11-02 rule that end users need only
   Forth; `leanforth capabilities` says so; V2 moves the deciding steps into Forth.

Open with V3: `sorry` in program proofs (as in Lean, never inserted by `verify`, exit 6); with FE2: contracts as
LeanForth text.

### Priorities: the S slices first (2026-11-13, midday)

The owner, at about 11:45: "I don't think we require an automatic mathlib run tonight. I don't think we are making
enough changes to require it yet. slow down the work on program correctness (but keep it up to date and moving very
slowly) prioritize the S2 path (and the following S? paths)".

1. **No automatic Mathlib run tonight.** The restored export stays ready; a full-Mathlib run waits for changes that
   need it (kernel, import or snapshot changes) or the owner's request.
2. **`leanforth verify` slowed down.** V1's work in flight (its review fixes) is finished, probed and merged, and its
   three gate questions ([bypass], [format], [parser]) are asked with the next batch; V2-V4 wait. The program track's
   plan rows and progress lines are kept current.
3. **The front end's slices first:** S1 to its done check, then S2 ($0 + n = n$ by `by-induction` and `by-rw`), then
   S3 onwards, each designed and reviewed before its code (plan 9.4.7).

### Slice S2 approved; S1's order amended; V1's gates (2026-11-13, early afternoon)

From the [S2 design note](../design/S2_INTERFACE.md) and its [design review](../development/design-reviews/2026-11-13-s2.md)
(blocking B1, B2 and M1-M4 fixed in the text), the owner chose every recommendation:

1. **S2's design approved,** both forms of FE1 included: by rewriting (`by-induction-with`, `by-rw[ ]`) and the plan's
   `by-case:`/`by-exact` form, which needs Lean's smart unfolding (S3's `by-decide` needs it too). FE1 is done only when
   the done checker runs both on all of `Init`.
2. **S1's order amended:** S2's merge A (`s2-unfold`: lazy delta and unfolding, measured to be needed by S1's `#check`
   midpoint and its test C1) is built after s1-meta-b and s1-synth and merges before s1-elab; the elaboration data goes
   to format 3 so that an older file is refused, never read as "no smart unfolding" (decided at merge A's [import]
   gate; S6's planned format becomes 4). S1_INTERFACE.md §11, amendment of 2026-11-13.
3. **[format] the step log** (`check --steps FILE|-`, NDJSON `leanforth-tactic-steps` version 1 with a schema, only for
   accepted declarations, read by nothing that decides) and S1's deferred `by-sorry` open-part wording: approved as
   designed; the gate is checked again with the real output at S2's end.
4. **`leanforth verify` V1's gates approved** on the reviewer's recommendation, after the review fixes were probed:
   [bypass] (nothing reaches "discharged" without LeanForth's kernel re-checking Lean's proof of the exact stated
   contract), [format] (report 0.1, whose exit 0 requires a discharged result; receipt 0.3 unchanged), [parser] (the
   contract translation). V1's done check follows when a slot is free; V2-V4 stay parked.

### Library reuse (2026-11-13, afternoon)

The owner, on learning that `lib/sort.fs` had no caller while new front-end code hand-wrote an insertion sort, and
that the library candidates of the 2026-11-12 backlog reviews were never extracted: "improve the code design and
development process so we reuse libraries and develop new ones as needed. this is really a bad problem and should
never happen. you need to code like an experienced expert programmer. not a beginner. write reusable high quality
code. add that to memory and agents.md", choosing a library audit of the front end now and a library stream beside
the S slices, the libraries S2 would otherwise duplicate first.

- **Rule** (AGENTS.md "Reuse first, and write code as an experienced expert would"): look before writing; a library
  first when something general is missing, every existing copy replaced in the same branch; a "Reuse" part in every
  design and brief; re-implementation and libraries without callers are blocking review findings
  ([FORTH_REVIEWER.md](../development/FORTH_REVIEWER.md), the design checklist of
  [DESIGN_STAGE_REVIEW.md](../development/DESIGN_STAGE_REVIEW.md)).
- **Work** (plan 9.4.8): the audit's library plan, one library per branch; kernel copies under the [kernel] gate.

### Library reuse: high priority, the whole code base (2026-11-13, afternoon)

The owner: "I view this refactor/reuse as fairly high priority. so we will fix all the existing code including the
kernel. do it carefully, but don't overtest each change, you should be able to do several at the same time. use unit
testing a lot on individual changes. some might cause subtle problems in backward compatibility, so expect to debug
that. report the number of lines of code before and after and the library use and also any new libraries found to
develop." Plan 9.4.8 runs beside the S slices at high priority: every copy the audit found is replaced, the kernel's
under the [kernel] gate (identical verdicts, fuel and snapshot bytes on Init); each branch batches several changes,
unit-tests each one, and runs its tier once. Reports give lines of code and library use before and after
(baseline at `14423237`: 202 Forth files, 61,177 lines, 37,800 code lines, 15,015 words; 30 libraries with 1,610 words,
361 of them used outside `lib/`) and the new libraries found.

**Fuel in the reuse work** (the owner, same afternoon: "a general sort with two algorithms split at n=32 might have
different fuel than a single algorithm not split … be careful forcing fuel to be identical with a big refactor").
Fuel is LeanForth's own work budget per declaration (`--fuel`, default 100,000,000), not Lean's; it only decides when
a check stops as exhausted. Verdicts, diagnostics and snapshot bytes must stay identical; fuel is expected to stay
identical where the work is the same, but no code is bent to reproduce an old count: a difference is measured per
declaration on Init, explained, and shown at the [kernel] gate. Of the eight sorts, only the kernel's level
normalization charges fuel (one unit per comparison), and it already uses the same insertion-then-merge split at 32
that `lib/sort.fs` copied from it.

The kernel's first batch under this decision is branch `reuse-k1` (plan 9.4.8e: `lib/sort.fs` in the kernel's sorts,
the new `lib/memo.fs` and `lib/pqueue.fs` in its memos and scheduler queues); it waits for the [kernel] gate (this
records no new decision).

### [import]: S1's library route (2026-11-13, afternoon)

The owner approved the [import] gate for branch `s1-meta-b` (S1 merge B; ADR 0021 Amendment 2, D13): while a
LeanForth file runs, the front end reads the library's declarations read-only from the importer's stage, decoding
them into scratch thrown away before the stage is sealed; only the finished declaration reaches the kernel. Evidence
shown: the stand-in `0 + 0 = 0` accepted and `0 + 0 = 1` refused with Lean's message; binder kinds equal Lean's on
S1's 16 declarations; the Forth review's two memory-corruption bugs and its trust-test gap fixed (a test asserts the
stage's tables are unchanged by decoding); 35 new planted faults caught; the tier passed; the coordinator's probe of
the key faults. The merge follows the independent re-check of the fix commits (AGENTS.md: every Forth change).

### [parser] and [import]: S1's instance tables (2026-11-13, evening)

The owner approved the [parser] gate (LeanForth rebuilds Lean's instance keys and instance order from the
elaboration data and checks every instance against its type: 2,321 of Init's 2,938 instances recomputed equal, 0
differing, 617 not checkable until S2's unfolding and answering "not supported" only when a search tries one;
candidate lists equal pinned Lean's on 13 of 13 problems) and the [import] gate for M6 (the elaboration data bound to
the export's manifest; other data refused, error 39) for branch `s1-synth`, after two review rounds whose findings
were fixed ([review](../development/forth-reviews/2026-11-13-s1-synth.md)). The second re-check's three minor items
are the first step of FE1e5 (`synth.fs`).

### [kernel]: the reuse batch outside the front end (2026-11-13, evening)

The owner approved the [kernel] gate for branches `reuse-k1` and `reuse-out` (one merge): the kernel's six sorts,
three caches, scheduler queue and about 58 loops on shared library words (`sort.fs`, new `memo.fs`, `pqueue.fs`,
`decimal.fs`, `bits.fs`, `blocks.fs`, the loop words of `outcome.fs`); the checker's rules unchanged. Evidence: all of
Init checked with the old and the new code, the same 59,349 declarations accepted with the same fuel (654,719,715) and
byte-identical snapshot files, confirmed independently twice; two kernel reviews and a re-check read every rewritten
loop against the old one ([review](../development/forth-reviews/2026-11-13-reuse-out.md)); the full tier passed.

### Overnight pace (2026-11-13, 21:30)

The owner chose "finish and review": the four running agents finish, their short independent re-checks run overnight,
the approval questions wait for the morning, and no new implementation agent starts overnight (weekly token budget).

### A proof set for S2-S4 (2026-11-13, night)

The owner asked whether LeanForth can develop several proofs natively and chose to add them: S2's acceptance gains
$x + 0 = x$, $0 + n = n$, $n + m = m + n$, $n + (m + k) = (n + m) + k$, $n \cdot (m + k) = n \cdot m + n \cdot k$ and
the length of a list append (or in S5 if its notation needs natural statements), each written in LeanForth, compared
node for node with pinned Lean's term and checked by LeanForth's kernel, its forms confirmed with pinned Lean to lie
within S2's tactics first; S3 gains `2 + 2 = 4` by `by-decide`, S4 `n < n + 1` by `by-omega`. The weekly token budget
resets Tuesday 2026-11-17 at 5 pm (Pacific).

### [import] S2's merge A and [parser] the instance search (2026-11-14, morning)

The owner approved the [import] gate for branch `s2-unfold` (S2's merge A: elaboration data format 3 carries Lean's 389
smart-unfolding bodies for Init and their `match_pattern` markers; the front end unfolds in Lean's order; the data stays
untrusted and the kernel re-checks every finished term; damaged or forged data is refused, errors 41-45), and the
[parser] gate for branch `s1-synth-b` (FE1e5, the instance search: a nested search that runs out of memory leaves
nothing behind, a malformed universe level answers invalid, a constant made inside another leaves the outer one's
levels alone), after a Forth review and two re-checks of each
([s2-unfold](../development/forth-reviews/2026-11-13-s2-unfold-a.md),
[s1-synth-b](../development/forth-reviews/2026-11-13-s1-synth-b.md)); the last re-check's remaining copies of the new
`ok-store`, the `slab-scoped` word and the unchecked pair count are plan 9.4.8k items for the front pass.

### Gforth 0.7.3 at the push only; fewer full-tier repeats (2026-11-14)

The owner asked why the same suites ran so often (about 30 full-tier runs since 2026-11-13 noon, each 30-40 minutes:
every review-fix round and every merge of main into a branch made a new tree, and the coordinator's briefs asked for
the tier each time) and decided: a branch's tier no longer runs Gforth 0.7.3, which runs at the push
(`scripts/push.sh`, `tested-tree.py tier --with-073`) and in the daily full run. The coordinator also returns to
`AGENTS.md`'s rule: a branch runs its full tier once, when first handed to review; fix rounds and merges of main into
a branch run the focused tests and faults of what they touch; main runs the full tier once per batch of merges, at the
push; at most two suites run at once. `make coverage-check` already stands for `make test` on Gforth 1.0 in the full
tier (plan 9.4.6); only `test-cli` runs in both, on purpose, for its `gforth-fast` runs.

### [parser] and [bypass]: S1's elaborator (2026-11-14)

The owner approved the [bypass] and [parser] gates for branch `s1-elab` (FE1e6-7: LeanForth text such as
`theorem t 0 0 + 0 = := by by-rfl end t` is elaborated with Lean's hidden arguments, instances and default numerals and
the finished terms are checked by the kernel as an export's are; `#check` between declarations; `--elab-fuel`). [bypass]:
nothing the elaborator builds is accepted without the kernel (a planted wrong term is rejected by the kernel; switching
off the kernel's comparison fails the tests; all 4,276 out-of-memory points of S1's theorem end in a refusal or the
identical accepted theorem). [parser]: `#check` inside a declaration is refused, in a term position with Lean's parser
message (140), inside a `by` block with a message saying Lean would end the tactic block there (141), both checked
against pinned Lean. After a Forth review, two fix rounds and three re-checks
([review](../development/forth-reviews/2026-11-13-s1-elab.md)); the last re-check's minor items are plan 9.4.8k
items for the front pass. S1 is called done only after the done checker runs it on all of `Init`.

### [kernel] and [import]: the reuse pass outside the front end (2026-11-14)

The owner approved the [kernel] and [import] gates for branch `reuse-out-2` (plan 9.4.8f, j, k): about 60 shared words
in place of duplicated code across the kernel, the import reader (the NDJSON number and manifest readers), the command
line, the printers and the libraries; the checker's rules unchanged; duplicate groups outside `src/front` 231 → 118,
each kept one with a written reason. Evidence: all 450 test exports (5,833 declarations) byte-identical in verdicts,
reasons, fuel and exit codes on main and the branch (the reviewer's own run after the last merge); all of Init the same
59,349 accepted with fuel 654,719,715 and byte-identical snapshots (the implementer's runs); 20 forged or malformed
export and manifest files refused as before; a Forth and kernel review and three re-checks
([review](../development/forth-reviews/2026-11-13-reuse-out-2.md),
[re-checks](../development/forth-reviews/2026-11-14-reuse-out-2-rc3.md)); the last re-check's small copies are plan
9.4.8k items for the next pass.

### S2's tactics now; a showcase of LeanForth proofs next (2026-11-14, afternoon)

At 93% of the week's tokens the owner started S2's tactics (branch `s2-tactics`, rewriting form first: `0 + n = n` by
`by-induction-with` and `by-rw[ ]`, then the proof set as far as rewriting reaches), and asked for what follows: a set
of nicely printed theorems written in LeanForth, each with its proof derived by LeanForth's tactics, checked by its
kernel, and shown annotated: every step with the goal it leaves and an English line for how it follows (plan 8.6.12,
the explained proofs), from S2's step log (s2-steps). The page joins docs/user/DEMOS.md's form (mathematics, LeanForth,
Lean) but for proofs LeanForth itself derived, and says exactly what was run.


## Faster merges: deferred duplication, batched coverage debt, the daily run out of the push (2026-11-17)

The owner, after an evening in which S2's branch worked (Lean comparisons and planted faults passing) but did not
merge for hours: "we are progressing too slowly ... too much testing ... too small work packages". Three decisions,
each asked in plain language with a recommendation:

1. **Duplication and style findings may merge as planned work** when a reuse pass is already scheduled next. The
   Forth reviewer still reports them; each becomes a named item of that pass (plan 9.4.8). Trust-boundary findings
   and differences from Lean still block the merge. This narrows "Reviews block on duplication" (2026-11-13).
2. **Coverage debt on failure branches may merge, recorded per slice.** Every new word still needs its main tests
   and a planted fault before the merge. Never-run refusal paths (a store or heap refusing, fuel running out,
   malformed records) may wait: the coverage baseline is raised in a commit that names the slice, the debt is listed
   per file in the slice's report and plan row, and one batch test pass pays it at the end of the slice, before the
   slice's done check. This narrows "coverage may not drop" (the 110% rule) for those branches only.
3. **The daily cache-off full run leaves the push.** It runs once a night by itself (and before a tag), recorded per
   tree. A push runs only its own change tier; Gforth 0.7.3's unit tests still run at code pushes. `scripts/push.sh`
   warns when the last daily run is old; it does not run it.

Unchanged: pinned-Lean comparisons, planted faults, the trust part of every Forth review, the owner's gates, and the
done checker.

## Tactic plug-ins: the step log's names, a tactic tier, the order (2026-11-17)

Asked with the tactic plug-in design (`TACTIC_PLUGINS.md` on branch `tactic-plugin-design`, not yet on main, in revision after its design
review, .claude/work/pending-reports/2026-11-17-tactic-plugins-design-review.md) and its measurement: of 18 front-end
branches since 2026-11-12, `tests/mutants/faults.toml` was changed by 18, the `Makefile` by 17, `src/main.fs` by 12 and
`src/author/errors.fs` by 11. The owner approved:

1. **[format] The step log's tactic names are a pattern, not a list.** `schemas/tactic-steps-1.schema.json` accepts
   any name matching `^[a-z][a-z0-9_]*[?!']*$`, so a new tactic needs no schema change. Nothing reads the log back.
2. **A lighter tier for a confined tactic branch.** A branch that an automatic check confirms only adds files in the
   tactics folder (a private wordlist, no writes to shared hooks) runs the front-end tests, every `.lf` end-to-end run
   and the S1/S2 comparisons; the nightly full run is the safety net. Not in force until that check exists.
3. **Order:** after the plug-in interface lands, `by-decide`, `apply` and `constructor` in parallel; `by-omega`
   starting with one shared-services branch; and the design of `simp`'s lemma data started now, because its [import]
   gate is the long step towards `norm_num`, `ring` and proofs about real numbers.

The owner also asked for the plug-in interface itself ("do the tactics plug in and keep going").

## Shorter test runs: per-target reuse, coverage on touched files, Gforth 0.7.3 nightly, more jobs (2026-11-17)

After a push of the test split took about 30 minutes (Lean comparisons 933 s, the unit suite under coverage 511 s,
Gforth 0.7.3 254 s, `gforth-fast` 110 s, two targets at a time), the owner: "30 minutes testing sounds too long for
the scope of those recent changes", and suggested fewer Gforth 0.7.3 runs and coverage on the touched files only.
Approved, all four, with the nightly full run (`make daily`: everything, Lean cache off, Gforth 0.7.3) as the safety
net:

1. A test target's recorded pass is reused while the files that target reads are unchanged, not only when the whole
   tree is identical. A target whose inputs cannot be determined always runs.
2. At a branch tier and at a push, coverage is measured for the tests of the changed files only; full coverage runs
   nightly. Known gap: a change in one file that lowers another file's coverage is found a day late.
3. Gforth 0.7.3 runs in the nightly run and before a tag, no longer at pushes (replaces "Gforth 0.7.3 at the push
   only", 2026-11-14).
4. A push runs more targets at a time when few agents are running.

Unchanged: the pinned-Lean comparisons and planted faults of every file a change can reach. Branch `test-reuse`.

## [format] S2's step log, and the smart-unfolding marker (2026-11-17)

Asked in plain language after the Forth review of `s2-finish` and its re-check
(.claude/work/pending-reports/2026-11-17-s2-finish-review-final.md; filed with the merge as
`2026-11-17-s2-finish.md` in the Forth reviews folder).

1. **[format] The step log, `check --steps FILE|-`, format `leanforth-tactic-steps` version 1: approved.** One header
   line per accepted declaration (name, steps, `axioms`, `open_parts`, `cut`) and one line per tactic step with its
   goals. Evidence: it is written only for accepted declarations and nothing reads it back; a declaration proved only
   with `by-sorry` shows `"axioms":["sorryAx"]` and `"open_parts":1` (probed by the reviewer); a log out of room is cut
   and marked and changes no verdict or exit code; the reviewer's planted faults (filter always true, cut unmarked)
   were caught. The tactic name is the pattern approved earlier today. Later fields are version 2.
2. **The smart-unfolding marker (core term tag 17): merge without a separate [kernel] gate.** No file under
   `src/kernel` or `src/import` changed. `core/terms.fs` gains one inert constant and
   `core/constant-term-boundary.fs` one case arm, both loaded by the kernel; the importer cannot make the marker, the
   hand-over refuses it first (error 200), the export writer refuses it, and no snapshot is written in a text run
   (planted faults caught in both reviews). The reviewer's judgement, which the owner accepted: kernel behaviour is
   unchanged, to be noted here and not gated.

Not yet done: S2's merge, its push and its done check.

## Tactics are ports of Lean's, by function; keep working overnight (2026-11-17, late)

Asked whether tactics should be exact ports of Lean's (so Lean and Mathlib proof scripts behave the same) or shorter
LeanForth-native ones, the owner: "we want 100% lean compatibility, so ports for tactics", and: "I don't see why
they would be particularly larger than other approaches, in Forth ... we are copying functionality, not line by line
C++." So: a tactic is a port of what Lean's tactic does (the same choices, the same order, the same proof term),
written as well-factored Forth on a shared tactic library, never a line-by-line transcription. Size estimates scaled
from Lean's source are to be checked against what is actually written (Forth lines per Lean function ported), and a
tactic's design first lists the Lean primitives it uses and the Forth words that exist for them.

The owner also asked that the `simp` work start if there is time, long Mathlib exports included, and that small tasks
continue overnight without waiting for guidance. The [import]/[format] gate for elaboration data format 4 is not
approved yet: the extraction tool and its data stay on a branch until the owner answers the design's five questions.

## Decisions of 2026-11-18 (morning page)

Asked in plain language with recommendations (2026-11-18, about 11:30), the owner approved each of these:

- **[kernel] the name store's index** (branch `names-index`): a hash index for finding names; each name checked once
  when made, lookups checking what they touch, and the full audit at each hand-over to the kernel. Accepted loss:
  damage to an old entry is noticed at the next hand-over, not at the next new name.
- **[kernel]/[import], in form: the library tidy-up** (branch `lib-tidy-3`), as a change of wordlists with no change
  of behaviour; `bytes.fs`'s reader gains options and LeanForth's callers pass the strict one.
- **[import]/[format] binder kinds** (plan FE1c-bk): the elaboration data carries Lean's own binder kinds, because
  the exporter merges expressions equal up to them.
- **[import]/[format] simp data, format 4** (`docs/design/SIMP_DATA.md`), all five questions as recommended: the
  format and its checks; Lean's on-demand theorems added at the next library export, the helpers of a user's own
  bracket lemmas made in Forth; simprocs ported family by family, an unported one that matches answering
  unsupported; Mathlib's simp data read lazily; the order SP1a-SP2b, MF, S8a1, S7, S8a2, S8b.
- **The Mathlib front end** (`docs/design/MATHLIB_FRONT.md`), all five questions as recommended: data format 3.1;
  instance records checked when first needed (the owner was offered a check once per data file and no check, as
  Lean, and chose this; it is done with the slice that loads Mathlib's data rather than as a large slice of its
  own); on-demand theorems checked as a layer on today's snapshot at the next export; no load target until a
  successful Mathlib run is profiled; the full-Mathlib front-end test only by hand, as a slice's done check.
- **Interface changes:** the command line's exit codes as the fix batch left them (a Forth fault in a run 5, an
  overflow 3, an output over an input, a manifest or `FILE.partial` 4, a full binder table 3); the step log's end
  record as step-log format version 2; U+202E stays printed escaped, a documented difference from Lean's printer.
- **[parser]:** the words `by-apply`, `by-assumption` and `by-constructor` (ports of Lean's, each compared with
  pinned Lean); and the front end's limit of 512 values in one expression lifted.
- **The nightly run** (`make daily`) is started by the agent each night a session is open, by itself; no system timer.
- **`src/program/verify-alias.fs` is retired** with its tests, in a reviewed commit (a superseded variant).
- **Disk:** finished agents' temporary data and the worktrees of merged branches may be deleted, the exact paths
  listed first, each worktree checked for a `.tools` link first, the unmerged branches' worktrees kept.
- **Small rules:** the step log's [format] approval covers the [bypass] gate its design listed (the log never
  changes a verdict); a tactic-only branch may also change documentation and keep the tactic tier.
- **[kernel], in form: tag bits clamped** (branch `small-fixes-1118`, approved later the same day): a term tag
  outside 0-31 is clamped before it becomes a bit mask (`lf-tag-place`, `lf-tag-set+` in `src/core/terms.fs`);
  valid tags behave as before.
- **LeanForth-specific libraries are prioritised** (plan PD20; the owner, 2026-11-18: "we are starting to use what
  would be the contents of several"): in the order listed there, the elaborator library and the simp and rewriting
  library first, designed and architected together with the tactic library and the tactics that will call them,
  while the tactic work continues.

## LeanForth-specific libraries: the design approved (2026-11-18)

On the design [LF_LIBRARIES.md](../design/LF_LIBRARIES.md), after the architect's independent review and its fixes,
the owner approved, each as recommended:

- **Scope and order.** Library 1, the elaborator (the S1/S2 core exists, about a third by Lean lines), and library
  2, simp and rewriting; the six changes to the tactic library's interface, made in slice LA; the order LA beside
  MF2+DT and S3, then SP1b-i beside FE4a (coercions) and FE2's first term forms, then SP1b-ii, then SP1c; the
  lookup tree's move out of `instances.fs` belongs to MF2+DT, not SP1a. LA waits for S2's remaining fixes.
- **Package size:** 1,500-2,500 lines with tests.
- **Parallel work:** a registry for term forms, each form its own file; at most one open branch per shared file;
  new code in the new folders `src/front/elab/`, `simp/` and `num/`; no mass moves of existing files.
- **[format] the coercion tag:** Lean's `coe_decl` tag is one more record kind of elaboration-data format 4, added
  before anything is built on that format; the term front end's structure records become format 5.

## Parallel running and re-entrancy (2026-11-18)

- **[kernel], in form:** `lf-const-levels` moves unchanged into `src/core/constant-term-boundary.fs` beside a new
  `lf-const-level@` (branch `tactic-lib-a2ii`); approved.
- The owner, on learning that large parallel runs were not routine and that the front end is not re-entrant: "I
  don't understand why parallel internal running hasn't been either routine or regularly tested. Re-entrancy is
  important as is speed from multiple internal threads." So: parallel checking is tested at scale every night and
  its speed-up recorded; module-level mutable state is audited and removed; reviews check re-entrancy; the front
  end is made re-entrant and `--jobs` then applies to LeanForth text (plan 9.4.8p).
- **[kernel], in form (branch `parallel-1`, approved 2026-11-18):** the term-tag sets of `src/core/terms.fs` cannot
  be changed once the first context exists; the test build's counter `lf-i2-misses` of
  `src/kernel/environment.fs` is added to atomically; `src/kernel/env-snapshot.fs` uses the library's `slab-data`.
- **The nightly speed-up** (Init at `--jobs 8` against `--jobs 1`) is recorded every night; a floor below which
  the run fails is proposed after about five runs on a quiet machine and needs the owner's approval.
- **Pace** (the owner will not work on Saturday or Sunday, whose share may be spent earlier): two implementing
  agents at a time on separate files, the orchestrator running the long tests. **Order:** S2's remaining fixes and
  its done check beside the simp data (format 4 with the coercion tag); then slice LA; then SP1b-i beside FE4a.

## Libraries first (2026-11-18, late evening)

The owner, on the state of the clean-up: "The libraries and their use should have more weight - more importantly is
changing the coding approach to produce well factored code with reusable words in libraries, with general purpose or
LeanForth specific. Why is the library port of existing tactics incomplete? Why is so much clean up work
incomplete?" Asked three questions with recommendations, the owner chose:

- **Duplication blocks a merge again**, for all new code. This replaces the deferral of "Faster merges"
  (2026-11-17), under which about 30 review items and 250 duplicate groups had been left for a reuse pass that kept
  being scheduled behind features. The coverage-debt and nightly-run parts of that decision stand.
- **One of the two implementing slots is always on libraries and clean-up** until the backlog is cleared: the
  older tactics (intro, rfl, rewrite, induction) onto the goal layer; copied words replaced by shared ones; the
  deferred review items (plan 9.4.8l-o); then the duplicate groups reduced week by week.
- **Library first, for every slice:** an architect step lists the words the slice needs, which exist, and which
  new ones belong in a library; the implementer writes the library words and their tests first, then the caller; a
  caller file holds only words specific to that caller; the review checks that list.

The same evening: **S2's done list loses one item.** The wrong twin of the `Eq.refl` proof (`s2w-add-zero.lf`,
which answers error 131, a coercion, where Lean says "Type mismatch") needs FE4's coercions; the owner agreed to
move it to FE4's acceptance, so that S2 is checked as done once `by-case:` and the `by-rfl` gap are fixed. The owner
also asked for better ordering: a slice that is integrated but not done is finished before the next feature slice
in its area starts.

**The talk.** The owner speaks about the project on Saturday 2026-11-21 and shows and releases the repository
(plan 9.4.8q); slices merge through Thursday and the freeze is Friday. For the talk the owner finds the ingestion
of all of Mathlib the interesting result, not a list of well-known theorems inside it; associativity and
commutativity are not interesting examples for a general audience.

## Clean-up: the stack approved, and how the rest is done (2026-11-19, morning)

Told that three clean-up batches had removed 42 duplicate groups for about 43,000 tokens a group (each replacement
made by hand, each proven equivalent again in review, three stacked branches), the owner asked for a more
efficient way and an easier way to fix unit-test coverage, and decided:

- **[kernel], [import], in form: the clean-up stack (branches `reuse-b`, `reuse-c`, `reuse-d`) is approved**, each
  change a replacement the independent reviewer showed identical: term-tag sets (`lf-tags`, `lf-tag-in?`,
  `lf-term-in?`) in place of comparison chains in `core/terms.fs`, `let-terms.fs`, `string-literals.fs`,
  `tagged-sort-boundary.fs` and the kernel's `whnf.fs`, `defeq.fs`, `mixed-compare.fs`, `inductive-nested.fs`;
  `lf-fvar-mvar-tag?` in `core/mvar-leaves.fs`; four telescope words in `core/compact-exprs.fs`; the library's
  `ok-and`, `ok-apply`, `ok-then2?` and `cell-at@` in place of hand-written copies in the kernel's
  `mixed-infer.fs`, `mixed-level-substitute.fs`, `reduce-nat.fs`, `environment.fs`, `mixed-open.fs`; the kernel's
  `level-normalize.fs` calling core's identical `lf-name-chain-ok?`; in import, the library's counted-list,
  bounded-append, indexing and outcome words in `manifest.fs`, `run-record.fs`, `feed.fs`, `stage-records.fs`,
  `snapshot-tier.fs`, and JSON kinds and strings read through bounds-checked readers (false outside the tape) in
  `manifest.fs`, `ndjson.fs`, `run-replay.fs`.
- **A standing rule for exact-phrase extractions.** When the duplicates script itself defines one word whose body
  is exactly a copied phrase and rewrites every member, the result is identical by construction; such a change in
  kernel, core or import files merges after the Forth review and the tier and is reported to the owner
  afterwards. Any other change to those files still needs the owner's approval first.
  Reported under this rule (a record of its use, not a new decision): branch `cleanup-families-1` (2026-11-19,
  commit "Extract the exact duplicate groups into shared words", plan 9.4.8l AH) rewrote three kernel members by
  `check-duplicates.py --extract`: `mixed-level-substitute.fs`'s `lf-mls-closed?` onto `lf-term-no-params?`
  (defined in `core/terms.fs`, its new line wrapped by hand to stay under 90 characters, tokens unchanged),
  `reduce-nat.fs`'s `lf-rn-node` onto `lf-made-term` (defined in `core/generation-handles.fs`) and
  `level-make.fs`'s `lf-lmk-pick` onto `first-or-second` (`lib/bounds.fs`).
  Reported under the owner's rule of 2026-11-19 (kernel, core and import code is code like any other:
  behaviour-preserving refactoring is ordinary work, with unit tests; nothing the checker accepts or rejects, no
  rule, no file format or saved record layout changes): branch `cleanup-families-2` (2026-11-19), the fixes of
  the Forth review of `cleanup-families-1` (B1): the kernel's last three copies of `lf-made-term`'s phrase,
  in `mixed-infer.fs` (`lf-minfer-sort`), `iota.fs` (`lf-iota-ctor-const`, with a `require` of
  `core/generation-handles.fs`) and `string-literals.fs` (`lf-sx-const`), now call it; and the pair-field family
  (plan 9.4.8l AF): `caches.fs` (`lf-cache-stats`, `lf-cent!`), `env-snapshot.fs` (`start@`, `site-paired`),
  `env-import.fs` (`entry-same?`), `env-layers.fs` (`lay-from`), `mixed-open.fs` (`lf-open-remember`),
  `replace-memo.fs` (`lf-rmemo-kept`) and `mixed-definition-probe.fs` (its claim and value accessors) read and
  write two adjacent cells with `lib/bounds.fs`'s `cell-pair@` and `cell-pair!`, every record's layout unchanged;
  and the counting-loop family (plan 9.4.8l Z): `env-layers.fs`'s `lay-count` counts a layer's slots with
  `lib/find.fs`'s `count-index` (its test `lay-slot?`, the same `slot-record?` call as the loop's); and the
  triple-field family: `env-import.fs`'s `imp-layer-decls`, `env-snapshot.fs`'s `snap-layer-slots!` and
  `env-signature.fs`'s `lf-envsig-actuals` read or write three adjacent cells with `cell-triple@` and
  `cell-triple!`, and `defeq.fs`'s `lf-dq-doubt` writes the doubt's two terms with `cell-pair!`, layouts unchanged.
  And the refusal-tail family: the tail `ok-then? if X else no-result then` (or `... else nip no-result then`)
  becomes `lib/outcome.fs`'s `['] X ok-apply` (or `ok-apply2`, two values dropped on a failure), the same stack
  for every outcome, in `iota.fs` (`lf-iota-typed`), `mixed-infer.fs` (`lf-minfer-put-closed`,
  `lf-minfer-typed`), `reduce-nat.fs` (`lf-rn-truth`, `lf-reduce-nat-constructor`) and `whnf.fs`
  (`lf-whnf-delta-of`, `lf-whnf-reapply`, `lf-nat-literal`). The fixes of its Forth review (branch
  `cleanup-families-2-fixed`): `core/string-literals.fs`'s `lf-str-fields?` counts the bytes since its
  first with `slab-since`; the kernel's `string-literals.fs` names `0 lf-sx-const` as `lf-sx-const0`, which
  `lf-sx-plain`, `lf-sx-char` and `lf-str-type` call through `ok-apply`; and new kernel unit tests pin the
  failing outcome of `lf-whnf-delta-of`, `lf-whnf-reapply`, `lf-iota-typed`, `lf-minfer-put-closed`,
  `lf-minfer-typed` and `lf-rn-truth` and that the snapshot writer's `site-paired` finds a site again.
  Branch `cleanup-families-3` (2026-11-19), the mid-word refusal guards: the kernel's `environment.fs`
  (`lf-axd-made` on `ok-apply2` with `lf-axd-add` and `lf-axd-row-for`), `inductive-nested.fs` (`lf-nest-instance`
  by `check-duplicates.py --rewrite`; `lf-nest-grow-ctor` on `lf-nest-ctor-room`, `lf-nest-ctor-blank` and
  `lf-nest-ctor-new`; `lf-nest-occurrence` on `lf-nest-if-candidate`, `lf-nest-if-type`, `lf-nest-new-key` and
  `lf-nest-no-change`) and `string-literals.fs` (`lf-str-expand` on `lf-sx-chars`, `lf-sx-of-chars` and
  `lf-sx-applied`), and the import's `snapshot-layer.fs` (`ly-fam-expr-of` on `ok-apply3`), steps chained with
  `lib/outcome.fs`'s `ok-apply`, `ok-apply2` and `ok-apply3`, the same stack for every outcome; the kernel's
  reducer and inner loops (whnf, iota, Nat literals, inference of projections, instantiation) keep their guards
  inline, as a chain adds an EXECUTE per step there. Then the comparison and budget families, rewritten by
  `check-duplicates.py --rewrite` onto `lib/bounds.fs`'s `one-of2?`, `one-of3?` and `cell-spend?`, the same flag
  for every input: the kernel's `check-declaration.fs` (`lf-check-short?`; since `fcccf762` it is `caches.fs`'s `lf-short?`), `env-schedule.fs`
  (`lf-sch-waiting?`), `environment.fs` (`lf-kind-bare?`, `lf-env-quot-open?`) and `env-import.fs`
  (`unrepeatable?`); core `derivation-log.fs` (`lf-log-level-leaf`, `lf-copier-spend`; check_log_isolation.py
  allows the two words), `tagged-sort-boundary.fs` (`lf-repr-mode?`) and `input.fs` (`lf-kind-valued?`); import
  `feed.fs` (`feed-member?`) and `stage-records.fs` (`valued?`). The kernel's `whnf.fs` (`lf-whnf-valued?`, once
  per delta step) and `mixed-open.fs` (`lf-open-rev?`, once per bound variable opened) keep the phrase.
- **Tools first:** the duplicates script gains a mode that replaces a group by a named word; a fast per-file
  coverage command lists a file's never-run blocks with line numbers, and a baseline entry can be updated per
  file. Then the remaining groups and coverage debt.
- **Order for 2026-11-19 and 2026-11-20:** the tools; the tactic move's last part (induction and case, S2's
  remaining coverage debt, then S2's done check); on Friday a set of larger LeanForth proofs for the talk beside
  the release work (plan 9.4.8q). The first real-number proof using a Mathlib lemma and further clean-up follow
  next week. About 43% of the week's tokens remained on the morning of 2026-11-19: one implementing agent at a
  time unless files are fully separate.

## S2's showcase page moves to plan 8.6.12 (2026-11-19, afternoon)

S2's third done check ([2026-11-19-s2-recheck.md](../development/done-checks/2026-11-19-s2-recheck.md)) found the
showcase page of S2's acceptance (owner, 2026-11-14: each proof printed step by step with the goal and an English
line, in three forms) still unwritten, because the English line for each step is plan 8.6.12 (explained proofs),
not started. Asked whether the page stays a condition of calling S2 done, the owner chose: **move it to plan
8.6.12**. S2 is judged on its tactics working, tested and compared with pinned Lean; the page is written when
explained proofs are built.


## Tactics in batches, and the order after them (2026-11-19, evening)

- **Parser gate, approved:** a first batch of five tactic words in one branch, each a port of Lean's tactic,
  compared with pinned Lean with wrong twins, on the same terms as `by-apply`, `by-assumption` and
  `by-constructor`: `by-left`, `by-right`, `by-exfalso`, `by-exists`, `by-intros`. Simple tactics are added several
  to a branch from now on (one architect word list, one review, one tier); each further batch of new words is
  still asked.
- **After the batch:** "the most useful bigger tactic that is also good to implement", chosen by the assistant:
  `by-decide` (S3, small, and omega's proofs use it) and then `by-omega` (S4: closes the linear arithmetic step of
  most induction proofs on the naturals, and is the first caller of `lib/bigint.fs`). `simp` follows as the
  library slot's work (LeanForth library 2).
- **Slots:** one feature agent and one clean-up agent run side by side when their files are separate (the
  "Libraries first" rule of 2026-11-18); this replaces "one implementing agent at a time" of the morning.
- **Friday 2026-11-20 is a checkpoint, not a freeze:** documents and install scripts are brought up to date;
  no refactoring, clean-up or feature work waits for it.
- **S2's showcase page:** see the section above; moved to plan 8.6.12.
- **The batch changed (2026-11-19, later):** the architect's word list
  (`.claude/work/briefs/TACTIC-BATCH1-WORDLIST.md`) found Lean's `exists` is a macro over `refine`, `trivial` and
  the anonymous-constructor syntax, none of which LeanForth has; `by-exists` moves to a batch after S3.
  **Parser gate, approved:** `by-clear` (Lean's `clear h`, one hypothesis) takes its place. The batch is
  `by-left`, `by-right`, `by-exfalso`, `by-intros`, `by-clear`. `by-intro` also gains Lean's implicit and
  strict-implicit binders (a difference from Lean closed, with its own pinned test).
- **No question for trivial changes (owner, 2026-11-19, on the `by-clear` question):** "I don't think you need to
  ask for trivial changes like you just asked about." As the assistant reads it: a simple tactic word that is a
  faithful port of Lean's tactic, compared with pinned Lean with wrong twins, is added without asking and
  reported afterwards. Anything that differs from Lean, other kernel, core or import changes, new formats and new
  dependencies are still asked first.

## Coverage debt ended (2026-11-19, evening)

Asked whether to end the exception of 2026-11-17 (never-run failure branches of new words may merge as coverage
debt and be paid before the slice's done check), the owner answered: "Yes end the deferred coverage issue."

- Every never-run branch of a new or changed word is tested in the branch that adds it, before the merge. The
  per-file tool (`make cover FILE=...`) lists the gaps in seconds; refusal paths are reached by the sweep harness
  `tests/support/meta-sweeps.fs`, which refuses each request in turn and compares the answer.
- Why: S2's deferred debt took a whole agent, a review and two tier runs to pay, found a real fault late
  (`lf-whnf-stuck`, plan 9.4.8l AA) and held up S2's done check through three runs.
- The assistant asked about front-end code; the owner's answer was general, and it is applied to all new code.
- Debt recorded before this date is paid by the clean-up slot (`make cover-debt` lists it).

## The kernel is code like any other (2026-11-19, evening)

Asked to approve mechanical clean-up of kernel, core and import files, the owner answered: "I think you are
protecting the kernel too much by avoiding making changes - if it is poor code it needs fixing. the kernel to me
isn't any different than other code - it is not done yet, it is perhaps closer to done, but it still needs edits,
we are improving it, and will test the same as everything else after fixing it. it needs clear easy to maintain,
well factored and well tested (unit) code. the mathlib import is a huge test of it. parallel import another big
test. normal unit tests another big test, well factored libraries another good test."

- Refactoring that keeps behaviour the same (clean-up, shared words and libraries, renaming, added unit tests)
  in `src/kernel`, `src/core` and `src/import` is ordinary work: no question first; the Forth review, the full
  tier with every pinned-Lean comparison, the nightly parallel run of Init, and a report afterwards. This
  replaces the rule that only tool-made exact extractions could touch those folders without asking.
- As the assistant reads it (not the owner's words): a change to what the checker accepts or rejects (a rule,
  an axiom, a file or record format, the trust boundary) still goes through the review gate of `AGENTS.md`
  (Lean's behaviour, differential tests, independent review, a short plain summary for the owner).
- **[kernel], in form (branch `s3a-decide`, 2026-11-19, ordinary work under this rule):** the Nat operation table
  of `src/kernel/reduce-nat.fs` (scratch arena, the fourteen operations, Bool answers, Nat.succ of a literal) and
  the operation names and the name `Nat.zero` of `src/kernel/whnf.fs` moved to `src/core/nat-ops.fs`, which the
  front end's reduceNat? shares; the kernel keeps
  its refusals (a count of 2^32 or more). Nothing the kernel accepts or rejects changes; one failure path no input
  reaches (an arena too small for the operands) no longer drops two cells too many.
- **[kernel], in form (branch `tb2-patterns-e2a`, 2026-11-24, ordinary work under this rule):** the kernel's
  `lf-rebuild-keep` (`src/kernel/mixed-rebuild.fs`), one of seven words with the body `drop outcome-ok` that the
  Forth review of pattern slice E2a found, now has the body `drop-ok`, the new word of `src/lib/outcome.fs`; the
  same in `src/core/scratch-marks.fs` (`lf-scratch-kept` removed, `lf-scratch-drop` calls `drop-ok`) and the
  import's `ly-number`, `rr-any` and `cin-pass-by`. Nothing the kernel or the import accepts, rejects, reads or
  writes changes.

## Coverage in the branch in seconds, the whole-suite ratchet at night (2026-11-19, evening)

The owner, on a batch of five ten-line tactics taking hours: "we have to be more productive with both time and
tokens. it is ridiculus that 5 tactics words will take hours, not minutes - we need better development and
testing approach." Measured the same evening: loading all of the source 0.4 s, one tactic proof against the S2
slice 1.5 s, but `check_s2.py` 464-516 s, the tier's coverage run (`make coverage-focus`) 712-1,064 s and a full
tier 20-25 minutes. Asked whether the whole-suite coverage ratchet should leave the tier, the owner answered:
"yes change item 4, the whole suite coverage ratchet."

- A tier and a push no longer run `make coverage-focus`. They run the branch coverage check instead: for each
  source file the branch touches, its unit tests under coverage (seconds a file), failing when a block on a line
  the branch added or changed is never run. This is the rule of "Coverage debt ended" above, checked directly.
- The whole-suite ratchet of every file (`make coverage-check`) stays in `make daily`, each night and before a tag.
- The rest of the plan the owner was shown the same evening, done by the assistant without further questions: the
  slow Python runners run their cases in parallel; one fast command checks one tactic; a scaffold makes a new
  tactic's files; kernel tests load a kernel-only file so a front-end change does not re-run them; a script
  checks that a plug-in is thin, and the Forth review of such a branch reads only new library words.

## Two approvals of 2026-11-19, late evening

- **Style baseline of `src/lib/bounds.fs`:** the owner: "raise the baseline from 3 to 6 for the file with
  comparison words". The return-stack count of that file goes from 3 to 6 for `one-of2? ( x a b -- flag )` and
  `one-of3?` (Forth review [2026-11-19-cleanup-families-3.md](../development/forth-reviews/2026-11-19-cleanup-families-3.md),
  item 3: a test of one value against two needs the return stack or a deep shuffle). Asked whether that form is
  also the fastest: measured the same evening, 10^8 calls, the return-stack form and the `rot` form take the same
  time (2.4 ns a call on gforth-fast, 6.6 to 6.8 ns on gforth); the phrase written out in place is about 1 ns a
  call faster (1.4 ns and 5.0 ns), which is why the hot paths of the kernel's reducer keep the phrase.
- **What a verification receipt says ran ([format]):** the owner: "m2 option 2". A receipt of `leanforth verify`
  names the launcher that actually checked its export (`bin/leanforth` or `bin/leanforth-checker`) instead of
  always saying `bin/leanforth` (Forth review of branch `layered-loads`, finding M2). The verdict is the same; the
  export-only tests then need not load the front end.

## Two answers of 2026-11-20, morning

Owner, 2026-11-20 (in the session, on the questions of the night's report):

- **Symbols as words: yes** (FE2's question 2, parser gate). `< > ≥ ≠ - / %` and `¬ ∧ ∨ ↔ ∣` may be words in
  theorem text, each meaning exactly what it means in Lean and building what the spelled-out name builds
  (word list `.claude/work/briefs/OPS-WORDLIST.md`, steps C2 and C3). Condition, in the owner's words: "make
  sure they can be entered, I've never typed the non ASCII ones": every symbol that is not ASCII must also
  have a spelling a plain keyboard can type (Lean's own ASCII form where Lean has one, else the name), and
  the language reference must show it beside the symbol.
- **The tag's name for the talk of 2026-11-21: `svfig-prepre-alpha`.** The name is decided; making the tag
  still needs a daily run of that exact tree (`make tag-check`) and the owner's go-ahead for the tag itself.

Later the same morning the owner answered the three remaining questions with "Yes to the new questions":

- **`^` may mean "to the power" in theorem text: yes** (parser gate; a new elaboration rule, Lean's
  `rightact%`: the exponent is elaborated apart and does not help choose the number type; word list step C4).
- **`nat-ops` refuses a non-literal operand: yes** (kernel gate, plan 9.4.8l AW). `lf-nat-lit-op`
  (`src/core/nat-ops.fs`) answers invalid when an operand is not a literal, where it answered ok with a made-up
  literal; no caller passes one. The owner's approval is the gate's fourth part; the change still needs its
  tests of every outcome, the pinned-Lean comparisons and an independent review with no open finding.
- **The repository goes public for the talk: yes.** The licence stays MIT (the repository's `LICENSE`). Before
  the switch the assistant checks the history and the tree for anything that must not be public and reports;
  the switch itself is made when the owner says so, with the tag.

### The gate record of `nat-ops` refusing a non-literal (2026-11-20)

The four parts of the checker gate (`AGENTS.md`, "Review gates") for the change the owner approved above:

1. Lean's rule: Lean's kernel tests both arguments for literals before anything else (`type_checker.cpp`,
   `is_nat_lit_ext` before `get_count_arg`; `is_nat_succ` gives a predecessor only of a non-zero literal;
   `nat_lit_to_constructor` asserts a literal). The new order of the kernel's word is Lean's.
2. Comparisons: every literal case answers as before (8,823 lines of the kernel grid byte-identical on the
   old and the new tree); the non-literal cases and the predecessor of 0, which no caller passes, answer
   invalid where they answered a made-up literal; a counter on the new refusals fired in no test but those
   written for them, over 146 unit test files, four export slices and four `by-decide` files; the tests reach
   every outcome, with 16 planted faults, each caught.
3. Independent review: [2026-11-20-nat-ops-fail-closed.md](../development/forth-reviews/2026-11-20-nat-ops-fail-closed.md),
   merge after fixes, the fixes made, and its re-check: no unresolved finding.
4. The owner's approval: "Yes to the new questions", 2026-11-20, on the question as put: the shared Nat
   operation table refuses a non-number instead of returning a made-up answer, a small kernel behaviour change
   on a path no caller reaches.

### One counted table in the reader (2026-11-20)

Owner, 2026-11-20, on the question whether `src/front/reader.fs` may hold one module-level table, its
style baseline for globals going from 0 to 1: "Ok to do the table... I believe it is read only after
creation and fully reentrant?" Yes to both, as checked by the independent re-check of the branch
(`docs/development/forth-reviews/2026-11-20-ops-symbols.md`, "Re-check", point 2): the table
`lfn-notations` holds the 22 symbol words and their Lean constants; it is written only while `reader.fs`
loads; `lfn-open` refuses every registration once a context exists (`context-new`), through
`lfn-operator:`, `lfn-notation-name:` and `lfn-entry,` alike, and a refused registration leaves the table
as it was; after that every context only reads it, so runs in several contexts or threads share it safely.
The first version of the branch held the same table in a form the counter did not see; the count is now
honest. Not part of this table, and still open as plan 9.4.8l (BB): the older word `lfa-natural!`
(`src/author/groups.fs`), which attaches a meaning to a syntax word, is not yet sealed the same way.


### Wrap up and tag (2026-11-20, late morning)

Owner, 2026-11-20, with the week's usage at 90%: "wrap up current work, update the docs, especially readme, tag
that build, probably in 2-4 hours". So: no new feature work or new agents; the work in flight is finished and
pushed; the README and the documents are brought up to date; then the tag `svfig-prepre-alpha` (the name given
the same morning) is put on that tree once `make daily` has passed on exactly it (`make tag-check`), and pushed.
This is the owner's go-ahead for the tag. Making the repository public stays a separate step on the owner's word.

### The word `divides` (2026-11-20, late morning)

Owner, 2026-11-20, on seeing that Lean's sign for "divides" and the bar that starts a case look alike: "Add the
divides word, the two vertical bars look identical, so saying | is or isn't the one on the keyboard is not helpful.
Find a better description." The owner's own alternatives (`||` for a case and `|` for divides, or `/` for divides)
were set aside after discussion: `/` is division, `||` is Lean's boolean or, and a bar meaning divides would look
like Lean's case bar. Decided (parser gate): `divides` is a word of LeanForth's own in theorem text, a synonym of
Lean's constant `Dvd.dvd` (`3 12 divides` is Lean's `3 ∣ 12`), building the same term; Lean's sign stays readable
for copied text and the bar key stays the case word only. The documents tell the two bars apart by where they
stand (between two values in a goal: divides; at the start of a line of a proof: a case), never by how they look,
and write divisibility with the word.


### A second tag (2026-11-20, evening)

Owner, 2026-11-20, after the install scripts and `make test` were given plain last lines (an install on the owner's
laptop had worked but did not say so): "Let's make second tag, svfig-preprealfa2, don't run overnight, we are at 94%
tokens". The tag `svfig-preprealfa2` (the owner's spelling) goes on the tree that holds those endings, the large-runs
page and the Mathlib record, once `make daily` has passed on exactly it; `svfig-prepre-alpha` stays on `677800d7`.
No nightly run tonight.


### Tactics at speed, and the spellings of the next batches (2026-11-21)

Owner, 2026-11-21, after the talk: implement tactics in larger numbers and cheaply ("10 per week would take half a
year ... how can we work smarter?"; "we need to improve the process for tactics so we can complete most of them this
week"). The answer is plan row TB2: tactics ordered by their use in Mathlib's source
([TACTIC_INVENTORY.md](../development/TACTIC_INVENTORY.md)), built in batches of 8 to 12 per branch with one word
list, one Forth review, one tier and one done check per batch. Reading Mathlib's source for the count is approved (it
was already in `.tools/mathlib/mathlib4`).

Spellings the owner accepted ("follow your spelling suggestions"; "bars ok"):
- `have`: `T e by-have: h` (type, proof, then the name), `e by-have` (unnamed), `T by-have-goal: h` (the proof
  follows as a new goal).
- Lean's `by_cases` is `p by-cases: h`, Lean's name kept beside `by-case:`.
- A right-to-left rewrite rule is `' lemma <-` inside `by-rw[ ]`; a location is a trailing `at: h1 h2`.
- Blocks: `by-try ... by-end`, `by-all-goals ... by-end`, and `by-first | ... | ... by-end`; the bar at the start of
  a proof line begins an alternative there as it does a case.
- The anonymous constructor: proposed `<< p q >>` (with Lean's `⟨ p q ⟩` beside it), the parts postfix terms, no
  comma; the owner asked how it reads and has not yet chosen between it and the counted postfix `p q 2 anon`:
  to confirm before batch 3.

Wording (owner, same day): describe a word by stack position, top and second, never "first" alone, and write a
stack comment that shows what comes out, as `$ ( func value -- func(value) )`.


### Lists sit between bracket words (2026-11-22)

Owner, 2026-11-22, asked whether `at: h1 h2` needs the end of the line to stop, and how Forth-like `by-rwa[ ... ]`
and the proposed name lists and `<< >>` are. Answer given: values before a word are postfix; a fixed number of names
after a word is Forth's defining-word pattern (`by-have: h`); a list up to a closing word is Forth's parsing-word
pattern (`by-rw[ ... ]`); a list to the end of the line was the odd one, built for `at:` in batch 3a by my mistake.
Decision ("Fix at["): a list of variable length always sits between a bracket word and its closing word and never
depends on the line. So `at[ h1 h2 ]` replaces `at: h1 h2`; my reading, from the same answer and the earlier
recommendations the owner did not object to, and reported back to the owner: several names are `by-intro[ a b c ]`
(`by-intro: h` stays for one name) and the anonymous constructor is `<< p q >>` beside Lean's `⟨ p q ⟩`, no comma.

Also: partly complete tactics are tracked in [TACTIC_STATUS.md](../development/TACTIC_STATUS.md), updated in every
tactic branch ("be sure to track those carefully"). Batteries and Mathlib tactics are ported from their source; nothing
of them is loaded at run time.

2026-11-22, later (owner: "we should allow line breaks ... a more vertical structure is better"): a list no longer
has to close on the line it opens. Every bracket list (names, rules, terms, `<< >>`) reads on into the next lines up
to its closing word; a forgotten closing word stops at the first word that can never be its item, at `end NAME`, `:=`
or the text's end, with error 458 at the word that opened the list (plan row TB2, batch 3c). The decision above,
lists between bracket words, is unchanged.


### Blocks in proof text (2026-11-22)

Owner, 2026-11-22, on the one page of [TACTIC_BLOCKS.md](../design/TACTIC_BLOCKS.md): "I don't like by-dot", then,
on the recommendations below, "Yes I agree, continue".
1. Lean's bullet `· tacs` is written `{ tacs }`: Lean's own second syntax for the same block, a bracket pair that
   closes itself (no `by-end`), free in LeanForth text. No `·` and no `by-dot`.
2. `t1 <;> t2` keeps Lean's token between the two steps; t2 is one tactic or one block (`<;> { ... }`).
3. `have h : T := by tacs` is `T by-have-by: h ... by-end` (its own word, so the term is Lean's node for node).
4. A block opened by a `by-` word closes with `by-end`; braces close themselves.
5. `by-any-goals`, `by-repeat`, `by-focus` follow the approved pattern of `by-try`, `by-first`, `by-all-goals`.
6. LeanForth stops at the first error where Lean logs it and goes on; the verdict is the same.
The design review comes before code; a finding against any of these returns to the owner.


## Case patterns (2026-11-22, afternoon)

Owner, 2026-11-22, on the one page of [TACTIC_PATTERNS.md](../design/TACTIC_PATTERNS.md) (second version, after its
[review](../development/design-reviews/2026-11-22-tactic-patterns.md)): "Case patterns are ok."
1. Lean's `cases h` is `' h by-cases` (with alternatives `' h by-cases-with | ... by-end`), beside `p by-cases: h`
   (Lean's `by_cases`).
2. Both `' h by-rcases[ pat ]` and `' h by-obtain[ pat ]` exist, the value first.
3. A pattern is Lean's pattern without commas or parentheses: a bar binds tighter than a space
   (`<< a b | c rfl >>` is Lean's `⟨a, b | c, rfl⟩`), Lean's left-nested group `(a | b) | c` is `<< a | b >> | c`,
   `by-rintro[ a | b c ]` is Lean's `rintro (a | b) c`. Inside an open bracket list a bar is that list's item, also
   at a line's start; outside brackets a bar at a line's start begins an alternative. `(` stays Forth's comment
   everywhere, so `( a | b )` inside a pattern is a comment; the language reference says so.
4. Typed pieces, `@` patterns and obtain's typed forms get their spelling in slice E5, with a measured count.
The owner also asked (same day) whether the line estimates are well factored and build reusable tactic-library
words; the E1 brief asks its review whether the existing eliminator (`elim.fs`) can be rebuilt on the new
low-level induction step, removing code.


## Four workers by default, and the workers' time in the report (2026-11-23)

Owner, 2026-11-23, on the parallel review ([PARALLEL_REVIEW.md](../development/PARALLEL_REVIEW.md)): "make the
jobs default 4, so the rest of the computer is still ok to run", and "the stall time monitor should be there, along
with other performance monitoring items". Done on branch `jobs-default` (2026-11-24):
1. `check` of an export or a snapshot without `--jobs` runs 4 workers, or the machine's hardware threads when fewer;
   `--jobs N` is unchanged, `--jobs 1` one at a time. A LeanForth text, `check --record`, `print` and `replay` stay
   one at a time without the option; the text's note and the refusal of `--jobs` with `--record` still need an
   explicit `--jobs N` above 1. Small exports measured no slower with 4 workers, so the default does not depend on
   the input's size ([COMMAND_LINE.md](../user/COMMAND_LINE.md#parallel-checking---jobs), with Init's curve).
2. `--resources` and the JSON report's `measured` give a run with workers' plan and jobs' run times and each task's
   busy and waiting seconds: the driving task, every worker, and all workers together; the snapshot save is a
   timed phase. The JSON members are optional ones added within report versions 0.4 and 0.5, as `anyLeanVersion`
   (2026-11-10) and `memoryPerCheck` (2026-11-11) were; no version number changed.
