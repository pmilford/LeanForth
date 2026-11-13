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
