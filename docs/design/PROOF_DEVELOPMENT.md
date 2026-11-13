# Proof development: how hard proofs are developed, and what LeanForth could add

**Status: research note, 2026-11-12 (late night). Nothing here is built.** It answers the owner's request of
2026-11-12: "we are working on strict lean compatibility now. We may want to have a mode that helps with developing
proofs, an example might be for a theorem that has two subparts, is to force one to be true to check the other. Come
up with other ways to help develop and prove difficult theorems, review the literature and lists ways people do it
and also come up with at least 10 ways on your own. What is this part of the process called? Proof development?
Imagine the process driven by a person and/or by an ai."

Everything proposed in §4 is **long-term work, after strict Lean compatibility** (the front end, plan FE1–FE12,
[design](FRONT_END.md), [ADR 0021](../adr/0021-front-end.md)), with one exception: Lean's own `sorry` with the
conditional report, which the owner decided tonight ([ADR 0021 Amendment 1](../adr/0021-front-end.md), proposed;
[OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md), "Kernel fixes, the kernel refactor and `sorry`") and which is
Lean behaviour. Plan rows PD1–PD15 are in [PLAN_DRAFT.md](../project/PLAN_DRAFT.md) (section "Phase 8, proof
development"). Owner questions are in §8. Code examples in LeanForth words are **illustrative spellings, not
implemented**; every Lean example and every Lean behaviour quoted was run on pinned Lean 4.35.0 tonight (§9).

## In plain words

- **The name.** The usual name is **proof development** (or *interactive proof development*): building a proof step by
  step with the tool, leaving gaps, testing ideas, and closing the gaps one by one. Around it are *proof engineering*
  (keeping large proofs working), *formalization* (turning written mathematics into checked statements and proofs),
  *blueprints* (a plan of lemmas and what depends on what) and *proof search* (the machine looks for the proof). §1
  says how they differ.
- **The owner's example is Lean's `sorry`.** In Lean you write `sorry` for the part you have not proved; Lean checks
  everything else and accepts the theorem with a warning, but the theorem then rests on the axiom `sorryAx`, which is
  false (it proves `0 = 1`), so the theorem is not proved. The owner decided tonight that LeanForth does exactly this,
  reports the theorem **NOT PROVED**, and adds a development report: everything else was checked by the kernel, the
  statement holds **if** each listed open part is true, and each open part is listed with its statement, its position
  and what depends on it (§3).
- **What else people do** (§2): look at the goals, split the proof into lemmas, let automation find small steps,
  search the library, test the statement on small cases to find counterexamples before trying to prove it, write a
  plan (blueprint) that a team or many AI agents fill in, and check the final result again with an independent
  checker against the exact statement that was asked for. AI provers today work the same way: they write a sketch
  with gaps, prove the gaps separately and repair what fails, using the checker's error messages.
- **What LeanForth could add** (§4, 17 ideas): an *assumption ledger* that tracks every open part and everything that
  depends on it; turning open parts into explicit hypotheses so the kernel proves "if these parts hold, the theorem
  holds" as a real theorem; checking one part while assuming others without editing the file; counterexample search
  whose refutations the kernel checks; statement sanity checks (contradictory hypotheses, unused hypotheses,
  truncating subtraction); proof sessions with saved states and branches at the Forth prompt; a JSON protocol with
  budgets for AI provers; fuel-based difficulty estimates; incremental re-checking; proof minimisation; explained
  partial proofs; and a shared queue of open parts for people and agents.
- **Trust** (§6): the kernel stays the only judge. A theorem with an open part is never "proved"; development features
  are opt-in, never the default, add no axiom, and every claim names the exact statement and its axioms.

## 1. What this part of the process is called

Short answer for the owner: **"proof development"** is right, and it is the term the Rocq (Coq) manual itself uses
for a proof under construction ("`Abort` … cancels the current proof development",
[Rocq manual, proof handling](https://rocq-prover.org/doc/V8.8.2/refman/proof-engine/proof-handling.html)). It covers
everything between "here is a statement" and "the kernel accepted a complete proof": exploring, sketching,
splitting into lemmas, leaving gaps, testing, searching and repairing. The neighbouring names stress one part of it:

| Name | What it stresses | Typical use and source |
| --- | --- | --- |
| Proof development, interactive proof development | Building one proof step by step with the tool's feedback (goals, errors) | Rocq's proof mode ([manual](https://rocq-prover.org/doc/V8.8.2/refman/proof-engine/proof-handling.html)); Lean's tactic mode and goal view |
| Interactive theorem proving | The field and the kind of tool (a person steers, the machine checks) | Lean, Isabelle, Rocq, Agda |
| Proof engineering | Building and *maintaining* large proof developments: organisation, automation, repair after changes | [Ringer et al., *QED at Large*](https://arxiv.org/abs/2003.06458) (survey) |
| Formalization; autoformalization | Turning written mathematics into formal statements and proofs; *auto*-: done by a machine | [Wu et al. 2022](https://arxiv.org/abs/2205.12615) |
| Blueprint-driven formalization | A written plan of definitions and lemmas with a dependency graph, filled in by many people | [leanblueprint](https://github.com/PatrickMassot/leanblueprint) (Massot); PFR, FLT (§2.2) |
| Sorry-driven, hole-driven, type-driven development | Write the outline first, leave holes (`sorry`, `?_`, `{! !}`), fill them later | Lean; [Agda holes](https://agda.readthedocs.io/en/v2.7.0/tools/emacs-mode.html); Idris "type, define, refine" ([Brady](https://livebook.manning.com/book/type-driven-development-with-idris/chapter-3)); [Hazel's typed holes](https://arxiv.org/abs/1805.00155) |
| Proof sketching; draft, sketch, prove | A formal skeleton with gaps, the gaps closed by automation | [Jiang et al. 2022](https://arxiv.org/abs/2210.12283) |
| Proof planning | An explicit plan for the shape of a proof (for example "induction, then rewrite to use the hypothesis") that guides the search | [Bundy 1988](https://doi.org/10.1007/BFb0012826) |
| Proof search, automated theorem proving | The machine finds the proof or a step of it | Hammers, tactic search, AI provers (§2.9) |
| Proof repair | Fixing proofs that broke after a change, or that an AI got almost right | [Ringer, *Proof Repair* (thesis, 2021)](https://homes.cs.washington.edu/~djg/theses/ringer_dissertation.pdf); [Baldur](https://arxiv.org/abs/2303.04910) |
| Counterexample finding, property-based testing | Trying to *refute* a statement before proving it | [Nitpick](https://www.proof.cit.tum.de/~nipkow/pubs/itp10.html), [Quickcheck](https://doi.org/10.1007/978-3-642-35308-6_10), [QuickChick](https://softwarefoundations.cis.upenn.edu/qc-current/index.html), [Plausible](https://github.com/leanprover-community/plausible) |
| Proof debugging, verification debugging | Finding where and why a proof fails | Dafny, F*, ACL2's checkpoints (§2.6, §2.7) |
| Heuristics, problem solving | How mathematicians find proofs at all: special cases, auxiliary problems, counterexamples | [Pólya, *How to Solve It*](https://en.wikipedia.org/wiki/How_to_Solve_It) (1945); [Lakatos, *Proofs and Refutations*](https://www.cambridge.org/core/books/proofs-and-refutations/575FC8A6B4FAB79E649EDF5FBB9C6E10) (1976) |

This note uses **proof development** for the whole activity, **open part** for a gap closed by `sorry` (the
owner's "subpart"), and **development mode** for the opt-in features of §4 that go beyond Lean.

## 2. How people develop hard proofs today

### 2.1 Lean 4 (what pinned Lean 4.35.0 offers, probed tonight)

Lean's working style is to keep a file that always checks: a hole is written as `sorry` (Lean accepts the declaration
with a warning) or as `?_` (a new goal for later in the same proof), and the *goal view* shows, at each point, the
hypotheses and what is left to prove. The brief for this note listed `exact?`, `apply?` and `rw?` as Mathlib-only;
the probe shows they are in core Lean 4.35.0 (library search began in Mathlib, as `library_search`).

| Tool | What it does for development | Where (probe of 2026-11-12, §9) |
| --- | --- | --- |
| `sorry`, `admit` | Close a goal without proof; the declaration is accepted with the warning "declaration uses `sorry`" and depends on `sorryAx` | core |
| `stop` | Skip the rest of a tactic block (closes it with `sorry`) | core |
| `?_` with `refine` or `exact` | Leave named or anonymous holes that become new goals of the same proof | core |
| Goal view; `trace_state` | Show the hypotheses and goals at a point | core (the view is the editor's) |
| `have`, `suffices`, `show`, `calc` | Structure a proof forwards ("we have …"), backwards ("it suffices to show …") and as a chain of equalities | core |
| `decide`, `omega`, `grind` | Decision procedures: closed decidable facts; linear arithmetic over `Nat` and `Int`; a congruence-closure and case-splitting prover | core |
| `simp?` | Run `simp` and print the `simp only [...]` call it used, so the proof stops depending on the whole simp set | core |
| `exact?`, `apply?`, `rw?` | Search the library for a lemma that closes or advances the goal, and print the call | core |
| `try?` | Try a portfolio of tactics and print the ones that work (tonight: `assumption`, `grind`, `grind only`) | core |
| `show_term` | Show the proof term a tactic built | core |
| `#check`, `#eval`, `#reduce`, `#print axioms`, `#check_failure`, `#guard` | Experiments: types, evaluation, which axioms a theorem rests on, expected failures, quick tests | core |
| `extract_goal` | Print the current goal as a stand-alone theorem ([Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ExtractGoal.html)) | Mathlib ("unknown tactic" in core) |
| `hint` | Try a list of tactics and report which work | Mathlib ("unknown tactic" in core) |
| `polyrith` | Find a linear combination of polynomial hypotheses; its Mathlib page says it "relied on an external Sage server which has been shut down" ([Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Polyrith.html)) | Mathlib ("unknown tactic" in core) |
| `aesop` | Rule-based best-first proof search ([Limperg and From, CPP 2023](https://doi.org/10.1145/3573105.3575671)) | the Aesop package, which Mathlib uses ("unknown tactic" in core) |
| `plausible` | Random testing of a goal; reports a counterexample with shrinking ([repository](https://github.com/leanprover-community/plausible)) | the Plausible package, which Mathlib uses ("unknown tactic" in core) |

**`sorry` in detail (pinned Lean 4.35.0).** For the owner's two-part example (§9, probe 1):

```lean
theorem two_parts (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  constructor
  · rfl
  · sorry
#print axioms two_parts      -- 'two_parts' depends on axioms: [sorryAx]
```

- Lean prints the warning ``declaration uses `sorry` `` and exits 0; with `-DwarningAsError=true` the same file is an
  error and exits 1.
- The first part (`n + 0 = n`, by `rfl`) is fully checked; the second is closed by the term
  ``sorryAx (∀ (tag : Lean.Name), 0 + n = n) false `‹label›` ``: Lean 4.35.0 gives every `sorry` its own **label**
  (a name made from the source position and a counter), so two `sorry`s are different terms.
- Dependence spreads: a theorem that uses `two_parts` also depends on `sorryAx`. `#print axioms` says *that* a theorem
  depends on some `sorry`, not *which* one.
- A theorem proved from a `sorry` of a false statement proves anything: `theorem bad : (0 : Nat) = 1 := sorry` and
  then `False` from it are both accepted with warnings.
- **Error recovery:** when a tactic fails (tonight: `omega` on `n + 1 = n`), Lean reports the error, exits 1, but
  still adds the declaration with `sorryAx` in place of the failed part and goes on checking the rest of the file, so
  that one run reports many errors.

### 2.2 Large Lean projects: blueprints, collaboration, independent checking

- **Blueprints.** Patrick Massot's [leanblueprint](https://github.com/PatrickMassot/leanblueprint) is a LaTeX
  document whose numbered statements carry `\uses{…}` (dependencies) and `\lean{…}` (the Lean name); it draws the
  dependency graph and colours each node by status (statement formalized, ready to prove, proved). The statuses come
  from marks the authors maintain; LeanArchitect, a later tool, reads them from the Lean code instead (as reported in
  the search summary of tonight, not verified in its source).
- **PFR.** The polynomial Freiman–Ruzsa conjecture ([Gowers, Green, Manners, Tao](https://arxiv.org/abs/2311.05762))
  was formalized with a blueprint by a team led by Terence Tao in about three weeks; on 5 December 2023 Tao announced
  the proof complete "without any sorrys"
  ([Quanta](https://www.quantamagazine.org/a-team-of-math-proves-a-critical-link-between-addition-and-sets-20231206/);
  [project](https://teorth.github.io/pfr)).
- **FLT.** Kevin Buzzard's project to formalize Fermat's Last Theorem, with an 86-page
  [blueprint](https://imperialcollegelondon.github.io/FLT/blueprint.pdf), is many-author and ongoing
  ([Lean use case](https://lean-lang.org/use-cases/flt)). Anthropic reported on 2026-09-04 a complete Lean proof of FLT
  written largely autonomously by Claude agents over 11 days, organised as a directed graph of theorem statements,
  checked by Lean with only the three standard axioms, and its statement matched to Mathlib's by a comparator tool;
  the post says the proof is "likely much longer than it needs to be"
  ([Anthropic](https://www.anthropic.com/research/formalizing-fermats-last-theorem); the vendor's own report).
- **Equational Theories Project.** Tao's project settled all of about 22 million implications between 4,694
  equational laws of magmas, every result checked in Lean: brute-force search over small finite magmas refuted many
  implications, automated provers did much of the rest, and people worked on the hard core
  ([final report](https://arxiv.org/abs/2512.07087); [project](https://teorth.github.io/equational_theories)).
  Counterexample search was as important as proof.
- **Strong prime number theorem.** Math, Inc.'s agent Gauss completed a Lean formalization (about 25,000 lines) begun
  by Tao and Kontorovich, with "targeted human scaffolding and review of key lemmas"
  ([project page](https://math-inc.github.io/strongpnt)).
- **Checking the final result.** The Lean reference's page
  [Validating Proofs](https://lean-lang.org/doc/reference/4.35.0-rc3/ValidatingProofs/) lists the steps of increasing
  strength: the editor's marks, `#print axioms` (it flags `sorryAx` and any custom axiom), re-checking the compiled
  library with `lean4checker`, and as the gold standard `comparator`, which checks in a sandbox that a submitted proof
  proves exactly a trusted challenge statement with only the permitted axioms, optionally with external checkers such
  as nanoda. It also says the statement's *meaning* is a separate question. LeanForth is one such independent
  checker.

### 2.3 Isabelle

- **`sorry` and abandoning a proof.** Isabelle's `sorry` skips a proof (outside interactive use it needs the
  `quick_and_dirty` option; [source history](https://isabelle.in.tum.de/repos/isabelle/rev/72348ff7d4a0)); `oops`
  abandons a proof attempt (from the Isar reference manual, which could not be fetched tonight).
- **Isar** structured proofs ("have … show … by …") read like written mathematics and are checked step by step
  ([Wenzel 1999](https://doi.org/10.1007/3-540-48256-3_12)).
- **Sledgehammer** sends the goal to external automatic provers and SMT solvers and turns what they find into an
  Isabelle proof that Isabelle checks: the translation may be unsound, so its output "cannot be trusted but does not
  need to be trusted" ([Paulson and Blanchette 2010](https://www21.in.tum.de/~blanchet/iwil2010-sledgehammer.pdf)).
  This is LeanForth's trust model exactly.
- **Nitpick** looks for counterexamples to higher-order statements with a SAT-based model finder
  ([Blanchette and Nipkow, ITP 2010](https://www.proof.cit.tum.de/~nipkow/pubs/itp10.html)); **Quickcheck** tests
  statements randomly, exhaustively on small values and symbolically
  ([Bulwahn, CPP 2012](https://doi.org/10.1007/978-3-642-35308-6_10)); both can run automatically on every new
  statement.
- **`try` and `try0`** run a selection of proof methods (`try` adds Quickcheck, Nitpick and Sledgehammer) and report
  what works ([Blanchette on the users' list](https://isabelle-prover.github.io/zulip-archive/stream/336180-Archive-Mirror.3A-Isabelle-Users-Mailing-List/topic/.5Bisabelle.5D.20Any.20fans.20of.20.22try.22.3F.html)).

### 2.4 Rocq (Coq)

- **`Admitted`** ends a proof by declaring its statement as an axiom; **`Abort`** cancels the current proof
  development ([manual](https://rocq-prover.org/doc/V8.8.2/refman/proof-engine/proof-handling.html)). **`Program`**
  lets a definition be written first and leaves its proof obligations to be discharged later (or admitted with
  `Admit Obligations`; [command index](https://coq.inria.fr/doc/v8.17/refman/coq-cmdindex.html)).
- **QuickChick** is property-based testing for Rocq ([Software Foundations, volume 4](https://softwarefoundations.cis.upenn.edu/qc-current/index.html)).
- **CoqHammer** translates goals to first-order logic for external provers and reconstructs proofs; about 40.8% of
  the standard library's theorems push-button ([Czajka and Kaliszyk 2018](https://cl-informatik.uibk.ac.at/research/publications/publications-2018/hammer-for-coq-automation-for-dependent-type-theory)).
- **Tactician** learns from the user's own tactic scripts as they write them and suggests or searches for the next
  steps ([Blaauwbroek, Urban and Geuvers 2020](https://arxiv.org/abs/2008.00120)).
- **Proof repair** uses what changed in a definition to fix the proofs that broke
  ([Ringer 2021](https://homes.cs.washington.edu/~djg/theses/ringer_dissertation.pdf)).

### 2.5 Agda, Idris and typed holes

- **Agda** programs and proofs are written with holes; the editor shows each hole's goal and context, splits a
  variable into cases (`C-c C-c`), refines a hole with a function and searches for a term (Auto)
  ([Emacs mode](https://agda.readthedocs.io/en/v2.7.0/tools/emacs-mode.html),
  [Auto](https://agda.readthedocs.io/en/v2.6.4/tools/auto.html)).
- **Idris**: "type, define, refine" — write the type, a definition with holes, then fill or sharpen the holes guided
  by the types ([Brady, *Type-Driven Development with Idris*](https://livebook.manning.com/book/type-driven-development-with-idris/chapter-3)).
- **Hazel** keeps *running* a program that has holes, evaluating around them
  ([Omar et al., POPL 2019](https://arxiv.org/abs/1805.00155)) — the same idea as checking the rest of a proof around
  its open parts.

### 2.6 Dafny and F*

- **Dafny** proves `assert`s with an SMT solver; `assume` adds a fact without proof, which later code may use. To
  find a failing or slow step, users split the work into separate solver queries (`{:split_here}`, `{:focus}`,
  `--isolate-assertions`; [verification optimization](https://dafny.org/latest/VerificationOptimization/VerificationOptimization),
  [FAQ](https://dafny.org/dafny/HowToFAQ/FAQSplitHere)); the reference manual has sections on debugging failing and
  brittle verification (not read tonight).
- **F\*** users debug with `admit()` placed and moved through a proof ("sliding admit"; listed on the
  [F* wiki](https://www.github.com/FStarLang/FStar/wiki); its page could not be fetched tonight): if everything before
  the `admit()` checks, the problem is after it.

### 2.7 ACL2: "The Method"

ACL2's documented method: submit the goal; when the proof fails, read the *key checkpoints* (the first goals the
prover could not simplify further), find the missing lemma they suggest, prove that lemma the same way, and try the
goal again ([THE-METHOD](https://www.cs.utexas.edu/~moore/acl2/v2-8/THE-METHOD.html),
[key checkpoints](https://www.cs.utexas.edu/~moore/acl2/v6-3/INTRODUCTION-TO-KEY-CHECKPOINTS.html)).

### 2.8 Mathematicians

- **Pólya** ([*How to Solve It*](https://en.wikipedia.org/wiki/How_to_Solve_It), 1945): understand the problem, devise
  a plan (a related problem, a special case, a generalisation, an auxiliary problem, working backwards), carry it out,
  look back (check the result, find a simpler proof, reuse it).
- **Lakatos** ([*Proofs and Refutations*](https://www.cambridge.org/core/books/proofs-and-refutations/575FC8A6B4FAB79E649EDF5FBB9C6E10),
  1976): proofs and counterexamples improve each other; a counterexample to a "theorem" points to a hidden lemma,
  which becomes a hypothesis of a corrected statement.
- In practice: compute small cases, look for counterexamples first, prove special cases, strengthen the induction
  hypothesis, split the proof into lemmas, and have colleagues check the argument.

### 2.9 AI-driven proof development

| Approach | Idea | Examples and sources |
| --- | --- | --- |
| Step-by-step tactic search | A model proposes the next tactic; a best-first or tree search explores the proof states the checker returns | GPT-f on Metamath ([Polu and Sutskever 2020](https://arxiv.org/abs/2009.03393)); HyperTree Proof Search ([Lample et al. 2022](https://arxiv.org/abs/2205.11491)) |
| Premise selection | Retrieve the few library lemmas likely to help, then generate tactics with them | ReProver in [LeanDojo](https://arxiv.org/abs/2306.15626); [Lean Copilot](https://arxiv.org/abs/2404.12534) (suggestions and search inside Lean) |
| Whole-proof generation and repair | Write a complete proof at once; on failure, give the model the checker's error and ask for a repair | [Baldur](https://arxiv.org/abs/2303.04910) (Isabelle: 47.9% alone, 65.7% with a search-based prover) |
| Draft, sketch, prove | An informal proof, then a formal sketch with gaps, the gaps closed by automation | [DSP](https://arxiv.org/abs/2210.12283) (20.9% → 39.3% on competition problems); in Lean 4 through [Pantograph](https://arxiv.org/abs/2410.16429), which resumes proofs containing `sorry` |
| Subgoal decomposition with `sorry` | A large model writes the proof outline with `sorry` for each subgoal; a prover closes the subgoals; the pieces are put together | [DeepSeek-Prover-V2](https://arxiv.org/abs/2504.21801); [Seed-Prover](https://arxiv.org/abs/2507.23726) (proposes and proves lemmas first, refines with Lean's feedback); [Goedel-Architect](https://arxiv.org/abs/2606.06468) (a blueprint as a Lean file of lemmas with unfilled proofs, rewritten when a lemma fails) |
| Growing lemma libraries | Keep proved lemmas as reusable "skills" | [LEGO-Prover](https://arxiv.org/abs/2310.00656) |
| Reinforcement learning at scale | Learn from millions of automatically formalized problems; for a hard problem, learn from variants at test time | [AlphaProof](https://research.google/pubs/olympiad-level-formal-mathematical-reasoning-with-reinforcement-learning/) (Nature, 2025) |
| Autoformalization | Translate written statements (and proofs) to formal ones | [Wu et al. 2022](https://arxiv.org/abs/2205.12615); Gauss (§2.2) |
| Agents over a dependency graph | Many agents prove nodes of a graph of statements, coordinated by a tool | FLT by Claude agents (§2.2) |
| Learning from the user | Online learning from the proofs being written | [Tactician](https://arxiv.org/abs/2008.00120) |

**What works.** Decomposition into lemmas with gaps that the checker validates structurally (every recent system);
the checker's error messages as feedback; retrieval of relevant library lemmas; large, parallel search budgets; and
at the end an independent check of the exact statement with the axioms listed.

**Known failure modes.**

1. **Proving the wrong statement (misformalization).** An audit of the ProofNet benchmark found 204 of 367 formal
   statements (56%) unfaithful to their informal versions ([Ground False, NeurIPS 2026](https://neurips.cc/virtual/2026/poster/139101));
   another audit of five Lean benchmarks certified 398 defects, among them false statements, vacuous theorems and
   unsound axioms ([Faults in Our Formal Benchmarking](https://arxiv.org/abs/2606.29493)). A proof of a wrong
   statement is still a correct proof — of something else.
2. **Vacuous statements.** Contradictory hypotheses make anything provable: pinned Lean accepts
   `(h1 : n < 2) (h2 : n > 5) : n * n = 7` by `omega` (§9, probe 5).
3. **Traps in the types.** Natural-number subtraction truncates (`2 - 5 = 0` in `Nat`; probe 5), and division by zero
   is zero; a statement that means one thing on paper can mean another in Lean.
4. **Gaps left in and checker bypasses.** A `sorry` left in; a reported bug of older Lean versions in which `apply?`
   let proofs pass without a checked declaration, exploited by a prover model ([arXiv 2606.29493](https://arxiv.org/abs/2606.29493));
   `native_decide`, which trusts compiled code through the axiom `Lean.ofReduceBool` (permanently unsupported in
   LeanForth, AGENTS.md). Hence `#print axioms`, re-checking and comparator (§2.2).
5. **Brittle and bloated proofs.** Proofs that depend on the whole `simp` set or on search break when the library
   changes (proof repair, `simp?`); machine-found proofs are often much longer than needed (FLT report above).
6. **Cost.** Search spends large budgets; without per-step accounting it is hard to see where.

## 3. Lean's `sorry` and the owner's decision of tonight

**The tension.** ADR 0021 D3 said that LeanForth text has no `sorry` and no error recovery, so that a text with an
open goal could never look finished. The owner's rule, though, is that LeanForth behaves exactly as Lean by default,
and every Lean user can write `sorry`; the owner had also answered on 2026-11-03, for exported declarations, "if lean
accepts sorryAx with a warning, so should we", and LeanForth already reports such declarations NOT PROVED.

**Decided tonight** ([ADR 0021 Amendment 1](../adr/0021-front-end.md), proposed; owner's words in
[OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md)):

- the explicit `sorry` (term or tactic) works exactly as in Lean 4.35.0; the kernel checks everything else; the
  verdict is Lean's (accepted, with `sorryAx` among its axioms), reported **NOT PROVED** with `sorryAx` named, never
  counted as proved;
- a **development report**: everything except the open parts was checked by the kernel; the statement holds **if**
  each open part is true; each open part is listed with its statement (three forms), its source position and the
  declarations that depend on it; it never says "proved";
- **no automatic error recovery**: a failed tactic still stops the text; LeanForth never fills a failure with
  `sorryAx` by itself (Lean does, §2.1, to report more errors; the file's result is a failure in both).

**The owner's further thought** — "I almost wonder if it is better for sorry to be true instead, so proof is called
valid if sorry section is true" — has an honest form and a dishonest one. Making `sorry` *true* inside the kernel
would be an axiom that proves everything (`sorryAx` proves `0 = 1`, probe 1), so it cannot be done. But "valid **if**
the open parts are true" is exactly a theorem the kernel *can* check without any extra axiom: take each open part as
an explicit hypothesis. Pinned Lean accepts, with no `sorryAx`:

```lean
theorem two_parts_given (gap : ∀ k : Nat, 0 + k = k) (n : Nat) :
    n + 0 = n ∧ 0 + n = n := ⟨rfl, gap n⟩
#print axioms two_parts_given     -- does not depend on any axioms
```

That theorem is *proved*; it is just a different statement ("if every `0 + k = k`, then …"). When the open part is
later proved, applying the conditional theorem to it gives the original theorem, also with no axiom (probe 5). Ideas
1 and 2 below build the decided report and this conditional theorem out in full.

## 4. Ideas for LeanForth

LeanForth's strengths shape these ideas: a small trusted kernel and deterministic re-checking; fuel and memory
accounting with outcomes that keep *exhausted* apart from *refuted* (ADR 0008); saved snapshots of checked libraries
(ADR 0020); the derivation log (ADR 0013) and explained proofs (plan 8.6.12); Forth's interactive interpreter, where
each word runs as soon as it is typed and stores can be rolled back to a mark; statements printed in three forms
(plan 8.6.2); the job pool for parallel checks; and the project's own habit of planted faults.

Each idea gives: what it is; how a person uses it; how an AI uses it; what the kernel still guarantees; whether it is
Lean behaviour or an opt-in beyond Lean; and a rough size (S, M, L as in the plan).

| # | Idea | Lean or opt-in | Size | Plan row |
| --- | --- | --- | --- | --- |
| 1 | The conditional report and the assumption ledger (decided report, built out) | Lean's verdict; the report is presentation (decided) | M | PD1, PD2 |
| 2 | Open parts as hypotheses: the kernel proves "if the open parts hold, the statement holds" | opt-in | M | PD3 |
| 3 | What-if checking: assume named parts without editing the text | opt-in | S–M | PD4 |
| 4 | A blueprint whose statuses the kernel computes | opt-in command | M | PD4 |
| 5 | Counterexample search on small instances, with refutations the kernel checks | opt-in command | M–L | PD5 |
| 6 | Statement sanity checks: vacuity, unused hypotheses, type traps | opt-in warnings | M | PD6 |
| 7 | Statement faithfulness: the three forms compared, equivalence proved | opt-in | M–L | PD6 |
| 8 | Proof sessions: saved states, branches and word-by-word stepping | opt-in interface | M | PD7 |
| 9 | A JSON prover protocol with budgets for AI tools | opt-in interface | M–L | PD8 |
| 10 | Fuel profile and difficulty estimates | opt-in report | S–M | PD9 |
| 11 | Incremental re-checking of only what changed | same verdicts | M | PD10 |
| 12 | Library search and a parallel tactic portfolio | Lean's tactics (ported); parallel run opt-in | L | PD11 |
| 13 | Proof minimisation and robustness checks | opt-in | M | PD12 |
| 14 | Explained partial proofs and outline-first skeletons | opt-in printing | M | PD13 |
| 15 | `calc` chains and `suffices` skeletons with automatic step attempts | opt-in | M | PD13 |
| 16 | Statement mutation testing | opt-in | M | PD14 |
| 17 | A shared queue of open parts for people and agents, with an attempt journal | opt-in | M–L | PD15 |

### Idea 1. The conditional report and the assumption ledger (decided report, built out)

**What.** For every declaration with open parts, the report the owner decided: *checked except for the open parts;
holds if each is true*; and, across a whole text or project, a **ledger** of open parts: for each, an identifier
(`G1`, `G2`, … stable across runs, derived from the declaration and the goal), its statement in three forms with the
local hypotheses it may use, the source position of its `sorry`, Lean's label, its status (open, closed, refuted),
the declarations that depend on it directly and through other declarations, and what the rest of the check cost
(fuel). The ledger also counts honestly: "5 declarations: 3 proved; 2 not proved, both holding if G1 and G2 hold".

**How the open parts are found.** Not by searching the source for the word `sorry`, but from the checked terms: after
the kernel accepts a declaration, its proof term and the closure of constants it uses are walked for applications of
`sorryAx`; each carries Lean's label (§2.1), so the report can say *which* open part each declaration rests on, where
Lean's `#print axioms` only says "some `sorry`". A `sorry` hidden in a library lemma, produced by a macro or
imported from a Lean export is therefore found too.

An illustrative report (wording and JSON fields are the owner's [format] decision when it is built):

```text
infinitely_many_primes: NOT PROVED (depends on sorryAx)
  Checked by the kernel: everything except 2 open parts.
  The statement holds IF these open parts are true:
    G1  exists_prime_dvd, primes.lf:21:69   ∀ n, 2 ≤ n → ∃ p, IsPrime p ∧ p ∣ n
        used by: infinitely_many_primes
    G2  not_dvd_fact_succ, primes.lf:23:20  ∀ n p, IsPrime p → p ≤ n → ¬ p ∣ fact n + 1
        used by: infinitely_many_primes
  Axioms besides sorryAx: propext, Quot.sound
```

**Person.** Writes the outline of a hard proof with `sorry` for each piece, checks it, and reads the ledger as the
to-do list; when a piece is proved, the ledger shows which theorems became proved.

**AI.** Reads the ledger as JSON; picks the open part with the most dependents or the lowest estimated difficulty
(Idea 10); receives that part as a stand-alone problem (its goal and hypotheses, as `extract_goal` prints them); and
submits a proof, which is checked in place (Idea 17). The ledger is the agent's memory between attempts and the
evidence of what is still missing when its budget ends.

**Kernel guarantee.** Everything outside the listed open parts was checked; the list is complete because it is read
from the checked terms. The verdict is Lean's; the report never says "proved".

**Lean or beyond.** The verdict and the `sorry` behaviour are Lean's (PD1); the report is presentation, decided by the
owner as the default for NOT PROVED declarations. The cross-run ledger file is opt-in. **Size** M.

**Extension: one report of everything a result rests on.** The same ledger can list every kind of assumption: open
parts; parts assumed on the command line (Idea 3); axioms outside the allowlist (NOT PROVED); for an imported result,
that Lean elaborated it and LeanForth re-checked the export; and for the program track, a receipt's runtime
assumptions. One place answers "what does this rest on?".

### Idea 2. Open parts as hypotheses: a conditional theorem the kernel proves

**What.** On request, LeanForth turns each open part into an explicit hypothesis and checks the result as a new
declaration with no `sorryAx`: from `T` with open parts `G1`, `G2` it writes `T.given` (name to be decided) with
statement "if `G1` and `G2`, then `T`", where each open part is first closed over the local hypotheses it used (as
`extract_goal` does), and each `sorry` is replaced by that hypothesis applied to them. Probe 6 shows the pattern on
the primes example: the main proof with its two lemmas as hypotheses is accepted by pinned Lean with axioms
`propext` and `Quot.sound` only. The report: **PROVED (conditional): if G1 and G2 hold, then
infinitely_many_primes holds** — a theorem in its own right, under its own name, never counted as `T`.

**Person.** This is the owner's "force one subpart to be true to check the other", made exact: a team can publish
"the main argument is correct given these two lemmas" as a checked fact while the lemmas are still open.

**AI.** A partial result that is real: the conditional theorem can be stored, cited and reused, and when a later
agent proves `G1`, the kernel closes the chain by application (no re-check of the main argument).

**Kernel guarantee.** Full: the conditional theorem is an ordinary declaration checked by the kernel, axioms
reported. What is new is only the *statement*, which LeanForth generates — so the generated statement is shown in
three forms and its construction passes the [parser] gate.

**Lean or beyond.** Opt-in (Lean has no such command; the generated text is ordinary Lean that pinned Lean accepts).
**Size** M (generalising a goal over its local context with dependent hypotheses and `let` values is the work).

### Idea 3. What-if checking without editing the text

**What.** `leanforth check --assume NAME … FILE.lf` treats the named declarations as open parts (their proofs are not
checked; their statements are), so a person can check the main theorem while a lemma's proof is broken or being
written by someone else. `--only NAME` checks one declaration and the statements (not proofs) of what it uses. The
results carry the conditional report of Idea 1 with the assumed names listed as open parts.

**Person.** Works on part 2 while part 1 is still red, exactly the owner's example, without touching the file.
**AI.** Parallel agents each check their own part against the others' statements. **Kernel guarantee.** As Idea 1;
the assumed parts are reported as open, the run is labelled "with assumptions" in its first line and JSON.
**Lean or beyond.** Opt-in (in Lean the same effect needs `sorry` edited into the file). **Size** S–M.

### Idea 4. A blueprint whose statuses the kernel computes

**What.** `leanforth blueprint FILE.lf` prints the dependency graph of a development — nodes are declarations, edges
are uses read from the checked terms — with each node's status computed, never typed by hand: *proved* (no open part
below it), *proved if* (its own proof complete, open parts below), *open*, *refuted* (a checked counterexample, Idea
5), *stopped* (the text failed there). Output as text, JSON, and a graph file for a diagram tool; each node with its
statement in three forms and a link to its explained proof (Idea 14).

**Person.** A leanblueprint whose colours cannot be wrong. **AI.** The graph is the plan an agent works through
(as the FLT agents' graph of statements, §2.2). **Kernel guarantee.** Statuses come from kernel verdicts and the
ledger. **Lean or beyond.** Opt-in command. **Size** M.

### Idea 5. Counterexample search on small instances, with refutations the kernel checks

**What.** A command (`#test`, and a tactic word `by-test`; spellings illustrative) that tries the statement on small
instances — natural numbers up to a bound, `Bool`, `Fin n`, short lists, small finite structures as in the Equational
Theories Project — by the front end's evaluation (FE12), within a fuel budget. When it finds a counterexample, it
writes the refutation as a theorem (for example `¬ ∀ n, …` proved by instantiating at the counterexample and
`decide`) and has the kernel check it: the result is **REFUTED, checked**, not a test result. When it finds none, it
says "no counterexample for n ≤ 30 — testing, not proof". Probe 6 shows the pattern: the first, wrong statement of a
lemma in the primes example (without `2 ≤ n`) is refuted at `n = 1` by a theorem pinned Lean accepts.

**Person.** Pólya's and Lakatos's first move, automated: before spending a day on a proof, find out whether the
statement is false; the counterexample suggests the missing hypothesis. **AI.** Prunes false subgoals early — a
decomposition that produced a false open part is abandoned at once (provers otherwise spend their whole budget
there). **Kernel guarantee.** A refutation is a checked theorem; a failed search proves nothing and says so.
**Lean or beyond.** Opt-in command (Lean has `decide` and the Plausible package for random testing, but no
kernel-checked refutation step). **Size** M–L (needs FE12's evaluation and FE1i's `decide`).

### Idea 6. Statement sanity checks

**What.** Opt-in warnings about the statement, before and after a proof:

- **vacuous**: bounded automation (`by-omega`, `by-decide`, a short search) tries to derive `False` from the
  hypotheses; success means "the hypotheses contradict each other: the theorem says nothing" (probe 5's `n < 2` and
  `n > 5`);
- **unused hypotheses**: after acceptance, a hypothesis the proof term never uses is reported ("the proof never used
  `h2`: the statement may be weaker than intended, or the proof proves more");
- **trivially true**: the statement closes by `rfl` or `decide` at once;
- **type traps**: natural-number subtraction, division and `%`, coercions the elaborator inserted, default instances
  chosen for numerals (for example a numeral that became `Nat` where the author meant `Int`) — each listed with its
  position;
- **suspicious shape**: an implication whose conclusion does not mention a bound variable, a `∀` over an empty type.

**Person.** Catches misformalization before the proof effort. **AI.** Rejects its own vacuous or trivial
decompositions automatically; benchmark builders can screen statements (the audits of §2.9 found exactly these
defects). **Kernel guarantee.** Warnings never change a verdict; a vacuity finding is itself a checked proof of
`False` from the hypotheses. **Lean or beyond.** Opt-in (part of the development mode). **Size** M.

### Idea 7. Statement faithfulness: the three forms compared, equivalence proved

**What.** LeanForth already prints every checked statement in mathematical notation, LeanForth words and Lean (plan
8.6.2). In development mode the author, or an AI, also writes the intended statement separately — in mathematics
(LaTeX, through the untrusted translator of plan 8.6.7) or as a trusted reference statement (a challenge file, a
Mathlib statement). LeanForth elaborates both, shows the differences side by side, and when they differ in form it
tries to prove `reference ↔ proved` (or `proved → reference`) — a checked theorem that the proved statement implies
what was asked. This is comparator's guarantee (§2.2) relaxed from "identical" to "proved equivalent".

**Person.** Reads three short forms, not a page of elaborated Lean, and sees exactly where the formal statement
differs from the paper. **AI.** An autoformalizing agent must link each statement it invents to the reference by a
checked equivalence, which removes the commonest failure (§2.9, item 1). **Kernel guarantee.** The equivalence is a
checked theorem; the display is presentation. **Lean or beyond.** Opt-in. **Size** M–L.

### Idea 8. Proof sessions: saved states, branches and word-by-word stepping

**What.** At the LeanForth prompt (plan 8.2.1e), a proof is developed the Forth way: each tactic word runs as it is
typed and `.goals` shows the state, as `.s` shows the stack. New words (illustrative): `mark: NAME` saves the proof
state (the metavariable context and the stores, by their marks, which the stores already support); `back: NAME`
returns to it; `undo` steps back one tactic; `.tree` shows the branches tried; a session can be saved to a file and
resumed, and replays deterministically. Restoring a mark is a pointer reset, not a re-elaboration, so trying ten
alternatives from one state is cheap.

**Person.** Explores: "try induction here; no — back to before, try cases". **AI.** Tree search over proof states
(best-first, as GPT-f or HTPS, §2.9) with cheap backtracking, through the JSON protocol of Idea 9. **Kernel
guarantee.** A session's result reads "checked in this session" until the text is saved and re-checked in a fresh
process (the rule of plan 8.2.1). **Lean or beyond.** Opt-in interface (Lean's editor and Pantograph offer goal
states; marks and branches are LeanForth's). **Size** M.

### Idea 9. A JSON prover protocol with budgets for AI tools

**What.** A versioned, documented protocol (JSON Schema, stable error codes, AGENTS.md's rules for LLM-facing APIs)
for driving proof development from a program: open a text or a statement; list goals (in the three forms and as
terms); apply a tactic; mark and restore; test (Idea 5); sanity-check (Idea 6); read the ledger (Idea 1); and finally
check. Every request carries a budget — fuel, memory, wall time — and every answer uses the outcome vocabulary (ok,
invalid, unsupported, exhausted, full, unknown), so "ran out of budget" is never confused with "false". The same
request on the same input gives the same bytes. No chat, no network, no model inside: the AI is a client.

**Person.** Scripts and editor plugins use the same protocol. **AI.** Everything in §5.2 runs through it; a training
or evaluation harness gets deterministic, reproducible episodes (LeanDojo, Pantograph and Lean's REPL play this role
for Lean today). **Kernel guarantee.** The protocol's only "proved" is the kernel's fresh check of the whole text,
with its axiom report; intermediate answers are labelled as session results. **Lean or beyond.** Opt-in interface;
builds on the planned API (plan 3.5.3, [interface contracts](../programming/INTERFACE_CONTRACTS.md), 8.5.1).
**Size** M–L.

### Idea 10. Fuel profile and difficulty estimates

**What.** LeanForth meters its work in fuel, the same on every machine. The profile reports fuel per tactic step,
per goal and per open part, for the front end and for the kernel separately, and marks each failed automation call as
*exhausted* (gave up) or *refuted* (proved impossible). From the failed attempts on an open part it estimates
difficulty ("three portfolio runs exhausted at 10 million fuel").

**Person.** Sees where a slow proof spends its time, and which step to make cheaper. **AI.** Allocates budget
between open parts, stops sinking budget into hopeless ones, and gets a cost signal that does not depend on hardware.
**Kernel guarantee.** Measurement only; verdicts identical with the profile on or off (the rule of plan W3).
**Lean or beyond.** Opt-in report (Lean's `maxHeartbeats` limits a whole declaration; it does not attribute cost per
step). **Size** S–M.

### Idea 11. Incremental re-checking of only what changed

**What.** Each declaration gets a hash of its statement, its proof text and the hashes of the statements it uses.
After an edit, only declarations whose hash changed are elaborated and checked again; when an open part is closed,
only its dependents are re-checked (they now use a proof instead of `sorryAx`), on top of a snapshot (ADR 0020).
A periodic fresh run confirms that the incremental verdicts equal a full check.

**Person and AI.** Fast feedback while developing a large text; an agent's thousands of small submissions cost a
fraction each. **Kernel guarantee.** Same verdicts as a fresh check (tested as a property, as snapshot verdicts are).
**Lean or beyond.** Same verdicts as Lean; the mechanism is LeanForth's. **Size** M (needs 8.2.1g, one declaration at
a time).

### Idea 12. Library search and a parallel tactic portfolio

**What.** Port Lean's own `exact?`, `apply?`, `rw?`, `simp?` and `try?` (core Lean 4.35.0, §2.1) — that is Lean
behaviour and belongs to the compatibility work when started — and add an opt-in parallel portfolio: the job pool runs
`try?`'s candidates, library-search candidates and the decision procedures side by side, each with its own fuel
budget, and reports every success with its fuel, so the cheapest and most robust script can be chosen.

**Person.** "What closes this?" answered with a list, fastest first. **AI.** Cheap first attempt on every open part
before any model is asked. **Kernel guarantee.** Each suggestion is a script whose result the kernel checks; nothing
is accepted because a search said so. **Lean or beyond.** The ported tactics are Lean's; the parallel portfolio and
fuel ranking are opt-in. **Size** L (needs FE9, FE10, FE3).

### Idea 13. Proof minimisation and robustness checks

**What.** After a proof is accepted: remove each step or hypothesis in turn and re-check (keep the removals that still
check); replace `simp` by the `simp only [...]` that `simp?` reports; inline or drop unused `have`s; then re-check
the result under perturbations — a newer library snapshot, renamed hypotheses, a smaller fuel limit — and list the
steps that are fragile. Report the proof's dependency cone ("uses 14 library lemmas") and its axioms.

**Person.** Shorter, clearer proofs that survive library changes (the proof-engineering concern of §2.4 and §2.9).
**AI.** Machine-found proofs are often bloated (§2.2); minimisation makes them reviewable and teaches better scripts.
**Kernel guarantee.** Every candidate is re-checked; the original stays the reference until a smaller one is
accepted. **Lean or beyond.** Opt-in. **Size** M.

### Idea 14. Explained partial proofs and outline-first skeletons

**What.** The explained-proof printer (plan 8.6.12: each line in mathematics with an English reason) applied to a
proof with open parts: checked steps are explained as usual and each open part appears in its place as
"[G2, open] We still need: for every prime p ≤ n, p does not divide n! + 1." In the other direction, a person writes
a numbered outline in mathematics; LeanForth (with the translator of 8.6.7, untrusted) writes a skeleton with one
`have` per step, each closed by `sorry`, and checks that the steps elaborate and that the main proof follows from them
— draft, sketch, prove (§2.9) for people.

**Person.** A mathematician who does not read Lean can review the argument's structure and see exactly what is
missing. **AI.** The outline is the sketch; the open parts are the subgoals. **Kernel guarantee.** Every explained
line points to a checked step (8.6.12's rule); open parts are marked open. **Lean or beyond.** Opt-in printing.
**Size** M.

### Idea 15. `calc` chains and `suffices` skeletons with automatic step attempts

**What.** The person writes only the chain of intermediate expressions (`a = b = c ≤ d`) or the chain of "it
suffices to show" statements; LeanForth writes the `calc` or `suffices` skeleton, tries each step with the portfolio
of Idea 12 within a budget, and reports which steps closed (with the script found) and which remain open parts.

**Person.** The usual blackboard proof, with the routine steps filled in. **AI.** A structured decomposition whose
pieces are small enough for automation. **Kernel guarantee.** As for any script. **Lean or beyond.** Opt-in (the
result is ordinary Lean `calc` and `suffices`). **Size** M.

### Idea 16. Statement mutation testing

**What.** The project tests its own code by planting faults (`tests/mutants/faults.toml`); the same idea applies to
statements. LeanForth makes small changes to a statement — drop a hypothesis, `≤` to `<`, change a constant, swap
`∀` and `∃` — and runs the proof script and the counterexample search on each mutant. A mutant that should be false
but is still proved points to a vacuous hypothesis or a proof that proves something else; mutants refuted by checked
counterexamples are evidence that the statement is sharp.

**Person.** Confidence that the statement says what was meant. **AI.** A cheap automatic check against the
"proved the wrong statement" failure. **Kernel guarantee.** Each verdict about a mutant is a kernel verdict or a
labelled test result. **Lean or beyond.** Opt-in. **Size** M.

### Idea 17. A shared queue of open parts for people and agents, with an attempt journal

**What.** The ledger (Idea 1) as a work queue: each open part can be taken by a person or an agent, exported as a
stand-alone text (its goal, hypotheses and the library snapshot), proved in isolation under a budget, and submitted;
the submission is checked in the full context by the kernel, and the open part is closed only when the kernel accepts
it with axioms on the allowlist. The job pool checks submissions in parallel. Every attempt, failed or not, is kept in
a deterministic journal (the research-validation task R3 asks to preserve failed attempts) but never counted.

**Person and AI.** The organisation of PFR, the Equational Theories Project and the FLT agents (§2.2), with statuses
from the kernel instead of from people. **Kernel guarantee.** Nothing closes an open part but a kernel acceptance in
context. **Lean or beyond.** Opt-in. **Size** M–L.

**Pólya's moves as commands** run through several ideas: *specialise* (instantiate and test or prove the instance:
Idea 5), *generalise* (replace a constant by a variable and re-check whether the proof still works: Idea 13's
re-check), *auxiliary problem* (an open part exported as a stand-alone lemma: Ideas 1 and 17), *work backwards*
(`suffices` skeletons: Idea 15), *look back* (minimisation and the explained proof: Ideas 13 and 14).

## 5. Three imagined workflows, end to end

The running example is Euclid's theorem in core Lean only (no Mathlib), with `IsPrime` and `fact` defined in the
text. Lean code is from probe 6 (§9), run on pinned Lean 4.35.0; LeanForth spellings are illustrative and the
reports are sketches of Ideas 1–17, none of which exists.

- **Mathematics.** For every natural number $n$ there is a prime $p > n$.
- **LeanForth** (illustrative; natural LeanForth's spelling of `∃` is FE2's):

  ```text
  theorem infinitely_many_primes
    Nat explicit: n
    exists: p  n p <  p IsPrime  And
  := by …
  ```

- **Lean:** `theorem infinitely_many_primes (n : Nat) : ∃ p, n < p ∧ IsPrime p`, where
  `def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`.

### 5.1 A person

| Step | The person | LeanForth | Checked by the kernel | Reported |
| --- | --- | --- | --- | --- |
| 1 | Writes the statement | Sanity checks (Idea 6): hypotheses consistent (there are none), numerals are `Nat`; prints the three forms | the statement is well typed | warnings only |
| 2 | Asks for a test | `#test` with $n \le 30$ (Idea 5) finds a prime above each $n$ | nothing (testing) | "no counterexample for n ≤ 30 — testing, not proof" |
| 3 | Writes the plan: lemma L1 "every $m$ has a prime divisor", lemma L2 "no prime $p \le n$ divides $n! + 1$", and the main proof from them, the lemmas closed by `sorry` | checks the text | everything but the two `sorry`s | `infinitely_many_primes`: NOT PROVED; holds IF G1 (L1) and G2 (L2); the ledger (Idea 1) |
| 4 | Tests L1 as written | `#test` finds $m = 1$: no prime divides 1; writes and checks the refutation | the refutation theorem (probe 6: `lemma1_wrong_refuted`) | "L1 REFUTED at m = 1 (checked)"; ledger: G1 refuted |
| 5 | Adds the hypothesis $2 \le m$ (Lakatos's "lemma incorporation") and gives the main proof the new side fact $2 \le n! + 1$ (from `fact_pos`) | re-checks only L1 and its dependents (Idea 11) | as step 3 | G1 open again, with the new statement; the statement change is logged |
| 6 | Asks for the conditional theorem | `--open-parts-as-hypotheses` (Idea 2) | `infinitely_many_primes.given`, axioms `propext`, `Quot.sound` (probe 6) | PROVED (conditional): if G1 and G2, then the theorem |
| 7 | Proves L2 with a session (Idea 8), trying two approaches with `mark:` and `back:` | `.goals` at each step; fuel per step (Idea 10) | L2's proof | G2 closed; the main theorem now rests on G1 only |
| 8 | Proves L1 by strong induction; one `by-omega` step is *exhausted*; splits it with a `suffices` skeleton (Idea 15) | the portfolio closes the routine steps | L1's proof | G1 closed |
| 9 | Checks the whole text in a fresh process | `leanforth check primes.lf` | every declaration | `infinitely_many_primes`: accepted; axioms `propext`, `Quot.sound`; no open parts |
| 10 | Looks back | minimisation and robustness (Idea 13); the explained proof (Idea 14) | each shortened candidate | the final script and the proof line by line in English |

### 5.2 An AI agent

The agent is a program speaking the protocol of Idea 9; requests and answers below are abbreviated sketches.

1. **Pin the statement.** The task gives the statement as a reference file; the agent elaborates it and records its
   hash. Every later "proved" must name this hash (comparator's rule, §2.2); any statement the agent invents is
   linked to it by a checked equivalence (Idea 7).
2. **Screen.** `sanity` and `test` requests (Ideas 6, 5): not vacuous, no small counterexample.
3. **Try the cheap things.** `portfolio` with a budget of 10 million fuel (Idea 12): exhausted.
4. **Sketch.** The agent writes an outline with open parts (draft, sketch, prove; §2.9) and sends `check`; the answer
   is the ledger: `{"declaration": "infinitely_many_primes", "outcome": "accepted", "proved": false, "open":
   [{"id": "G1", …, "dependents": [...]}, {"id": "G2", …}]}`.
5. **Prune.** Each open part is tested (Idea 5) — G1 as first written is refuted with a checked counterexample, so the
   agent adds the missing hypothesis, or abandons the sketch, instead of spending its budget on a false goal.
6. **Work the queue.** For each open part: open a session on it (Idea 8), search with marks and restores, submit a
   proof; the kernel checks it in context (Idea 17); the ledger and the fuel profile (Idea 10) choose the next part.
   Failed attempts go to the journal.
7. **Stop honestly.** When the budget ends with open parts left, the agent's result is the ledger and, if asked, the
   conditional theorem (Idea 2) — "the main argument is proved given G1" — never "proved".
8. **Finish.** With no open parts, a fresh-process `check` of the whole text; only an acceptance whose statement hash
   is the pinned one and whose axioms are on the allowlist may be reported as proved, with the axioms listed. Then
   minimisation (Idea 13).

### 5.3 A person and agents together

The person writes the statement and a numbered outline in mathematics; an agent proposes LeanForth statements for
each step and links each to the outline by the three-form comparison (Idea 7); the person approves the statements
(their hashes are pinned). The skeleton is checked; the blueprint (Idea 4) shows the open parts; agents take the
routine ones from the queue (Idea 17) in parallel; the person takes the one the fuel profile marks hardest, using the
explained partial proof (Idea 14) to see the context in English. At every moment the blueprint's statuses are the
kernel's; at the end, one fresh check.

## 6. Trust and honesty rules for any development mode

1. **The kernel is the only judge.** Every development tool — tests, search, suggestions, translators, AI clients —
   is untrusted; nothing is accepted because a tool said so (AGENTS.md).
2. **Never "proved" with an open part.** A declaration with `sorry` is NOT PROVED with `sorryAx` named, and so is
   everything that uses it; counts of proved results never include it (ADR 0021 Amendment 1).
3. **Open parts are read from the checked terms**, not from the source text, so none can be missed.
4. **A conditional theorem is reported as what it is**: a different statement, "if G1 and G2 then T", under its own
   name, never as `T`.
5. **Axioms.** Every result lists its axioms; the allowlist is unchanged; development features add no axiom;
   `Lean.ofReduceBool` and anything like it stay unsupported.
6. **Testing is not proof.** A counterexample is reported as a refutation only when the kernel has checked it;
   "no counterexample found" always says "testing, not proof".
7. **Lean by default.** With no flags LeanForth behaves as Lean 4.35.0 (with the owner's NOT PROVED report);
   everything else in §4 is opt-in, never the default, recorded in [BEYOND_LEAN.md](../project/BEYOND_LEAN.md) when
   designed, and a run that uses it says so in its first line and in its JSON.
8. **The statement is pinned.** A final claim names the exact statement (three forms and a hash); a change of
   statement during development is recorded in the ledger, never silent.
9. **Fresh check for final claims.** Session and incremental results read "checked in this session" until a fresh
   process re-checks the saved text (plan 8.2.1's rule).
10. **No automatic error recovery.** A failure stops the text; LeanForth never fills a failure with `sorryAx`
    (Amendment 1).
11. **Determinism and budgets.** The same input and budget give the same output; running out of budget is
    *exhausted*, never *false* and never *proved*.
12. **Failed attempts are kept, never counted** (research task R3).

## 7. Plan rows

[PLAN_DRAFT.md](../project/PLAN_DRAFT.md), section "Phase 8, proof development: PD1–PD15", has one row per item, each
"not started", with acceptance criteria and dependencies on the front-end milestones. PD1 (Lean's `sorry` with the
decided report) is Lean behaviour and fits with FE1g and FE5; PD2–PD15 are long term, after strict Lean
compatibility (FE1–FE12), unless the owner brings one forward (question 3).

## 8. Questions for the owner

The `sorry` question is decided (§3). Three other choices:

1. **One development mode, or separate switches?** Everything in §4 except the decided NOT PROVED report goes beyond
   Lean. Options: (a) a single opt-in switch, `--develop`, that turns on the information-only features together (the
   ledger file, sanity warnings, fuel profile, explained partial proofs, tests), with separate explicit switches for
   anything that assumes or generates something (`--assume`, conditional theorems, minimisation rewrites);
   (b) every feature its own switch; (c) the information-only features on by default.
   **Recommendation: (a).** One switch is easy to remember and easy to see in a report; features that assume or
   create statements deserve their own explicit choice; (c) would break the rule that LeanForth with no flags
   behaves as Lean.
2. **Conditional theorems (Idea 2).** When asked, should LeanForth write and check "if the open parts hold, the
   theorem holds" as a real theorem with no `sorryAx`, reported as *PROVED (conditional)* under its own name?
   Options: (a) yes, opt-in; (b) only the report decided tonight, no new theorem; (c) yes, always.
   **Recommendation: (a).** It is the honest form of "the proof is valid if the `sorry` section is true": the kernel
   proves it outright, it can be stored and reused, and closing the open parts later completes the original theorem;
   but it adds a declaration Lean would not have, so it should be asked for.
3. **When to start.** Options: (a) everything after the front end is complete (FE1–FE12); (b) PD1 with the core
   tactics (FE1g/FE5, since it is Lean behaviour), the ledger (PD2) and the AI protocol (PD8) right after FE5 because
   agents writing LeanForth proofs need them, the rest after FE12; (c) start the ledger now.
   **Recommendation: (b).** `sorry` is part of matching Lean; the ledger is small and makes every later proof effort,
   human or AI, measurable; the rest is valuable but must not delay strict compatibility, as the owner asked.

## 9. Reproduction: the Lean probes

Pinned Lean 4.35.0 (`.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean FILE.lean`, never an elan proxy),
2026-11-12, run under `timeout -k 5 120 nice -n 15` on the development machine. Probe files were scratch files; their
essential lines and results are given here.

| Probe | What was run | Result |
| --- | --- | --- |
| 1 | `two_parts` (§2.1) with `#print axioms` and `set_option pp.explicit true in #print`; a theorem using it; `refine ⟨?_, ?_⟩`; `omega` on `n + 1 = n`; a later theorem; `admit`; `suffices`; `sorry` for `(0 : Nat) = 1`, then `False` from it | `two_parts`: warning, axioms `[sorryAx]`, term `sorryAx (∀ (tag : Lean.Name), …) false` with a label; the user depends on `sorryAx`; holes: no axioms; failed `omega`: error, the declaration still depends on `sorryAx`, the next theorem checked; `admit`: `sorryAx`; `False` from the false `sorry`: accepted with `sorryAx`; exit 1 (because of the error) |
| 2 | `exact?`, `apply?`, `rw?`, `simp?`, `try?`, `grind`, `show_term`, `decide`, `extract_goal`, `plausible`, `aesop`, `hint`, `polyrith`, `#check_failure`, `#guard`, `trace_state`, `stop` | core: all but `extract_goal`, `plausible`, `aesop`, `hint` and `polyrith` ("unknown tactic"); `exact?` printed `exact Nat.add_comm a b`; `try?` printed `assumption`, `grind`, `grind only`; `stop` leaves `sorryAx` |
| 3, 4 | a file whose only problem is `sorry`; `decide` on `2 + 2 = 5` | sorry only: warning, exit 0; with `-DwarningAsError=true`: error, exit 1; `decide`: "proved that the proposition … is false", exit 1 |
| 5 | `case left => rfl` / `case right => sorry`; `two_parts_given` (§3); `zero_add''` and `two_parts_full := two_parts_given zero_add'' n`; `(h1 : n < 2) (h2 : n > 5) : n * n = 7 := by omega`; `(2 : Nat) - 5 = 0 := by decide` | `sorryAx` for the first; **no axioms** for `two_parts_given` and `two_parts_full`; the vacuous theorem accepted (axioms `propext`, `Quot.sound`); the truncating subtraction accepted; exit 0 |
| 6 | §5's example: `IsPrime`, `fact`, `fact_pos`; `lemma1_wrong_refuted : ¬ ∀ n, ∃ p, IsPrime p ∧ p ∣ n` (via `h 1`, `Nat.le_of_dvd`, `omega`); `exists_prime_dvd` and `not_dvd_fact_succ` by `sorry`; `infinitely_many_primes` from them; `infinitely_many_primes_given` with the two lemmas as hypotheses | refutation accepted (`propext`, `Quot.sound`); the main theorem depends on `propext`, `sorryAx`, `Quot.sound`; the conditional theorem on `propext`, `Quot.sound` only; exit 0 |

The main proof of probe 6, for reference:

```lean
theorem infinitely_many_primes (n : Nat) : ∃ p, n < p ∧ IsPrime p := by
  obtain ⟨p, hp, hd⟩ := exists_prime_dvd (fact n + 1) (by have := fact_pos n; omega)
  cases Nat.lt_or_ge n p with
  | inl h => exact ⟨p, h, hp⟩
  | inr h => exact absurd hd (not_dvd_fact_succ n p hp h)
```

Literature: found with web searches on 2026-11-12; each claim above links its source. Where a primary source could
not be fetched (the Isar manual's `oops`, the F* wiki's sliding-admit page, LeanArchitect), the text says so.
Figures quoted from papers are the authors' own.
