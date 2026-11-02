# Decisions and proposed work

## Bootstrap boundary

The first Forth module is a host smoke test, not a proof kernel, a verified
program, or a specification of mathematical integers. Gforth cell arithmetic
and execution are host assumptions. The CI distribution Gforth is a separate
compatibility check; it does not establish Gforth 1.0 coverage.

## Kernel and execution design — proposed, human review required

Compare indexed expression DAGs with pointer-linked trees before choosing a
representation; indexed arenas support portable serialization but require
explicit bounds and lifetime management. Compare per-check arenas against
reference counting with respect to reclamation and auditability. FFI belongs
outside the kernel, behind a separate host adapter; no ABI or allocator choice
is approved by this note. Define typing rules, axioms, serialization, resource
limits and negative tests in an ADR before any kernel semantics are implemented.

## First meaningful examples — proposed

- Theorem track: construct a polymorphic composition proof, given `A → B` and
  `B → C` derive `A → C`; reject a composition with incompatible intermediate
  types. Compare both with pinned Lean when the supported fragment exists.
- Program track: specify and verify a bounded integer clamp, including its
  range and behavior inside the bounds; reject a faulty implementation or
  contract. See `docs/programming/PROGRAM_EXAMPLE.md` for the proposed contract and runtime
  assumptions to resolve before implementing.

Neither example is implemented or verified. A smaller identity proof may be
needed first to validate the core typing rules.

## Bootstrap backlog

1. Make installation repeatable on a clean Ubuntu/WSL machine; authenticate
   release hashes and eliminate unnecessary optional dependencies.
2. Establish CI on the pinned Gforth release; record actual remote CI status.
3. Review the first kernel ADR and Lean oracle cases, including invalid terms.
4. Specify the executable example and separate source proof from runtime trust.
5. Design versioned API schemas and explicit proof-step provenance.
6. Evaluate the bundled Forth tester with deliberate failures and establish the
   unit, interface, functional and regression layers in `docs/development/TESTING_STRATEGY.md`.

## Symbolic universes — proposed, not trusted

ADR 0004 proposes symbolic universe DAGs because Lean's polymorphic library
cannot be represented by concrete levels alone. Alternatives such as treating
parameters as arbitrary concrete numbers or adding them as axioms are rejected:
neither checks a polymorphic declaration. Name resolution, equality, immutable
storage and the typing interaction remain open and require human review.
ADR 0007 proposes distinct concrete/symbolic Sort representations, complete
consumer validation and generation-bound lifetimes; it is not approved.

## Owner policy decisions — 2026-11-02

The owner answered four plain-language questions; details, options and
reasons are in `docs/project/OWNER_DECISIONS.md`. Lean is the referee for checker
correctness: follow Lean's rules, require pinned-Lean differential evidence,
an independent AI review and owner approval of a plain-language summary,
and label results *not independently audited* until an outside expert
audit. The first checker accepts only simple definitions and theorems, with
three tested outcomes (accepted, rejected, unsupported/unknown). Conversion
is cautious first, with Lean-style unfolding next. There are no axioms at
first, later exactly `propext`, `Classical.choice` and `Quot.sound`, and
never the compiler-trust axioms. Rejected alternatives: blocking on an
outside expert before any checker work (stalls the project); treating AI
review as sufficient (shared blind spots); including data types in the first
checker (too large a first step); full Lean equality at once (too large and
risky); no axioms ever, or whatever Lean allows (respectively, Mathlib
unusable, or Lean's compiler silently trusted).

## Tooling, CI and agent handover — 2026-11-02

These are infrastructure decisions; none changes kernel semantics.

- **Agents.** Work after the `pre-claude` tag uses Claude Code alongside the
  Codex setup. `AGENTS.md` stays the single shared rule set; `.claude/CLAUDE.md`
  imports it rather than copying it, so the two cannot drift. The Forth
  reviewer exists in both `.codex/agents/` and `.claude/agents/`.
- **Lean invocation.** The Makefile calls the pinned toolchain binary under
  `.tools/elan/toolchains/` directly. Rejected: relying on the elan proxy,
  which silently downloads a 3 GB toolchain into `~/.elan` when `ELAN_HOME` is
  unset.
- **Installers.** `scripts/install-gforth.sh` and `scripts/install-lean.sh`
  verify SHA-256 hashes and are used by both CI and users. Rejected for CI:
  running the elan installer script, which adds an unpinned download step.
- **CI.** One workflow with two jobs: distribution Gforth 0.7.3 for
  portability, and pinned Gforth 1.0.0 plus Lean 4.35.0 running `make check`.
  Toolchains are cached and actions are pinned to commit SHAs. Rejected:
  running only Forth tests in CI, which left about 40 Lean comparisons
  unchecked on every push.
- **Aggregate targets.** `make test` (no Lean) and `make check` (everything
  except the unsafe symbolic-inference draft and profiling) replace long
  hand-written target lists in docs.
- **ADR numbering.** The two ADRs numbered 0005 were disambiguated by keeping
  the earlier one (structured names, 2026-10-31 08:45) as 0005 and renumbering
  the later one (Sort representation boundary) to 0007. ADR contents are
  unchanged apart from the title number.
- **Documentation layout.** Documents moved from a flat `docs/` into
  `user/`, `programming/`, `development/`, `project/` and `reviews/`, with
  `adr/` unchanged and an index in `docs/README.md`. Dated review records and
  `prompts/` keep their original text and paths, because they record what
  was reviewed or requested at the time; the index maps old paths to new.
  `scripts/check-doc-links.py` runs in `make test` so links cannot silently
  break again. Rejected: moving `adr/` under a design folder, which would
  have broken more historical references for no gain in findability.
