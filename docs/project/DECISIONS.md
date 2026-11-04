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

## Source layout — 2026-11-02 (owner approved)

`src/` is organised by what the code does, not by a single "experimental"
label that applied to everything: `lib/` (general Forth tools, no Lean
knowledge), `core/` (Lean data and operations, current path), `kernel/`
(trusted checker; empty until code passes the review gate), `import/`,
`program/`, `legacy/` (superseded variants kept only for their tests), and
`main.fs`, one loader for all current code. `src/README.md` states the rules
and the old-to-new map. The split was computed, not guessed: the 22 modules
in `core/` beside `terms.fs` are exactly those the current `mixed-*` path
uses, found from which `lf-` words each file uses. That is why
`tagged-sort-boundary.fs`, `symbolic-session.fs` and `generation-handles.fs`
are in `core/` despite their names, while all `tagged-*` passes, the
`raw-*` signature index and the `constant-*`/`context-*` probes are
`legacy/`. This identifies the variant each later step builds on (the first
part of roadmap Q9). File names were kept, so history and the frozen review
records stay traceable; modules are renamed when they are refactored.
`make smoke` loads `main.fs` and fails if loading prints anything, which
catches two modules defining the same word.

Owner note, same day: the kernel is developed in `kernel/`; an in-progress
project is not expected to have verified code, and nothing counts as
verified until the owner says so after the review gate. The 13 checking
modules (universe substitution, value and comparison; signatures; the
`mixed-*` passes; the definition probe) therefore moved from `core/` to
`kernel/`, leaving the 10 data-model modules in `core/`. No `core/` module
uses a `kernel/` one. The owner also asked that user documentation show
each example concretely in mathematical notation, Forth syntax and Lean.

Rejected: keeping `core/` versus `experimental/` (the names said nothing
about content and `core/` was mistaken for the trusted kernel); an empty
`kernel/` reserved for reviewed code (superseded by the owner's note above); leaving
superseded copies in `core/` (mixes current and old code); deleting them now
(their 14 Lean comparisons must first move to the current path; owner chose
to keep them); one wordlist per folder in this step (needs an ADR; later).

## Forth library and the bottom-layer refactor — 2026-11-02

The term, level and name stores repeated the same array-plus-count code
with raw offsets. They now share `src/lib/store.fs`: a `store:` defining
word whose header is a `BEGIN-STRUCTURE` record (capacity, width, base,
count, generation, serial), with identities and records after it.
`src/lib/node.fs` names the three node fields. The refactor keeps every
public word and stack effect: words that were `VARIABLE`s (`lf-term-count`,
`lf-level-serial`, `lf-name-generation`, …) are now colon words returning
the same field addresses, because about 33 modules save and restore them
for rollback and tests corrupt them on purpose. `names.fs` no longer passes
its query through four `VARIABLE` registers; the prefix, number or length
travel on the stack and string bytes are read from the existing input copy.
The new tests also pass against the previous implementation, which is the
evidence that behavior did not change.

Modules load the library with `require ../lib/lib.fs`. The name `REQUIRE`
sees depends on the chain of includers (for example
`tests/core/../../src/legacy/../core/../lib/lib.fs`), so a Forth that does not
normalize paths could load it twice; Gforth 1.0 normalizes them. `lib.fs`
therefore also guards itself with a marker word, `lf-lib-loaded`, and
`make smoke` reports any second load as a "redefined" warning. Library
words carry no `lf-` prefix: they are generic, and collisions with Gforth
and project words were checked. The portability adapter defines Forth-2012
versions of the few Gforth extensions the code uses (`>=`, `<=`, `0<=`,
`-rot`) only where a host lacks them, rather than editing 85 call sites.

An independent Forth review of the change found no behavior difference
from the previous code on any API result: it ran a randomized differential
of old and new code, 8–16 seeds of 20,000 operations per module, with
corrupted counters and aliased inputs, plus `make check`. It found library
defects, now fixed, which are deliberate changes from the first version:
`cells-zero?` with a negative count read past its buffer; `lf-term-leaf`
accepted a binary tag and could create a dangling child; and the store's
shape (capacity, width, base) became writable header cells that every bound
trusted, where the old code used constants. The shape is now checked when
a store is defined and sealed with a check value, so corrupting any one
shape field makes every check fail closed. `upto?` and the new `between?`
use signed comparisons only, because `WITHIN` wraps around for negative
limits. Removed public words, none still referenced: `lf-term-storage`,
`lf-level-storage`, `lf-name-storage`, the four `lf-name-query-*`
variables, `lf-name-number-match?` and `lf-name-string-match?`. One order
changed: allocation now advances the count before the record is written;
nothing can fail in between today, but a future `CATCH`/`THROW` convention
must roll the count back (ADR needed, style guide section 6).

Rejected: renaming the store fields' public words now (would touch 100 test
files for no behavior gain; do it module by module); `require` of each
library file individually (more chances of a double load on a Forth that
does not normalize paths); trusting the shape fields as the old constants
were trusted (they are now writable memory); locals (factoring
kept every word to one to three lines without them).

## Walk records and the next refactor layer — 2026-11-02

The level-scope, Sort-representation, session and handle checks each had
their own work stack, fuel variable and `tag`/`first`/`second` variables
used as registers, with near-identical loops. `src/lib/walk.fs` now holds
that loop once: a `walk:` record keeps the fuel, the current node, one cell
for the visitor and the work stack, and every walk word takes the record's
address. The walk words keep no state, so a visitor may run a complete walk
on another record, as the session check does with level scope; but each
module owns a single walk record, so a module's own check is still not
re-entrant (ADR 0009 plans per-worker contexts). Visitors read
the node's fields onto the stack and dispatch with `CASE`. The
`src/lib/outcome.fs` vocabulary (ADR 0008) replaces the modules' own status
constants, which remain as aliases with the same values, and one
`outcome-sane` replaces a status-translation `CASE`. The fuel each walk
leaves is still read back by its callers, and the stacks that
`level-substitute.fs` and `mixed-level-substitute.fs` borrow keep their old
names and layout until those modules get records of their own.

At the owner's request, `make forth-metrics` now counts every table made by
a project defining word as a global, and the owner asked for re-entrant
code with parallel checking in mind: ADR 0009 proposes the direction, after
measuring Gforth 1.0's native pthread tasks (about 6× on 12 tasks).
The owner also suggested a "not yet implemented" outcome; ADR 0008 adds it
as *unsupported*, distinct from *unknown*.

An independent Forth review ran a randomized old/new differential (41
seeds, about 122,000 operations, every fuel cell compared) and found no
behavior difference. Its safety findings are fixed: `walk:` and
`walk-room?` no longer trust a negative capacity, `flag>outcome` accepts
only a true flag, and a visitor's result is passed through `outcome-sane`.
`lf-href-check` now refuses negative fuel (previously it never ran out);
callers always pass nonnegative fuel. Record fields are named
`record-field` with hyphens, never with `>` (style guide, section 5).
`tests/core/walker-interface.fs` pins the fuel each check leaves and the
layout of the borrowed stacks; it also passes against the previous code,
apart from the deliberate `lf-href-check` change.

Rejected: an execution-token dispatch table per walker (a five-arm `CASE`
is as clear for these tag sets); one generic visitor taking a table of
handlers (five stack items); keeping per-module status constants with
different names but equal values (invites mapping mistakes).

## Owner planning answers — 2026-11-02

The owner answered the draft plan's questions and approved ADRs 0008 and
0009 ([owner decisions](OWNER_DECISIONS.md#planning-answers-2026-11-02-later-the-same-day)).
Three answers change designs:

- **Parallelism uses Forth tasks.** The owner prefers Forth's own
  multitasking (tasks with `USER` variables) to operating-system processes.
  ADR 0009 now makes a task pool in one image the parallel method, with the
  task words in one adapter file per host; process sharding is dropped from
  phase 7. Rationale: one copy of the environment in memory, no
  serialization needed before any speed-up, and the cooperative tasker of
  Gforth 0.7.3 can still test interleaving in CI. Separately, the checker
  runs as its own program apart from user Forth code (OQ-1), for
  protection rather than speed.
- **Out of fuel and out of room are different outcomes.** *Exhausted* (2)
  keeps its number and now means the fuel budget ran out; *full* (6) means a
  store, stack or depth limit was reached. Rejected: renumbering (breaks
  tests and scripts); one combined code (hides which limit to raise).
- **Development runs may reuse saved results; final runs never do.**
  Results reused from a saved file are labelled as not re-checked in this
  run. Rejected: always re-checking in development (slow at Mathlib scale
  for no benefit to the owner's research use).

## Paired walks and the constant-term scope check — 2026-11-02

`src/lib/walk.fs` gains paired walks (`walk2:`): each work item is a node
plus one context cell, here the number of binders available at that node,
popped together into `walk-node` and `walk-context`. The constant-term scope
check is rebuilt on one, removing its seven register variables; a
randomized differential against the previous code (40 seeds, 28,160
comparisons of outcome and fuel) found no difference, and a planted fault
was caught in every seed. The kernel's shift and instantiate passes, which
also carry a binder depth, are expected to reuse it where they walk rather
than rebuild.

The independent review of the previous batch found no behavior change for
inputs within the module contract. Acted on: `lf-cref-new` no longer reads
the level array when the name or store is already invalid (an unreadable
address now fails instead of crashing), `lf-cref-store` uses the store's
allocation flag instead of dropping it, the reference record's fields are
renamed `lf-crec-*` so they are not confused with the public `lf-cref-*`
words, comments state which callers rely on the fuel left, and tests cover
corrupted counts, argument counts outside 0..8, serial exhaustion and
return-stack balance. `make forth-metrics` now finds defining words that
create through another defining word (`walk2:` through `walk-sized`).

Rejected: one walk record type with a width-two stack only (doubles the
memory of every one-cell walk); encoding node and depth in one cell (limits
both to half a cell and hides the layout).

## Kernel refactor in parallel groups — 2026-11-02

At the owner's request the remaining modules were refactored by five
agents working in parallel, each in its own git worktree from the same
commit with a shared brief (behaviour-preserving, state in named records,
shared outcomes, style guide), then merged one at a time with `make test`
on Gforth 1.0 and 0.7.3, `make check` and every group's randomized
differential rerun on the merged tree:

- **A, level passes:** level substitution and mixed level substitution got
  their own walk and job records instead of borrowing other modules' work
  stacks; each constant reference is validated once instead of once per
  position; level value and level comparison recurse through a deferred word
  with values on the data stack.
- **B, rebuild passes:** a new library defining word, `frames:`, gives shift,
  instantiate and beta one record each for fuel, depth limit and binder
  context. They use more return stack per level than before (about 1,200
  cells in the worst case at today's capacity, under Gforth 0.7.3's default
  of 1,920); the plan (task 6.2.0) moves recursive passes to explicit stacks
  before the capacity grows.
- **C, probes, loader and program examples:** state in records; the program
  examples keep the exact instruction sequences the Lean models assume.
- **D, compare, convert and infer:** compare and convert now run on paired
  walks instead of recursion; infer keeps bounded recursion with one job
  record. Deliberate change: convert no longer writes compare's fuel cell.
- **E, legacy tests:** moved to `tests/legacy/` beside the legacy code, with
  a coverage map for retiring both.

Evidence: about 17 million randomized operations against the previous code
across the groups, with differences only in the two documented fuel cells,
and planted faults caught. Fifteen status-translation words were deleted
after tracing that every code the wrapped helper can return maps to itself;
four narrowing words remain for review.

Open: three recursion patterns now coexist (frames, deferred recursion with
data-stack values, and explicit paired walks); one should be chosen after
the independent reviews. Several modules still write each other's record
fields; stack interfaces replace them next. Cost: about 2 million agent
tokens in total, including one group that started five helper agents
unasked; later briefs forbid that.

Rejected: converting module by module in one session (several times
slower); letting each group also change shared library files (conflicting
merges; only group B was allowed one new library file).

## Legacy retired — 2026-11-02

With the owner's approval (OQ-8 and the answers of the same evening in
[owner decisions](OWNER_DECISIONS.md#legacy-retirement-and-the-first-checkers-rules-2026-11-02-evening)),
the superseded code was deleted by exact path: `src/legacy/` (28 modules,
2,676 lines) and `tests/legacy/` (91 files), with the Make targets
`test-legacy`, `test-legacy-differential`, `test-symbolic-infer-draft` and
the 18 pinned-Lean comparisons in `LEGACY_DIFFERENTIAL_TARGETS`. Roadmap Q9
is done. Deletion came only after the coverage map of groups E and F had
closed every gap: tests that reached current modules through a legacy
helper were rebuilt on current code, each legacy-only case got a unit test
of current code, and all 18 comparisons were ported to the current passes
(`tests/core/lean-differential.py`, 11 tables, every Sort symbolic).

| Retired | Replaced by |
| --- | --- |
| plain and `tagged-` shift, instantiate, beta | `mixed-shift`, `mixed-instantiate`, `mixed-beta` |
| `compare`, `tagged-compare`, `tagged-convert` | `mixed-compare`, `mixed-convert` |
| `infer`, `tagged-infer`, the unsafe `symbolic-infer` draft | `mixed-infer` |
| `scope` | `core/constant-term-scope` |
| `declaration-probe`, `tagged-declaration-probe`, `candidate-definition-probe` | `mixed-definition-probe` (any Sort; see O1) |
| `raw-declaration-index`, `raw-signature-specialize` | `lf-msp-*` in `mixed-signature-probe` |
| `constant-signature-probe`, `constant-term-type-probe`, `constant-application-probe`, `constant-spine-probe` | `lf-mixed-infer` on constant roots and applications |
| `term-level-substitute` | `mixed-level-substitute` (see O4) |
| `arena.fs` | `lib/store.fs` and `lib/node.fs` |
| `tagged-context-infer`, `context-constant-spine`, `context-validation-probe`, `validated-context-spine` | none (see O3) |

The owner's answers on what only legacy code could do (all four were the
recommended options):

- **O1, theorem mode.** Only the legacy probes required a theorem's
  statement to be a proposition; the definition probe accepts a claim in
  any Sort. Not ported first: theorem mode is rebuilt in phase 2 (roadmap
  Q7, "check a real closed definition and a theorem").
- **O2, concrete Sorts.** No current checker pass accepts a concrete
  `lf-tag-sort`. The old loader, `src/import/load.fs`, which stages only
  concrete Sorts, stays with its round-trip tests until the Forth NDJSON
  reader replaces it; nothing checks what it stages. ADR 0007 item 5 is
  updated.
- **O3, open terms under a supplied context.** No current interface;
  closing a term with lambdas exercises the same rules. It waits for a
  Lean-style local context.
- **O4, universe parameters of a declaration.** Legacy substitution let a
  declaration's universe parameters lie outside the use-site context; the
  current substitution rejects that, and this stricter rule stays. The
  checked environment needs a per-declaration universe scope.
- **O5, profiling** (approved with the retirement): the profiling workload
  now times the current universe substitution and is renamed
  `mixed-level-substitution-48`, a new timing series not comparable with
  the old `term-level-substitution-48`.

Also removed: three words of the handle audit (`lf-href-pending`,
`lf-href-work`, `lf-href-push`) that only legacy code used to borrow its
work stack, and the legacy exemption in `scripts/check-portable-forth.py`.
Kept: `tests/support/term-cases.fs` and `composition.fs`, still used by
`tests/core/composition-table.fs`.

Accepted losses, with no current need: the pair arena, the two-tier raw
index and its lookup word, standalone constant probes with separate budgets,
the eight-argument spine and external context-array interfaces, and
concrete-universe overflow handling. Two semantic changes are intended:
syntactic comparison treats Sorts with equal level syntax as equal, and
conversion reduces binder domains instead of requiring them to match.

Rejected: porting the four legacy-only capabilities before deleting (they
would have been rebuilt on superseded designs; the owner chose to rebuild
them where the plan needs them); keeping legacy as a reference copy (two
versions of each operation, where AGENTS.md prefers retiring superseded
experiments).

## Each module requires its direct dependencies — 2026-11-02

At the owner's direction ("main should only require its direct
requirements, not the ones needed by the modules"), every source module
now `require`s the files whose words it uses, with paths relative to
itself, and `main.fs` requires only the five top modules (the definition
probe, the loader and the three program files). The dependency lists were
computed from the words each file actually defines and uses, not from the
old header prose, which was removed. Tests `require` the modules whose
words they use. `make smoke` now loads every module on its own and fails
on any output, and `make check-portable-forth` refuses `include` of a
source module.

Why `require` and not `include`: Gforth's `REQUIRE` loads a file once even
when two modules reach it by different relative paths (checked on Gforth
1.0 and 0.7.3), whereas `INCLUDE` reloads it, and a second load would
create a second term store with earlier words still bound to the first.
`REQUIRE` is in Forth-2012's optional File-Access extension; how a path is
resolved is host-defined, which `lib.fs`'s load marker guards against.

Rejected: modules requiring individual library files (`../lib/store.fs`)
rather than the library as one unit (more lines, and a host that treats
different relative paths as different files could load a library file
twice); keeping the dependency order in `main.fs` and every test (the
order lived in 80 places and the header comments drifted).

## Forth NDJSON reader, and no binary quick import yet — 2026-11-02

Following the owner's decision that a Forth reader replaces Python on the
user's path (OQ-4), `src/lib/bytes.fs`, `src/lib/json.fs` and
`src/import/ndjson.fs` read lean4export format 3.1.0
([NDJSON_READER.md](../development/NDJSON_READER.md)). Each record is
checked whole (exact fields, JSON types, dense in-order indices, earlier
references, pinned metadata) before a handler per kind receives it; an
inductive block is handed over only after the whole block passes; a kind
with no handler stops the read. On all of Mathlib the reader's counts and
field-by-field decoding equal Python's `json` module; it takes 1 min 43 s
with `gforth-fast` (3.3 times faster than `gforth`) and 17 MB.

The owner's proposed binary quick-import is not built: reading is under two
minutes against 6.5 minutes to export and hours to check, a second format
would need its own specification and tests, and a final run re-reads the
source anyway (owner answer to OQ-3). Open: the reader classifies nesting
deeper than 64 as a limit and unknown fields as malformed, where the Python
preview differs in places; plan item 3.2.1 settles one classification
through the import review gate. Staging decoded records into growable
stores is next (plan 3.2–3.3).

## Out of fuel and out of room are separate outcomes — 2026-11-02

ADR 0008's split, approved by the owner, is implemented: *exhausted* (2)
now means only that the fuel budget ran out, and *full* (6) that a store,
work stack, frame or depth limit, binder context, or a value at the cell
maximum left no room. When a visit is admitted against both fuel and room
(a frame, a depth limit or a context level) and has neither, fuel decides.
Limits checked inside a visit that has already been paid for (work-stack
pushes, a binder depth at `max-n` while rebuilding or scope-checking, and
mixed-infer's binder context) are checked independently of fuel and
report full even after the last unit was spent. The site-by-site
classification is in ADR 0008's "Implemented" section. Evidence: on 616 randomized seeds (2.2 million lines) every
difference from the previous code was exhausted becoming full, each traced
to a room site; 36 planted misclassifications were caught by unit tests;
no pinned-Lean table changed. The NDJSON reader, merged meanwhile, reports
its limits (line length, nesting, token and string limits, heap) as full.

Review follow-up, the same day. An independent review found no
correctness or trust problem and three low findings, now acted on.
`frame-under` checked its context before the fuel, so with no fuel left at
`max-n` it reported full; it now admits the visit first (fuel, then
frames) and only then examines the context. A frames record with a limit
below 1 and a walk whose root cannot be pushed (possible only with a
corrupted capacity) reported full; both are now invalid, before fuel or
room is considered. The test of `lf-cterm-check`'s outcome set now
includes full, which its contract allows but today's capacities never
reach. `visit-outcome` in `outcome.fs` states the fuel-first
rule once (`frame-room` replaces `frame-open?` and `frame-shut`, and the
level-value, level-compare and mixed-infer room words use it), and the 49
per-module status aliases were removed: tests use the `outcome-*` names.
Evidence: through the public entry points, 800 randomized seeds (2.80
million output lines) give exactly the output of the previous code; a
library-level differential (250 seeds, 450,156 operations, and 20 more
seeds on Gforth 0.7.3) differs only in the three intended
reclassifications; eight planted faults were each caught by unit or model
tests. Rejected: moving the work-stack and
binder-depth checks behind a fuel check (they occur inside a visit that
is already paid for, and a walk visitor has no fuel interface); keeping
exhausted for a corrupted limit when no fuel is left (a corrupted record
is invalid whatever its fuel).

## Program reader: names ignore ASCII case; receipt schema 0.1 tightened — 2026-11-02

The independent review of the program reader found that it compared names
exactly while Gforth finds them ignoring case: a file defining
`: True 0 ;` got the IR of the proven clamp although Gforth then runs the
file's own `True`. The reader now looks every token up with A–Z folded to
a–z, as Gforth 0.7.3 and 1.0 do and as Forth-2012 3.4.2 allows (a system
must find the standard words spelled in upper case), and writes names to
the IR in lower case, so `CLAMP`, `clamp` and `Clamp` give byte-identical
IR. A definition or constant whose folded name is already known is a
redefinition and refused. A line holding any byte other than printable
ASCII, space or tab is refused, comments included (both Gforths end a line
at a lone carriage return, which could hide code), because how a system
folds other characters is implementation-defined. The reader splits lines
into tokens itself and never hands source text to the host's interpreter
(a second review found that the file's lines were still split by the
host's `READ-LINE`; the reader now reads blocks with `READ-FILE` and
splits them at LF itself, dropping one CR just before an LF and refusing
any other CR); numbers are written in decimal whatever `BASE` is;
literals have at most 10 digits.
The owner prompted the choice ("Forth is case independent"). Rejected:
refusing upper-case names (the review's first suggestion), because that
refuses the standard spelling of the standard words; exact comparison,
because it is unsound against a case-insensitive host.

Receipt schema 0.1 was tightened in place rather than renumbered: no
receipt has been produced under it and it is an unapproved draft. Once
the owner approves it, every change gets a new version number. Rules the
schema cannot express (an empty axiom list, a theorem missing from the
check, duplicate assumption IDs, more failures than cases, the Lean
version, the receipt's generator) are left to the receipt generator and
replay.

## Program reader: no division before CONSTANT; the reader ends lines itself — 2026-11-02

The second independent review of the program reader found a file it
accepted that Gforth does not load: `1 0 / constant junk` throws while
Gforth loads the file (the Lean model evaluates a constant only when it
is used), so the words after it are never defined and an older word of
the same name may run instead. `/` and `MOD` are now refused before
`CONSTANT` (*unsupported*); they are the only IR 0.1 primitives that can
throw while a file loads (division by zero, the smallest cell divided by
−1); shifts, `*`, `NEGATE` and `ABS` were checked not to throw on either
host. The reader now reads files with `READ-FILE` and splits lines at LF
itself, dropping one CR before an LF and refusing any other CR, so its
idea of a line no longer depends on the host's `READ-LINE`. A test loads
every source the reader accepts into Gforth itself and checks it loads
without a throw and leaves the stack as it was. Rejected: refusing a
definition whose name the host already defines (`FORTH-WORDLIST
SEARCH-WORDLIST`), because acceptance would then depend on what the
reading session had loaded and differ between Gforth versions; instead
receipts assume that nothing compiled after the file uses a host word it
redefines.

## Tag `refactor-parallel` — 2026-11-02

The owner asked to tag the refactor and parallel version once it was
ready, before new features. The annotated tag `refactor-parallel` marks
`ada6dba`: the core and kernel rebuilt on `src/lib`, legacy retired,
every module requiring its own dependencies, all checker state in
per-task contexts with diagnostics, and the job pool; each change
independently reviewed with its findings fixed; CI run 41568918311
passed. It was placed after the review fixes of the context conversion
(agent Z) rather than at the conversion itself, so that the tagged
version has no known open finding in that work.

## LeanForth Forth syntax — proposed, 2026-11-02

[ADR 0017](../adr/0017-leanforth-syntax.md) proposes how theorems,
definitions and proofs are written in LeanForth itself (plan task 8.1.1;
gate [parser]; nothing implemented). Following the owner's requirement
that theorems and proofs be LeanForth words, not strings that are parsed,
every token is a Forth word run by Forth's own interpreter in the separate,
untrusted authoring program (OQ-1); no string carries mathematics. The
canonical *kernel form* maps one-to-one onto Lean's kernel terms: `$`
applies a function (`g f value $ $` is Lean's `g (f value)`), `^` gives a
constant a universe argument, `TYPE explicit: NAME … fun|forall` is a
binder whose word for the variable pushes the right de Bruijn index (also
`implicit:`, `strict-implicit:`, `instance:`), `A B ->` an arrow, and
`theorem NAME … := … end NAME` a declaration whose binders still open at
`:=` are its parameters and whose `end` defines its word. The search order
holds only LeanForth's wordlists (syntax, variables, namespaces, constants),
so Forth's own words are invisible in proof text. Rule R1: every syntax
word is a reserved Lean keyword or contains a character no Lean identifier
has. Names stay case-sensitive although Forth's lookup is not: one word per
spelling-up-to-case re-reads its invoking token from `SOURCE`/`>IN` and
acts on an exact match, else hands the token to the wordlists after its
own (537 groups of Mathlib names differ only in case; `x : X` is common). A
short name found through a namespace must not also exist elsewhere
(ambiguity is an error). Every node records a source position. Steps take
`label:`, `note"` (a person) and `ai-note"` (an AI), kept in the source,
printed and round-tripped, never checked (OQ-11). No Forth standard word
gets a mathematical meaning: `+` stays machine addition (the plan's "`+` in
a math wordlist" question, answered no). Literals, `let`/`have`,
projections, inductive types, structures (fields as constructor binders),
holes and `by-` tactic words are sketched.

Evidence: a throwaway prototype ran 18 example files as words through
Gforth's interpreter; 24 declarations printed as words ran again to
identical terms and text; output was byte-identical on Gforth 1.0, Gforth
0.7.3 and case-sensitive wordlists; 17 print exactly as Lean 4.35.0's
`#print` (the five fixtures as in `fixtures.golden`); five planted faults
were caught, one (the spelling check disabled) only by comparison with
Lean, so 8.1.2 keeps both tests; four mistakes stopped with line and
column. A word per constant costs about 119 bytes and 6 µs in Gforth 1.0.
The examples found a term-printer difference (Lean omits an instance
binder's name in `fun` when the printed body does not show it). Rejected: a
string-parsed surface syntax (owner's preference); this ADR's first draft, a
reader with its own lookup (a parser of its own); Gforth-only
case-sensitive wordlists or recognizers; forbidding case-only differences;
one wordlist per binder (search-order depth); plain-word connectives
(`app`, `proof`, `succ`, `max` are common Mathlib binder names); brackets
or S-expressions; unchecked first-match lookup; application with an
argument count; universe arguments popped by the constant itself; levels
inside tokens; two-cell tagged values; per-kind closing words; and notes
kept apart from the source. Open for the owner: the five decisions at the
end of the ADR.

## Exceptions: `THROW` only inside one operation — 2026-11-02 (proposed)

[ADR 0018](../adr/0018-exceptions.md), plan task 1.1.6, awaiting the
owner. Outcomes stay the interface of every word other modules and tests
call; *ok*, *rejected*, *unknown* and *unsupported* are never thrown.
Inside one operation a module may throw *invalid*, *exhausted* and *full*
with the project codes −4113, −4114 and −4118, in a range reserved for
LeanForth (−4096 to −4351, below every code Gforth 0.7.3 and 1.0
produce; the job pool's −4096 to −4101 keep their numbers). Only four
kinds of word may `CATCH`: a transaction boundary (marks its stores
before the `CATCH`, rolls back, maps the three codes to outcomes, throws
anything else on), the check boundary (any code: invalid, context spent,
as ADR 0012's G-P6), a resource owner (releases and re-throws) and a
tool's top level. No code maps to *ok*. All eleven current `CATCH` sites
fit. Pilot on `mixed-level-substitute.fs` in scratch: words giving an
outcome 33 → 10, plumbing tokens 45 → 6 (plus 18 exception words), code
lines 151 → 129, hand-written count saving replaced by store marks;
identical output on 400 random seeds (330,308 substitutions), a planted
missing rollback caught, failing calls about 6% slower. Found on the way:
Gforth 1.0 workers share the main task's exception-backtrace string, so a
`THROW` in the main task before the pool starts followed by throws in jobs
corrupts the heap (5 of 5 runs); a per-worker reset in `src/lib/task.fs`
fixes it and is recommended now, on its own. Rejected: outcomes only
(plumbing, hand-written rollback), throwing every non-ok outcome (hides
the owner's three outcomes), throwing outcome numbers, Gforth's
`exception` numbers, catching host errors in inner boundaries.

## Wordlists: a public and a private list per group — 2026-11-02 (proposed)

[ADR 0010](../adr/0010-wordlists.md), plan task 1.1.7, awaiting the
owner. `src/lib/module.fs` would make `lf-lib`, `lf-core`, `lf-kernel`,
`lf-import`, `lf-program`, `lf-present` and a private list for each, plus
`lf-env-private` for the checked environment's internals, with
`module-open`, `module-close`, `order+` and `order-` on Forth-2012
search-order words. A group's public list joins the search order when the
group loads, so public words stay visible as today; helpers are found only
inside their group and by tests that ask with one line. Measured: both
Gforths ignore case in wordlists, warn "redefined" only within the current
wordlist, and allow 1,024 (0.7.3) or unlimited (1.0) search-order
entries; so `make smoke` gains a duplicate-name check. Pilot on `src/lib`
in scratch: 432 of 638 names hidden, every test passing on both Gforths,
20 of 125 test files given one line, 182 visibility-switch lines, no
run-time cost, 2–5% more load time. Worked example: `lf-env-unpublish`
and `lf-env-guarded` would be hidden from everything outside the
environment. Wordlists hide names, not memory, so untrusted code still
runs in a separate program (OQ-1). Rejected: export lists through
`SYNONYM` (outside the chosen word set; 0.7.3 needs a non-standard
adapter), one wordlist per module, a single public list (kept as a
fallback for hosts with eight search-order entries), keeping everything in
FORTH-WORDLIST.

## Compact store for Mathlib-scale input — proposed, 2026-11-02

[ADR 0016](../adr/0016-compact-store.md) proposes the store that holds an
entire export: 16-byte nodes of four 32-bit fields (tag and payload, two
children, a data word with Lean's loose-bound-variable range, flags and
capped depth), no stored hash, a sealed read-only input tier shared by
every worker, a per-check scratch tier emptied by epoch with exact undo,
open-addressing hash tables (one probe per new node), names resolved to
declarations at sealing, and per-context substitution memos, following
the measured profile of Lean's kernel. A prototype loaded all of Mathlib
into a 2.94 GB input tier (4.16 GB peak) and re-emitted every record
identically. Rejected: B-trees and balanced trees (no ordered search is
needed; access is by index and by hash), unshared trees (10^14 nodes),
64-bit fields everywhere (about twice the memory), a stored hash,
chaining, file-backed storage (not needed below about 20 GB), and one
copy of the input per worker. Open for the owner: the three decisions at
the end of the ADR.

## 2026-11-03: rejection rules approved; behave identically to Lean; compact store accepted

The owner approved the rejection rules' [kernel] gate (plan 2.2.1) and ADR
0016 (the compact store) as recommended, and set the principle that
LeanForth must give Lean 4.35.0's exact verdicts: "Working worse than Lean
is of no use." Consequence: Lean's rejection of a "for all" whose body is
not a type, which the first rule set left as *unknown*, is scheduled as an
ADR 0011 amendment rather than deferred. Also recorded: the one-thread
speed goal (match or beat Lean's kernel), a cap of about 10 busy processes
on the owner's machine, a later GPU investigation (outside the trusted
kernel, with a CPU path kept), and durable agent notes after a restart
wiped `/tmp`. Rejected alternative: keeping LeanForth deliberately more
cautious than Lean where Lean decides; the owner wants identical behaviour
first, improvements later. See
[OWNER_DECISIONS.md](OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03).

## 2026-11-03: MiniForth reviewed as related work

The owner asked to review MiniForth (<https://github.com/leodemoura/MiniForth>,
commit `e8756e2`), a Forth written in Lean by Leonardo de Moura. Its ideas
are adopted as proposals (see [the review](../development/MINIFORTH_REVIEW.md)):
early binding of calls and a Lean well-formedness check for ADR 0019, a
fuel-free semantics proved equivalent to the fuelled one for IR v1, and
verification conditions as proved Lean rules plus a tactic. Rejected:
unbounded integers, a late-bound global dictionary, Lean quotation syntax as
the canonical form, a mandatory ELSE, and using it as a test oracle. It has
no licence, so no code is copied. The review found that plan task 5.5.1
depends on nested inductive types (5.2.5); recorded in the plan.
## Program words in two modes — proposed, 2026-11-03

[ADR 0019](../adr/0019-program-words-two-modes.md) answers the owner's
preference for option 2 (the program reader's [parser] gate is paused):
the same source file is loaded either with a LeanForth correctness
vocabulary, whose words have the names of Forth's words and write IR 0.1
when Forth's own interpreter runs them, or with ordinary Forth to run it.
Decided in the proposal: `:` leaves Forth interpreting, so each body word
runs once and writes its instruction, and the structure words write nested
blocks from a frame stack of their own, never evaluating a condition;
calls are bound when Forth finds the word, and redefinition stays refused
so a name is one definition; numbers are read by Forth and checked by every
word against the text before it (plain decimals only, as many as the stack
grew, with the written values), which is portable without recognizers and
leaves nothing a number could forge; only the vocabulary and the file's
own word list are in the search order, `BASE` is ten, `STATE` never
changes, and the caller's settings are restored; it runs in the authoring
program (8.2.1). IR stays the single proved meaning: symbolic execution
comes later as an untrusted producer checked against it, growing into the
proof producer for LeanForth's checker. Today's reader becomes a test
oracle until the switch, then retires. A throwaway prototype loaded the
real example files unchanged and wrote byte-identical IR on Gforth 1.0.0
and 0.7.3, ran them in plain Forth, replayed the reader's 106 verdict
tests with no difference, refused 81 of 86 hostile inputs (the other five
are meant to pass), round-tripped IR with awkward names and caught four
planted faults. Rejected: compiling and then running in an emit mode, our
own token loop (option 1 again), Gforth recognizers, signed or tagged
stack values, symbolic results as the obligations themselves, a late-bound
dictionary, and running in the checker's process. Prior art cited:
MiniForth (<https://github.com/leodemoura/MiniForth>, commit `e8756e2`,
no licence, ideas only). Open for the owner: the four questions at the end
of the ADR.

## Program words in two modes: answers, mode shift, loops — 2026-11-03

The owner answered ADR 0019's four questions: option 2, "but also consider
if there is a way to do it with a mode shift rather than an alias. Either
case probably needs special handling of defining words and looping"; IR
first and symbolic execution later; today's reader kept as a cross-check,
then retired; names that read as numbers refused (any name Forth-2012 or
Gforth could read as a number). The ADR is accepted in direction; whether
the second meaning comes from a separate vocabulary (the alias) or from a
mode shift stays open. ADR 0019 §9 weighs dual-mode words that test a flag
(rejected: run mode would no longer be plain Gforth, would be slower, and
would run trusted wrappers), a third state of Gforth 1.0's own interpreter
through `translate-method:` (works, 1.0 only, experimental words), a
portable third state — Forth's own words found with `SEARCH-WORDLIST`,
each with *verification semantics* kept in a table keyed by its identity,
performed by a short loop inside the line as Forth's input source — and
"verify while loading" (rejected: the file's code would run inside the
verifier). Prototypes of both mode shifts gave byte-identical golden IR,
no difference on the reader's 108 replayed tests and identical
diagnostics on 86 hostile inputs; the mode shift also refused a Forth with
`MAX` redefined, which the alias accepts. Host quirks found: Gforth 0.7.3
gives all compile-only words one execution token and Gforth 1.0 moves
`RECURSE`'s token, so a word is known by token and name. Recommendation
to the owner: the portable mode shift. §10 designs defining words
(`CONSTANT`, `VARIABLE`, top-level `CREATE` tables, `VALUE`/`TO`,
`CREATE … DOES>` and user-written defining words, run at the top level on
LeanForth's model, never on the host, and refused inside definitions) and
loops (`DO`/`?DO`/`LOOP`/`+LOOP`/`LEAVE`/`I`/`J`/`UNLOOP`,
`BEGIN`/`UNTIL`/`AGAIN`, several `WHILE`s, `RECURSE` bound to the current
definition) with what IR v1 must gain, including MiniForth's semantics
without fuel and loop rules with invariants. Prototyped once and given to
both designs, they wrote the same 95-line draft IR v1 on both Gforths.

## Test speed: parallel make and the pinned-Lean cache — 2026-11-03

Agent TT, test tooling, no owner gate. `make test` had grown to 36 s and
`make check` to 345 s run one target at a time, and agents ran them several
times per task.

- **Parallel make is the default** (8 jobs unless `-j` is given; `JOBS=1`
  runs one at a time). Every target writes only into temporary folders of
  its own, so targets cannot disturb each other, and each target's output is
  printed in one piece. The slowest targets start first. A failing target
  stops make from starting others. Rejected: parallelism only in CI (agents
  and the owner wait locally too) and making the user ask for `-j`
  (forgotten, and an agent would then run the slow way).
- **The Lean cache replays Lean's own run, keyed on everything that run
  reads.** Pinned Lean's verdicts are deterministic and most of `make
  check` was Lean re-checking unchanged files. A stored result is replayed
  only when the SHA-256 of the toolchain (the `lean` binary, its shared
  libraries and its library folder), the options, the source text, the main
  module's name and every file of each `LEAN_PATH` folder are all the
  same; any other input runs the real Lean. Keying on the whole input
  including the toolchain means an upgraded Lean can never replay an older
  Lean's verdict, which matters because the project's rule is Lean 4.35.0's
  exact answers. Calls that read the clock, files, stdin or other IO, and
  calls that import an `.olean` the cache did not see compiled, are never
  cached. Only Lean's run is skipped: the Forth side of each comparison
  always runs.
- **CI runs without the cache** (`LEAN_CACHE=0`, set explicitly in the
  workflow), so a green CI run is a real Lean run and the record; a local
  pass with the cache is trusted like the working tree. `LEAN_CACHE=verify`
  re-runs every call and flags a differing stored result.
- **Rejected: caching whole make targets** (keyed on the files a target
  reads). A target's inputs include the Forth code under test, so the key
  would be easy to get wrong and a stale pass would hide a real failure in
  our own code, the thing the tests exist to catch. The cache skips only
  the one deterministic external tool. **Rejected: no cache**, at 345 s
  (now 43 s with a filled cache, 69 s with an empty one, 75 s without it;
  [timings](../development/TESTING_STRATEGY.md)) the suite was run less
  often. A related tool, `make test-changed` and `make check-changed`,
  runs only the targets that use changed files, for working, not for the
  record.

## Stores that grow on the heap, not fixed capacities — 2026-11-03

Agent KC, ADR 0016 C9 step 3 in part, plan 1.1.5 and 3.2.2; merged, the
[kernel] gate is pending.

- **Decision.** The term, level, name, reference and declaration stores are
  heap stores: a block that doubles up to a limit and is freed when the
  context is released. Each context sets its capacities
  (`lf-term-capacity!` and the others), with the old values (64, 64, 64, 32
  and 32) as defaults, so every existing verdict, fuel count and diagnostic
  stays the same: 2,000 random checker trials give identical digests to the
  code before the change. Per-index side data moved into columns that grow
  with their store. Universe arguments are variable-length, at most 64 per
  reference (was 8). Growth that the limit, the heap or a test hook refuses
  gives *full* and changes nothing.
- **Why.** `Init` has 59,349 declarations and 6.1 million term nodes, and
  Mathlib needs millions of entries; a build-time or fixed capacity cannot
  serve both a 64-entry test and a library. Capacities per context keep
  the small tests small and let one check run many declarations, and the
  growth refusal is a normal outcome (*full*) rather than a crash, which the
  failure-path suite exercises.
- **Rejected: bigger fixed capacities.** They cost memory for every check
  and every test, still have a ceiling, and would change where tests reach
  *full*, moving the points that the failure-path tables rely on.
  **Rejected for now: reading the compact store's terms in place.** The
  kernel reads terms through slot addresses and identities, and
  hash-consing the context's own terms would move the points where a store
  fills; the input's terms are copied (about 80 bytes per node) and
  reading in place stays for steps 3 to 6 of ADR 0016.
- **Cost.** `Init` end to end uses up to 1.27 GB. Agent KC reports a
  slowdown of about 2.2 times on the random trials (65 s against 30 s),
  under investigation; the verdicts are identical. `bin/leanforth check`
  still uses the default small capacities.

## Axioms and the default are Lean — cross-reference, 2026-11-03

The owner's answers of 2026-11-03 (late night) are recorded in
[OWNER_DECISIONS.md](OWNER_DECISIONS.md#data-types-axioms-and-imports-2026-11-03-late-night)
and amend earlier entries here: by default LeanForth gives Lean's kernel
verdict, so a declaration that uses `sorryAx` or another axiom outside
`propext`, `Classical.choice` and `Quot.sound` is accepted as Lean accepts
it but labelled NOT PROVED, never counted as proved in receipts or reports;
`--standard-axioms-only` answers *unsupported* instead. With no flags,
LeanForth is always 100% Lean compatible; every option that differs
(`--strict-builtins`, `--standard-axioms-only`, a strict import) is opt-in.
Only the three standard axioms count as proved, and `Lean.ofReduceBool` and
`Lean.trustCompiler` are never allowed. The importer stage was approved
([import]) and ADR 0015 accepted as a design in the same answers. These
rules are decided, not yet implemented.

## The importer's two passes must read the same bytes — 2026-11-03

The third review of the run records (rvRP3, round 2, R2-1) showed that
`cin-read-checked` (`src/import/checker-input.fs`), which reads an export
twice (names first, then terms and declarations), checked each pass against
the manifest as it stood for that pass. An export swapped, with its
manifest, during the first pass only gave a check that paired one file's
names with another file's terms: an enforced run record, and a plain
`bin/leanforth check`, then reported verdicts that the hashed file's check
does not give (a test reproduces it through a FIFO).

- **Decision.** A checked read keeps the first pass's SHA-256 and requires
  the second pass's to equal it, else the read is invalid ("the export
  changed between the two passes"). The run records then compare that
  SHA-256 with the one `rr-start` recorded, so an enforced record's
  verdicts are those of bytes with the recorded SHA-256. This is [import]
  code and needs human review.
- **Rejected: narrowing the documented claim** to exclude a change during
  the first pass. It would leave plain checks exposed and make the run
  record's `enforced` weaker than it reads.
- **Not affected:** the importer stage (`src/import/stage.fs`) reads the
  export once, hashing the very lines it stages, and `src/import/feed.fs`
  reads no file.
