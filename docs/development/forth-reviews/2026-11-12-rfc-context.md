# Forth review of refactor-rfc item 1, context.fs (bfdfa7c..c201906), 2026-11-12 — not blocking

Range `bfdfa7c..c201906`, 2 commits: daa0486 (tests first), c201906 (refactor). Findings: 0 high, 0 medium, 2 low, 4
info. Every finding of 2026-11-12-context.md this item set out to fix is fixed (L1, L2, L3, I4). Behaviour is
unchanged, and no word now resolves to a different definition than before.

Reviewer: forth-reviewer (Opus), read-only; `git diff`/`git show`, runs in `git archive` copies of bfdfa7c, daa0486
and c201906. Scope: src/lib/context.fs; tests/lib/context.fs, tests/cli/leanforth.fs, tests/support/context-canon.fs,
tests/core/mixed-infer-coverage.fs, tests/mutants/faults.toml; tests/forth-quality-baseline.json,
docs/development/FORTH_LIBRARY.md. Basis: 2026-11-12-context.md, ADR 0010, module.fs, REFACTOR.md.

## The earlier review's findings
- L1 done: two teardowns throwing 91 and 93 → `context-free` gives 91 (the newest's); a setup word and a teardown both
  throwing → `context-new` gives the setup word's 56 and holds no block; a context walk grown to twice its room, then
  freed → 0 blocks. Faults context-ior-last, context-new-ior-order, context-walks-not-freed caught.
- L2 done: usage example, Interface list, `context-slab:` listed; lf-lib gained exactly the 32 listed words and
  lf-lib-private the other 74 names (traverse-wordlist, base vs head, nothing removed); the example runs as written on
  Gforth 1.0 and 0.7.3 with 0 heap blocks left.
- L3 done: `context-undo`; old and new failure paths give the same `( 0 ior )`, iors combined in the same order.
- I4 done: `member-listed` lays down the same two-cell node in the same order; no line over 90 characters.

## Does any word now resolve to a different definition? No.
1. Every name defined in context.fs has exactly one definition in the loaded system (lf-lib and lf-lib-private
   traversed after loading src/main.fs; none of the 106 names in forth-wordlist at head or in bare Gforth 1.0/0.7.3).
2. No other file defines one of these names (static scan of src, tests and scripts, all defining words); at base only
   mixed-infer-coverage.fs's `context-claim`, now `binder-claim`.
3. Users of the now-private words: three, each inside `lf-lib-private order+ … order-` (tests/cli/leanforth.fs:640,
   tests/lib/context.fs:151, tests/support/context-canon.fs:46); no src file or script uses a private name.
4. context.fs's references into lf-lib resolve as before (lf-lib was already searched first).
5. module.fs loads at the same dictionary point; after loading context.fs the order is lf-lib, forth, forth, root and
   the current wordlist forth, on both hosts.
6. "redefined" warnings identical at base and head except the removed `context-claim`; tests/lib/context.fs passes at
   daa0486 and c201906 with byte-identical output; contexts.fs and contexts-main.fs outputs identical.

## Findings
- **L1 (tests, library rule):** the library's own test does not cover freeing slab members: a fault making
  `slab-listed` a no-op survives tests/lib/context.fs (caught only by tests/front/elab-data.fs). Declare a
  `context-slab:` member in tests/lib/context.fs, reserve it past its first room, free the context, expect
  `blocks-held` 0; plant `context-slabs-not-freed`.
- **L2 (style):** the list node's fields are raw offsets and the three freeing loops repeat one shape (`cell+ @
  lf-context @ +` in slabs-free, walks-free, frames-free and tests/support/context-canon.fs:48). Name the fields
  (`/listed`: listed-next, listed-offset), `listed-member`, and `listed-each ( list xt -- )`.
- I1: c201906's message says 33 interface words; there are 32.
- I2: silent shadowing (ADR 0010 hazard): a later forth-wordlist definition named like an lf-lib word gets no
  "redefined" warning and the lf-lib word wins every later lookup. Suggest a make-test check that no name is defined
  both in lf-lib/lf-lib-private and anywhere else.
- I3: 14 `lf-lib set-current` and 13 `lf-lib-private set-current` switches; a one-line comment at `/context-header`
  saying which parts are public would help.
- I4: an equivalent fault (`context-undo` runs only with a nonzero ior).

## Style
context.fs, bfdfa7c → c201906: words 73 → 75; 1-2 lines 58 → 61; 3-5 lines 15 → 14; none longer; deep shuffles 8 → 7;
return-stack ops 21 → 21; globals 6 → 6; long lines 1 → 0. Baseline lowered for this file only.

## Tests and faults
`mutants --check` 1359 entries, 0 stale; all 17 faults on src/lib/context.fs caught; the reviewer's 6 faults: 3 caught,
1 survived (L1, caught by elab-data.fs), 1 equivalent (I4), 1 did not load.

## Runs
Gforth 1.0.0 at c201906 (all rc 0): tests/lib/context.fs (seed 2718, 6000 steps, 0 differences),
tests/core/contexts.fs, contexts-main.fs, mixed-infer-coverage.fs, tests/cli/leanforth.fs; the same at bfdfa7c and
daa0486 for comparison; Gforth 0.7.3: the same five files at c201906, rc 0. Probes of wordlists, search order and the
header example on both hosts. Not run: make test, make check, make coverage, 32-bit hosts.
