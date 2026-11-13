\ The check of an inductive block (src/kernel/inductive-block.fs and the
\ passes it runs; plan tasks 5.2.1a, 5.2.1b; ADR 0015), on cases of the
\ inductive table (tests/core/check-block-cases/, each the export pinned
\ Lean printed; tests/core/check-block.fs checks their verdicts, rules,
\ diagnostics and steps). This file adds coverage class 5 of
\ docs/development/TEST_COVERAGE_REVIEW.md inside each pass of the block
\ check: for blocks of every shape (an enumeration, a recursive type with
\ a parameter, an indexed family, a mutual block, a reflexive type,
\ universe levels) and rejected ones (a negative occurrence, a parameter
\ mismatch, a universe too large), about n budgets spread from 0 to the
\ least that suffices give exhausted, that least and above the verdict
\ plenty gives (never ok earlier, never another failure); about n of the
\ block check's allocations, each refused in turn, give full; a crowded
\ term store gives full. The runs fail where fuel or room fails inside
\ the telescope walk, the constructor checks, positivity, the universe
\ checks and the recursor's construction.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

\ The case's block (its last declaration's), n runs of each sweep.
: block-swept ( c-addr u n -- fuel-ok? refusals-ok? crowded verdict )
  >r cs-load cs-block-target r> cs-sampled cs cs-normal @ cs-unload ;

T{ s" ind.bool" 61 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.list" 53 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.vec" 47 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.eq" 53 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.reflexive" 47 block-swept -> true true outcome-full outcome-ok }T
T{ s" mutual.tree-forest" 47 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.universe-max" 47 block-swept -> true true outcome-full outcome-ok }T
T{ s" pos.negative" 53 block-swept -> true true outcome-full outcome-rejected }T
T{ s" params.constructor-mismatch" 53 block-swept -> true true outcome-full outcome-rejected }T
T{ s" universe.field-too-big" 53 block-swept -> true true outcome-full outcome-rejected }T
\ A constructor's parameter that is another argument is rejected before
\ the check allocates anything (no refusal to sweep: false), so crowded
\ it is still rejected.
T{ s" uniform.other-argument" 53 block-swept -> true false outcome-rejected outcome-rejected }T
bye
