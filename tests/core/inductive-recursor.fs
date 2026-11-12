\ The recursor a block check builds and compares with the file's
\ (src/kernel/inductive-recursor.fs; plan tasks 5.2.1a, 5.2.1b; ADR 0015
\ B3, G1), on cases of the inductive table (tests/core/check-block-cases/,
\ each the export pinned Lean printed; tests/core/check-block.fs checks
\ their verdicts and the B3 comparison field by field). This file adds
\ coverage class 5 of docs/development/TEST_COVERAGE_REVIEW.md inside the
\ recursor's construction: for recursors of every shape -- minor premises
\ with induction hypotheses (Nat), a reflexive field (W), an indexed
\ family (Vec, Acc), elimination into Prop only (Exists, And), an empty
\ type, a mutual block's two recursors -- about n budgets spread from 0
\ to the least that suffices give exhausted, that least and above the
\ verdict plenty gives; about n of the block check's allocations, each
\ refused in turn, give full; a crowded term store gives full. The
\ generated recursor rebuilt for a later use is tests/core/
\ generated-recursor.fs's.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

: block-swept ( c-addr u n -- fuel-ok? refusals-ok? crowded verdict )
  >r cs-load cs-block-target r> cs-sampled cs cs-normal @ cs-unload ;

T{ s" ind.nat" 41 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.w-type" 37 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.acc" 37 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.exists" 41 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.and" 41 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.empty-prop" 41 block-swept -> true true outcome-full outcome-ok }T
T{ s" ind.reflexive-indexed" 31 block-swept -> true true outcome-full outcome-ok }T
T{ s" mutual.even-odd-constructors" 31 block-swept -> true true outcome-full outcome-ok }T
bye
