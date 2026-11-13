\ Nested inductive blocks (src/kernel/inductive-nested.fs; plan task
\ 5.2.5; ADR 0020): the translation into a mutual block with auxiliary
\ types, its check, and the restoration of the nested occurrences, on
\ cases of the inductive table (tests/core/check-block-cases/, each the
\ export pinned Lean printed; tests/core/check-block.fs checks their
\ verdicts, the auxiliary recursors and the tampered replays). This file
\ adds coverage class 5 of docs/development/TEST_COVERAGE_REVIEW.md inside
\ the translation and restoration passes: for nestings through List,
\ Option and Prod and in a mutual block, and rejected ones (a negative
\ occurrence inside the nesting, a local variable in the nested
\ argument), about n budgets spread from 0 to the
\ least that suffices give exhausted, that least and above the verdict
\ plenty gives; about n of the block check's allocations, each refused in
\ turn, give full; a crowded term store gives full.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

: block-swept ( c-addr u n -- fuel-ok? refusals-ok? crowded verdict )
  >r cs-load cs-block-target r> cs-sampled cs cs-normal @ cs-unload ;

T{ s" nested.tree" 23 block-swept -> true true outcome-full outcome-ok }T
T{ s" nested.option" 19 block-swept -> true true outcome-full outcome-ok }T
T{ s" nested.prod" 19 block-swept -> true true outcome-full outcome-ok }T
T{ s" nested.mutual" 11 block-swept -> true true outcome-full outcome-ok }T
T{ s" nested.non-positive" 19 block-swept -> true true outcome-full outcome-rejected }T
\ A local variable in the nested argument is rejected before the check
\ allocates anything (no refusal to sweep: false): crowded, it is still
\ rejected.
T{ s" nested.local-variable" 23 block-swept -> true false outcome-rejected outcome-rejected }T
bye
