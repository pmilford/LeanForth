\ Definitional equality's later steps under fuel (src/kernel/defeq.fs,
\ with whnf.fs and iota.fs; Lean's is_def_eq_core, lazy_delta_reduction
\ and the eta and unit-like rules, type_checker.cpp 1100-1230), on cases
\ of the inductive table (tests/core/check-block-cases/, each the export
\ pinned Lean printed; tests/core/check-block.fs checks their verdicts
\ against Lean): structure eta (eta.structure, iota.structure-eta),
\ unit-like types (unit.pair-of-units, rejected), lazy delta through
\ projections (proj.lazy-fields, proj.unfold-proj-app) and the
\ comparison cache's projection index (cache.projection-index-differs,
\ rejected). Coverage classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 7. The target's outcome with plenty of fuel, as Lean's.
\ 5. Fuel: about 40 budgets from 0 to the least that suffices, spread
\    evenly, so that the fuel runs out inside each step of the comparison
\    (the step's failure is passed up, never taken as an answer): every
\    one below the least is exhausted, the least and the one below it as
\    they must be (cs-fuel-sampled).
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

: swept ( c-addr u -- fuel-ok? outcome )
  cs-load 40 cs-fuel-sampled cs cs-normal @ cs-unload ;
T{ s" eta.structure" swept -> true outcome-ok }T
T{ s" iota.structure-eta" swept -> true outcome-ok }T
T{ s" unit.pair-of-units" swept -> true outcome-rejected }T
T{ s" proj.lazy-fields" swept -> true outcome-ok }T
T{ s" proj.unfold-proj-app" swept -> true outcome-ok }T
T{ s" cache.projection-index-differs" swept -> true outcome-rejected }T
bye
