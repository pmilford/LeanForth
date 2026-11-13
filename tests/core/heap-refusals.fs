\ The heap refusing inside a check (tests/support/heap-watch.fs): each
\ ALLOCATE or RESIZE of the target's check of a case of
\ tests/core/check-block-cases/ refused in turn -- the caches' tables and
\ entries (kernel/caches.fs), the replace memo (kernel/replace-memo.fs),
\ the passes' frames and work arrays. Coverage class 5 of
\ docs/development/TEST_COVERAGE_REVIEW.md, with class 1: a refusal is
\ full, or, where the check does without the room (a memo or a cache that
\ cannot keep an entry only forgets it), the outcome with plenty of room;
\ never another outcome, so a refused allocation never becomes a verdict.
\ The first run counts the allocations; later runs make fewer, their
\ arrays already grown, so a refusal past them is not reached and the
\ outcome is the plain one. Test-only; nothing here accepts a theorem.
include ../support/heap-watch.fs
require ../support/case-sweeps.fs

variable heap-k
: arm ( -- ) heap-k @ heap-refusals ! ;
\ The target's outcome with its k-th allocation refused, and the
\ refusals left (0: the k-th was reached).
: heap-at ( k -- outcome left )
  heap-k ! ['] arm cs-probe! cs-run heap-refusals @ 0 heap-refusals ! 0 cs-probe! ;
\ The allocations of a first run; 0 when the target's check did not run
\ (a block's later member).
: window ( -- n )
  0 cs-probe-runs ! max-n heap-at nip max-n swap - cs-probe-runs @ 0<> and ;
\ Whether refusal k gives full or the plain outcome.
: kept? ( k -- flag )
  heap-at 0= if dup outcome-full = swap cs cs-normal @ = or exit then cs cs-normal @ = ;
: refusals-kept? ( -- n flag )
  cs-plenty cs-at cs cs-normal ! window dup true swap 1+ 1 ?do i kept? and loop ;
: case-kept ( c-addr u -- allocations? flag outcome )
  cs-load refusals-kept? swap 0> swap cs cs-normal @ cs-unload ;
T{ s" primitive.string-major-two-constructors" case-kept -> true true outcome-ok }T
T{ s" eta.structure" case-kept -> true true outcome-ok }T
T{ s" proj.lazy-fields" case-kept -> true true outcome-ok }T
T{ s" proj.lazy-fields-wrong" case-kept -> true true outcome-rejected }T
T{ s" quot.lift-on-mk" case-kept -> true true outcome-ok }T
T{ s" lit.pow-multi-limb-base" case-kept -> true true outcome-ok }T
T{ s" unit.pair-of-units" case-kept -> true true outcome-rejected }T
T{ s" iota.structure-eta" case-kept -> true true outcome-ok }T
T{ s" cache.projection-index-differs" case-kept -> true true outcome-rejected }T
bye
