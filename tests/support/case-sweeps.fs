\ Test support: one case of tests/core/check-block-cases/ (an export that
\ pinned Lean printed) checked end to end, every declaration with plenty
\ of fuel except one, the target (by default the last), whose check runs
\ with a chosen budget, with its k-th allocation refused (alloc-fail.fs),
\ with its term store crowded, or with a probe run first inside its check
\ (the check's snapshot of the checked environment is then current, so a
\ probe may call the kernel's words as a check would). The sweeps then
\ check the resource classes of docs/development/TEST_COVERAGE_REVIEW.md
\ (class 5) on the passes the target's check runs:
\ - cs-fuel-sweep: every budget below the least that suffices gives
\   exhausted, that budget and the ones above it the outcome plenty gives;
\ - cs-refusal-sweep: each allocation of the target's check refused in
\   turn gives full, never another outcome (a check that goes on after a
\   refusal would end with a wrong verdict);
\ - cs-crowded: no free term record from the target's start gives full.
\ Include it first (alloc-fail.fs must come before src/lib/store.fs).
\ State: one test-only record, cs; single-threaded. Test-only: nothing
\ here accepts a theorem.
require ./alloc-fail.fs
require ./tester.fs
require ../../src/import/feed.fs
require ../../src/kernel/check-declaration.fs
decimal

1000000 constant cs-plenty
create cs-stage /stage allot
create cs-feed /feed allot
begin-structure /cs
  field: cs-env       \ the environment of the run
  field: cs-target    \ the declaration whose check is varied
  field: cs-budget    \ its fuel
  field: cs-refuse    \ the allocation of its check to refuse, 0 for none
  field: cs-crowd     \ true: its check starts with no free term record
  field: cs-probe     \ xt ( -- ) run first inside its check, or 0
  field: cs-seen      \ allocations its check made
  field: cs-hit       \ the store whose allocation was refused, or 0
  field: cs-normal    \ its outcome at plenty of fuel
  field: cs-low       \ the least budget that does not exhaust it
  field: cs-cap       \ the term store's capacity before its check
end-structure
create cs /cs allot  cs /cs erase

: cs-must ( flag -- ) 0= abort" case-sweeps: refused" ;
: cs+ ( c-addr u -- ) pad count + swap dup pad c@ + pad c! move ;
: cs-path ( c-addr u -- c-addr' u' )
  0 pad c! s" tests/core/check-block-cases/" cs+ cs+ s" .ndjson" cs+ pad count ;

\ Stage case name, its last declaration the target, at plenty of fuel.
: cs-defaults ( -- )
  cs /cs erase cs-plenty cs cs-budget ! lf-input-count 1- cs cs-target ! ;
: cs-load ( c-addr u -- )
  cs-path 16 cs-stage stage-init ok? cs-must cs-stage stage-load-unchecked ok? cs-must
  cs-stage cs-feed lf-feed ok? cs-must cs-defaults ;
: cs-unload ( -- ) lf-name-viewed? if lf-name-detach then cs-stage stage-free ;
: cs-target! ( d -- ) cs cs-target ! ;
\ A block is checked with its first member, whose check is the target's.
: cs-first-member ( d -- d' )
  dup lf-input-decl lf-idecl-header ?dup if nip lf-hdr-first lf-more-field then ;
: cs-block-target ( -- ) cs cs-target @ cs-first-member cs-target! ;
: cs-probe! ( xt -- ) cs cs-probe ! ;

\ A probe's assertions (tester.fs's T{ ... }T) run inside a check, whose
\ publisher would take a THROW for a failed check: there a failed
\ assertion, or a THROW out of the probe, is reported and counted in
\ cs-probe-errors, which the caller tests after the run.
variable cs-probe-errors  0 cs-probe-errors !
variable cs-probe-runs    0 cs-probe-runs !
: cs-probe-fail ( c-addr u -- ) type source type cr 1 cs-probe-errors +! ;
: cs-probing ( xt -- )
  1 cs-probe-runs +! error-xt @ >r ['] cs-probe-fail error-xt ! catch r> error-xt !
  if ." case-sweeps: the probe threw" cr 1 cs-probe-errors +! then ;

\ The check of each declaration; the target's as set above. A crowded
\ term store gets its capacity back after the check.
: cs-target? ( -- flag ) lf-env-limit cs cs-target @ = ;
: cs-crowding ( -- )
  lf-term-capacity cs cs-cap ! cs cs-crowd @ if lf-term-count @ lf-term-capacity! drop then ;
: cs-armed ( -- ) cs cs-refuse @ af-arm ;
: cs-counted ( -- )
  af-seen@ cs cs-seen ! af-hit cs cs-hit ! af-off cs cs-cap @ lf-term-capacity! drop ;
: cs-varied ( -- )
  cs cs-budget @ lf-check-budget cs cs-probe @ ?dup if cs-probing then
  cs-crowding cs-armed lf-check-declaration cs-counted ;
: cs-check ( -- )
  cs-target? if cs-varied exit then cs-plenty lf-check-budget lf-check-declaration ;

\ One run in a new environment: the target's outcome.
: cs-fresh ( -- )
  cs-plenty lf-check-budget 4096 lf-env-new ok? cs-must dup cs cs-env ! lf-env-use ok? cs-must ;
: cs-run ( -- outcome )
  cs-fresh ['] cs-check ['] lf-check-no-maker lf-env-run drop lf-env-view ok? cs-must
  cs cs-target @ lf-env-outcome cs cs-env @ lf-env-free ok? cs-must ;
: cs-at ( budget -- outcome ) cs cs-budget ! cs-run cs-plenty cs cs-budget ! ;
: cs-refused ( k -- outcome ) cs cs-refuse ! cs-run 0 cs cs-refuse ! ;
\ The target's outcome with no free term record from its start.
: cs-crowded ( -- outcome ) true cs cs-crowd ! cs-run false cs cs-crowd ! ;
\ The allocations the target's check makes with nothing refused.
: cs-window ( -- n ) 0 cs-refused drop cs cs-seen @ ;

\ The least budget that does not exhaust the target (bisection).
: cs-halfway ( lo hi -- lo hi mid ) 2dup + 2/ ;
: cs-least ( -- budget )
  -1 cs-plenty begin 2dup - -1 < while
    cs-halfway dup cs-at outcome-exhausted = if rot drop swap else nip then
  repeat nip ;

\ Every step-th budget from 0 to the least, and the least and one below
\ it: exhausted below the least, the plenty outcome from it on. True
\ when every run agrees.
: cs-measure ( -- ) cs-plenty cs-at cs cs-normal ! cs-least cs cs-low ! ;
: cs-expected ( budget -- outcome )
  cs cs-low @ < if outcome-exhausted else cs cs-normal @ then ;
: cs-agrees? ( budget -- flag ) dup cs-expected swap cs-at = ;
: cs-edge? ( -- flag ) cs cs-low @ dup cs-agrees? swap 1- 0 max cs-agrees? and ;
: cs-fuel-sweep ( step -- flag )
  cs-measure true cs cs-low @ 1+ 0 ?do i cs-agrees? and over +loop nip cs-edge? and ;

\ Each step-th allocation of the target's check refused: full, and the
\ refusal reached. True when every run agrees; false for a check that
\ allocates nothing.
: cs-full-at? ( k -- flag ) cs-refused outcome-full = cs cs-hit @ 0<> and ;
: cs-refusal-sweep ( step -- flag )
  cs-window dup 0= if 2drop false exit then
  true swap 1+ 1 ?do i cs-full-at? and over +loop nip ;

\ ---------------------------------------------------------------------------
\ Probes. A probe runs inside the target's check, before it, with the
\ check's snapshot current; it leaves its findings with cs-note, read
\ after the run with cs-noted (the first note is 0). cs-probed runs case
\ name with probe xt and gives the target's outcome and the number of the
\ probe's failed assertions.
64 constant cs-most-notes
create cs-notes cs-most-notes 1+ cells allot  0 cs-notes !
: cs-note ( x -- )
  cs-notes @ cs-most-notes < 0= abort" case-sweeps: notes"
  1 cs-notes +! cs-notes dup @ cells + ! ;
: cs-noted ( i -- x ) 1+ cells cs-notes + @ ;
: cs-probed ( c-addr u xt -- outcome errors )
  0 cs-notes ! 0 cs-probe-errors ! 0 cs-probe-runs ! >r cs-load r> cs-probe! cs-run cs-unload
  cs-probe-runs @ 1 <> abort" case-sweeps: the probe did not run once"
  cs-probe-errors @ ;
\ The same for a probe with assertions of its own (tester.fs keeps one
\ assertion's state, so T{ ... }T cannot hold another): stop the file
\ when one failed or the target's check did not end with outcome.
: cs-probe-gives ( c-addr u xt outcome -- )
  >r cs-probed abort" case-sweeps: a probe's assertion failed"
  r> <> abort" case-sweeps: the target's check ended otherwise" ;
\ Declaration d's type and value; the target's type.
: cs-type-of ( d -- node ) lf-input-decl lf-idecl-type @ ;
: cs-value-of ( d -- node ) lf-input-decl lf-idecl-value @ ;
: cs-type ( -- node ) cs cs-target @ cs-type-of ;

\ A pass of the checker, ( node fuel -- x outcome ), run on a node in an
\ inference job of its own (environment mode, with fuel), then the job's
\ scratch rolled back, so that the next run starts where this one did
\ and makes the same nodes. Lean's whnf (whnf.fs) is one.
: cs-whnf ( node fuel -- node' outcome ) lf-minfer-start-env lf-minfer-frames lf-whnf-on ;
begin-structure /cs-pass
  field: csp-node     \ the node the pass runs on
  field: csp-xt       \ the pass
  field: csp-x        \ its result with plenty of fuel
  field: csp-outcome  \ and that result's outcome
end-structure
create cs-the-pass /cs-pass allot
: cs-pass! ( node xt -- ) cs-the-pass csp-xt ! cs-the-pass csp-node ! ;
: cs-pass ( fuel -- x outcome )
  cs-the-pass csp-node @ swap cs-the-pass csp-xt @ execute
  outcome-ok lf-minfer-rollback drop ;
: cs-plenty-pass ( -- ) cs-plenty cs-pass cs-the-pass csp-outcome ! cs-the-pass csp-x ! ;
: cs-gives? ( fuel -- flag )
  cs-pass cs-the-pass csp-outcome @ = swap cs-the-pass csp-x @ = and ;
: cs-short? ( fuel -- flag ) cs-pass nip outcome-exhausted = ;
\ The least fuel with which the pass is not exhausted (from 0 up).
: cs-pass-least ( -- fuel ) 0 begin dup cs-short? over cs-plenty < and while 1+ repeat ;
\ Every fuel below the least is exhausted (by the search); the least and
\ the next two give what plenty gives. Notes: the pass's result and
\ outcome with plenty of fuel.
: cs-pass-sweep ( node pass -- flag )
  cs-pass! cs-plenty-pass cs-the-pass csp-x @ cs-note cs-the-pass csp-outcome @ cs-note
  cs-pass-least dup cs-gives? over 1+ cs-gives? and swap 2 + cs-gives? and ;
\ Each allocation of the pass refused in turn: full, and the refusal
\ reached; false for a pass that allocates nothing.
: cs-pass-window ( -- n ) 0 af-arm cs-plenty cs-pass 2drop af-seen@ af-off ;
: cs-pass-full? ( k -- flag )
  af-arm cs-plenty cs-pass nip outcome-full = af-hit 0<> and af-off ;
: cs-pass-refusals ( node pass -- flag )
  cs-pass! cs-pass-window dup 0= if drop false exit then
  true swap 1+ 1 ?do i cs-pass-full? and loop ;

