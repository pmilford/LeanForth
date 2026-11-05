\ Untrusted mixed-term shift: add an amount to every bound variable at or
\ above a cutoff, rebuilding the term. Structural transformation only; no
\ proof judgment.
\ State: one job record, lf-mshift-job (fields lf-shiftjob-*): the pass's
\ frames (fuel, nesting, and the cutoff as context) and the amount; a
\ member of the checker context (lib/context.fs), whose frames a set-up
\ word prepares in every context. Single-threaded within one context: the
\ instantiate pass shifts its replacement on this record, which a shift in
\ progress refuses. Exclude raw mutation, resets and concurrent access
\ during a call.

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/local-context.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./mixed-rebuild.fs

max-n constant lf-mshift-max

\ The frames come first, so the visitor finds the job record at the
\ address of the frames it is given (checked here) and needs no pointer
\ to it, which would go stale when a context moves.
begin-structure /lf-shiftjob
  /frames +field lf-shiftjob-frames   \ fuel, nesting, the cutoff as context
  field: lf-shiftjob-amount           \ added to each variable at or above the cutoff
end-structure
0 lf-shiftjob-frames 0<> [if] .( mixed-shift.fs: frames must come first) cr abort [then]
/lf-shiftjob context-record: lf-mshift-job

: lf-mshift-frames ( -- frames ) lf-mshift-job lf-shiftjob-frames ;
\ Fuel left after a shift; mixed-infer continues with it.
: lf-mshift-fuel ( -- addr ) lf-mshift-frames frame-fuel ;
: lf-mshift-amount ( -- addr ) lf-mshift-job lf-shiftjob-amount ;

\ Visiting one node of the shift. The preaudit establishes tags, payloads
\ and backward edges. A variable below the cutoff is kept; the others move
\ up by the amount, which is full past lf-mshift-max (no room in a cell).
\ Leaves are kept (a free variable too: it binds nothing and is bound by
\ nothing, core/local-context.fs) and binary nodes rebuilt; any other tag
\ is invalid.
: lf-mshift-amount@ ( frames -- amount ) lf-shiftjob-amount @ ;
: lf-mshift-site ( -- site ) c" mixed-shift lf-mixed-shift" ;
\ No room in a cell: recorded with the index and the amount.
: lf-mshift-past ( index amount -- -1 outcome )
  lf-mshift-site lf-diag-cell-maximum lf-diag-note lf-rebuild-full ;
: lf-mshift-up ( index amount -- result outcome )
  2dup lf-mshift-max swap - > if lf-mshift-past
  else + lf-term-bvar lf-rebuild-allocated then ;
: lf-mshift-bvar ( node frames -- result outcome )
  over lf-term-first@ over frame-context @ < if lf-rebuild-keep exit then
  lf-mshift-amount@ swap lf-term-first@ swap lf-mshift-up ;
: lf-mshift-leaf ( node frames tag -- result outcome )
  case lf-tag-bvar of lf-mshift-bvar endof  lf-tag-fvar of lf-rebuild-keep endof
    lf-tag-constant of lf-rebuild-keep endof  lf-tag-proj of lf-rebuild-keep endof
    lf-tag-symbolic-sort of lf-rebuild-keep endof
    >r lf-rebuild-bad r> endcase ;
\ The visit's first step (lib/frame.fs).
: lf-mshift-visit ( node frames -- ... frames next )
  over lf-term-valid? lf-rebuild-tag
  dup lf-term-binary-tag? if drop lf-rebuild-binary else over >r lf-mshift-leaf r> 0 then ;
\ The frames and their visitor, set up once in every context; their stack
\ is freed with the context.
: lf-mshift-setup ( -- ) ['] lf-mshift-visit lf-mshift-frames frame-init ;
' lf-mshift-setup context-setup
: lf-mshift-free ( -- ) lf-mshift-frames frame-free ;
' lf-mshift-free context-teardown

\ Shift a node by amount from cutoff zero, from inside another pass whose
\ frames record lends its fuel and gets back what is left. A shift in
\ progress refuses, changing nothing: no result, invalid. Nothing is rolled
\ back here; the caller's pass does that. Running out of fuel or frames is
\ recorded as a diagnostic.
: lf-mshift-explain ( outcome -- outcome )
  lf-mshift-frames lf-mshift-site lf-diag-frames ;
: lf-mshift-borrow ( frames -- flag ) frame-fuel @ lf-mshift-frames frame-budget ;
: lf-mshift-inside ( node amount frames -- result outcome )
  dup lf-mshift-borrow 0= if drop 2drop lf-rebuild-invalid exit then
  >r lf-mshift-amount ! 0 lf-mshift-frames frame-run lf-mshift-explain
  lf-mshift-fuel @ r> frame-fuel ! ;

\ Shift a live mixed root. Validation and traversal share fuel; invalid
\ input, running out of fuel (exhausted) and running out of room (full) are
\ distinct. On failure discard appended nodes, but never rewind allocation
\ serials. Negative fuel is invalid and leaves lf-mshift-fuel unchanged; a
\ negative cutoff or amount is invalid; a failed audit leaves fuel at zero.
\ Leaf constants and symbolic sorts are reused with their original stamps.
\ A zero shift returns the audited root without allocating or traversing
\ it.
: lf-mshift-refuse ( index identity cutoff amount -- -1 0 status )
  2drop 2drop outcome-invalid lf-rebuild-none ;
: lf-mshift-args? ( cutoff amount -- flag ) 0< swap 0< or 0= ;
: lf-mshift-copy ( index identity cutoff -- index identity status )
  lf-mshift-amount @ 0= if drop outcome-ok exit then
  nip lf-mshift-frames lf-rebuild-run ;
: lf-mshift-root ( index identity cutoff -- index identity status )
  >r 2dup lf-mshift-frames lf-rebuild-audit dup ok?
  if drop r> lf-mshift-copy else r> drop nip nip lf-rebuild-none then ;
: lf-mshift-pass ( index identity cutoff amount fuel -- index identity status )
  lf-mshift-frames frame-budget 0= if lf-mshift-refuse exit then
  2dup lf-mshift-args? if lf-mshift-amount ! lf-mshift-root lf-mshift-explain
  else lf-mshift-refuse then ;
\ The derivation log (ADR 0013): with it on, the pass is one shift step of
\ the term by the amount; both paths run the same pass. The shift inside
\ instantiation (lf-mshift-inside) is part of that step, not logged.
: lf-mshift-logged ( index identity cutoff amount fuel -- index identity status )
  4 pick 2 pick lf-rule-shift lf-log-open lf-mshift-pass lf-log-close-handle ;
: lf-mixed-shift ( index identity cutoff amount fuel -- index identity status )
  lf-log? if lf-mshift-logged else lf-mshift-pass then ;
