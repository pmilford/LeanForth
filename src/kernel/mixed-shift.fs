\ Untrusted mixed-term shift: add an amount to every bound variable at or
\ above a cutoff, rebuilding the term. Structural transformation only; no
\ proof judgment. Load mixed-rebuild.fs and its dependencies first.
\ State: one job record, lf-mshift-job (fields lf-shiftjob-*): the pass's
\ frames (fuel, nesting, and the cutoff as context) and the amount. Not
\ re-entrant and single-threaded: the instantiate pass shifts its
\ replacement on this record, which a shift in progress refuses. Exclude
\ raw mutation, resets and concurrent access during a call.

outcome-ok constant lf-mshift-ok
outcome-invalid constant lf-mshift-invalid
outcome-exhausted constant lf-mshift-exhausted
max-n constant lf-mshift-max

begin-structure /lf-shiftjob
  /frames +field lf-shiftjob-frames   \ fuel, nesting, the cutoff as context
  field: lf-shiftjob-amount           \ added to each variable at or above the cutoff
end-structure
create lf-mshift-job /lf-shiftjob allot

: lf-mshift-frames ( -- frames ) lf-mshift-job lf-shiftjob-frames ;
\ Fuel left after a shift; mixed-infer continues with it.
: lf-mshift-fuel ( -- addr ) lf-mshift-frames frame-fuel ;
: lf-mshift-amount ( -- addr ) lf-mshift-job lf-shiftjob-amount ;

\ Visiting one node of the shift. The preaudit establishes tags, payloads
\ and backward edges. A variable below the cutoff is kept; the others move
\ up by the amount, which exhausts past lf-mshift-max. Leaves are kept and
\ binary nodes rebuilt; any other tag is invalid.
: lf-mshift-amount@ ( frames -- amount ) frame-job @ lf-shiftjob-amount @ ;
: lf-mshift-up ( index amount -- result outcome )
  2dup lf-mshift-max swap - > if 2drop lf-rebuild-exhausted
  else + lf-term-bvar lf-rebuild-allocated then ;
: lf-mshift-bvar ( node frames -- result outcome )
  over lf-term-first@ over frame-context @ < if lf-rebuild-keep exit then
  lf-mshift-amount@ swap lf-term-first@ swap lf-mshift-up ;
: lf-mshift-leaf ( node frames tag -- result outcome )
  case lf-tag-bvar of lf-mshift-bvar endof
    lf-tag-constant of lf-rebuild-keep endof
    lf-tag-symbolic-sort of lf-rebuild-keep endof
    >r lf-rebuild-bad r> endcase ;
\ A binary node goes straight to lf-rebuild-binary: no word in between.
: lf-mshift-visit ( node frames -- result outcome )
  over lf-term-valid? lf-rebuild-tag
  dup lf-term-binary-tag? if drop lf-rebuild-binary else lf-mshift-leaf then ;
\ The visitor is set once, here.
lf-term-capacity ' lf-mshift-visit lf-mshift-frames frame-init
lf-mshift-job lf-mshift-frames frame-job !

\ Shift a node by amount from cutoff zero, from inside another pass whose
\ frames record lends its fuel and gets back what is left. A shift in
\ progress refuses, changing nothing: no result, invalid. Nothing is rolled
\ back here; the caller's pass does that.
: lf-mshift-borrow ( frames -- flag ) frame-fuel @ lf-mshift-frames frame-budget ;
: lf-mshift-inside ( node amount frames -- result outcome )
  dup lf-mshift-borrow 0= if drop 2drop lf-rebuild-invalid exit then
  >r lf-mshift-amount ! 0 lf-mshift-frames frame-run lf-mshift-fuel @ r> frame-fuel ! ;

\ Shift a live mixed root. Validation and traversal share fuel; invalid input
\ and resource exhaustion are distinct. On failure discard appended nodes,
\ but never rewind allocation serials. Negative fuel is invalid and leaves
\ lf-mshift-fuel unchanged; a negative cutoff or amount is invalid; a failed
\ audit leaves fuel at zero. Leaf constants and symbolic sorts are reused
\ with their original stamps. A zero shift returns the audited root without
\ allocating or traversing it.
: lf-mshift-refuse ( index identity cutoff amount -- -1 0 status )
  2drop 2drop outcome-invalid lf-rebuild-none ;
: lf-mshift-args? ( cutoff amount -- flag ) 0< swap 0< or 0= ;
: lf-mshift-copy ( index identity cutoff -- index identity status )
  lf-mshift-amount @ 0= if drop outcome-ok exit then
  nip lf-mshift-frames lf-rebuild-run ;
: lf-mshift-root ( index identity cutoff -- index identity status )
  >r 2dup lf-mshift-frames lf-rebuild-audit dup ok?
  if drop r> lf-mshift-copy else r> drop nip nip lf-rebuild-none then ;
: lf-mixed-shift ( index identity cutoff amount fuel -- index identity status )
  lf-mshift-frames frame-budget 0= if lf-mshift-refuse exit then
  2dup lf-mshift-args? if lf-mshift-amount ! lf-mshift-root else lf-mshift-refuse then ;
