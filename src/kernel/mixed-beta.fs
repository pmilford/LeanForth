\ Untrusted mixed-term weak-head beta reduction. Load mixed-instantiate.fs
\ and its dependencies first. Handles are session-local diagnostics, not
\ capabilities or serialized values.
\ State: one frame record, lf-mbeta-frames (fuel, nesting, the starting
\ term count). Each contraction runs the public instantiate pass on its own
\ record. Not re-entrant and single-threaded; exclude concurrent mutation,
\ resets, raw edits and nested calls.

outcome-ok constant lf-mbeta-ok
outcome-invalid constant lf-mbeta-invalid
outcome-exhausted constant lf-mbeta-exhausted
lf-term-capacity frames: lf-mbeta-frames

\ Fuel left after a reduction; mixed-convert continues with it.
: lf-mbeta-fuel ( -- addr ) lf-mbeta-frames frame-fuel ;
: lf-mbeta-reduce ( node -- result outcome ) lf-mbeta-frames frame-call ;
\ The fields of an application node read earlier in this visit.
: lf-mbeta-function ( node -- function ) lf-term-slot node-first @ ;
: lf-mbeta-argument ( node -- argument ) lf-term-slot node-second @ ;

\ Contract a lambda body with an argument through the public instantiate
\ pass, which continues with this pass's fuel, then reduce the result.
\ Generated nodes are live roots and are passed with their identities,
\ which are fetched once both nodes are known to be live.
: lf-mbeta-live? ( body argument -- flag ) lf-term-valid? swap lf-term-valid? and ;
: lf-mbeta-handle ( node -- node identity ) dup lf-term-identity drop ;
: lf-mbeta-instantiate ( body argument -- result outcome )
  >r lf-mbeta-handle r> lf-mbeta-handle
  lf-mbeta-fuel @ lf-mixed-instantiate lf-minst-fuel @ lf-mbeta-fuel ! nip ;
: lf-mbeta-contract ( body argument -- result outcome )
  2dup lf-mbeta-live? 0= if 2drop lf-rebuild-invalid exit then
  lf-mbeta-instantiate dup ok? if drop lf-mbeta-reduce then ;

\ After the function reduced to the head r: a lambda head contracts with
\ the argument, an unchanged head keeps the node, and any other head is
\ applied to the argument.
: lf-mbeta-apply ( node r -- result outcome )
  over lf-mbeta-function over = if drop outcome-ok
  else swap lf-mbeta-argument lf-term-app lf-mshift-allocated then ;
: lf-mbeta-head ( node r -- result outcome )
  dup lf-term-read 0= if 2drop lf-rebuild-invalid exit then
  nip swap lf-tag-lam = if nip swap lf-mbeta-argument lf-mbeta-contract
  else drop lf-mbeta-apply then ;

\ Visit the function spine only; anything but an application is its own
\ head. Each visit costs fuel; instantiation's audits, traversal and shifts
\ share it.
: lf-mbeta-visit ( node -- result outcome )
  dup lf-term-read 0= if drop lf-rebuild-invalid exit then
  2drop lf-tag-app <> if outcome-ok exit then
  dup lf-mbeta-function lf-mbeta-reduce dup ok? if drop lf-mbeta-head else rot drop then ;

\ ( index identity fuel -- index identity status )
\ Audit the complete mixed graph before allocating, even discarded arguments
\ and lambda annotations. Fuel covers audit (including level visits), spine
\ visits and all instantiation work; repeated DAG visits are charged again.
\ Bounded reference/context scans are unmetered as in lf-cterm-check. On
\ failure restore the initial term count, never allocation serials; negative
\ fuel and a failed preflight conservatively leave zero fuel. Success
\ returns a live stamped root; unchanged constants and Sorts retain their
\ identities. Exhaustion includes fuel, frame, arena and index limits. Does
\ not check scope, types, declarations, equality, proofs, or
\ executable-program correctness.
: lf-mbeta-refuse ( index identity outcome -- -1 0 outcome ) nip nip lf-rebuild-none ;
: lf-mbeta-unfueled ( index identity -- -1 0 status )
  0 lf-mbeta-fuel ! outcome-invalid lf-mbeta-refuse ;
: lf-mixed-beta ( index identity fuel -- index identity status )
  lf-mbeta-frames frame-budget 0= if lf-mbeta-unfueled exit then
  2dup lf-mbeta-frames lf-rebuild-audit dup ok? 0= if lf-mbeta-refuse exit then
  2drop 0 ['] lf-mbeta-visit lf-mbeta-frames lf-rebuild-run ;
