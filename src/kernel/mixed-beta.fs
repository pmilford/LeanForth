\ Untrusted mixed-term weak-head beta reduction. Handles are session-local
\ diagnostics, not capabilities or serialized values.
\ State: one frames record, lf-mbeta-frames (fuel, nesting), a member of
\ the checker context (lib/context.fs), declared after its visitor below.
\ Each contraction runs the public instantiate pass on its own record.
\ Single-threaded within one context; exclude concurrent mutation, resets,
\ raw edits and nested calls.

require ../lib/lib.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/terms.fs
require ./mixed-instantiate.fs
require ./mixed-rebuild.fs
require ./mixed-shift.fs

\ The fields of an application node read earlier in this visit.
: lf-mbeta-function ( node -- function ) lf-term-first@ ;
: lf-mbeta-argument ( node -- argument ) lf-term-second@ ;

\ Contract a lambda body with an argument through the public instantiate
\ pass, which continues with this pass's fuel, then reduce the result.
\ Generated nodes are live roots and are passed with their identities,
\ which are fetched once both nodes are known to be live.
: lf-mbeta-live? ( body argument -- flag ) lf-term-valid? swap lf-term-valid? and ;
: lf-mbeta-handle ( node -- node identity ) dup lf-term-identity drop ;
: lf-mbeta-handles ( body argument -- body bid argument aid )
  >r lf-mbeta-handle r> lf-mbeta-handle ;
: lf-mbeta-instantiate ( body argument frames -- result outcome )
  >r lf-mbeta-handles r@ frame-fuel @ lf-mixed-instantiate nip
  lf-minst-fuel @ r> frame-fuel ! ;
\ The derivation log (ADR 0013): with it on, the instantiation is one beta
\ step of the lambda body and the argument, closed before the contractum
\ is reduced further; both paths run the same instantiation.
: lf-mbeta-step-logged ( body argument frames -- result outcome )
  >r 2dup lf-rule-beta lf-log-open r> lf-mbeta-instantiate lf-log-close ;
: lf-mbeta-step ( body argument frames -- result outcome )
  lf-log? if lf-mbeta-step-logged else lf-mbeta-instantiate then ;
: lf-mbeta-contract ( body argument frames -- result outcome )
  >r 2dup lf-mbeta-live? 0= if 2drop r> drop lf-rebuild-invalid exit then
  r@ lf-mbeta-step dup ok? if drop r> frame-call else r> drop then ;

\ After the function reduced to the head r: a lambda head contracts with
\ the argument, an unchanged head keeps the node, and any other head is
\ applied to the argument.
: lf-mbeta-apply ( node r -- result outcome )
  over lf-mbeta-function over = if drop outcome-ok
  else swap lf-mbeta-argument lf-term-app lf-rebuild-allocated then ;
: lf-mbeta-lambda? ( node -- flag ) lf-term-tag@ lf-tag-lam = ;
: lf-mbeta-head ( node frames r -- result outcome )
  dup lf-term-valid? 0= if drop lf-rebuild-bad exit then
  dup lf-mbeta-lambda? if lf-term-second@ rot lf-mbeta-argument rot lf-mbeta-contract
  else nip lf-mbeta-apply then ;

\ Visit the function spine only; anything but an application is its own
\ head. Each visit costs fuel; instantiation's audits, traversal and shifts
\ share it.
: lf-mbeta-app? ( node -- flag ) lf-term-tag@ lf-tag-app = ;
: lf-mbeta-visit ( node frames -- result outcome )
  over lf-term-valid? 0= if lf-rebuild-bad exit then
  over lf-mbeta-app? 0= if drop outcome-ok exit then
  over lf-mbeta-function over frame-call ok-keep2? if lf-mbeta-head then ;
\ The frames, whose visitor is set once, here.
lf-depth-limit ' lf-mbeta-visit context-frames: lf-mbeta-frames

\ Fuel left after a reduction; mixed-convert continues with it.
: lf-mbeta-fuel ( -- addr ) lf-mbeta-frames frame-fuel ;

\ ( index identity fuel -- index identity status )
\ Audit the complete mixed graph before allocating, even discarded arguments
\ and lambda annotations. Fuel covers audit (including level visits), spine
\ visits and all instantiation work; repeated DAG visits are charged again.
\ Bounded reference/context scans are unmetered as in lf-cterm-check. On
\ failure restore the initial term count, never allocation serials; negative
\ fuel and a failed preflight conservatively leave zero fuel. Success
\ returns a live stamped root; unchanged constants and Sorts retain their
\ identities. Running out of fuel is exhausted; the frame, arena, binder
\ context and index limits are full. Does not check scope, types,
\ declarations, equality, proofs, or executable-program correctness.
: lf-mbeta-refuse ( index identity outcome -- -1 0 outcome ) nip nip lf-rebuild-none ;
: lf-mbeta-unfueled ( index identity -- -1 0 status )
  0 lf-mbeta-fuel ! outcome-invalid lf-mbeta-refuse ;
: lf-mbeta-site ( -- site ) c" mixed-beta lf-mixed-beta" ;
: lf-mbeta-explain ( outcome -- outcome ) lf-mbeta-frames lf-mbeta-site lf-diag-frames ;
: lf-mbeta-pass ( index identity fuel -- index identity status )
  lf-mbeta-frames frame-budget 0= if lf-mbeta-unfueled exit then
  2dup lf-mbeta-frames lf-rebuild-audit dup ok? 0= if lf-mbeta-refuse exit then
  2drop 0 lf-mbeta-frames lf-rebuild-run lf-mbeta-explain ;
\ The derivation log (ADR 0013): with it on, a reduction that changes the
\ term is one whnf step (one that changes nothing writes no record).
: lf-mbeta-logged ( index identity fuel -- index identity status )
  2 pick lf-log-none lf-rule-whnf lf-log-open lf-mbeta-pass lf-log-close-whnf ;
: lf-mixed-beta ( index identity fuel -- index identity status )
  lf-log? if lf-mbeta-logged else lf-mbeta-pass then ;

\ Recovery. A THROW out of any of the three rebuilding passes (such as a
\ host stack overflow) leaves their records busy, so that every later pass
\ refuses as invalid, and leaves in the term store whatever the pass
\ appended. The code that catches it must discard those nodes (reset the
\ store, or restore lf-term-count) and then make the records idle again.
: lf-mixed-rebuild-reset ( -- )
  lf-mbeta-frames frame-reset lf-minst-frames frame-reset lf-mshift-frames frame-reset ;

\ Host stacks. A beta visit runs instantiate passes and an instantiate
\ visit runs shift passes, each pass up to lf-depth-limit frames deep, so
\ up to three times lf-depth-limit frames can be nested at once. By stack
\ painting (Gforth 0.7.3 and 1.0 agree), one frame holds at most 4
\ return-stack and 3 data-stack cells in beta, 6 and 4 in instantiate, and
\ 5 and 4 in shift; the slack covers the entry words, the work at the
\ deepest frame and a shallow caller. Loading stops when the host's stacks
\ are smaller, so that no input overflows them from a shallow caller (an
\ overflow would throw, never give ok); a caller that itself recurses must
\ add its own need (mixed-infer.fs does). Hosts that do not report their
\ stack sizes are not checked. Jobs (lib/task.fs) run on their workers'
\ stacks instead: the need is stated with context-need, and the pool
\ refuses to start with stack settings that do not cover it, whichever of
\ this file and task.fs loads first.
15 constant lf-mbeta-rs-level   \ return-stack cells: one frame of each pass
11 constant lf-mbeta-ds-level   \ data-stack cells: one frame of each pass
256 constant lf-mbeta-stack-slack
: lf-mbeta-need ( cells-per-level -- cells ) lf-depth-limit * lf-mbeta-stack-slack + ;
lf-mbeta-rs-level lf-mbeta-need constant lf-mbeta-return-cells
lf-mbeta-ds-level lf-mbeta-need constant lf-mbeta-data-cells
: lf-mbeta-fits? ( need c-addr u -- flag ) environment? if > 0= else drop true then ;
\ Whether the host's own stacks hold data-cells and return-cells.
: lf-mbeta-host? ( data-cells return-cells -- flag )
  s" RETURN-STACK-CELLS" lf-mbeta-fits? swap s" STACK-CELLS" lf-mbeta-fits? and ;
lf-mbeta-data-cells lf-mbeta-return-cells lf-mbeta-host?
0= [if] .( mixed-beta.fs: host stacks too small for lf-depth-limit) cr abort [then]
lf-mbeta-data-cells lf-mbeta-return-cells context-need
