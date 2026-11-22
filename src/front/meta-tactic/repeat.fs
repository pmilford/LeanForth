\ Meta.repeat' of the tactic library (plan row TB2, tactic batch 2b), a
\ port of Lean 4.35.0's src/lean/Lean/Meta/Tactic/Repeat.lean:27-58
\ (repeat'Core and its go, without the progress flag, which repeat'
\ drops): f run on each goal, then on the goals it gives, depth first.
\   lf-goals-repeat ( goals xt -- goals' )  xt ( goal -- goals true |
\       false ) is f: true and its new goals (a run), or false, f failed
\       (its changes undone: lf-commit-when, Lean's observing?); goals'
\       the goals f failed on, in the order met, less those assigned
\       since; an assigned goal is passed over unvisited; f is called at
\       most lf-repeat-iters times (Lean's maxIters, 100000), after which
\       the goals not visited follow, in order. A failure f throws is
\       thrown on (Lean's observing? would catch any exception: f answers
\       false only for Lean's failure, so not supported is never a
\       failure)
\   lf-goals-repeat-n ( goals xt n -- goals' )  the same with maxIters n
\ The goals to visit are a stack (lib/runs.fs, the next one last), so the
\ walk is not recursive; f may call lf-goals-repeat itself (a frame per
\ call open).
\ Lean call list: isAssigned -> lf-goal-assigned?; observing? ->
\ lf-commit-when; filterM isAssigned -> run-filter of
\ lf-meta-unassigned?.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mrp-frames (a frame per call open, meta-must.fs's
\ lf-with-record), in the checker context (ADR 0009). Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/context.fs
require ../mvars.fs
require ../goals.fs
require ../fun-info.fs
require ../meta-must.fs

100000 constant lf-repeat-iters

begin-structure /mrp
  field: mrp-xt          \ f ( goal -- goals true | false )
  field: mrp-todo        \ the goals to visit, the next one last (a run)
  field: mrp-acc         \ the goals f failed on (a run)
  field: mrp-left        \ the calls of f left
  field: mrp-goal        \ the goal f runs on
  field: mrp-new         \ and the goals it gave
end-structure
/mrp context-slab: mrp-frames
: mrp ( -- frame ) mrp-frames slab-last ;

\ ---- The stack of goals to visit, and the goals kept.
\ The run held at addr, then goal.
: mrp-onto ( addr goal -- ) over @ swap run-push lf-must swap ! ;
: mrp-push1 ( goal -- ) mrp mrp-todo swap mrp-onto ;
: mrp-push ( goals -- )
  dup run-count begin ?dup while 1- 2dup run@ mrp-push1 repeat drop ;
: mrp-last ( -- n ) mrp mrp-todo @ run-count 1- ;
: mrp-pop ( -- goal )
  mrp mrp-todo @ mrp-last 2dup run@ >r run-take lf-must mrp mrp-todo ! r> ;
: mrp-keep ( goal -- ) mrp mrp-acc swap mrp-onto ;

\ ---- One visit: f from a saved state, its goals visited next.
: mrp-f ( -- flag ) mrp mrp-goal @ mrp mrp-xt @ execute dup if swap mrp mrp-new ! then ;
: mrp-step ( goal -- )
  dup mrp mrp-goal ! -1 mrp mrp-left +! ['] mrp-f lf-commit-when
  if drop mrp mrp-new @ mrp-push else mrp-keep then ;
: mrp-visit ( goal -- ) dup lf-goal-assigned? if drop else mrp-step then ;
: mrp-more? ( -- flag ) mrp mrp-todo @ run-count 0<> mrp mrp-left @ 0> and ;
: mrp-loop ( -- ) begin mrp-more? while mrp-pop mrp-visit repeat ;
\ What is left unvisited follows, then the goals assigned since go.
: mrp-rest ( -- ) begin mrp mrp-todo @ run-count while mrp-pop mrp-keep repeat ;
: mrp-result ( -- goals )
  mrp-rest mrp mrp-acc @ ['] lf-meta-unassigned? run-filter lf-must ;
: mrp-fill ( goals xt n -- )
  mrp mrp-left ! mrp mrp-xt ! 0 mrp mrp-todo ! 0 mrp mrp-acc ! mrp-push ;
: mrp-run ( goals xt n -- goals' ) mrp-fill mrp-loop mrp-result ;
: lf-goals-repeat-n ( goals xt n -- goals' ) mrp-frames ['] mrp-run lf-with-record ;
: lf-goals-repeat ( goals xt -- goals' ) lf-repeat-iters lf-goals-repeat-n ;
base !   \ the BASE this file was loaded with
