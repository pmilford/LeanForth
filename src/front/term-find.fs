\ Whether a term holds a leaf that passes a test (Lean's Expr.find? for a
\ predicate on leaves): a bottom-up walk (front/dag-walk.fs, heap stacks,
\ a memo per node) whose image is 1 where a leaf passes, the or of the
\ two parts' at a binary node (application, binders, let, projection).
\ A smart-unfolding annotation (core/annotations.fs) is a leaf: the test
\ sees it.
\ lf-term-holds? ( term xt -- flag outcome ), xt ( leaf -- flag ): ok, or
\ full when the walk's heap blocks are refused (dag-walk.fs's outcomes).
\ lf-term-holds-with? ( term x xt -- flag outcome ), xt ( x leaf -- x
\ flag ): the same with a context x the test reads (Lean's findMVar? or
\ getMVars with a closure, plan 9.4.8l L5), so that no test reads a
\ register set for it.
\ lf-term-holds-node? ( term xt -- flag outcome ), xt ( node -- flag ):
\ the same with every node shown to the test, the term itself and each
\ binary node too (Lean's Expr.find? with a predicate on any expression,
\ for instance a let node; review s3a-decide B2), each node once.
\ Users: meta-tactic/goal.fs and tactic-core.fs (open holes, outside variables),
\ meta-tactic/rewrite.fs, meta-tactic/apply.fs, telescope.fs,
\ app-builder.fs, front/whnf.fs (dite in a matcher's value,
\ unfoldNestedDIte), tactics/decide.fs (a let in decide's goal, every
\ node). Moved from tactic-basic.fs (S2 merge B) so that whnf.fs, loaded
\ before it, can use it.
\ Not re-entrant: one walk at a time per context (the test must not
\ start another).
\ Untrusted front-end code.
\ State: the record tf (the test and the walk) in the checker context.

require ../lib/lib.fs
require ../core/terms.fs
require ./dag-walk.fs

begin-structure /tf
  field: tf-test         \ the leaf test ( x leaf -- x flag )
  field: tf-x            \ and its context x
  /dw +field tf-walk     \ and its walk
end-structure
/tf context-record: tf

: tf-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: tf-pending ( node walk -- child true | false )
  over lf-term-binary? 0= if 2drop false exit then
  over lf-term-first@ over tf-undone if nip nip true exit then
  swap lf-term-second@ swap tf-undone ;
\ The test's answer on a node (a leaf, or any node for lf-term-holds-node?).
: tf-leaf ( node -- 0|1 ) tf tf-x @ swap tf tf-test @ execute nip 1 and ;
: tf-build ( node walk -- 0|1 )
  over lf-term-binary? if dw-part-images or else drop tf-leaf then ;
\ The same with every node shown to the test once: a binary node's image
\ is its own answer or its parts'.
: tf-build-node ( node walk -- 0|1 )
  over lf-term-binary? if over tf-leaf >r dw-part-images r> or or else drop tf-leaf then ;
: tf-walk! ( build -- )
  tf tf-walk tuck dw-build ! ['] tf-pending over dw-pending !
  lf-term-base lf-term-count @ + swap dw-size ! ;
: tf-run ( term x xt build -- flag outcome )
  tf-walk! tf tf-test ! tf tf-x ! tf tf-walk dw-run swap 0<> swap ;
: lf-term-holds-with? ( term x xt -- flag outcome ) ['] tf-build tf-run ;
: tf-bare ( xt leaf -- xt flag ) over execute ;
: lf-term-holds? ( term xt -- flag outcome ) ['] tf-bare lf-term-holds-with? ;
: lf-term-holds-node? ( term xt -- flag outcome ) ['] tf-bare ['] tf-build-node tf-run ;
