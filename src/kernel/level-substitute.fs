\ Simultaneous substitution of universe levels: replace each parameter of a
\ level DAG by the level given for it, appending only the nodes that change.
\ Untrusted. IDs are opaque cells, not Lean names; raw indices cannot detect
\ stale references after a reset. This neither checks declarations nor
\ authorizes proofs. No simplification, level equality, serialization or
\ cross-store handles are provided. The caller's two arrays hold count cells
\ each, aligned, readable and disjoint from every store and from this
\ module's data; aliasing is not detected, and empty lists permit arbitrary
\ unused addresses. The parameter context (level-scope) describes the
\ caller's scope, not the formal scope.
\ State: one walk record, lf-lsubst-walker (the source walk and the fuel
\ left), and one job record, lf-lsubst-job (the substitution in use, the
\ reachable nodes and the planned new nodes). Not re-entrant and
\ single-threaded: the store, the context and the arrays must not change
\ during a call. mixed-level-substitute sets the substitution with
\ lf-lsubst-use and runs the checks below from its own passes.

require ../lib/lib.fs
require ../core/level-scope.fs
require ../core/levels.fs

outcome-ok constant lf-lsubst-ok
outcome-invalid constant lf-lsubst-invalid
outcome-exhausted constant lf-lsubst-exhausted

begin-structure /lf-lsrec
  field: lf-lsrec-formals      \ address of the formal parameter IDs
  field: lf-lsrec-actuals      \ address of their replacement levels
  field: lf-lsrec-count        \ number of formals
  field: lf-lsrec-new-count    \ new nodes planned
  lf-level-capacity cells +field lf-lsrec-seen       \ reached by the source walk
  lf-level-capacity cells +field lf-lsrec-results    \ each reached node's image
  lf-level-capacity /node * +field lf-lsrec-new-nodes
end-structure
lf-level-capacity walk: lf-lsubst-walker
create lf-lsubst-job /lf-lsrec allot
lf-lsubst-job /lf-lsrec erase

\ Fuel left after a call or check; mixed-level-substitute continues with it.
: lf-lsubst-fuel ( -- addr ) lf-lsubst-walker walk-fuel ;
\ The substitution in use, set only by lf-lsubst-use. A source audit alone
\ reads no actuals and may give address 0 for them.
: lf-lsubst-formals ( -- addr ) lf-lsubst-job lf-lsrec-formals ;
: lf-lsubst-actuals ( -- addr ) lf-lsubst-job lf-lsrec-actuals ;
: lf-lsubst-count ( -- addr ) lf-lsubst-job lf-lsrec-count ;
: lf-lsubst-new-count ( -- addr ) lf-lsubst-job lf-lsrec-new-count ;
: lf-lsubst-use ( formals actuals count -- )
  lf-lsubst-count ! lf-lsubst-actuals ! lf-lsubst-formals ! ;

\ Entries of the substitution; the position is in 0..count-1.
: lf-lsubst-formal@ ( position -- id ) cells lf-lsubst-formals @ + @ ;
: lf-lsubst-actual@ ( position -- root ) cells lf-lsubst-actuals @ + @ ;
\ Position of a formal ID among the first n formals.
: lf-lsubst-position ( id n -- position true | false )
  0 ?do dup i lf-lsubst-formal@ = if drop i true unloop exit then loop drop false ;
: lf-lsubst-in? ( id n -- flag ) lf-lsubst-position dup if nip then ;
: lf-lsubst-find ( id -- position true | false ) lf-lsubst-count @ lf-lsubst-position ;

\ Inputs: each formal is positive and new, and each actual passes level
\ scope in the caller's context, charging the given walk's fuel. Formal i
\ and actual i are checked before formal i+1; the order decides which
\ failure is reported and how much fuel is left.
: lf-lsubst-new-formal? ( i -- flag )
  dup lf-lsubst-formal@ dup 0> if swap lf-lsubst-in? 0= else 2drop false then ;
: lf-lsubst-input ( i walk -- outcome )
  over lf-lsubst-new-formal? if swap lf-lsubst-actual@ swap lf-lscope-walk-check
  else 2drop outcome-invalid then ;
: lf-lsubst-inputs ( walk -- outcome )
  lf-lscope-context-valid? 0= if drop-invalid exit then
  lf-lsubst-count @ 0 ?do
    i over lf-lsubst-input dup ok? 0= if nip unloop exit then drop loop drop outcome-ok ;

\ The source walk: shape as in level-scope, except that a parameter must be
\ a formal, and children are visited first child first. Every node read is
\ marked as reached. Each occurrence costs fuel; the work stack is bounded
\ independently of fuel.
: lf-lsubst-seen ( index -- addr ) cells lf-lsubst-job lf-lsrec-seen + ;
: lf-lsubst-mark ( walk -- ) true swap walk-node @ lf-lsubst-seen ! ;
: lf-lsubst-formal? ( id -- flag ) lf-lsubst-count @ lf-lsubst-in? ;
: lf-lsubst-param ( first second walk -- outcome )
  drop 0= over 0> and if lf-lsubst-formal? flag>outcome else drop-invalid then ;
: lf-lsubst-binary ( first second walk -- outcome ) >r swap r> walk-children ;
: lf-lsubst-dispatch ( first second walk tag -- outcome )
  over lf-lsubst-mark dup lf-level-binary-tag? if drop lf-lsubst-binary exit then
  case lf-level-tag-zero of lf-lscope-zero endof
    lf-level-tag-param of lf-lsubst-param endof
    lf-level-tag-succ of lf-lscope-succ endof walk-bad-tag endcase ;
: lf-lsubst-visit ( walk -- outcome ) lf-levels ['] lf-lsubst-dispatch walk-visit ;

\ Check the DAG reachable from root against the formals, with the fuel in
\ lf-lsubst-fuel. The zero node is checked even when root does not reach it.
: lf-lsubst-ready? ( root -- flag ) lf-level-valid? lf-lscope-zero-ok? and ;
: lf-lsubst-unseen ( -- ) 0 lf-lsubst-seen lf-level-capacity cells erase ;
: lf-lsubst-walk ( root -- outcome ) ['] lf-lsubst-visit lf-lsubst-walker walk-run ;
: lf-lsubst-source ( root -- outcome )
  dup lf-lsubst-ready? if lf-lsubst-unseen lf-lsubst-walk else drop-invalid then ;
\ The same check from inside another walk: start with its fuel and give it
\ back the rest.
: lf-lsubst-walk-source ( level walk -- outcome )
  tuck walk-fuel @ lf-lsubst-fuel ! lf-lsubst-source lf-lsubst-fuel @ rot walk-fuel ! ;

\ Planning, in index order, so children are planned before parents: a
\ parameter becomes its actual, zero stays zero, and a node whose children
\ keep their indices is reused, so shared nodes stay shared. Any other node
\ is staged at the index it will receive; nothing is allocated yet.
: lf-lsubst-result ( index -- addr ) cells lf-lsubst-job lf-lsrec-results + ;
: lf-lsubst-image ( index -- index' ) lf-lsubst-result @ ;
: lf-lsubst-new-node ( n -- addr ) /node * lf-lsubst-job lf-lsrec-new-nodes + ;
\ A succ keeps its unused second field.
: lf-lsubst-images ( tag first second -- tag first' second' )
  >r lf-lsubst-image over lf-level-tag-succ = r> swap 0= if lf-lsubst-image then ;
: lf-lsubst-kept? ( first' second' index -- flag )
  lf-level-slot dup node-first @ swap node-second @ rot = >r = r> and ;
\ The index the next staged node will receive.
: lf-lsubst-next ( -- index ) lf-level-count @ lf-lsubst-new-count @ + ;
: lf-lsubst-staged ( tag first second -- index outcome )
  lf-lsubst-new-count @ lf-lsubst-new-node node!
  lf-lsubst-next 1 lf-lsubst-new-count +! outcome-ok ;
: lf-lsubst-stage ( tag first second -- index outcome )
  lf-lsubst-next lf-level-capacity <
  if lf-lsubst-staged else 2drop drop 0 outcome-exhausted then ;
: lf-lsubst-inner ( index -- index' outcome )
  >r r@ lf-level-slot node@ lf-lsubst-images 2dup r@ lf-lsubst-kept?
  if 2drop drop r> outcome-ok else r> drop lf-lsubst-stage then ;
: lf-lsubst-actual ( index -- root outcome )
  lf-level-slot node-first @ lf-lsubst-find
  if lf-lsubst-actual@ outcome-ok else 0 outcome-invalid then ;
: lf-lsubst-target ( index -- index' outcome )
  dup lf-level-slot node-tag @ case
    lf-level-tag-zero of drop 0 outcome-ok endof
    lf-level-tag-param of lf-lsubst-actual endof
    >r lf-lsubst-inner r> endcase ;
: lf-lsubst-plan-node ( index -- outcome )
  dup lf-lsubst-target ok-then? if swap lf-lsubst-result ! outcome-ok else nip then ;
: lf-lsubst-plan-at ( index -- outcome )
  dup lf-lsubst-seen @ if lf-lsubst-plan-node else drop outcome-ok then ;
\ Every staged node needs an identity: the serial must not run out.
: lf-lsubst-ids? ( -- flag ) max-n lf-level-serial @ - lf-lsubst-new-count @ < 0= ;
: lf-lsubst-plan ( root -- outcome )
  0 lf-lsubst-new-count ! 1+ 0 ?do
    i lf-lsubst-plan-at dup ok? 0= if unloop exit then drop loop
  lf-lsubst-ids? if outcome-ok else outcome-exhausted then ;

\ Appending the staged nodes. The plan checked every precondition of the
\ allocation, so a failure means the store changed during the call: the
\ call then reports invalid input and puts the level count back, so no
\ node stays appended (identities already issued are not reused).
: lf-lsubst-add ( n -- flag ) lf-lsubst-new-node node@ lf-level-add dup if nip then ;
: lf-lsubst-commit ( -- outcome )
  lf-lsubst-new-count @ 0 ?do i lf-lsubst-add 0= if outcome-invalid unloop exit then loop
  outcome-ok ;
: lf-lsubst-finish ( root -- result ok | status )
  lf-level-count @ >r lf-lsubst-commit ok-then?
  if r> drop lf-lsubst-image outcome-ok else r> lf-level-count ! then ;
: lf-lsubst-prepare ( root -- root outcome )
  lf-lsubst-walker lf-lsubst-inputs dup ok? if drop dup lf-lsubst-source then
  dup ok? if drop dup lf-lsubst-plan then ;
: lf-lsubst-run ( root -- result ok | status )
  lf-lsubst-prepare ok-then? if lf-lsubst-finish then ;

\ Substitute count formals by count actuals in root. Invalid input or scope
\ is invalid; fuel, work stack, store or identity exhaustion is exhausted.
\ A failure appends no node. Fuel counts every occurrence in every actual,
\ even an unused one, and in the source; checking the bounded formal list
\ and staging nodes are additional bounded work. The job record and the
\ level-scope walk record change even on failure.
: lf-lsubst-levels? ( -- flag ) lf-level-count-valid? lf-level-serial @ 0< 0= and ;
: lf-lsubst ( root formal-addr actual-addr count fuel -- result lf-lsubst-ok | status )
  lf-lsubst-walker walk-budget 0= if 2drop 2drop outcome-invalid exit then
  dup lf-level-capacity upto? 0= if 2drop 2drop outcome-invalid exit then
  lf-lsubst-use lf-lsubst-levels? if lf-lsubst-run else drop-invalid then ;
