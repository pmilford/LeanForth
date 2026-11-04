\ Simultaneous substitution of universe levels: replace each parameter of a
\ level DAG by the level given for it, as Lean's kernel instantiates a
\ constant's universe parameters (ADR 0011, Amendment 1): instantiate
\ (level.cpp 317-340) with replace (261-277), update_succ (301-306) and
\ update_max (308-315), so a rebuilt max or imax is simplified by mk_max or
\ mk_imax (level-make.fs). [kernel] code: experimental, not through the
\ review gate. Untrusted. IDs are opaque cells standing for interned Lean
\ names; raw indices cannot detect stale references after a reset. This
\ neither checks declarations nor authorizes proofs. No level equality,
\ serialization or cross-store handles are provided. The caller's two
\ arrays hold count cells each, aligned, readable and disjoint from every
\ store and from this module's data; aliasing is not detected, and empty
\ lists permit arbitrary unused addresses. The parameter context
\ (level-scope) describes the caller's scope, not the formal scope.
\ State: one walk record, lf-lsubst-walker (the source walk and the fuel
\ left), and one job record, lf-lsubst-job (the substitution in use, the
\ reachable nodes, their images and a mark of the level store), both
\ members of the checker context (lib/context.fs); the facts of
\ level-make. Single-threaded within one context: the store, the
\ parameter context and the arrays must not change during a call.
\ mixed-level-substitute sets the substitution with lf-lsubst-use and runs
\ the checks below from its own passes.

require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/store-columns.fs
require ../core/diagnostics.fs
require ../core/level-scope.fs
require ../core/levels.fs
require ./level-make.fs

begin-structure /lf-lsrec
  field: lf-lsrec-formals      \ address of the formal parameter IDs
  field: lf-lsrec-actuals      \ address of their replacement levels
  field: lf-lsrec-count        \ number of formals
  /store-mark +field lf-lsrec-mark                  \ the level store before a build
end-structure
lf-level-walk-room context-walk: lf-lsubst-walker
/lf-lsrec context-record: lf-lsubst-job
\ Per level, columns of the level store (lib/store-columns.fs): whether
\ the source walk reached it, and its image.
/slab context-record: lf-lsubst-seen-column
1 cells ' lf-lsubst-seen-column lf-level-columns column-add
/slab context-record: lf-lsubst-results-column
1 cells ' lf-lsubst-results-column lf-level-columns column-add

\ Fuel left after a call or check; mixed-level-substitute continues with it.
: lf-lsubst-fuel ( -- addr ) lf-lsubst-walker walk-fuel ;
\ The substitution in use, set only by lf-lsubst-use. A source audit alone
\ reads no actuals and may give address 0 for them.
: lf-lsubst-formals ( -- addr ) lf-lsubst-job lf-lsrec-formals ;
: lf-lsubst-actuals ( -- addr ) lf-lsubst-job lf-lsrec-actuals ;
: lf-lsubst-count ( -- addr ) lf-lsubst-job lf-lsrec-count ;
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
: lf-lsubst-seen ( index -- addr ) lf-lsubst-seen-column column-at ;
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
: lf-lsubst-unseen ( -- ) lf-lsubst-seen-column column-erase ;
: lf-lsubst-site ( -- site ) c" level-substitute lf-lsubst" ;
: lf-lsubst-walk ( root -- outcome )
  ['] lf-lsubst-visit lf-lsubst-walker walk-run
  lf-lsubst-walker lf-lsubst-site lf-diag-walk ;
: lf-lsubst-source ( root -- outcome )
  dup lf-lsubst-ready? if lf-lsubst-unseen lf-lsubst-walk else drop-invalid then ;
\ The same check from inside another walk: start with its fuel and give it
\ back the rest.
: lf-lsubst-walk-source ( level walk -- outcome )
  tuck walk-fuel @ lf-lsubst-fuel ! lf-lsubst-source lf-lsubst-fuel @ rot walk-fuel ! ;

\ Building, in index order, so children come before parents, as Lean's
\ instantiate does: zero and every node without a parameter stay as they
\ are (replace, 320-321), a parameter becomes its actual, a succ over a
\ changed child is a new succ (update_succ; Lean's mk_succ is raw), and a
\ max or imax with a parameter is rebuilt from its children's images with
\ mk_max or mk_imax (update_max), which may give one of them. Lean keeps
\ such a node unchanged when both images are the very objects it had
\ (is_eqp, pointer identity), which no input records: when both images
\ are structurally unchanged and mk_max or mk_imax would simplify the
\ node, Lean's result depends on that sharing, and the substitution is
\ unknown (ADR 0011, rule K6), recorded with the node. Otherwise the node
\ is kept when its images are unchanged and rebuilt when they are not.
\ Nodes are appended as needed; a failure rolls the store back.
: lf-lsubst-result ( index -- addr ) lf-lsubst-results-column column-at ;
: lf-lsubst-image ( index -- index' ) lf-lsubst-result @ ;
: lf-lsubst-images ( index -- first' second' )
  dup lf-level-first@ lf-lsubst-image swap lf-level-second@ lf-lsubst-image ;
\ Room for one more node: a spent identity serial is full, recorded with
\ the serial and the one identity needed; a full store is full, recorded
\ with the index the node would get.
: lf-lsubst-spent ( -- outcome )
  lf-level-serial @ 1 lf-lsubst-site lf-diag-serial-spent lf-diag-note outcome-full ;
: lf-lsubst-no-room ( -- outcome )
  lf-level-count @ lf-level-capacity lf-lsubst-site lf-diag-levels-full lf-diag-note
  outcome-full ;
: lf-lsubst-room ( -- outcome )
  lf-levels store-spent? if lf-lsubst-spent exit then
  lf-level-count @ lf-level-capacity < if outcome-ok else lf-lsubst-no-room then ;
\ An allocation the store still refuses after the room check (an injected
\ failure, tests/support/alloc-fail.fs) is full too, recorded by the store.
: lf-lsubst-made ( level true | false -- level outcome )
  if outcome-ok else 0 outcome-full then ;
: lf-lsubst-child ( index -- child' child ) lf-level-first@ dup lf-lsubst-image swap ;
: lf-lsubst-succ ( index -- index' outcome )
  dup lf-lsubst-child = if outcome-ok exit then
  lf-level-first@ lf-lsubst-image
  lf-lsubst-room ok-then? if lf-level-succ lf-lsubst-made else 0 swap then ;
\ mk_max or mk_imax (by tag) of two images: one of them, or a new node.
: lf-lsubst-choice ( first' second' tag -- choice )
  lf-level-tag-max = if lf-lmk-max-choice else lf-lmk-imax-choice then ;
: lf-lsubst-new ( first' second' tag -- level outcome )
  >r lf-lsubst-room ok-then? if r> lf-level-binary lf-lsubst-made exit then
  r> drop nip 0 swap ;
: lf-lsubst-mk ( first' second' tag -- level outcome )
  >r 2dup r@ lf-lsubst-choice dup 3 = if drop r> drop lf-level-tag-max recurse exit then
  ?dup if r> drop lf-lmk-pick outcome-ok else r> lf-lsubst-new then ;
\ Whether both images are structurally the children they replace.
: lf-lsubst-same? ( index first' second' -- flag )
  rot dup lf-level-second@ rot lf-lmk-same? >r lf-level-first@ lf-lmk-same? r> and ;
: lf-lsubst-shared ( index -- 0 outcome )
  0 lf-lsubst-site lf-diag-shared-level lf-diag-note 0 outcome-unknown ;
: lf-lsubst-unchanged ( index -- index' outcome )
  dup lf-lsubst-images rot dup >r lf-level-tag@ lf-lmk-simplifies?
  r> swap if lf-lsubst-shared else outcome-ok then ;
: lf-lsubst-rebuild ( index -- index' outcome )
  dup lf-lmk-param? 0= if outcome-ok exit then
  dup dup lf-lsubst-images lf-lsubst-same? if lf-lsubst-unchanged exit then
  dup lf-lsubst-images rot lf-level-tag@ lf-lsubst-mk ;
: lf-lsubst-actual ( index -- root outcome )
  lf-level-slot node-first @ lf-lsubst-find
  if lf-lsubst-actual@ outcome-ok else 0 outcome-invalid then ;
: lf-lsubst-target ( index -- index' outcome )
  dup lf-level-tag@ case
    lf-level-tag-zero of drop 0 outcome-ok endof
    lf-level-tag-param of lf-lsubst-actual endof
    lf-level-tag-succ of lf-lsubst-succ endof
    >r lf-lsubst-rebuild r> endcase ;
: lf-lsubst-build-node ( index -- outcome )
  dup lf-lsubst-target ok-then? if swap lf-lsubst-result ! outcome-ok else nip then ;
: lf-lsubst-build-at ( index -- outcome )
  dup lf-lsubst-seen @ if lf-lsubst-build-node else drop outcome-ok then ;
: lf-lsubst-build ( root -- outcome )
  1+ 0 ?do i lf-lsubst-build-at dup ok? 0= if unloop exit then drop loop outcome-ok ;

\ The level store is marked before the build and rolled back after a
\ failure, so no node stays appended (identities already issued are not
\ reused); a refused rollback is invalid.
: lf-lsubst-store-mark ( -- addr ) lf-lsubst-job lf-lsrec-mark ;
: lf-lsubst-undo ( outcome -- outcome )
  lf-lsubst-store-mark lf-levels store-rollback ok? 0= if drop outcome-invalid then ;
: lf-lsubst-finish ( root outcome -- result ok | status )
  dup ok? if drop lf-lsubst-image outcome-ok else nip lf-lsubst-undo then ;
: lf-lsubst-prepare ( root -- root outcome )
  lf-lsubst-walker lf-lsubst-inputs dup ok? if drop dup lf-lsubst-source then
  dup ok? if drop lf-lsubst-store-mark lf-levels store-mark then ;
: lf-lsubst-run ( root -- result ok | status )
  lf-lsubst-prepare ok-then? 0= if exit then
  lf-lmk-sync dup lf-lsubst-build lf-lsubst-finish ;

\ Substitute count formals by count actuals in root. Invalid input or scope
\ is invalid; running out of fuel is exhausted; a full work stack or level
\ store, or a spent identity serial, is full; a result that depends on
\ object sharing in Lean (rule K6) is unknown.
\ A failure leaves no node appended. Fuel counts every occurrence in every
\ actual, even an unused one, and in the source; checking the bounded
\ formal list, Lean's simplifications and appending nodes are additional
\ bounded work. The job record, the facts of level-make and the
\ level-scope walk record change even on failure.
: lf-lsubst-levels? ( -- flag ) lf-level-count-valid? lf-level-serial @ 0< 0= and ;
: lf-lsubst ( root formal-addr actual-addr count fuel -- result ok | status )
  lf-lsubst-walker walk-budget 0= if 2drop 2drop outcome-invalid exit then
  dup 0< if 2drop 2drop outcome-invalid exit then
  lf-lsubst-use lf-lsubst-levels? if lf-lsubst-run else drop-invalid then ;
