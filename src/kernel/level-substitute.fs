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
\ left), one job record, lf-lsubst-job (the substitution in use, the
\ walk's stamp and count of reached nodes, and a mark of the level store),
\ the list of reached nodes (lf-lsubst-reached-cells) and two columns of
\ the level store (each node's stamp and image), all members of the
\ checker context (lib/context.fs); the facts of level-make.
\ Single-threaded within one context: the store, the parameter context and
\ the arrays must not change during a call. mixed-level-substitute sets
\ the substitution with lf-lsubst-use and runs the checks below from its
\ own passes, and sorts its own reached terms with lf-cells-sort.
\ Cost (plan task 6.5.5; step S0 of the compact-store plan): a call's work
\ is proportional to the nodes it reaches, not to the store's size: a new
\ walk takes a new stamp instead of erasing a column, and the build visits
\ only the reached nodes, sorted, instead of every index up to the root.

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
  field: lf-lsrec-stamp        \ the source walk's stamp, 0 before the first
  field: lf-lsrec-reached      \ nodes it reached (lf-lsubst-reached-cells)
  /store-mark +field lf-lsrec-mark                  \ the level store before a build
end-structure
lf-level-walk-room context-walk: lf-lsubst-walker
/lf-lsrec context-record: lf-lsubst-job
\ Per level, columns of the level store (lib/store-columns.fs): the stamp
\ of the last source walk that reached it, and its image.
/slab context-record: lf-lsubst-seen-column
1 cells ' lf-lsubst-seen-column lf-level-columns column-add
/slab context-record: lf-lsubst-results-column
1 cells ' lf-lsubst-results-column lf-level-columns column-add
\ The nodes the source walk reached, each listed once: a growable array
\ with no fixed limit (plan task 6.2.0); one the heap cannot grow is full.
1 cells context-slab: lf-lsubst-reached-cells

\ Two general tools on cell arrays, also used by mixed-level-substitute.
\ Appending x after the first n cells of a slab used from unit 0 (its
\ count kept by the caller): n+1 and ok, or n and full when the heap
\ refuses room.
: lf-cells-add ( x n slab -- n' outcome )
  over 1+ over slab-hold ok-then? 0= if rot drop exit then
  over swap slab-at rot swap ! 1+ outcome-ok ;
\ Sorting n cells at addr ascending, in place: heapsort, so about 2n log n
\ comparisons whatever the order, no scratch and no recursion.
: lf-cell-at ( i addr -- addr' ) swap cells + ;
: lf-cells-less? ( i j addr -- flag ) tuck lf-cell-at @ >r lf-cell-at @ r> < ;
: lf-cells-swap ( i j addr -- )
  tuck lf-cell-at >r lf-cell-at r> 2dup @ swap @ rot ! swap ! ;
\ The child of i that a sift follows in a heap of n cells: 2i+1, or 2i+2
\ when that one is below n and larger; n or more when i has none.
: lf-heap-child ( addr n i -- addr n c )
  2* 1+ 2dup 1+ > if dup dup 1+ 4 pick lf-cells-less? - then ;
\ One step of a sift: when i's child c is below n and larger, the two
\ swap and the sift goes on from c (true); otherwise it ends (false).
: lf-heap-down? ( addr n i -- addr n c true | addr n i false )
  dup >r lf-heap-child 2dup > if r@ over 4 pick lf-cells-less? else false then
  if r> over 4 pick lf-cells-swap true else drop r> false then ;
: lf-heap-sift ( addr n i -- ) begin lf-heap-down? 0= until drop 2drop ;
: lf-heapify ( addr n -- addr n )
  dup 2/ begin ?dup while 1- >r 2dup r@ lf-heap-sift r> repeat ;
: lf-cells-sort ( addr n -- )
  lf-heapify begin dup 1 > while
    1- 0 over 3 pick lf-cells-swap 2dup 0 lf-heap-sift repeat 2drop ;

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
\ marked as reached: its stamp becomes the walk's, and the first time it is
\ listed. Each occurrence costs fuel; the work stack is bounded
\ independently of fuel.
: lf-lsubst-seen ( index -- addr ) lf-lsubst-seen-column column-at ;
: lf-lsubst-stamp ( -- addr ) lf-lsubst-job lf-lsrec-stamp ;
: lf-lsubst-reached ( -- addr ) lf-lsubst-job lf-lsrec-reached ;
: lf-lsubst-reached? ( index -- flag ) lf-lsubst-seen @ lf-lsubst-stamp @ = ;
\ A list the heap cannot grow is full, recorded with its count and room.
: lf-lsubst-site ( -- site ) c" level-substitute lf-lsubst" ;
: lf-lsubst-crowded ( n -- n )
  dup dup lf-lsubst-reached-cells slab-capacity lf-lsubst-site
  lf-diag-work-stack-full lf-diag-note ;
: lf-lsubst-list ( index -- outcome )
  lf-lsubst-reached @ lf-lsubst-reached-cells lf-cells-add
  dup outcome-full = if swap lf-lsubst-crowded swap then swap lf-lsubst-reached ! ;
: lf-lsubst-mark ( walk -- outcome )
  walk-node @ dup lf-lsubst-reached? if drop outcome-ok exit then
  lf-lsubst-stamp @ over lf-lsubst-seen ! lf-lsubst-list ;
: lf-lsubst-formal? ( id -- flag ) lf-lsubst-count @ lf-lsubst-in? ;
: lf-lsubst-param ( first second walk -- outcome )
  drop 0= over 0> and if lf-lsubst-formal? flag>outcome else drop-invalid then ;
: lf-lsubst-binary ( first second walk -- outcome ) >r swap r> walk-children ;
: lf-lsubst-refused ( first second walk tag outcome -- outcome ) >r 2drop 2drop r> ;
: lf-lsubst-dispatch ( first second walk tag -- outcome )
  over lf-lsubst-mark dup ok? 0= if lf-lsubst-refused exit then drop
  dup lf-level-binary-tag? if drop lf-lsubst-binary exit then
  case lf-level-tag-zero of lf-lscope-zero endof
    lf-level-tag-param of lf-lsubst-param endof
    lf-level-tag-succ of lf-lscope-succ endof walk-bad-tag endcase ;
: lf-lsubst-visit ( walk -- outcome ) lf-levels ['] lf-lsubst-dispatch walk-visit ;

\ Check the DAG reachable from root against the formals, with the fuel in
\ lf-lsubst-fuel. The zero node is checked even when root does not reach it.
: lf-lsubst-ready? ( root -- flag ) lf-level-valid? lf-lscope-zero-ok? and ;
\ A new walk takes a new stamp, so that no node counts as reached, and
\ lists nothing yet. Stamps start at 1 (a new unit is 0); only when they
\ would run out is the column erased and they restart.
: lf-lsubst-restamp ( -- ) lf-lsubst-seen-column column-erase 0 lf-lsubst-stamp ! ;
: lf-lsubst-unseen ( -- )
  lf-lsubst-stamp @ max-n = if lf-lsubst-restamp then
  1 lf-lsubst-stamp +! 0 lf-lsubst-reached ! ;
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
\ The reached nodes, sorted: the order of every index up to the root,
\ skipping the nodes not reached, at a cost of the nodes reached.
: lf-lsubst-node ( i -- index ) lf-lsubst-reached-cells slab-at @ ;
: lf-lsubst-sorted ( -- )
  0 lf-lsubst-reached-cells slab-at lf-lsubst-reached @ lf-cells-sort ;
: lf-lsubst-build ( -- outcome )
  lf-lsubst-sorted lf-lsubst-reached @ 0 ?do
    i lf-lsubst-node lf-lsubst-build-node dup ok? 0= if unloop exit then drop
  loop outcome-ok ;

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
  lf-lmk-sync lf-lsubst-build lf-lsubst-finish ;

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
