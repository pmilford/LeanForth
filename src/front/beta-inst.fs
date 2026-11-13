\ Instantiation with beta of the front end (plan FE1c; ADR 0021 D6): a
\ port of Lean 4.35.0's Expr.instantiateBetaRevRange
\ (Lean/Meta/InferType.lean), which inferType and Meta's telescopes use
\ to put arguments in for a type's bound variables.
\ lf-meta-instantiate-rev-beta ( body addr m -- term outcome ): the m
\ terms in cells at addr, a0 .. am-1, put in for body's loose bound
\ variables, #k (k < m, counted from the depth of each occurrence) by ak,
\ as Lean's instantiateRev, and each larger loose index m less; and where
\ an application's head is a bound variable, its image applied to its
\ arguments' images takes them by one head beta step (Lean's betaRev: a
\ motive put in for #1 in `#1 #0` becomes its body). A subterm with no
\ loose bound variable at its depth is kept (its data word tells), so is
\ a node whose parts do not change; a rebuilt binder keeps its name and
\ kind (present/binder-table.fs). The arguments must have no loose bound
\ variable, and a beta step under a binder whose arguments have one (Lean
\ lifts them, liftLooseBVars) answers unsupported, as front/instantiate.fs
\ does: never another term.
\ The walk keeps its pending (node, depth) items on a heap stack and makes
\ the image of each pair once (a memo table, as Lean's cache), so no depth
\ needs the host's stacks (plan task 6.2.0).
\ Outcomes: ok; invalid for a term that is not in the store (the body or
\ an argument) or a negative m; unsupported as above; full when a store or the heap has no
\ room. A failure gives -1 for the term. Untrusted.
\ State: the record ib-state (the arguments, the walk's outcome and the
\ memo's hash table) and the slabs ib-memo, ib-pending and ib-spine, in
\ the checker context. The table is made afresh for each walk and freed
\ with the context. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/htab.fs
require ../lib/hash32.fs
require ../core/terms.fs
require ../core/mvar-leaves.fs
require ../present/binder-table.fs
require ./instantiate.fs
require ./meta-spine.fs

begin-structure /ib
  field: ib-xs                 \ the arguments: the address of their cells
  field: ib-xs#                \ and how many
  field: ib-outcome            \ ok, or the walk's first failure
  2 cells +field ib-key        \ the (node depth) sought in the memo
  /htab-hooks +field ib-hooks  \ the memo table's hooks
  /htab +field ib-table        \ the memo: (node depth) to its entry
end-structure
/ib context-record: ib-state
3 cells context-slab: ib-memo      \ entries: node depth image
2 cells context-slab: ib-pending   \ the walk's stack: node depth
1 cells context-slab: ib-spine     \ the beta case's arguments, last first
:noname ( -- ) ib-state ib-table htab-free ; context-teardown

: ib-fail ( outcome -- ) ib-state ib-outcome dup @ ok? if ! else 2drop then ;
: ib-tag ( node -- tag ) lf-term-tag@ ;
: ib-binary? ( node -- flag ) ib-tag lf-term-binary-tag? ;
: ib-binder? ( node -- flag ) ib-tag lf-term-binder-tag? ;
: ib-bvar? ( node -- flag ) ib-tag lf-tag-bvar = ;
: ib-app? ( node -- flag ) ib-tag lf-tag-app = ;
: ib-head ( node -- head ) begin dup ib-app? while lf-term-first@ repeat ;
\ An application whose head is a bound variable: Lean's beta case.
: ib-beta? ( node -- flag ) dup ib-app? if ib-head ib-bvar? else drop false then ;

\ Kept as it is: no loose bound variable at the depth (a binary node's
\ data word, unknown when it holds a metavariable: then visited).
: ib-leaf-range ( leaf -- range ) dup ib-bvar? if lf-term-first@ 1+ else drop 0 then ;
: ib-range ( node -- range true | false )
  dup ib-binary? 0= if ib-leaf-range true exit then
  lf-term-data@ if lf-data-loose true else false then ;
: ib-closed? ( node depth -- flag ) swap ib-range if < 0= else drop false then ;

\ The memo: entries in a slab, found through a hash table by (node depth).
: ib-entry ( n -- addr ) ib-memo slab-at ;
: ib-hash ( node depth -- h ) swap hash-fmix swap hash-step ;
: ib-rehash ( n htab -- h ) drop ib-entry 2@ ib-hash ;
: ib-same ( n key htab -- flag ) drop swap ib-entry 2@ rot 2@ d= ;
: ib-hooks-made ( -- hooks )
  ['] ib-rehash ['] ib-same ib-state ib-hooks htab-hooks! ib-state ib-hooks ;
: ib-tab ( -- htab ) ib-state ib-table ;
: ib-table-make ( -- outcome ) ib-tab htab-free 4 ib-hooks-made ib-tab htab-init ;
: ib-sought ( -- addr ) ib-state ib-key ;
: ib-find ( node depth -- n true | i false )
  2dup ib-sought 2! ib-hash ib-sought swap ib-tab htab-find ;
: ib-image? ( node depth -- image true | false )
  2dup ib-closed? if drop true exit then
  ib-find if ib-entry 2 cells + @ true else drop false then ;
: ib-ready? ( node depth -- flag ) ib-image? dup if nip then ;
: ib-image ( node depth -- image ) ib-image? drop ;
: ib-room ( -- outcome ) ib-tab htab-ready dup ok? if drop 1 ib-memo slab-room then ;
: ib-entry! ( node depth image n -- ) ib-entry tuck 2 cells + ! 2! ;
: ib-claim ( node depth image -- n ) 1 ib-memo slab-claim drop dup >r ib-entry! r> ;
: ib-keep ( node depth image -- outcome )
  ib-room dup ok? 0= if nip nip nip exit then drop
  ib-claim dup ib-entry 2@ ib-find drop ib-tab htab-put outcome-ok ;

\ The stack.
: ib-top ( -- node depth ) ib-pending dup slab-count 1- swap slab-at 2@ ;
: ib-pop ( -- ) -1 ib-pending slab-commit ;
: ib-push ( node depth -- )
  1 ib-pending slab-claim dup ok?
  if drop ib-pending slab-at 2! else ib-fail drop 2drop then ;
: ib-push-if ( node depth -- pushed? )
  2dup ib-ready? if 2drop false else ib-push true then ;

\ Bound variables: #k below the depth is itself; one of the m an
\ argument; a larger one m less.
: ib-made ( index true | false -- image ) 0= if outcome-full ib-fail -1 then ;
: ib-x ( k -- x ) cells ib-state ib-xs @ + @ ;
: ib-m ( -- m ) ib-state ib-xs# @ ;
: ib-bvar ( node depth -- image )
  over lf-term-first@ swap - dup 0< if drop exit then
  dup ib-m < if nip ib-x exit then
  drop lf-term-first@ ib-m - lf-term-bvar ib-made ;
: ib-leaf ( node depth -- image ) over ib-bvar? if ib-bvar else drop then ;

\ Binary nodes: children's images, the node rebuilt when one changes.
: ib-first ( node depth -- child depth ) swap lf-term-first@ swap ;
: ib-second ( node depth -- child depth' ) over ib-binder? - swap lf-term-second@ swap ;
: ib-images ( node depth -- i1 i2 )
  2dup ib-first ib-image >r ib-second ib-image r> swap ;
: ib-same-pair? ( i1 i2 node -- i1 i2 flag )
  >r 2dup r@ lf-term-second@ = swap r> lf-term-first@ = and ;
: ib-rebuild ( i1 i2 node -- image )
  dup >r ib-tag lf-term-binary
  if r> lf-meta-named ib-fail else r> drop outcome-full ib-fail -1 then ;
: ib-pair-image ( node depth -- image )
  over >r ib-images r@ ib-same-pair? if 2drop r> exit then r> ib-rebuild ;

\ The beta case: the head's image applied to the spine's arguments'
\ images (each at the depth, in ib-spine, last first), one head beta step
\ taken when the head's image is a lambda (Lean's betaRev).
: ib-spine-fill ( node -- outcome )
  ib-spine slab-clear begin dup ib-app? while
    dup lf-term-second@ ib-spine lf-meta-push dup ok? 0= if nip exit then drop
    lf-term-first@ repeat drop outcome-ok ;
: ib-spine-arg ( i -- arg ) ib-spine dup slab-count 1- rot - swap slab-at @ ;
: ib-apply ( f depth -- f' )
  ib-spine slab-count 0 ?do
    i ib-spine-arg over ib-image rot swap lf-term-app ib-made swap
  loop drop ;
: ib-lam? ( term -- flag ) dup 0< if drop false else ib-tag lf-tag-lam = then ;
: ib-head-beta ( f -- f' )
  dup 0< if exit then lf-meta-head-beta dup ok? if drop else ib-fail drop -1 then ;
: ib-head-image ( node depth -- image ) swap ib-head swap ib-bvar ;
: ib-beta-apply ( himage depth -- image )
  over >r ib-apply r> ib-lam? if ib-head-beta then ;
: ib-beta-image ( node depth -- image )
  over ib-spine-fill dup ok? 0= if ib-fail 2drop -1 exit then drop
  tuck ib-head-image swap ib-beta-apply ;
: ib-arg ( node depth -- arg depth ) swap lf-term-second@ swap ;
: ib-args-pushed? ( node depth -- pushed? )
  false -rot begin over ib-app? while
    2dup ib-arg ib-push-if if rot drop true -rot then ib-first
  repeat 2drop ;

\ One step on the top pair: done already, a child first, or made.
: ib-done ( node depth image -- ) ib-keep ib-fail ib-pop ;
: ib-step-beta ( node depth -- )
  2dup ib-args-pushed? if 2drop exit then 2dup ib-beta-image ib-done ;
: ib-step-pair ( node depth -- )
  2dup ib-first ib-push-if if 2drop exit then
  2dup ib-second ib-push-if if 2drop exit then 2dup ib-pair-image ib-done ;
: ib-step ( -- )
  ib-top 2dup ib-ready? if 2drop ib-pop exit then
  over ib-beta? if ib-step-beta exit then
  over ib-binary? if ib-step-pair else 2dup ib-leaf ib-done then ;
: ib-busy? ( -- flag ) ib-pending slab-count 0> ib-state ib-outcome @ ok? and ;
: ib-start ( -- outcome )
  outcome-ok ib-state ib-outcome ! ib-memo slab-clear ib-pending slab-clear
  ib-table-make ;
: ib-run ( body -- term outcome )
  dup 0 ib-push begin ib-busy? while ib-step repeat
  ib-state ib-outcome @ dup ok? if drop 0 ib-image outcome-ok else nip no-result then ;

\ The arguments: terms with no loose bound variable.
: ib-xs! ( addr m -- ) ib-state tuck ib-xs# ! ib-xs ! ;
: ib-x-ok ( x -- outcome )
  dup lf-term-root? 0= if drop outcome-invalid exit then
  lf-meta-loose ok-then? if 0= if outcome-ok else outcome-unsupported then then ;
: ib-args-ok ( -- outcome ) outcome-ok ib-m 0 ?do i ib-x ib-x-ok outcome-and loop ;
: lf-meta-instantiate-rev-beta ( body addr m -- term outcome )
  dup 0< if 2drop drop -1 outcome-invalid exit then ib-xs!
  dup lf-term-root? 0= if drop -1 outcome-invalid exit then
  ib-args-ok dup ok? 0= if nip no-result exit then drop
  ib-m 0= if outcome-ok exit then ib-start ok-then? if ib-run else no-result then ;

base !   \ the BASE this file was loaded with
