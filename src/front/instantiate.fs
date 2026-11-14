\ Bound-variable instantiation and abstraction of the front end (plan
\ FE1c; ADR 0021 D6), ports of Lean 4.35.0's Expr.instantiate1 (Lean/Expr
\ .lean, the extern lean_expr_instantiate1: kernel/instantiate.cpp's
\ instantiate, which Meta uses too), Expr.abstract (lean_expr_abstract,
\ kernel/abstract.cpp) and Expr.headBeta (Lean/Expr.lean's betaRev,
\ without its mdata and zeta options) over the term store.
\ - lf-meta-instantiate1 ( body value -- term outcome ): body's loose
\   bound variable 0 becomes value, each larger loose index one less. A
\   subterm with no loose bound variable at its depth is kept (Lean's
\   get_loose_bvar_range test, from the data word, terms.fs), so is a
\   node whose parts do not change; a rebuilt binder keeps its name and
\   kind (present/binder-table.fs). A value with loose bound variables
\   (instantiateMVars meets one: an argument under the binders of the
\   term it instantiates, as fun h => ?n h after intro, plan FE1g-4) is
\   put in as it is where no binder of body lies around the variable;
\   under one Lean lifts it (lift_loose_bvars), which is not ported: such
\   a value there answers unsupported.
\ - lf-meta-abstract ( term addr n -- term' outcome ): the n terms in
\   cells at addr, x0 .. xn-1 (free variables or metavariables), become
\   loose bound variables, xn-1 the innermost: under k binders xi is
\   #(k + n - 1 - i), the last match winning, as Lean's loop from the
\   end; a subterm known to hold no free variable or metavariable (its
\   data word) is kept. Lean's abstract instantiates no metavariable, and
\   neither does this.
\ - lf-meta-head-beta ( term -- term' outcome ): for f a1 .. an with f a
\   lambda, each lambda of f takes the next argument (instantiate1; for
\   closed arguments the same term as Lean's instantiate of them all at
\   once) and the arguments left over are applied to the result; any other
\   term is itself. One step, as Lean's headBeta (whnfCore repeats it).
\ Each walk keeps its pending (node, depth) items on a heap stack and
\ makes the image of each pair once (a memo table, as the cache of Lean's
\ replace), so a DAG costs its size and no depth needs the host's stacks
\ (plan task 6.2.0). A value whose data word is unknown (it holds a
\ metavariable) has its loose range computed by a walk of dag-walk.fs.
\ Outcomes: ok; invalid for a term that is not in the store; unsupported
\ as above; full when a store or the heap has no room. Untrusted.
\ Words: lf-meta-instantiate1, lf-meta-abstract, lf-meta-head-beta,
\ lf-meta-loose ( term --
\ range outcome ): 1 + the largest loose bound variable index, or 0.
\ State: the record in-state (with the memo's hash table and the loose
\ walk), the slabs in-memo, in-pending and in-args: members of the
\ checker context (ADR 0009). The table is made afresh for each walk
\ (its hooks record lives in in-state) and freed with the context.

require ../lib/lib.fs
require ../lib/htab.fs
require ../lib/hash32.fs
require ../core/terms.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../present/binder-table.fs
require ./dag-walk.fs
require ./meta-spine.fs

begin-structure /in
  field: in-value              \ the term put in for bound variable 0
  field: in-abstracting        \ true: abstract (in-xs), else instantiate1
  field: in-xs                 \ abstract's terms: the address of their cells
  field: in-xs#                \ and how many
  field: in-outcome            \ ok, or the walk's first failure
  field: in-lifts              \ true: the value has loose bound variables
  2 cells +field in-key        \ the (node depth) sought in the memo
  /htab-hooks +field in-hooks  \ the memo table's hooks
  /htab +field in-table        \ the memo: (node depth) to its entry
  /dw +field in-walk           \ the loose-range walk
end-structure
/in context-record: in-state
3 cells context-slab: in-memo      \ entries: node depth image
2 cells context-slab: in-pending   \ the walk's stack: node depth
1 cells context-slab: in-args      \ head-beta's arguments, last first
:noname ( -- ) in-state in-table htab-free ; context-teardown

: in-fail ( outcome -- ) in-state in-outcome outcome-first! ;

\ Loose ranges (Lean's looseBVarRange): a leaf's from itself, a node's
\ from its data word when known.
: in-leaf-range ( leaf -- range )
  dup lf-term-bvar? if lf-term-first@ 1+ else drop 0 then ;
: in-range ( node -- range true | false )
  dup lf-term-binary? 0= if in-leaf-range true exit then
  lf-term-data@ if lf-data-loose true else false then ;
: in-closed? ( node depth -- flag ) swap in-range if < 0= else drop false then ;
\ For abstract: a node known to hold no free variable or metavariable
\ (a metavariable makes a data word unknown).
: in-hole? ( leaf -- flag ) lf-term-tag@ dup lf-tag-fvar = swap lf-tag-mvar = or ;
: in-solid? ( node -- flag )
  dup lf-term-binary? 0= if in-hole? 0= exit then
  lf-term-data@ if lf-data-fvar? 0= else false then ;
: in-abstracting? ( -- flag ) in-state in-abstracting @ ;
: in-kept? ( node depth -- flag ) in-abstracting? if drop in-solid? else in-closed? then ;

\ The loose range by a walk, for a node whose data word is unknown.
: in-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: in-loose-pending ( node walk -- child true | false )
  over lf-term-binary? 0= if 2drop false exit then
  over lf-term-first@ over in-undone if nip nip true exit then
  swap lf-term-second@ swap in-undone ;
: in-loose-pair ( node walk -- range )
  over lf-term-first@ over dw-image >r swap dup lf-term-second@ rot dw-image
  swap lf-term-binder? + 0 max r> max ;
: in-loose-build ( node walk -- range )
  over lf-term-binary? if in-loose-pair else drop in-leaf-range then ;
: in-loose-walk ( -- walk )
  in-state in-walk ['] in-loose-build over dw-build !
  ['] in-loose-pending over dw-pending ! lf-term-base lf-term-count @ + over dw-size ! ;
: lf-meta-loose ( term -- range outcome )
  dup lf-term-root? 0= if drop -1 outcome-invalid exit then
  dup in-range if nip outcome-ok else in-loose-walk dw-run then ;

\ The memo: entries in a slab, found through a hash table by (node depth).
: in-entry ( n -- addr ) in-memo slab-at ;
: in-hash ( node depth -- h ) swap hash-fmix swap hash-step ;
: in-rehash ( n htab -- h ) drop in-entry 2@ in-hash ;
: in-same ( n key htab -- flag ) drop swap in-entry 2@ rot 2@ d= ;
: in-hooks-made ( -- hooks )
  ['] in-rehash ['] in-same in-state in-hooks htab-hooks! in-state in-hooks ;
: in-tab ( -- htab ) in-state in-table ;
: in-table-make ( -- outcome ) in-tab htab-free 4 in-hooks-made in-tab htab-init ;
: in-sought ( -- addr ) in-state in-key ;
: in-find ( node depth -- n true | i false )
  2dup in-sought 2! in-hash in-sought swap in-tab htab-find ;
: in-image? ( node depth -- image true | false )
  2dup in-kept? if drop true exit then
  in-find if in-entry 2 cells + @ true else drop false then ;
: in-ready? ( node depth -- flag ) in-image? dup if nip then ;
: in-image ( node depth -- image ) in-image? drop ;
\ Keep the image of a pair not in the memo: ok, or full.
: in-room ( -- outcome ) in-tab htab-ready dup ok? if drop 1 in-memo slab-room then ;
: in-entry! ( node depth image n -- ) in-entry tuck 2 cells + ! 2! ;
: in-claim ( node depth image -- n ) 1 in-memo slab-claim drop dup >r in-entry! r> ;
: in-keep ( node depth image -- outcome )
  in-room dup ok? 0= if nip nip nip exit then drop
  in-claim dup in-entry 2@ in-find drop in-tab htab-put outcome-ok ;

\ The stack.
: in-top ( -- node depth ) in-pending slab-last 2@ ;
: in-pop ( -- ) in-pending slab-drop ;
: in-push ( node depth -- ) in-pending slab-2push in-fail ;
: in-push-if ( node depth -- pushed? )
  2dup in-ready? if 2drop false else in-push true then ;

\ Images: a bound variable at the depth is the value, a larger one is
\ one less, a leaf is itself; a node whose parts change is rebuilt.
: in-made ( index true | false -- image ) 0= if outcome-full in-fail -1 then ;
\ (A value with loose bound variables under binders would need lifting.)
: in-unlifted ( depth -- )
  0> in-state in-lifts @ and if outcome-unsupported in-fail then ;
: in-bvar ( node depth -- image )
  swap lf-term-first@ tuck = if in-unlifted in-state in-value @ exit then
  1- lf-term-bvar in-made ;
: in-x ( i -- x ) cells in-state in-xs @ + @ ;
: in-count ( -- n ) in-state in-xs# @ ;
: in-xs-index ( leaf -- i true | false )
  in-count begin dup while 1- 2dup in-x = if nip true exit then repeat 2drop false ;
\ xi under depth binders: #(depth + n - 1 - i).
: in-index ( depth i -- k ) in-count swap - 1- + ;
: in-abstract-leaf ( node depth -- image )
  over in-xs-index if in-index nip lf-term-bvar in-made else drop then ;
: in-instantiate-leaf ( node depth -- image )
  over lf-term-bvar? if in-bvar else drop then ;
: in-leaf ( node depth -- image )
  in-abstracting? if in-abstract-leaf else in-instantiate-leaf then ;
: in-first ( node depth -- child depth ) swap lf-term-first@ swap ;
: in-second ( node depth -- child depth' )
  over lf-term-binder? - swap lf-term-second@ swap ;
: in-images ( node depth -- i1 i2 )
  2dup in-first in-image >r in-second in-image r> swap ;
: in-same-pair? ( i1 i2 node -- i1 i2 flag )
  >r 2dup r@ lf-term-second@ = swap r> lf-term-first@ = and ;
: in-named ( new old -- new ) lf-meta-named in-fail ;
: in-rebuild ( i1 i2 node -- image )
  dup >r lf-term-tag@ lf-term-binary
  if r> in-named else r> drop outcome-full in-fail -1 then ;
: in-pair-image ( node depth -- image )
  over >r in-images r@ in-same-pair? if 2drop r> exit then r> in-rebuild ;

\ One step on the top pair: done already, a child first, or made.
: in-done ( node depth image -- ) in-keep in-fail in-pop ;
: in-step-pair ( node depth -- )
  2dup in-first in-push-if if 2drop exit then
  2dup in-second in-push-if if 2drop exit then 2dup in-pair-image in-done ;
: in-step ( -- )
  in-top 2dup in-ready? if 2drop in-pop exit then
  over lf-term-binary? if in-step-pair else 2dup in-leaf in-done then ;
: in-busy? ( -- flag ) in-pending slab-count 0> in-state in-outcome @ ok? and ;
: in-start ( value abstracting? -- outcome )
  in-state tuck in-abstracting ! tuck in-value ! outcome-ok swap in-outcome !
  in-memo slab-clear in-pending slab-clear in-table-make ;
: in-run ( body -- term outcome )
  dup 0 in-push begin in-busy? while in-step repeat
  in-state in-outcome @ dup ok? if drop 0 in-image outcome-ok else nip no-result then ;
: in-value-ok ( value -- outcome )
  lf-meta-loose dup ok? if drop 0> in-state in-lifts ! outcome-ok else nip then ;
: lf-meta-instantiate1 ( body value -- term outcome )
  2dup lf-term-pair-valid? 0= if 2drop -1 outcome-invalid exit then
  dup in-value-ok ok-then? 0= if nip no-result exit then
  false in-start ok-then? if in-run else no-result then ;
: in-xs! ( addr n -- ) in-state tuck in-xs# ! in-xs ! ;
: lf-meta-abstract ( term addr n -- term' outcome )
  dup 0< if 2drop drop -1 outcome-invalid exit then
  rot dup lf-term-root? 0= if drop 2drop -1 outcome-invalid exit then
  -rot in-xs! 0 true in-start ok-then? if in-run else no-result then ;

\ Head beta: the arguments of f a1 .. an, last first, in in-args; each
\ lambda of f takes the next one; the rest are applied.
: hb-arg ( i -- arg ) in-args slab-at @ ;
: hb-beta ( f i -- f' i' outcome )
  >r lf-term-second@ r@ hb-arg lf-meta-instantiate1 r> 1- swap ;
\ The lambdas f opens with, at most n: betaRev's go counts them on f
\ itself, never on what an instantiation makes.
: hb-depth ( f n -- m )
  0 swap 0 ?do over lf-term-lam? 0= if leave then 1+ swap lf-term-second@ swap loop nip ;
: hb-beta-k ( f i k -- f' i' outcome ) drop hb-beta ;
: hb-lams ( f i m -- f' i' outcome ) ['] hb-beta-k ok-each ;
: hb-apply ( f i -- f' outcome )
  begin dup 0< 0= while >r r@ hb-arg lf-term-app 0= if r> drop -1 outcome-full exit then
  r> 1- repeat drop outcome-ok ;
: hb-reduce ( f -- f' outcome )
  dup in-args slab-count hb-depth >r in-args slab-count 1- r> hb-lams
  ok-then2? if hb-apply else no-result then ;
: hb-target ( term -- term' outcome )
  dup in-args lf-meta-spine ok-then? 0= if nip no-result exit then
  dup lf-term-lam? if nip hb-reduce else drop outcome-ok then ;
: lf-meta-head-beta ( term -- term' outcome )
  dup lf-term-root? if hb-target else drop -1 outcome-invalid then ;
