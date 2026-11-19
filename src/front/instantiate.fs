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
\   A smart-unfolding annotation (core/annotations.fs) is looked through
\   at the head and between lambdas while arguments are left (betaRev);
\   lf-meta-head-beta-keep ( term -- term' outcome ) keeps it there
\   instead (preserveMData, deltaBetaDefinition's smart path). Every walk
\   here carries an annotation with its key (Lean's mdata).
\ Each walk keeps its pending (node, depth) items on a heap stack and
\ makes the image of each pair once (a memo table, as the cache of Lean's
\ replace), so a DAG costs its size and no depth needs the host's stacks
\ (plan task 6.2.0). A value whose data word is unknown (it holds a
\ metavariable) has its loose range computed by a walk of dag-walk.fs.
\ Outcomes: ok; invalid for a term that is not in the store; unsupported
\ as above; full when a store or the heap has no room. Untrusted.
\ Words: lf-meta-instantiate1, lf-meta-open ( binder x -- body outcome )
\ (a binder's body, its variable x), lf-meta-abstract, lf-meta-head-beta,
\ lf-meta-loose ( term --
\ range outcome ): 1 + the largest loose bound variable index, or 0.
\ State: the record in-state (instantiate1's value, abstract's terms,
\ head beta's mode, the loose walk and the rebuild walk, offset-walk.fs's
\ record) and the slab in-args, members of the checker context (ADR
\ 0009); the rebuild walk's blocks are freed with the context.

require ../lib/lib.fs
require ../core/terms.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../core/annotations.fs
require ../present/binder-table.fs
require ./dag-walk.fs
require ./meta-spine.fs
require ./offset-walk.fs

begin-structure /in
  field: in-abstracting        \ true: abstract (in-xs), else instantiate1
  field: in-value              \ the term for bound variable 0 (2! in in-set)
  field: in-xs                 \ abstract's terms: the address of their cells
  field: in-xs#                \ and how many
  field: in-lifts              \ true: the value has loose bound variables
  field: in-mdata              \ head beta: true keeps an annotation (preserveMData)
  /dw +field in-walk           \ the loose-range walk
  /ow +field in-replace        \ the rebuild walk
end-structure
/in context-record: in-state
1 cells context-slab: in-args      \ head-beta's arguments, last first
:noname ( -- ) in-state in-replace ow-free ; context-teardown

\ Loose ranges (Lean's looseBVarRange): a leaf's from itself, a node's
\ (an annotation's too: core/annotations.fs) from its data word when
\ known.
: in-leaf-range ( leaf -- range )
  dup lf-term-bvar? if lf-term-first@ 1+ else drop 0 then ;
: in-inner? ( node -- flag ) dup lf-term-binary? swap lf-annot? or ;
: in-range ( node -- range true | false )
  dup in-inner? 0= if in-leaf-range true exit then
  lf-term-data@ if lf-data-loose true else false then ;
: in-closed? ( node depth -- flag ) swap in-range if < 0= else drop false then ;
\ For abstract: a node known to hold no free variable or metavariable
\ (a metavariable makes a data word unknown).
: in-hole? ( leaf -- flag ) lf-fvar-mvar-tags lf-term-in? ;
: in-solid? ( node -- flag )
  dup in-inner? 0= if in-hole? 0= exit then
  lf-term-data@ if lf-data-fvar? 0= else false then ;
: in-abstracting? ( -- flag ) in-state in-abstracting @ ;
: in-kept? ( node depth -- flag ) in-abstracting? if drop in-solid? else in-closed? then ;

\ The loose range by a walk, for a node whose data word is unknown.
: in-loose-pending ( node walk -- child true | false )
  over in-inner? 0= if 2drop false exit then
  over lf-term-first@ over dw-want if nip nip true exit then
  over lf-annot? if 2drop false exit then
  swap lf-term-second@ swap dw-want ;
: in-loose-pair ( node walk -- range )
  over lf-term-first@ over dw-image >r swap dup lf-term-second@ rot dw-image
  swap lf-term-binder? + 0 max r> max ;
: in-loose-build ( node walk -- range )
  over lf-annot? if swap lf-annot-child swap dw-image exit then
  over lf-term-binary? if in-loose-pair else drop in-leaf-range then ;
' in-loose-build ' in-loose-pending 2constant in-loose-hooks
: in-loose-walk ( -- walk ) in-loose-hooks in-state in-walk dw-on-terms ;
: lf-meta-loose ( term -- range outcome )
  dup lf-term-root? 0= if drop -1 outcome-invalid exit then
  dup in-range if nip outcome-ok else in-loose-walk dw-run then ;

\ Images: a bound variable at the depth is the value, a larger one is
\ one less, a leaf is itself; a node whose parts change is rebuilt
\ (offset-walk.fs).
: in-made ( index true | false -- image ) room-result ow-fail ;
\ (A value with loose bound variables under binders would need lifting.)
: in-unlifted ( depth -- )
  0> in-state in-lifts @ and if outcome-unsupported ow-fail then ;
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
' in-kept? ' in-leaf ' false ow-kind constant in-kind
: in-run ( body -- term outcome ) in-kind in-state in-replace ow-run ;
: in-set ( value abstracting? -- ) in-state in-abstracting 2! ;
: in-value-ok ( value -- outcome )
  lf-meta-loose dup ok? if drop 0> in-state in-lifts ! outcome-ok else nip then ;
: lf-meta-instantiate1 ( body value -- term outcome )
  2dup lf-term-pair-valid? 0= if 2drop -1 outcome-invalid exit then
  dup in-value-ok ok-then? 0= if nip no-result exit then
  false in-set in-run ;
\ A binder's body opened with x for its variable (Lean's
\ bindingBody!.instantiate1 x, the step of every telescope).
: lf-meta-open ( binder x -- body outcome )
  swap lf-term-second@ swap lf-meta-instantiate1 ;
: in-xs! ( addr n -- ) in-state tuck in-xs# ! in-xs ! ;
: lf-meta-abstract ( term addr n -- term' outcome )
  dup 0< if 2drop drop -1 outcome-invalid exit then
  rot dup lf-term-root? 0= if drop 2drop -1 outcome-invalid exit then
  -rot in-xs! 0 true in-set in-run ;

\ Head beta: the arguments of f a1 .. an, last first, in in-args; each
\ lambda of f takes the next one; the rest are applied. An annotation
\ met while arguments are left is looked through (betaRev's
\ preserveMData false), or ends the lambdas (true, in-mdata).
: hb-arg ( i -- arg ) in-args slab-at @ ;
: hb-in ( f -- f' ) in-state in-mdata @ if exit then lf-annot-strip ;
\ isHeadBetaTargetFn: a lambda, also under annotations (headBeta);
\ with in-mdata (deltaBetaDefinition's betaRev) the head itself.
: hb-lam? ( f -- flag ) hb-in lf-term-lam? ;
: hb-open ( f -- body ) hb-in lf-term-second@ ;
: hb-beta ( f i -- f' i' outcome ) >r hb-open r@ hb-arg lf-meta-instantiate1 r> 1- swap ;
\ The lambdas f opens with, at most n: betaRev's go counts them on f
\ itself, never on what an instantiation makes.
: hb-depth ( f n -- m )
  0 swap 0 ?do over hb-lam? 0= if leave then 1+ swap hb-open swap loop nip ;
: hb-beta-k ( f i k -- f' i' outcome ) drop hb-beta ;
: hb-lams ( f i m -- f' i' outcome ) ['] hb-beta-k ok-each ;
: hb-apply ( f i -- f' outcome )
  begin dup 0< 0= while >r r@ hb-arg lf-term-app 0= if r> drop -1 outcome-full exit then
  r> 1- repeat drop outcome-ok ;
: hb-rest ( f i -- f' outcome ) dup 0< 0= if swap hb-in swap then hb-apply ;
: hb-reduce ( f -- f' outcome )
  dup in-args slab-count hb-depth >r in-args slab-count 1- r> hb-lams
  ok-then2? if hb-rest else no-result then ;
: hb-target ( term -- term' outcome )
  dup in-args lf-meta-spine ok-then? 0= if nip no-result exit then
  dup hb-lam? if nip hb-reduce else drop outcome-ok then ;
: hb-run ( term keep -- term' outcome )
  in-state in-mdata ! dup lf-term-root? if hb-target else drop -1 outcome-invalid then ;
: lf-meta-head-beta ( term -- term' outcome ) false hb-run ;
: lf-meta-head-beta-keep ( term -- term' outcome ) true hb-run ;
