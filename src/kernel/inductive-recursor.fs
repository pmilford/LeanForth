\ The recursors of a block of inductive types -- one, or several in a
\ mutual block -- built as Lean 4.35.0's kernel builds them
\ (inductive.cpp, commit eb6cafb7: mk_rec_infos 632-717,
\ declare_recursors 795-819, mk_rec_rules 748-793; plan tasks 5.2.1a,
\ 5.2.1b and 5.2.5a, ADR 0015 rules G1 and G2). Lean builds with free
\ variables and abstracts them (mk_pi, mk_lambda); LeanForth builds the
\ same terms directly with bound variables. With p parameters, M types,
\ type d's n_d indices and m constructors over the block, motive universe
\ u (or Prop), for each type T_d:
\   T_d.rec : (As : D_0 .. D_p-1) -> (motives Cs : MT_0 .. MT_M-1)
\           -> (minor_0 .. minor_m-1) -> (is : I_d) -> (t : T_d As is)
\           -> motive_d is t
\   MT_d  = (is : I_d) -> (t : T_d As is) -> Sort u
\   minor_j : (b : F_0 .. F_k-1) -> (v : IH_0 .. IH_r-1) -> motive_o js (c_j As b)
\           for c_j : (As) -> (b : F_0 .. F_k-1) -> T_o As js
\   IH_i  = (xs : X_0 .. X_s-1) -> motive_e ks (u xs)
\           for the i-th recursive field u : (xs : X_0 ..) -> T_e As ks
\   rule_j  = fun As Cs minors (b : F_0 ..) => minor_j b v'_0 .. v'_r-1
\   v'_i  = fun (xs : X_0 ..) => T_e.rec As Cs minors ks (u xs)
\ with the D_i the binder domains of the first type's telescope and I_d
\ type d's index domains (after
\ check-block.fs's whnf), the F_q of the constructor's raw telescope, and
\ the X_t and ks those of a recursive field's type in whnf, binder by
\ binder (is_rec_argument 426-433, mk_rec_infos 690-709, mk_rec_rules
\ 770-785). A field is recursive when that whnf ends in an application of
\ T; a field type that does not mention T is not, without reduction
\ (reduction never makes an occurrence). The block check found that whnf
\ there is whnfB (P1, P2), so this builder reduces with whnfB.
\ Every binder type of a local -- each D_i, F_q and X_t -- is first
\ stripped of outer type annotations, as Lean's mk_local_decl_for does
\ with consume_type_annotations (inductive.cpp 221-228; Lean/Expr.lean
\ 1717-1746): outParam _ and semiOutParam _ give their argument, optParam
\ _ _ and autoParam _ _ their first, repeatedly, matched by name at the
\ head. The recursor in a rule is T.rec at Lean's get_rec_levels: the
\ motive's universe parameter (when it has one), then the block's.
\ Binder names and annotations are not represented (Lean's == ignores
\ them).
\ The terms go into the term store as scratch above the input, live until
\ the check's rollback; nothing here is trusted: check-block.fs compares
\ them with the exported recursor (B3), as Lean's replay does.
\ [kernel] code: experimental, not through the review gate.
\ State: the block's record lf-ind-state (inductive-block.fs): the facts
\ check-block.fs computed; and here, in lf-rcr-state and its slabs, the
\ build's first failure, the universe arguments of its constants (the
\ block's, and the recursor's for the rules), the recursive fields of
\ every constructor (lf-rcr-ih-cells, with their x domains in
\ lf-rcr-x-cells and each constructor's first in lf-rcr-ih-starts), and
\ the one being built. A failure is sticky: once a node cannot be made,
\ every later step gives -1 and the build reports the first failure
\ (full, exhausted or invalid).

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/generation-handles.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/terms.fs
require ./inductive-block.fs
require ./mixed-beta.fs
require ./mixed-shift.fs

begin-structure /lf-rcr
  field: lf-rcr-status       \ the first failure of the build; ok while none
  field: lf-rcr-scratch-count  \ binder domains in the scratch
  field: lf-rcr-ctor-roots   \ the constructors' types to read, an array; 0: the input's
  field: lf-rcr-ih-count     \ recursive fields recorded
  field: lf-rcr-x-count      \ their x domains recorded
  field: lf-rcr-rec-count    \ the recursors' universe arguments, for the rules
  field: lf-rcr-q            \ the recursive field built on: its position
  field: lf-rcr-xs           \ its first x domain
  field: lf-rcr-s            \ its x domains
  field: lf-rcr-e            \ the type its type's end names
  field: lf-rcr-end          \ its type's end, T_e As ks
  field: lf-rcr-past         \ binders between the parameters and the fields there
  field: lf-rcr-gap          \ binders between the field and the place built at
end-structure
/lf-rcr context-record: lf-rcr-state
\ The scratch: domains about to be bound, as many as a telescope has.
1 cells context-slab: lf-rcr-scratch-cells
\ The type's levels, as many as it has universe parameters (no fixed limit).
2 cells context-slab: lf-rcr-pair-cells
\ The recursor's levels for its rules: the motive's (when it has one) first.
2 cells context-slab: lf-rcr-rec-pairs
\ A recursive field: its position among the constructor's fields, its
\ type's x domains (the first, in lf-rcr-x-cells, and how many), its end
\ and the type of the block that end names.
begin-structure /lf-ih
  field: lf-ih-field
  field: lf-ih-first
  field: lf-ih-xs
  field: lf-ih-end
  field: lf-ih-type
end-structure
/lf-ih context-slab: lf-rcr-ih-cells
1 cells context-slab: lf-rcr-x-cells
\ Each constructor's first recursive field in lf-rcr-ih-cells, and the count.
1 cells context-slab: lf-rcr-ih-starts

: lf-rcr-ok? ( -- flag ) lf-rcr-state lf-rcr-status @ ok? ;
: lf-rcr-failing ( outcome -- -1 )
  lf-rcr-ok? if lf-rcr-state lf-rcr-status ! else drop then -1 ;
: lf-rcr-made ( index identity true | false -- node )
  if drop else outcome-full lf-rcr-failing then ;
\ A node as a handle; a dead node or -1 gets identity 0, which every
\ constructor refuses.
: lf-rcr-handle ( node -- node identity ) dup lf-term-identity 0= if 0 then ;
\ A binary node, tag lf-tag-app, lf-tag-lam or lf-tag-pi.
: lf-rcr-bind ( left right tag -- node )
  >r swap lf-rcr-handle rot lf-rcr-handle r> lf-hterm-binary lf-rcr-made ;
: lf-rcr-pi ( domain body -- node ) lf-tag-pi lf-rcr-bind ;
: lf-rcr-app ( function argument -- node ) lf-tag-app lf-rcr-bind ;
: lf-rcr-bvar ( k -- node ) lf-hterm-bvar lf-rcr-made ;
: lf-rcr-sort ( level -- node )
  dup lf-level-identity if lf-hterm-sort lf-rcr-made exit then
  drop outcome-full lf-rcr-failing ;
\ Shift the variables at or above cutoff by amount (none: the node
\ itself), on the block's fuel.
: lf-rcr-shifted ( index identity status -- node )
  lf-mshift-fuel @ lf-ind-fuel ! dup ok? if 2drop else nip nip lf-rcr-failing then ;
: lf-rcr-shift ( node cutoff amount -- node' )
  dup 0= if 2drop exit then
  rot lf-rcr-handle 2swap lf-ind-fuel @ lf-mixed-shift lf-rcr-shifted ;

\ ---------------------------------------------------------------------------
\ consume_type_annotations, by name at the head of an application spine.
: lf-rcr-named? ( node c-addr u -- flag )
  rot dup lf-tag-constant lf-ind-tag? 0= if drop 2drop false exit then
  lf-ind-const-name dup lf-name-prefix@ if drop 2drop false exit then
  dup lf-name-tag@ lf-name-tag-str = 0= if drop 2drop false exit then
  lf-name-text compare 0= ;
: lf-rcr-gadget? ( head n -- flag )
  dup 1 = if
    drop dup s" outParam" lf-rcr-named? swap s" semiOutParam" lf-rcr-named? or exit
  then
  2 = if dup s" optParam" lf-rcr-named? swap s" autoParam" lf-rcr-named? or
  else drop false then ;
\ The type an annotated node stands for: argument 0 of its spine.
: lf-rcr-unwrapped ( node n -- node' ) 0 lf-ind-arg ;
: lf-rcr-consume ( node -- node' )
  begin dup lf-ind-spine 2dup lf-rcr-gadget? while nip lf-rcr-unwrapped repeat 2drop ;

\ ---------------------------------------------------------------------------
\ Constants of the block at its universe parameters, as Lean's
\ mk_constant(name, m_levels): the parameters' levels, made once per
\ build.
: lf-rcr-pair ( k -- addr ) lf-rcr-pair-cells slab-at ;
: lf-rcr-level! ( k -- )
  dup lf-ind-lparam lf-level-param if dup lf-level-identity drop swap rot lf-rcr-pair 2!
  else drop outcome-full lf-rcr-failing drop then ;
: lf-rcr-levels ( -- )
  lf-ind-lparams nip dup lf-rcr-pair-cells slab-hold ok? 0=
  if drop outcome-full lf-rcr-failing drop exit then
  0 ?do i lf-rcr-level! loop ;
: lf-rcr-referenced ( index identity true | false -- node )
  if lf-cterm-new lf-rcr-made else outcome-full lf-rcr-failing then ;
: lf-rcr-const ( name -- node )
  lf-rcr-ok? 0= if drop -1 exit then
  lf-name-generation @ 0 lf-rcr-pair lf-ind-lparams nip lf-cref-new
  lf-rcr-referenced ;
\ f applied to the variables #(top), #(top-1), ... count of them.
: lf-rcr-apply-vars ( f top count -- node )
  0 ?do over over i - lf-rcr-bvar lf-rcr-app -rot nip loop drop ;
\ T.rec at the recursor's levels (get_rec_levels 720-725), for the rules:
\ the name, and the motive's level (when it has one) then the block's
\ parameters' levels, made once per build after lf-rcr-levels.
: lf-rcr-rec-pair ( k -- addr ) lf-rcr-rec-pairs slab-at ;
: lf-rcr-large ( -- 0|1 ) lf-ind-state lf-ind-large @ 0<> 1 and ;
: lf-rcr-elim-pair ( -- )
  lf-ind-state lf-ind-elim @ dup lf-level-identity drop swap 0 lf-rcr-rec-pair 2! ;
: lf-rcr-rec-pairs! ( -- )
  lf-ind-lparams nip lf-rcr-large + dup lf-rcr-state lf-rcr-rec-count !
  lf-rcr-rec-pairs slab-hold ok? 0= if outcome-full lf-rcr-failing drop exit then
  lf-rcr-large if lf-rcr-elim-pair then
  lf-ind-lparams nip 0 ?do i lf-rcr-pair 2@ i lf-rcr-large + lf-rcr-rec-pair 2! loop ;
\ T_e.rec, its name as the block check made it (step 6).
: lf-rcr-rec-const ( e -- node )
  lf-rcr-ok? 0= if drop -1 exit then
  lf-ind-ty lf-ty-rec-name @ lf-name-generation @ 0 lf-rcr-rec-pair
  lf-rcr-state lf-rcr-rec-count @ lf-cref-new lf-rcr-referenced ;

\ ---------------------------------------------------------------------------
\ The pieces. p parameters, M types (one motive each), m constructors,
\ type d's n_d indices.
: lf-rcr-p ( -- p ) lf-ind-nparams ;
\ Constructor j's type: the input's, or the caller's instance of it
\ (lf-recursor-build-at).
: lf-rcr-ctor-type ( j -- root )
  lf-rcr-state lf-rcr-ctor-roots @ ?dup if swap cells + @ else lf-ind-ctor-type then ;
: lf-rcr-mm ( -- M ) lf-ind-types@ ;
: lf-rcr-n ( d -- n ) lf-ind-n ;
: lf-rcr-m ( -- m ) lf-ind-ctors@ ;
: lf-rcr-dom ( i -- node ) lf-ind-domain @ ;
\ T_d As is, at depth depth: the parameters #(depth-1) .. #(depth-p),
\ then the indices, the innermost n_d binders, #(n_d-1) .. #0.
: lf-rcr-major ( depth d -- node )
  dup lf-ind-tname lf-rcr-const rot 1- lf-rcr-p lf-rcr-apply-vars
  swap lf-rcr-n dup 1- swap lf-rcr-apply-vars ;
\ Binding a telescope: the scratch holds the domains, outermost first;
\ wrapping binds them around body, innermost first, with tag.
: lf-rcr-scratch ( k -- addr ) cells lf-rcr-scratch-cells slab-base + ;
: lf-rcr-scratch# ( -- n ) lf-rcr-state lf-rcr-scratch-count @ ;
: lf-rcr-room ( n -- flag )
  dup lf-rcr-scratch-cells slab-hold ok? 0=
  if drop outcome-full lf-rcr-failing drop false exit then
  lf-rcr-state lf-rcr-scratch-count ! true ;
: lf-rcr-wrap ( body tag domain -- node tag ) swap >r swap r@ lf-rcr-bind r> ;
: lf-rcr-over-scratch ( body tag -- node tag )
  lf-rcr-scratch# 0 ?do lf-rcr-scratch# 1- i - lf-rcr-scratch @ lf-rcr-wrap loop ;
\ Type d's index domains, each shifted past amount binders inserted
\ between the parameters and the indices, and consumed.
: lf-rcr-index-dom ( d j amount -- node )
  >r tuck lf-ind-index-domain @ swap r> lf-rcr-shift lf-rcr-consume ;
: lf-rcr-indices! ( d amount -- )
  over lf-rcr-n lf-rcr-room 0= if 2drop exit then
  over lf-rcr-n 0 ?do 2dup i swap lf-rcr-index-dom i lf-rcr-scratch ! loop 2drop ;
\ Constructor j's fields: k of them; field q's domain is the domain of
\ the raw telescope's binder p+q, shifted past amount binders inserted
\ between the parameters and the fields, and consumed.
: lf-rcr-k ( j -- k ) lf-ind-nfields @ ;
: lf-rcr-skip ( node count -- node' ) 0 ?do lf-term-second@ loop ;
: lf-rcr-field-dom ( j q -- node )
  swap lf-rcr-ctor-type lf-rcr-p rot + lf-rcr-skip lf-term-first@ ;
: lf-rcr-field ( j q amount -- node )
  >r tuck lf-rcr-field-dom swap r> lf-rcr-shift lf-rcr-consume ;
: lf-rcr-fields! ( j amount -- )
  over lf-rcr-k lf-rcr-room 0= if 2drop exit then
  over lf-rcr-k 0 ?do 2dup i swap lf-rcr-field i lf-rcr-scratch ! loop 2drop ;

\ ---------------------------------------------------------------------------
\ Recursive fields (see the header): whnfB on the block's fuel; whether a
\ node mentions T; a Pi; an application of T.
: lf-rcr-reduced ( index identity status -- node )
  lf-mbeta-fuel @ lf-ind-fuel ! dup ok? if 2drop else nip nip lf-rcr-failing then ;
: lf-rcr-whnf ( node -- node' )
  lf-rcr-ok? 0= if drop -1 exit then
  lf-rcr-handle lf-ind-fuel @ lf-mixed-beta lf-rcr-reduced ;
: lf-rcr-mentions? ( node -- flag )
  lf-rcr-ok? 0= if drop false exit then
  lf-ind-occurrences dup ok? if drop 0<> else lf-rcr-failing 2drop false then ;
: lf-rcr-pi? ( node -- flag ) lf-rcr-ok? if lf-tag-pi lf-ind-tag? else drop false then ;
: lf-rcr-headed? ( node -- flag ) lf-rcr-ok? if lf-ind-headed? else drop false then ;
\ Recording an x domain, then a recursive field (full when the heap
\ refuses more room).
: lf-rcr-x ( i -- addr ) lf-rcr-x-cells slab-at ;
: lf-rcr-xs@ ( -- i ) lf-rcr-state lf-rcr-x-count @ ;
: lf-rcr-x! ( node -- )
  lf-rcr-xs@ dup 1+ lf-rcr-x-cells slab-hold ok? 0=
  if 2drop outcome-full lf-rcr-failing drop exit then
  lf-rcr-x ! 1 lf-rcr-state lf-rcr-x-count +! ;
: lf-rcr-ih ( k -- entry ) lf-rcr-ih-cells slab-at ;
\ The type an end T_e As ks names: e.
: lf-rcr-target ( end -- e ) lf-ind-spine drop lf-ind-which ;
: lf-rcr-ih! ( q first s end -- )
  lf-rcr-state lf-rcr-ih-count @ dup 1+ lf-rcr-ih-cells slab-hold ok? 0=
  if drop 2drop 2drop outcome-full lf-rcr-failing drop exit then
  lf-rcr-ih >r dup lf-rcr-target r@ lf-ih-type ! r@ lf-ih-end ! r@ lf-ih-xs !
  r@ lf-ih-first ! r> lf-ih-field ! 1 lf-rcr-state lf-rcr-ih-count +! ;
\ A type in whnfB, binder by binder: its Pis' domains recorded as x
\ domains, its end given.
: lf-rcr-telescope ( node -- end )
  lf-rcr-whnf begin dup lf-rcr-pi? while
    dup lf-term-first@ lf-rcr-x! lf-term-second@ lf-rcr-whnf
  repeat ;
: lf-rcr-since ( first -- first s ) lf-rcr-xs@ over - ;
\ Field q of constructor j, its type read under the constructor's p+q
\ binders: recorded when recursive, its x domains given back otherwise.
: lf-rcr-field-ih ( j q -- )
  2dup lf-rcr-field-dom lf-rcr-mentions? 0= if 2drop exit then
  tuck lf-rcr-field-dom lf-rcr-consume lf-rcr-xs@ swap lf-rcr-telescope
  dup lf-rcr-headed? if >r lf-rcr-since r> lf-rcr-ih! exit then
  drop lf-rcr-state lf-rcr-x-count ! drop ;
\ Every constructor's recursive fields, when scan? (a block without a
\ field mentioning T has none: its constructors are not scanned).
: lf-rcr-start ( j -- addr ) lf-rcr-ih-starts slab-at ;
: lf-rcr-ctor-ihs ( j scan? -- )
  over lf-rcr-state lf-rcr-ih-count @ swap lf-rcr-start !
  if dup lf-rcr-k 0 ?do dup i lf-rcr-field-ih loop then drop ;
: lf-rcr-ihs ( scan? -- )
  0 lf-rcr-state lf-rcr-ih-count ! 0 lf-rcr-state lf-rcr-x-count !
  lf-rcr-m 1+ lf-rcr-ih-starts slab-hold ok? 0=
  if drop outcome-full lf-rcr-failing drop exit then
  lf-rcr-m 0 ?do i over lf-rcr-ctor-ihs loop drop
  lf-rcr-state lf-rcr-ih-count @ lf-rcr-m lf-rcr-start ! ;
\ Constructor j's recursive fields: r of them, the i-th.
: lf-rcr-r ( j -- r ) dup 1+ lf-rcr-start @ swap lf-rcr-start @ - ;
: lf-rcr-ih-of ( j i -- entry ) swap lf-rcr-start @ + lf-rcr-ih ;
: lf-rcr-kr ( j -- k+r ) dup lf-rcr-k swap lf-rcr-r + ;

\ Building on a recursive field (lf-rcr-take): its pieces, read under the
\ constructor's p+q binders and the x binders before them, are relocated
\ to a place past more binders: past between the parameters and the
\ fields (the motive and minor premises), gap between field q and the
\ place. A node under s' x binders: variables of the fields before q
\ move by gap, of the parameters by past + gap (two shifts).
: lf-rcr-take ( entry -- )
  dup lf-ih-field @ lf-rcr-state lf-rcr-q ! dup lf-ih-first @ lf-rcr-state lf-rcr-xs !
  dup lf-ih-xs @ lf-rcr-state lf-rcr-s ! dup lf-ih-type @ lf-rcr-state lf-rcr-e !
  lf-ih-end @ lf-rcr-state lf-rcr-end ! ;
: lf-rcr-q@ ( -- q ) lf-rcr-state lf-rcr-q @ ;
: lf-rcr-s@ ( -- s ) lf-rcr-state lf-rcr-s @ ;
: lf-rcr-e@ ( -- e ) lf-rcr-state lf-rcr-e @ ;
: lf-rcr-place! ( past gap -- ) lf-rcr-state lf-rcr-gap ! lf-rcr-state lf-rcr-past ! ;
\ Take hypothesis i of minor j and place it past past binders, extra more
\ than its constructor's k fields after it: the gap is k + extra - q.
: lf-rcr-gap-of ( j extra -- gap ) swap lf-rcr-k + lf-rcr-q@ - ;
: lf-rcr-place ( j i past extra -- )
  >r >r over swap lf-rcr-ih-of lf-rcr-take r> swap r> lf-rcr-gap-of lf-rcr-place! ;
: lf-rcr-relocate ( node s' -- node' )
  tuck lf-rcr-q@ + lf-rcr-state lf-rcr-past @ lf-rcr-shift
  swap lf-rcr-state lf-rcr-gap @ lf-rcr-shift ;
\ X_t consumed, and argument p+t of the end T_e As ks (index t), each
\ relocated.
: lf-rcr-x-dom ( t -- node )
  dup lf-rcr-state lf-rcr-xs @ + lf-rcr-x @ swap lf-rcr-relocate lf-rcr-consume ;
: lf-rcr-k-arg ( t -- node )
  lf-rcr-state lf-rcr-end @ lf-rcr-p lf-rcr-e@ lf-rcr-n + rot lf-rcr-p + lf-ind-arg
  lf-rcr-s@ lf-rcr-relocate ;
\ Under the x binders: the first motive is #b (lf-rcr-base), motive e
\ #(b-e), the field u #(gap+s-1), the xs #(s-1) .. #0.
: lf-rcr-base ( -- b )
  lf-rcr-state lf-rcr-past @ lf-rcr-q@ + lf-rcr-state lf-rcr-gap @ + lf-rcr-s@ + 1- ;
: lf-rcr-ks ( f -- node ) lf-rcr-e@ lf-rcr-n 0 ?do i lf-rcr-k-arg lf-rcr-app loop ;
: lf-rcr-u-xs ( -- node )
  lf-rcr-state lf-rcr-gap @ lf-rcr-s@ + 1- lf-rcr-bvar
  lf-rcr-s@ dup 1- swap lf-rcr-apply-vars ;
\ The x binders around body, innermost first, with tag.
: lf-rcr-over-xs ( body tag -- node )
  lf-rcr-s@ 0 ?do lf-rcr-s@ 1- i - lf-rcr-x-dom lf-rcr-wrap loop drop ;
\ The outer binders of every recursor's type and of every rule: the
\ parameters (consumed), the M motives, the m minor premises.
: lf-rcr-param-dom ( i -- node ) lf-rcr-dom lf-rcr-consume ;
: lf-rcr-over-minors ( body tag -- node tag )
  lf-rcr-m 0 ?do lf-rcr-m 1- i - lf-ind-minor-type @ lf-rcr-wrap loop ;
: lf-rcr-over-motives ( body tag -- node tag )
  lf-rcr-mm 0 ?do lf-rcr-mm 1- i - lf-ind-ty lf-ty-motive @ lf-rcr-wrap loop ;
: lf-rcr-over-params ( body tag -- node tag )
  lf-rcr-p 0 ?do lf-rcr-p 1- i - lf-rcr-param-dom lf-rcr-wrap loop ;
: lf-rcr-outer ( body tag -- node )
  lf-rcr-over-minors lf-rcr-over-motives lf-rcr-over-params drop ;

\ Type d's motive, at depth p+d (the earlier motives before it): (is) ->
\ (t : T_d As is) -> Sort u.
: lf-rcr-elim-sort ( -- node ) lf-ind-state lf-ind-elim @ lf-rcr-sort ;
: lf-rcr-motive-type ( d -- node )
  dup dup lf-rcr-n + lf-rcr-p + over lf-rcr-major lf-rcr-elim-sort lf-rcr-pi
  swap dup lf-rcr-indices! lf-tag-pi lf-rcr-over-scratch drop ;

\ Minor premise j, of a constructor of type o, at depth p+M+j: (b) -> (v)
\ -> motive_o js (c_j As b), with k fields and r induction hypotheses,
\ its body at depth d = p+M+j+k+r, where motive_o is #(M+j+k+r-1-o), the
\ indices js are the constructor result's (shifted past the motives and
\ the j earlier minors, then past the r hypotheses), the parameters
\ #(d-1) .. #(d-p) and the fields #(k-1+r) .. #r.
: lf-rcr-result ( j -- node ) dup lf-rcr-ctor-type swap lf-rcr-k lf-rcr-p + lf-rcr-skip ;
: lf-rcr-js ( j i -- node )
  over lf-rcr-result lf-rcr-p 3 pick lf-ind-owner lf-rcr-n + rot lf-rcr-p + lf-ind-arg
  over lf-rcr-k 2 pick lf-rcr-mm + lf-rcr-shift 0 rot lf-rcr-r lf-rcr-shift ;
: lf-rcr-motive-app ( j -- node )
  dup dup lf-rcr-kr + lf-rcr-mm + 1- over lf-ind-owner - lf-rcr-bvar
  over lf-ind-owner lf-rcr-n 0 ?do over i lf-rcr-js lf-rcr-app loop nip ;
: lf-rcr-intro ( j d -- node )
  over lf-ind-ctor lf-idecl-name @ lf-rcr-const swap 1- lf-rcr-p lf-rcr-apply-vars
  swap dup lf-rcr-kr 1- swap lf-rcr-k lf-rcr-apply-vars ;
: lf-rcr-minor-depth ( j -- d ) dup lf-rcr-kr + lf-rcr-p + lf-rcr-mm + ;
: lf-rcr-minor-body ( j -- node )
  dup lf-rcr-motive-app over dup lf-rcr-minor-depth lf-rcr-intro lf-rcr-app nip ;
\ Hypothesis i of minor j, into type e, at depth p+M+j+k+i (past M+j, gap
\ k+i-q): (xs) -> motive_e ks (u xs).
: lf-rcr-ih-type ( j i -- node )
  over lf-rcr-mm + over lf-rcr-place
  lf-rcr-base lf-rcr-e@ - lf-rcr-bvar lf-rcr-ks lf-rcr-u-xs lf-rcr-app
  lf-tag-pi lf-rcr-over-xs ;
: lf-rcr-over-ihs ( body tag j -- node tag )
  dup lf-rcr-r 0 ?do
    dup dup lf-rcr-r 1- i - lf-rcr-ih-type swap >r lf-rcr-wrap r>
  loop drop ;
: lf-rcr-minor ( j -- node )
  dup lf-rcr-minor-body lf-tag-pi rot dup >r lf-rcr-over-ihs
  r> dup lf-rcr-mm + lf-rcr-fields! lf-rcr-over-scratch drop ;

\ Type d's recursor's type: the goal motive_d is t at depth p+M+m+n_d+1,
\ #(M+m+n_d-d) applied to the indices #n_d .. #1 and the major premise
\ #0, under the major premise, the indices (shifted past the motives and
\ the minors) and the outer binders.
: lf-rcr-goal ( d -- node )
  dup lf-rcr-n dup >r lf-rcr-mm + lf-rcr-m + swap - lf-rcr-bvar r> dup lf-rcr-apply-vars
  0 lf-rcr-bvar lf-rcr-app ;
: lf-rcr-type ( d -- node )
  dup lf-rcr-p lf-rcr-mm + lf-rcr-m + over lf-rcr-n + swap lf-rcr-major
  over lf-rcr-goal lf-rcr-pi
  swap lf-rcr-mm lf-rcr-m + lf-rcr-indices! lf-tag-pi lf-rcr-over-scratch lf-rcr-outer ;

\ Rule j: fun As motives minors (b) => minor_j b v'_0 .. v'_r-1, the body
\ at depth p+M+m+k, where minor_j is #(m-1-j+k) and the fields (shifted
\ past the motives and the m minors) #(k-1) .. #0. The recursor call of
\ hypothesis i into type e, under its x binders (past M+m, gap k-q):
\ T_e.rec at the parameters #(b+p) .., the motives #b .., the minors
\ #(b-M) .., then ks and u xs.
: lf-rcr-rec-call ( -- node )
  lf-rcr-e@ lf-rcr-rec-const lf-rcr-base lf-rcr-p + lf-rcr-p lf-rcr-apply-vars
  lf-rcr-base lf-rcr-mm lf-rcr-apply-vars
  lf-rcr-base lf-rcr-mm - lf-rcr-m lf-rcr-apply-vars
  lf-rcr-ks lf-rcr-u-xs lf-rcr-app ;
: lf-rcr-v ( j i -- node )
  lf-rcr-mm lf-rcr-m + 0 lf-rcr-place lf-rcr-rec-call lf-tag-lam lf-rcr-over-xs ;
: lf-rcr-rule-body ( j -- node )
  dup lf-rcr-k lf-rcr-m 1- 2 pick - over + lf-rcr-bvar swap dup 1- swap lf-rcr-apply-vars
  over lf-rcr-r 0 ?do over i lf-rcr-v lf-rcr-app loop nip ;
: lf-rcr-rule ( j -- node )
  dup lf-rcr-rule-body swap lf-rcr-mm lf-rcr-m + lf-rcr-fields! lf-tag-lam
  lf-rcr-over-scratch lf-rcr-outer ;

\ Build every type's motive, the minor premises, every type's recursor's
\ type and, with rules?, the rules into the block's records, from the
\ facts check-block.fs computed (indices, domains, field counts,
\ elimination level): ok, or the first failure (full, exhausted,
\ invalid), the terms then unusable.
: lf-rcr-motives ( -- )
  lf-rcr-mm 0 ?do i lf-rcr-motive-type i lf-ind-ty lf-ty-motive ! loop ;
: lf-rcr-minors ( -- ) lf-rcr-m 0 ?do i lf-rcr-minor i lf-ind-minor-type ! loop ;
: lf-rcr-types ( -- ) lf-rcr-mm 0 ?do i lf-rcr-type i lf-ind-ty lf-ty-rec-type ! loop ;
: lf-rcr-rules ( -- ) lf-rcr-m 0 ?do i lf-rcr-rule i lf-ind-rule ! loop ;
: lf-rcr-terms ( rules? -- outcome )
  lf-rcr-motives lf-rcr-minors lf-rcr-types if lf-rcr-rules then
  lf-rcr-state lf-rcr-status @ ;
: lf-rcr-begin ( roots -- )
  outcome-ok lf-rcr-state lf-rcr-status ! lf-rcr-state lf-rcr-ctor-roots ! ;
: lf-recursor-build ( -- outcome )
  0 lf-rcr-begin lf-rcr-levels lf-rcr-rec-pairs!
  lf-ind-recursive? lf-rcr-ihs true lf-rcr-terms ;
\ The same instantiated, for a declaration after the block that uses the
\ recursor (generated-recursor.fs), which needs only its type: the
\ block's constants at the level pairs the caller put in the pair cells
\ (lf-rcr-pair, as many as the block has universe parameters), the
\ motive's Sort at lf-ind-elim, and the binder domains read from
\ instances of the block's types the caller made -- the type's in
\ lf-ind-domain, the constructors' at roots, one cell each -- with the
\ block's universe parameters replaced by the same levels. Its recursive
\ fields are found again on those instances, every constructor scanned.
: lf-recursor-build-at ( roots -- outcome )
  lf-rcr-begin true lf-rcr-ihs false lf-rcr-terms ;
