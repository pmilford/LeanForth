\ The recursor of a block of one non-recursive inductive type, built as
\ Lean 4.35.0's kernel builds it (inductive.cpp, commit eb6cafb7:
\ mk_rec_infos 632-717, declare_recursors 795-819, mk_rec_rules 748-793;
\ plan task 5.2.1a, ADR 0015 rules G1 and G2). Lean builds with free
\ variables and abstracts them (mk_pi, mk_lambda); LeanForth builds the
\ same terms directly with bound variables. With p parameters, n indices
\ and m constructors, motive universe u (or Prop):
\   T.rec : (As : D_0 .. D_p-1) -> (motive : MT) -> (minor_0 .. minor_m-1)
\           -> (is : D_p .. D_p+n-1) -> (t : T As is) -> motive is t
\   MT    = (is : D_p ..) -> (t : T As is) -> Sort u
\   minor_j : (b : F_0 .. F_k-1) -> motive js (c_j As b)
\           for c_j : (As) -> (b : F_0 .. F_k-1) -> T As js
\   rule_j  = fun As motive minors (b : F_0 ..) => minor_j b
\ with the D_i the binder domains of the type's telescope (after
\ check-block.fs's whnf) and the F_q of the constructor's raw telescope.
\ Every binder type of a local -- each D_i and F_q -- is first stripped of
\ outer type annotations, as Lean's mk_local_decl_for does with
\ consume_type_annotations (inductive.cpp 221-228; Lean/Expr.lean
\ 1717-1746): outParam _ and semiOutParam _ give their argument, optParam
\ _ _ and autoParam _ _ their first, repeatedly, matched by name at the
\ head. Non-recursive blocks have no recursive field, so no induction
\ hypothesis and no call of the recursor in a rule; binder names and
\ annotations are not represented (Lean's == ignores them).
\ The terms go into the term store as scratch above the input, live until
\ the check's rollback; nothing here is trusted: check-block.fs compares
\ them with the exported recursor (B3), as Lean's replay does.
\ [kernel] code: experimental, not through the review gate.
\ State: the block's record lf-ind-state (inductive-block.fs): the facts
\ check-block.fs computed, and here the build's first failure and the
\ universe arguments of its constants. A failure is sticky: once a node
\ cannot be made, every later step gives -1 and the build reports the
\ first failure (full, exhausted or invalid).

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/generation-handles.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/terms.fs
require ./inductive-block.fs
require ./mixed-shift.fs

begin-structure /lf-rcr
  field: lf-rcr-status       \ the first failure of the build; ok while none
  field: lf-rcr-motive       \ the motive's type
  field: lf-rcr-scratch-count  \ binder domains in the scratch
  lf-ind-binder-capacity cells +field lf-rcr-scratch-cells   \ domains about to be bound
  lf-cref-argument-capacity 2* cells +field lf-rcr-pairs   \ the type's levels
end-structure
/lf-rcr context-record: lf-rcr-state

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
: lf-rcr-pair ( k -- addr ) lf-rcr-state lf-rcr-pairs swap lf-cref-pair ;
: lf-rcr-level! ( k -- )
  dup lf-ind-lparam lf-level-param if dup lf-level-identity drop swap rot lf-rcr-pair 2!
  else drop outcome-full lf-rcr-failing drop then ;
: lf-rcr-levels ( -- ) lf-ind-lparams nip 0 ?do i lf-rcr-level! loop ;
: lf-rcr-referenced ( index identity true | false -- node )
  if lf-cterm-new lf-rcr-made else outcome-full lf-rcr-failing then ;
: lf-rcr-const ( name -- node )
  lf-rcr-ok? 0= if drop -1 exit then
  lf-name-generation @ lf-rcr-state lf-rcr-pairs lf-ind-lparams nip lf-cref-new
  lf-rcr-referenced ;
\ f applied to the variables #(top), #(top-1), ... count of them.
: lf-rcr-apply-vars ( f top count -- node )
  0 ?do over over i - lf-rcr-bvar lf-rcr-app -rot nip loop drop ;

\ ---------------------------------------------------------------------------
\ The pieces. p parameters, n indices, m constructors.
: lf-rcr-p ( -- p ) lf-ind-nparams ;
: lf-rcr-n ( -- n ) lf-ind-state lf-ind-indices @ ;
: lf-rcr-m ( -- m ) lf-ind-ctors@ ;
: lf-rcr-dom ( i -- node ) lf-ind-domain @ ;
\ T As is, at depth d: the parameters #(d-1) .. #(d-p), then the indices,
\ the innermost n binders, #(n-1) .. #0.
: lf-rcr-major ( d -- node )
  lf-ind-name lf-rcr-const swap 1- lf-rcr-p lf-rcr-apply-vars
  lf-rcr-n 1- lf-rcr-n lf-rcr-apply-vars ;
\ Binding a telescope: the scratch holds the domains, outermost first;
\ wrapping binds them around body, innermost first, with tag.
: lf-rcr-scratch ( k -- addr ) cells lf-rcr-state lf-rcr-scratch-cells + ;
: lf-rcr-scratch# ( -- n ) lf-rcr-state lf-rcr-scratch-count @ ;
: lf-rcr-room ( n -- flag )
  dup lf-ind-binder-capacity > if drop outcome-full lf-rcr-failing drop false exit then
  lf-rcr-state lf-rcr-scratch-count ! true ;
: lf-rcr-wrap ( body tag domain -- node tag ) swap >r swap r@ lf-rcr-bind r> ;
: lf-rcr-over-scratch ( body tag -- node tag )
  lf-rcr-scratch# 0 ?do lf-rcr-scratch# 1- i - lf-rcr-scratch @ lf-rcr-wrap loop ;
\ The index domains D_p+j, each shifted past amount binders inserted
\ between the parameters and the indices, and consumed.
: lf-rcr-index-dom ( j amount -- node )
  >r dup lf-rcr-p + lf-rcr-dom swap r> lf-rcr-shift lf-rcr-consume ;
: lf-rcr-indices! ( amount -- )
  lf-rcr-n lf-rcr-room 0= if drop exit then
  lf-rcr-n 0 ?do i over lf-rcr-index-dom i lf-rcr-scratch ! loop drop ;
\ Constructor j's fields: k of them; field q's domain is the domain of
\ the raw telescope's binder p+q, shifted past amount binders inserted
\ between the parameters and the fields, and consumed.
: lf-rcr-k ( j -- k ) lf-ind-nfields @ ;
: lf-rcr-skip ( node count -- node' ) 0 ?do lf-term-second@ loop ;
: lf-rcr-field-dom ( j q -- node )
  swap lf-ind-ctor-type lf-rcr-p rot + lf-rcr-skip lf-term-first@ ;
: lf-rcr-field ( j q amount -- node )
  >r tuck lf-rcr-field-dom swap r> lf-rcr-shift lf-rcr-consume ;
: lf-rcr-fields! ( j amount -- )
  over lf-rcr-k lf-rcr-room 0= if 2drop exit then
  over lf-rcr-k 0 ?do 2dup i swap lf-rcr-field i lf-rcr-scratch ! loop 2drop ;
\ The outer binders of the recursor's type and of every rule: the
\ parameters (consumed), the motive, the minor premises.
: lf-rcr-param-dom ( i -- node ) lf-rcr-dom lf-rcr-consume ;
: lf-rcr-over-minors ( body tag -- node tag )
  lf-rcr-m 0 ?do lf-rcr-m 1- i - lf-ind-minor-type @ lf-rcr-wrap loop ;
: lf-rcr-over-motive ( body tag -- node tag ) lf-rcr-state lf-rcr-motive @ lf-rcr-wrap ;
: lf-rcr-over-params ( body tag -- node tag )
  lf-rcr-p 0 ?do lf-rcr-p 1- i - lf-rcr-param-dom lf-rcr-wrap loop ;
: lf-rcr-outer ( body tag -- node )
  lf-rcr-over-minors lf-rcr-over-motive lf-rcr-over-params drop ;

\ The motive's type, at depth p: (is) -> (t : T As is) -> Sort u.
: lf-rcr-elim-sort ( -- node ) lf-ind-state lf-ind-elim @ lf-rcr-sort ;
: lf-rcr-motive-type ( -- node )
  lf-rcr-p lf-rcr-n + lf-rcr-major lf-rcr-elim-sort lf-rcr-pi
  0 lf-rcr-indices! lf-tag-pi lf-rcr-over-scratch drop ;

\ Minor premise j, at depth p+1+j: (b) -> motive js (c_j As b), its body
\ at depth d = p+1+j+k, where the motive is #(j+k), the indices js are
\ the constructor result's (shifted past the motive and the j earlier
\ minors), the parameters #(d-1) .. #(d-p) and the fields #(k-1) .. #0.
: lf-rcr-result ( j -- node ) dup lf-ind-ctor-type swap lf-rcr-k lf-rcr-p + lf-rcr-skip ;
: lf-rcr-js ( j i -- node )
  over lf-rcr-result lf-rcr-p lf-rcr-n + rot lf-rcr-p + lf-ind-arg
  swap dup lf-rcr-k swap 1+ lf-rcr-shift ;
: lf-rcr-motive-app ( j -- node )
  dup dup lf-rcr-k + lf-rcr-bvar lf-rcr-n 0 ?do over i lf-rcr-js lf-rcr-app loop nip ;
: lf-rcr-intro ( j d -- node )
  over lf-ind-ctor lf-idecl-name @ lf-rcr-const swap 1- lf-rcr-p lf-rcr-apply-vars
  swap lf-rcr-k dup 1- swap lf-rcr-apply-vars ;
: lf-rcr-minor-depth ( j -- d ) dup lf-rcr-k + lf-rcr-p + 1+ ;
: lf-rcr-minor-body ( j -- node )
  dup lf-rcr-motive-app over dup lf-rcr-minor-depth lf-rcr-intro lf-rcr-app nip ;
: lf-rcr-minor ( j -- node )
  dup lf-rcr-minor-body swap dup 1+ lf-rcr-fields! lf-tag-pi lf-rcr-over-scratch drop ;

\ The recursor's type: the goal motive is t at depth p+1+m+n+1, under the
\ major premise, the indices (shifted past the motive and the minors) and
\ the outer binders.
: lf-rcr-goal ( -- node )
  lf-rcr-m lf-rcr-n + 1+ lf-rcr-bvar lf-rcr-n lf-rcr-n lf-rcr-apply-vars
  0 lf-rcr-bvar lf-rcr-app ;
: lf-rcr-type ( -- node )
  lf-rcr-p 1+ lf-rcr-m + lf-rcr-n + lf-rcr-major lf-rcr-goal lf-rcr-pi
  lf-rcr-m 1+ lf-rcr-indices! lf-tag-pi lf-rcr-over-scratch lf-rcr-outer ;

\ Rule j: fun As motive minors (b) => minor_j b, the body at depth
\ p+1+m+k, where minor_j is #(m-1-j+k) and the fields (shifted past the
\ motive and the m minors) #(k-1) .. #0.
: lf-rcr-rule-body ( j -- node )
  dup lf-rcr-k lf-rcr-m 1- rot - over + lf-rcr-bvar swap dup 1- swap lf-rcr-apply-vars ;
: lf-rcr-rule ( j -- node )
  dup lf-rcr-rule-body swap lf-rcr-m 1+ lf-rcr-fields! lf-tag-lam lf-rcr-over-scratch
  lf-rcr-outer ;

\ Build the motive's type, the minor premises, the recursor's type and the
\ rules into the block's record, from the facts check-block.fs computed
\ (indices, domains, field counts, elimination level): ok, or the first
\ failure (full, exhausted, invalid), the terms then unusable.
: lf-rcr-minors ( -- ) lf-rcr-m 0 ?do i lf-rcr-minor i lf-ind-minor-type ! loop ;
: lf-rcr-rules ( -- ) lf-rcr-m 0 ?do i lf-rcr-rule i lf-ind-rule ! loop ;
: lf-recursor-build ( -- outcome )
  outcome-ok lf-rcr-state lf-rcr-status ! lf-rcr-levels
  lf-rcr-motive-type lf-rcr-state lf-rcr-motive ! lf-rcr-minors
  lf-rcr-type lf-ind-state lf-ind-rec-type ! lf-rcr-rules lf-rcr-state lf-rcr-status @ ;
