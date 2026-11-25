\ Congruence argument kinds (plan row FE9, simp slice SL1a-1 of
\ docs/design/TACTIC_SIMP.md): Lean 4.35.0's getCongrSimpKinds and
\ fixKindsForDependencies (Lean/Meta/CongrTheorems.lean:122-212), the
\ kinds simp's congrDefault asks for first (mkCongrSimp?,
\ Simp/Types.lean:773-800): which arguments of an application may be
\ rewritten (eq), stay as they are (fixed), are cast (a proof) or are a
\ subsingleton instance. Later callers: SL2's automatic congruence
\ theorems, congr and convert.
\ - lf-congr-simp-kinds ( f -- n outcome ): the kinds of f's parameters
\   (getFunInfo f: every parameter of its type, fun-info.fs's
\   lf-meta-fun-deps, at most 62), each read by lf-congr-kind ( i --
\   kind ): lf-ck-fixed, lf-ck-eq, lf-ck-cast, lf-ck-subsingleton (Lean's
\   CongrArgKind fixed, eq, cast, subsingletonInst). In order: a
\   parameter the result's type holds is fixed; a proof cast; an
\   instance subsingletonInst when it is a Decidable instance one of
\   whose earlier parameters is eq (shouldUseSubsingletonInst), else
\   fixed; any other eq; then every parameter a later eq or fixed one
\   depends on is fixed.
\ - lf-congr-plain? ( n -- flag ): every kind fixed or eq (mkCongrSimp?'s
\   test: simp builds its proof with congrArg, congrFun' and congr).
\ isInstance (FunInfo.lean:111: a class type under a binder that is not
\ explicit) and isDecInst (:117: Decidable past the pis) are read from
\ the parameter type's head name (fun-info.fs's lf-param-head): a head
\ that is a definition, which Lean's isClass? and forallTelescopeReducing
\ unfold, answers unsupported where it decides, as does an undecided
\ head; an instance parameter of a constructor (getClassSubobjectMask?,
\ a class constructor's subobject fields) is unsupported too (SL2).
\ Outcomes: ok; unsupported as above and where fun-info.fs is; invalid
\ and full as there. Untrusted: a kind only chooses how simp builds the
\ proof the kernel checks. State: the context slab ck-kinds and the
\ record cks (whether f is a constructor), valid until the next call.
\ Loads in decimal whatever BASE is, then restores it.
\
\ Example: @Eq Nat a b's head Eq ( {α} (a b : α) ): fixed eq eq.
\   s" Eq" lf-mk-const1 lf-congr-simp-kinds  \ 3 outcome-ok
\   0 lf-congr-kind 1 lf-congr-kind          \ lf-ck-fixed lf-ck-eq

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ./meta-env.fs
require ./elab-data.fs
require ./fun-info.fs

0 constant lf-ck-fixed   1 constant lf-ck-eq   2 constant lf-ck-cast
3 constant lf-ck-subsingleton
1 cells context-slab: ck-kinds
begin-structure /cks
  field: cks-ctor   \ true: f is a constructor
end-structure
/cks context-record: cks
: lf-congr-kind ( i -- kind ) ck-kinds slab-at @ ;
: ck-kind! ( kind i -- ) ck-kinds slab-at ! ;
: ck-bit? ( mask i -- flag ) 1 swap lshift and 0<> ;

\ ---- A head name's facts.
: ck-decl-kind ( name -- kind ) lf-menv-find ok? if lf-menv-kind else drop -1 then ;
: ck-defn? ( name -- flag ) ck-decl-kind lf-kind-definition = ;
: ck-class? ( name -- flag )
  lf-menv-data-decl if elab-class-of dup if nip then else false then ;
: ck-ctor! ( f -- )
  dup lf-term-const? if lf-const-name ck-decl-kind lf-kind-constructor =
  else drop false then
  cks cks-ctor ! ;
: ck-undecided ( name -- flag outcome )
  ck-defn? if false outcome-unsupported else false outcome-ok then ;
: ck-named-inst ( name -- flag outcome )
  dup ck-class? 0= if ck-undecided exit then
  drop cks cks-ctor @ if false outcome-unsupported else true outcome-ok then ;
\ isInstance: a class past the pis, under a binder that is not explicit.
: ck-instance? ( i -- flag outcome )
  dup lf-meta-param drop lf-binder-default = if drop false outcome-ok exit then
  lf-param-head dup 0< if drop false outcome-unsupported exit then
  ?dup if ck-named-inst else false outcome-ok then ;
\ isDecInst: Decidable past the pis.
: ck-dec-inst? ( i -- flag outcome )
  lf-param-head dup s" Decidable" lf-name-dotted?
  if drop true outcome-ok else ck-undecided then ;

\ ---- getCongrSimpKinds' loop (CongrTheorems.lean:189-211).
: ck-eq-at? ( mask j -- flag )
  tuck ck-bit? if lf-congr-kind lf-ck-eq = else drop false then ;
: ck-eq-dep? ( i -- flag )
  dup lf-param-back-deps swap false swap 0 ?do over i ck-eq-at? or loop nip ;
: ck-inst-kind ( i -- kind outcome )
  dup ck-dec-inst? ok-then? 0= if nip no-result exit then
  if ck-eq-dep? if lf-ck-subsingleton else lf-ck-fixed then else drop lf-ck-fixed then
  outcome-ok ;
: ck-result-dep? ( i -- flag ) lf-fun-result-deps swap ck-bit? ;
: ck-plain-kind ( i -- kind outcome )
  dup ck-instance? ok-then? 0= if nip no-result exit then
  if ck-inst-kind else drop lf-ck-eq outcome-ok then ;
: ck-kind-of ( i -- kind outcome )
  dup ck-result-dep? if drop lf-ck-fixed outcome-ok exit then
  dup lf-meta-param nip if drop lf-ck-cast outcome-ok exit then ck-plain-kind ;
: ck-kind-at ( i -- outcome ) ck-kind-of ok-then? if ck-kinds slab-push then ;

\ ---- fixKindsForDependencies (:122-131): i fixed when a later parameter
\ that is eq or fixed depends on it.
: ck-holds? ( i j -- flag )
  dup lf-congr-kind lf-ck-eq lf-ck-fixed one-of2?
  if lf-param-back-deps swap ck-bit? else 2drop false then ;
: ck-fixed? ( i n -- flag )
  over 1+ ?do dup i ck-holds? if drop true unloop exit then loop drop false ;
: ck-fix ( i n -- ) over swap ck-fixed? if lf-ck-fixed over ck-kind! then drop ;
: ck-fix-all ( n -- ) dup 0 ?do i over ck-fix loop drop ;

: ck-kinds-run ( m -- n outcome )
  ck-kinds slab-clear dup ['] ck-kind-at ok-each dup ok? if over ck-fix-all then ;
: lf-congr-simp-kinds ( f -- n outcome )
  dup ck-ctor! fi-deps-most 1+ lf-meta-fun-deps
  ok-then? if ck-kinds-run else no-result then ;
: lf-congr-plain? ( n -- flag )
  true swap 0 ?do i lf-congr-kind lf-ck-eq lf-ck-fixed one-of2? and loop ;

base !   \ the BASE this file was loaded with
