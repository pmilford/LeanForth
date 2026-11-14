\ Terms (plan S1, FE1e7; design docs/design/FE1E_APPLICATIONS.md 2.1,
\ 2.3, 2.4 and 2.6), after Lean 4.35.0's Elab/Term/TermElabM.lean
\ (elabTerm, elabTermEnsuringType, elabType, ensureType), Elab/App.lean
\ (elabAtom, elabApp), Elab/BuiltinTerm.lean (elabNumLit) and
\ Elab/Extra.lean (binop% and binrel%: toTree, analyze, applyCoe,
\ toExprCore, toExpr, elabBinRelCore, hasHomogeneousInstance with
\ Meta/AppBuilder.lean's mkAppM, hasHeterogeneousDefaultInstances), over
\ the natural reader's syntax (front/syntax.fs).
\ - lf-elab-term-call ( node expected frames cont -- ... ) is the visit
\   elab-app.fs calls; lf-elab-term ( node expected -- term outcome ),
\   Lean's elabTerm (expected -1: none), runs one as a pass. By kind: a
\   numeral is elabNumLit (a synthetic ?T : Sort ?v, isDefEq expected ?T,
\   getDecLevel ?T, whose failure against an expected type is "numerals
\   are data" 127 or 128, then mkInstMVar (OfNat.{u} ?T n) and
\   @OfNat.ofNat.{u} ?T n ?i); a constant (at new universe
\   metavariables), a declaration's variable or a tactic's hypothesis is
\   elabAtom, an application elabApp: elabAppArgs (elab-app.fs); binop%
\   and binrel% are Extra.lean's, their operator resolved at the root. An
\   expected type whose whnfForall is a pi is unsupported (133: Lean's
\   implicit lambda reads its binder's kind, plan FE2).
\ - binop% (elabOp): toTree (operands that are binop% are entered,
\   anything else elaborated with no expected type; then
\   synthesizeSyntheticMVars, postponing), analyze (the leaves' types,
\   oldest first: the first known one is the max type; another not
\   defeq to it, in a new depth with isDefEqStuckEx, is a coercion: 131
\   when CoeT is in the environment, else Lean's uncomparable), then with
\   no max type toExprCore and ensureHasType, else applyCoe (an operator
\   below the root needs hasHomogeneousInstance: mkAppM C [max, max,
\   max] and trySynthInstance of it; without one Lean elaborates the
\   subtree apart, 139; a leaf of unknown type is left as it is when its
\   operator's class has heterogeneous default instances, else must be
\   isDefEqGuarded to the max type, else a coercion, 131), toExprCore
\   (each operator elabAppArgs of its two operands, no out-parameter
\   support), isDefEqGuarded of its type and the max type when no leaf
\   was unknown, and ensureHasType. binrel% (elabBinRelCore): inside
\   withSynthesizeLight, the two sides' trees, analyze with no expected
\   type, then either both sides alone, the right one made to have the
\   left one's type and the relation applied by elabAppArgs, or applyCoe
\   with the root a predicate and toExprCore.
\ - lf-elab-ensuring ( node expected -- term outcome ), elabTermEnsuringType;
\   lf-elab-type ( node -- type outcome ), elabType: against Sort ?u, then
\   ensureType (isType, else isDefEq of its type with a new Sort; a
\   coercion to a sort is 131).
\ - The declaration's variables (syntax var nodes, by binder slot):
\   lf-elab-vars-reset ( -- ), lf-elab-var+ ( fvar -- outcome ) for the
\   next slot.
\ Untrusted: only the kernel's check of a finished term decides anything.
\ State: the slabs et-tree (binop trees, a range each while open),
\ et-ops (the binop% and binrel% in progress), et-vars, the record et-am
\ (mkAppM's walk, one at a time) and the cell et-u (the universe level of
\ the numeral being made, read at once), in the checker context (ADR
\ 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/literals.fs
require ../core/tagged-sort-boundary.fs
require ../core/mvar-leaves.fs
require ../core/constant-term-boundary.fs
require ../lib/bounds.fs
require ../present/binder-table.fs
require ../author/errors.fs
require ../author/declarations.fs
require ../author/constants.fs
require ./syntax.fs
require ./mvars.fs
require ./lctx-views.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./term-eqv.fs
require ./instantiate.fs
require ./whnf.fs
require ./infer.fs
require ./fun-info.fs
require ./elab-pending.fs
require ./elab-app.fs

begin-structure /tn      \ a node of a binop% tree
  field: tn-f            \ an operator's function, or -1 for a leaf
  field: tn-lhs          \ an operator's operands
  field: tn-rhs
  field: tn-val          \ a leaf's term
  field: tn-node         \ the syntax
  field: tn-up           \ the operator above's function (applyCoe's f?), or -1
  field: tn-left         \ true: the left operand of the operator above
end-structure
/tn context-slab: et-tree
begin-structure /eo      \ an elabOp or elabBinRelCore in progress
  field: eo-root         \ its tree's first node
  field: eo-expected
  field: eo-max          \ analyze's max type, or -1
  field: eo-unknown      \ a leaf of unknown type
  field: eo-uncomp       \ uncomparable types
  field: eo-saved        \ binrel%: the pending list set aside
  field: eo-lhs          \ binrel% with no max type: the left side
  field: eo-rel          \ true: binrel%
end-structure
/eo context-slab: et-ops
1 cells context-slab: et-vars
begin-structure /am      \ mkAppM's walk
  field: am-d            \ the class
  field: am-app          \ the application so far
  field: am-type         \ the rest of its type
  field: am-k            \ binders passed
  field: am-xs           \ explicit arguments given
  field: am-max          \ the argument
end-structure
/am context-record: et-am
1 cells context-record: et-u   \ a numeral's level u, for OfNat.{u} and OfNat.ofNat.{u}

: et-at! ( node -- ) syn-at@ lf-elab-at! ;
: et-app1 ( f a -- t outcome )
  lf-term-app if outcome-ok else outcome-full no-result then ;
: et-app2 ( f a b -- t outcome )
  -rot et-app1 ok-then? if swap et-app1 else nip no-result then ;
: et-resolve ( name -- d outcome )
  lf-menv-find dup outcome-invalid = if drop lfa-e-unknown-constant lf-elab-fail exit then
  lf-elab-meta ;
: et-name-gen ( d -- name gen ) lf-menv-name lf-name-generation @ ;
\ The constant of that name at the numeral's level (Lean's mkConst n [u]).
: et-at-u ( c-addr u -- c outcome )
  lfa-intern et-resolve ok-then? if et-name-gen et-u 1 lf-meta-const-at else no-result then ;
\ Every visit here runs on the elaborator's frames (elab-app.fs): a step
\ drops the record it is given and names it again where it hands it on.
: et-fr ( -- frames ) lf-elab-frames ;
: et-failed ( outcome -- -1 outcome frames 0 ) no-result et-fr 0 ;

\ ---- The declaration's variables.
: lf-elab-vars-reset ( -- ) et-vars slab-clear ;
: lf-elab-var+ ( fvar -- outcome ) et-vars slab-push ;

\ ---- Heads: a constant, a variable, a hypothesis.
: et-const ( decl -- f outcome )
  lfa-decl-name et-resolve ok-then? if lf-meta-const-fresh else no-result then ;
: et-var ( slot -- f outcome )
  dup et-vars slab-count index? 0= if drop -1 outcome-invalid exit then
  et-vars slab-at @ outcome-ok ;
: et-hyp ( name -- f outcome )
  lf-mctx-view swap lf-view-named 0= if -1 outcome-invalid exit then
  lf-mctx-view swap lf-view-local lf-local-fvar outcome-ok ;
: et-head ( node -- f outcome )
  dup syn-a@ swap syn-kind@ case syn-k-const of et-const endof syn-k-var of et-var endof
    syn-k-hyp of et-hyp endof nip -1 outcome-invalid rot endcase ;

\ ---- elabNumLit.
: et-type-mvar ( -- T outcome )   \ mkFreshTypeMVar synthetic
  lf-level-mvar-new lf-elab-meta ok-then? 0= if no-result exit then
  lf-term-symbolic-sort 0= if outcome-full no-result exit then
  mv-synthetic lf-mvar-new lf-elab-meta ;
: et-type-for ( expected -- T outcome )   \ mkFreshTypeMVarFor
  et-type-mvar ok-then? 0= if nip no-result exit then
  over 0< if nip outcome-ok exit then tuck lf-elab-defeq lf-elab-meta nip ;
: et-numeral-error ( expected -- outcome )
  dup 0< if drop lfa-e-universe-level lf-elab-fail exit then
  lf-meta-is-prop lf-elab-meta ok-then? 0= if exit then
  if lfa-e-elab-numeral else lfa-e-elab-numeral-u then lf-elab-fail ;
: et-dec-level ( T expected -- u outcome )
  swap lf-meta-dec-level dup outcome-invalid = 0= if rot drop lf-elab-meta exit then
  2drop et-numeral-error no-result ;
: et-lit ( n -- lit outcome )
  lf-hterm-cell if drop outcome-ok else outcome-full no-result then ;
\ OfNat.{u} ?T lit, the instance's type; @OfNat.ofNat.{u} ?T lit ?i
\ from it and the instance metavariable.
: et-of-nat-type ( T lit -- type outcome )
  s" OfNat" et-at-u ok-then? if -rot et-app2 else nip nip no-result then ;
: et-type-args ( type -- T lit ) dup lf-term-first@ lf-term-second@ swap lf-term-second@ ;
: et-of-nat-value ( type i -- term outcome )
  s" OfNat.ofNat" et-at-u ok-then? 0= if nip nip no-result exit then
  rot et-type-args et-app2 ok-then? if swap et-app1 else nip no-result then ;
: et-of-nat ( T lit -- term outcome )
  et-of-nat-type ok-then? 0= if no-result exit then
  dup lf-elab-inst-mvar ok-then? if et-of-nat-value else nip no-result then ;
: et-num. ( node -- node ) s" num " lf-elab-note dup syn-a@ lf-elab-n. lf-elab-nl ;
: et-numeral ( node expected -- term outcome )
  over et-num. drop dup et-type-for ok-then? 0= if nip nip no-result exit then
  tuck swap et-dec-level ok-then? 0= if nip nip no-result exit then
  et-u ! swap syn-a@ et-lit ok-then? if et-of-nat else nip no-result then ;

\ ---- elabTerm: the position (Lean's withRef) set for the visit and put
\ back at its end; the implicit-lambda test; the elaborator by kind.
: et-at-back ( result outcome frames -- result outcome frames 0 )
  dup frame-restore lf-elab-at! 0 ;
: et-at-scope ( node -- node )
  lf-elab-at et-fr frame-save ['] et-at-back et-fr frame-save dup et-at! ;
: et-lambda? ( expected -- outcome )
  dup 0< if drop outcome-ok exit then
  lf-meta-whnf-forall lf-elab-meta ok-then? 0= if exit then
  lf-term-pi? if lfa-e-elab-lambda lf-elab-fail else outcome-ok then ;
: et-app-call ( -- ... frames next ) 0 0 et-fr ['] frame-return lf-elab-app-call ;
: et-num ( node expected -- term outcome frames 0 ) et-numeral et-fr 0 ;
: et-atom ( node expected -- ... frames next )
  swap et-head dup ok? 0= if nip nip et-failed exit then drop
  swap lf-elab-app-new dup ok? 0= if et-failed exit then drop et-app-call ;
: et-app ( node expected -- ... frames next )
  swap dup syn-a@ et-head ok-then? 0= if nip nip et-failed exit then
  rot lf-elab-app-new dup ok? 0= if nip et-failed exit then drop
  lf-elab-app-syntax! et-app-call ;
defer et-op ( node expected -- ... frames next )
defer et-rel ( node expected -- ... frames next )
: et-dispatch ( node expected -- ... frames next )
  over syn-kind@ case syn-k-num of et-num endof syn-k-app of et-app endof
    syn-k-binop of et-op endof syn-k-binrel of et-rel endof >r et-atom r> endcase ;
: et-visit ( node expected frames -- ... frames next )
  drop swap et-at-scope swap dup et-lambda? dup ok? 0= if nip nip et-failed exit then
  drop et-dispatch ;
:noname ( node expected frames cont -- ... frames next ) ['] et-visit lf-elab-open ;
is lf-elab-term-call
: et-term-call ( node expected frames cont -- ... frames next ) lf-elab-term-call ;
: lf-elab-term ( node expected -- term outcome ) ['] et-term-call lf-elab-visit ;

\ ---- binop% trees: toTree's go, a node per operator (pre-order) and per
\ leaf (its term elaborated with no expected type).
: tn ( i -- addr ) et-tree slab-at ;
: et-tn-fill ( node f addr -- ) dup /tn erase tuck tn-f ! tuck tn-node ! -1 swap tn-up ! ;
: et-tn-new ( node f -- i outcome )
  1 et-tree slab-claim ok-then? 0= if nip nip no-result exit then
  dup >r tn et-tn-fill r> outcome-ok ;
: et-leaf? ( i -- flag ) tn tn-f @ 0< ;
: et-leaf. ( term -- term ) s" leaf " lf-elab-note dup lf-elab-term. lf-elab-nl ;
: et-leaf-new ( term node -- i outcome )
  -1 et-tn-new ok-then? if tuck tn tn-val ! outcome-ok else nip no-result then ;
: et-leafed ( term outcome frames -- i outcome frames 0 )
  frame-restore over ok? 0= if drop nip et-failed exit then
  nip swap et-leaf. swap et-leaf-new et-fr 0 ;
: et-go-leaf ( node -- ... frames next )
  dup et-fr frame-save -1 et-fr ['] et-leafed lf-elab-term-call ;
: et-up! ( child parent -- ) tn tn-f @ swap tn tn-up ! ;
: et-lhs! ( child parent -- ) 2dup tn tn-lhs ! over tn true swap tn-left ! et-up! ;
: et-rhs! ( child parent -- ) 2dup tn tn-rhs ! et-up! ;
: et-op-fail ( x outcome frames -- -1 outcome frames 0 ) 1 swap frame-drop nip et-failed ;
: et-parent ( -- i ) 0 et-fr frame-pick ;
defer et-go-call ( node x frames cont -- ... frames next )
: et-op-rhs ( i outcome frames -- i outcome frames 0 )
  over ok? 0= if et-op-fail exit then frame-restore rot over et-rhs! swap et-fr 0 ;
: et-op-lhs ( i outcome frames -- ... frames next )
  over ok? 0= if et-op-fail exit then 2drop et-parent et-lhs!
  et-parent tn tn-node @ syn-c@ 0 et-fr ['] et-op-rhs et-go-call ;
: et-op. ( f -- f ) s" binop " lf-elab-note dup lf-elab-term. lf-elab-nl ;
: et-op-f ( node -- f outcome )
  syn-a@ et-resolve ok-then? if lf-meta-const-fresh else no-result then ;
: et-go-op ( node -- ... frames next )
  dup et-op-f ok-then? 0= if nip et-failed exit then et-op.
  over swap et-tn-new ok-then? 0= if nip et-failed exit then
  et-fr frame-save syn-b@ 0 et-fr ['] et-op-lhs et-go-call ;
: et-go ( node x frames -- ... frames next )
  2drop dup syn-kind@ syn-k-binop = if et-go-op else et-go-leaf then ;
:noname ( node x frames cont -- ... frames next ) ['] et-go lf-elab-open ; is et-go-call
\ toTree: go, then synthesizeSyntheticMVars (postponing).
: et-tree-end ( i outcome frames -- i outcome frames 0 )
  drop dup ok? if drop lf-postpone-yes lf-elab-synthesize then et-fr 0 ;
: et-tree-call ( node x frames cont -- ... frames next )
  over frame-save ['] et-tree-end et-go-call ;

\ ---- analyze (Extra.lean:256): the max type over the leaves, oldest first.
: eo ( -- addr ) et-ops slab-last ;
: et-unknown? ( t -- flag ) lf-meta-head lf-mvar? ;
: et-leaf-type ( i -- type outcome )
  tn tn-val @ lf-infer lf-elab-meta ok-then? 0= if no-result exit then
  lf-instantiate-mvars lf-elab-meta ;
: et-max! ( type -- ) dup et-unknown? if drop else eo eo-max ! then ;
: et-max-start ( expected -- outcome )
  -1 eo eo-max ! false eo eo-unknown ! false eo eo-uncomp !
  dup 0< if drop outcome-ok exit then
  lf-instantiate-mvars lf-elab-meta ok-then? if et-max! outcome-ok then ;
: et-stuck ( -- flags mode ) lf-defeq-flags lf-defeq-stuck or lf-defeq-mode ;
: et-stuck-guarded ( t s -- flag outcome ) ['] lf-elab-guarded et-stuck lf-meta-with ;
: et-deep-guarded ( t s -- flag outcome )
  false lf-mctx-depth{ ok-then? 0= if nip nip false swap exit then
  -rot et-stuck-guarded rot }lf-mctx-depth outcome-and lf-elab-meta ;
: et-coe-t? ( -- flag ) s" CoeT" lfa-intern lf-menv-find nip ok? ;
: et-uncomparable ( -- outcome )
  et-coe-t? if lfa-e-elab-coercion lf-elab-fail else true eo eo-uncomp ! outcome-ok then ;
: et-compared ( type -- outcome )
  eo eo-max @ swap et-deep-guarded ok-then? 0= if exit then
  if outcome-ok else et-uncomparable then ;
: et-analyze-leaf ( i -- outcome )
  et-leaf-type ok-then? 0= if exit then
  dup et-unknown? if drop true eo eo-unknown ! outcome-ok exit then
  eo eo-max @ 0< if eo eo-max ! outcome-ok else et-compared then ;
: et-analyze-at ( i -- outcome )
  dup et-leaf? if et-analyze-leaf else drop outcome-ok then ;
: et-analyzing? ( i -- flag ) et-tree slab-count < eo eo-uncomp @ 0= and ;
: et-max. ( -- )
  eo eo-max @ dup 0< if drop s" none" lf-elab-note else lf-elab-term. then ;
: et-analyze. ( -- ) s" analyze max " lf-elab-note et-max. lf-elab-nl ;
: et-analyze ( expected -- outcome )
  et-max-start dup ok? 0= if exit then drop
  eo eo-root @ begin dup et-analyzing? while
    dup et-analyze-at dup ok? 0= if nip exit then drop 1+ repeat
  drop et-analyze. outcome-ok ;
: et-no-max? ( -- flag ) eo eo-uncomp @ eo eo-max @ 0< or ;

\ ---- mkAppM (AppBuilder.lean:345) of a class at the max type, as many
\ times as it takes explicit arguments up to three, in a new depth: -1
\ (ok) where Lean's app builder throws (an argument whose type does not
\ fit, too many arguments). An instance binder, which mkAppMFinal fills
\ by synthInstance, and a result with metavariables left (Lean throws
\ only for those of the new depth) are 139.
: et-am-dom ( -- dom ) et-am am-type @ lf-term-first@ ;
: et-am-none ( -- outcome ) -1 et-am am-app ! outcome-ok ;
: et-am-enter ( x -- outcome )
  et-am am-type @ lf-term-second@ swap lf-meta-instantiate1 lf-elab-meta
  ok-then? if et-am am-type ! 1 et-am am-k +! outcome-ok then ;
: et-am-put ( x -- outcome )
  et-am am-app @ over lf-term-app 0= if drop outcome-full exit then
  et-am am-app ! et-am-enter ;
: et-am-hole ( kind -- outcome )
  et-am-dom swap lf-mvar-new lf-elab-meta ok-then? if et-am-put then ;
: et-am-fits ( flag -- outcome )
  if 1 et-am am-xs +! et-am am-max @ et-am-put else et-am-none then ;
: et-am-explicit ( -- outcome )
  et-am am-max @ lf-infer lf-elab-meta ok-then? 0= if exit then
  et-am-dom swap lf-elab-defeq lf-elab-meta ok-then? if et-am-fits then ;
: et-am-binder ( kind -- outcome )
  case lf-binder-default of et-am-explicit endof
    lf-binder-instance of lfa-e-elab-step lf-elab-fail endof
    >r mv-natural et-am-hole r> endcase ;
: et-am-kind ( -- kind true | false ) et-am am-d @ et-am am-k @ lf-menv-kind@ ;
: et-am-reduce ( -- outcome )
  et-am am-type @ lf-meta-whnf lf-elab-meta ok-then? 0= if exit then
  lf-term-pi? if lfa-e-elab-binder lf-elab-fail else et-am-none then ;
: et-am-step ( -- outcome )
  et-am am-type @ lf-term-pi? 0= if et-am-reduce exit then
  et-am-kind if et-am-binder else lfa-e-elab-binder lf-elab-fail then ;
: et-am-going? ( -- flag ) et-am am-xs @ 3 < et-am am-app @ 0< 0= and ;
: et-am-final ( -- type outcome )
  et-am am-app @ dup 0< if outcome-ok exit then lf-instantiate-mvars lf-elab-meta
  ok-then? 0= if no-result exit then lfa-e-elab-step lf-elab-closed
  dup ok? 0= if nip no-result then ;
: et-am-start ( d max -- outcome )
  et-am /am erase et-am am-max ! dup et-am am-d ! lf-meta-const-fresh ok-then? 0= if exit then
  dup et-am am-app ! lf-infer lf-elab-meta ok-then? if et-am am-type ! outcome-ok then ;
: et-am-run ( d max -- type outcome )
  et-am-start dup ok? 0= if no-result exit then drop
  begin et-am-going? while et-am-step dup ok? 0= if no-result exit then drop repeat
  et-am-final ;
: et-app-m ( d max -- type outcome )
  false lf-mctx-depth{ ok-then? 0= if nip nip no-result exit then
  -rot et-am-run rot }lf-mctx-depth outcome-and ;

\ ---- hasHomogeneousInstance (Extra.lean:387): the operator's class (its
\ name's prefix; none: false) at the max type, synthesized.
: et-class-of ( f -- d true outcome | false outcome )
  lf-const-name lf-name-prefix@ lf-menv-find dup outcome-invalid =
  if 2drop false outcome-ok exit then
  lf-elab-meta ok-then? if true outcome-ok else false swap then ;
: et-synthesized ( type -- flag outcome )
  dup 0< if drop false outcome-ok exit then
  lf-try-synth ok-then2? if nip lf-synth-some = outcome-ok else false swap then ;
: et-homogeneous ( f -- flag outcome )
  et-class-of ok-then? 0= if false swap exit then 0= if false outcome-ok exit then
  eo eo-max @ et-app-m ok-then? if et-synthesized else false swap then ;

\ ---- hasHeterogeneousDefaultInstances (Extra.lean:367): the operator's
\ class has two or more default instances and one's type ends in
\ C a b c with b (a left leaf) or a (a right one) headed by the max
\ type's head constant.
: et-head-name ( t -- name true | false )
  lf-meta-head dup lf-term-const? if lf-const-name true else drop false then ;
: et-args3 ( t -- a b true | false )
  dup lf-term-app? 0= if drop false exit then lf-term-first@
  dup lf-term-app? 0= if drop false exit then dup lf-term-second@ swap lf-term-first@
  dup lf-term-app? 0= if 2drop false exit then lf-term-second@ swap true ;
: et-side ( a b left? -- t ) if nip else drop then ;
: et-default-type ( v -- type outcome )
  elab-default@ drop nip lf-menv-of-data ok-then? if lf-menv-type outcome-ok
  else no-result then ;
: et-def-hit? ( name left? type -- flag )
  lf-meta-forall-body et-args3 0= if 2drop false exit then
  rot et-side et-head-name if = else drop false then ;
: et-scan-one ( name left? v -- name left? flag outcome )
  dup lf-default-gap? if drop false lfa-e-elab-step lf-elab-fail exit then
  et-default-type lf-elab-meta ok-then? 0= if false swap exit then
  >r 2dup r> et-def-hit? outcome-ok ;
: et-hetero-scan ( name left? addr n -- flag outcome )
  dup 2 < if 2drop 2drop false outcome-ok exit then cells over + swap ?do
    i @ et-scan-one lf-elab-settled? if 2swap 2drop unloop exit then 2drop
  cell +loop 2drop false outcome-ok ;
\ The class's default instances: the data's, by its declaration there.
: et-data-class ( d -- d' true | false ) lf-menv-name lf-menv-data-decl ;
: et-hetero-of ( name left? f -- flag outcome )
  et-class-of ok-then? 0= if nip nip false swap exit then
  0= if 2drop false outcome-ok exit then
  et-data-class 0= if 2drop false outcome-ok exit then
  lf-elab-default-instances ok-then2? if et-hetero-scan else nip nip false swap then ;
: et-hetero ( i -- flag outcome )
  eo eo-max @ et-head-name 0= if drop false outcome-ok exit then
  over tn tn-left @ rot tn tn-up @ et-hetero-of ;

\ ---- applyCoe (Extra.lean:415), the tree in pre-order: an operator below
\ a predicate root needs a homogeneous instance (else Lean elaborates its
\ subtree apart: 139); a leaf is left as it is, or must have the max type
\ (else a coercion, 131).
: et-pred? ( i -- flag ) eo eo-root @ = eo eo-rel @ and ;
: et-coe-op ( i -- outcome )
  dup et-pred? if drop outcome-ok exit then
  tn tn-f @ et-homogeneous ok-then? 0= if exit then
  if outcome-ok else lfa-e-elab-step lf-elab-fail then ;
: et-fits ( flag outcome -- outcome )
  ok-then? if if outcome-ok else lfa-e-elab-coercion lf-elab-fail then then ;
: et-coe-check ( type -- outcome ) eo eo-max @ swap lf-elab-guarded lf-elab-meta et-fits ;
: et-kept? ( i type -- flag outcome )
  et-unknown? 0= if drop false outcome-ok exit then
  dup tn tn-up @ 0< if drop false outcome-ok else et-hetero then ;
: et-coe-leaf ( i -- outcome )
  dup et-leaf-type ok-then? 0= if nip exit then
  2dup et-kept? ok-then? 0= if nip nip exit then
  if 2drop outcome-ok else nip et-coe-check then ;
: et-coe-at ( i -- outcome ) dup et-leaf? if et-coe-leaf else et-coe-op then ;
: et-apply-coe ( -- outcome )
  et-tree slab-count eo eo-root @ ?do i et-coe-at dup ok? 0= if unloop exit then drop loop
  outcome-ok ;

\ ---- toExprCore (Extra.lean:325): a leaf's term, an operator's mkBinOp,
\ elabAppArgs of its two operands' terms with no expected type.
defer et-x-call ( i x frames cont -- ... frames next )
: et-binop-new ( lhs rhs f -- outcome )
  -1 lf-elab-app-new dup ok? 0= if nip nip exit then drop lf-elab-app-plain
  swap lf-elab-app-term+ dup ok? 0= if nip exit then drop lf-elab-app-term+ ;
: et-x-rhs ( term outcome frames -- ... frames next )
  over ok? 0= if 2 swap frame-drop nip et-failed exit then 2drop
  et-fr frame-restore swap et-fr frame-restore tn tn-f @ et-binop-new
  dup ok? 0= if et-failed exit then drop et-app-call ;
\ The operator node toExprCore is at: the frame cell under the left
\ operand's term that et-x-lhs saves.
: et-x-node ( -- i ) 1 et-fr frame-pick ;
: et-x-lhs ( term outcome frames -- ... frames next )
  over ok? 0= if et-op-fail exit then nip frame-save
  et-x-node tn tn-rhs @ 0 et-fr ['] et-x-rhs et-x-call ;
: et-x-visit ( i x frames -- ... frames next )
  2drop dup et-leaf? if tn tn-val @ outcome-ok et-fr 0 exit then
  dup et-fr frame-save tn tn-lhs @ 0 et-fr ['] et-x-lhs et-x-call ;
:noname ( i x frames cont -- ... frames next ) ['] et-x-visit lf-elab-open ; is et-x-call

\ ---- elabOp and elabBinRelCore, a record each on et-ops.
: et-eo-fill ( expected rel? addr -- )
  dup /eo erase tuck eo-rel ! tuck eo-expected ! et-tree slab-count swap eo-root ! ;
: et-eo-new ( expected rel? -- outcome )
  1 et-ops slab-claim ok-then? 0= if nip nip exit then
  et-ops slab-at et-eo-fill outcome-ok ;
: et-eo-end ( term outcome -- term outcome frames 0 )
  eo eo-root @ et-tree slab-cut et-ops slab-drop et-fr 0 ;
: et-eo-fail ( outcome -- -1 outcome frames 0 ) no-result et-eo-end ;
\ The max type is recorded only when analyze found one, comparable and
\ with every leaf's type known (elabOp's `unless r.hasUnknown`).
: et-record-max ( term -- term outcome )
  eo eo-unknown @ et-no-max? or if outcome-ok exit then
  dup lf-infer lf-elab-meta ok-then? 0= if exit then
  eo eo-max @ lf-elab-guarded lf-elab-meta nip ;
: et-expected ( term -- term outcome ) eo eo-expected @ lf-elab-ensure ;
: et-op-finish ( term -- term outcome )
  et-record-max ok-then? if et-expected else no-result then ;
: et-op-done ( term outcome frames -- term outcome frames 0 )
  drop ok-then? if et-op-finish else no-result then et-eo-end ;
: et-root-call ( cont -- ... frames next ) >r eo eo-root @ 0 et-fr r> et-x-call ;
\ applyCoe only with a max type and nothing uncomparable.
: et-coerced ( -- outcome ) et-no-max? if outcome-ok else et-apply-coe then ;
: et-op-tree ( i outcome frames -- ... frames next )
  drop nip dup ok? 0= if et-eo-fail exit then drop eo eo-expected @ et-analyze
  dup ok? 0= if et-eo-fail exit then drop
  et-coerced dup ok? 0= if et-eo-fail exit then drop ['] et-op-done et-root-call ;
:noname ( node expected -- ... frames next )
  false et-eo-new dup ok? 0= if nip et-failed exit then drop
  0 et-fr ['] et-op-tree et-tree-call ;
is et-op
\ binrel%: the root an operator node of the relation; both sides' trees
\ inside withSynthesizeLight (the pending list set aside, back at the end).
: et-window-back ( -- ) eo eo-saved @ }lf-elab-window ;
: et-rel-fail ( x outcome frames -- -1 outcome frames 0 )
  drop nip et-window-back et-eo-fail ;
: et-rel-done ( term outcome frames -- term outcome frames 0 )
  drop dup ok? if drop lf-postpone-yes lf-elab-synthesize then et-window-back
  dup ok? 0= if nip no-result then et-eo-end ;
: et-rel-ensure ( rhs -- rhs' outcome )
  eo eo-lhs @ lf-infer lf-elab-meta ok-then? if lf-elab-ensure else nip no-result then ;
: et-rel-app ( rhs -- outcome )
  eo eo-root @ tn tn-f @ eo eo-expected @ lf-elab-app-new dup ok? 0= if nip exit then
  drop lf-elab-app-plain eo eo-lhs @ lf-elab-app-term+ dup ok? 0= if nip exit then drop
  lf-elab-app-term+ ;
: et-rel-failing ( outcome -- -1 outcome frames 0 ) 0 swap et-fr et-rel-fail ;
: et-rel-r ( term outcome frames -- ... frames next )
  over ok? 0= if et-rel-fail exit then 2drop et-rel-ensure ok-then? if et-rel-app then
  dup ok? 0= if et-rel-failing exit then drop 0 0 et-fr ['] et-rel-done lf-elab-app-call ;
: et-rel-l ( term outcome frames -- ... frames next )
  over ok? 0= if et-rel-fail exit then 2drop eo eo-lhs !
  eo eo-root @ tn tn-rhs @ 0 et-fr ['] et-rel-r et-x-call ;
: et-rel-lhs-call ( -- ... frames next )
  eo eo-root @ tn tn-lhs @ 0 et-fr ['] et-rel-l et-x-call ;
: et-rel-maxed ( -- ... frames next )
  et-apply-coe dup ok? 0= if et-rel-failing exit then drop ['] et-rel-done et-root-call ;
: et-rel-rhs ( i outcome frames -- ... frames next )
  over ok? 0= if et-rel-fail exit then 2drop eo eo-root @ et-rhs!
  -1 et-analyze dup ok? 0= if et-rel-failing exit then drop
  et-no-max? if et-rel-lhs-call else et-rel-maxed then ;
: et-rel-lhs ( i outcome frames -- ... frames next )
  over ok? 0= if et-rel-fail exit then 2drop eo eo-root @ et-lhs!
  eo eo-root @ tn tn-node @ syn-c@ 0 et-fr ['] et-rel-rhs et-tree-call ;
: et-rel. ( f -- f ) s" binrel " lf-elab-note dup lf-elab-term. lf-elab-nl ;
: et-rel-root ( node -- outcome )
  dup et-op-f ok-then? 0= if nip exit then et-rel. et-tn-new nip ;
:noname ( node expected -- ... frames next )
  true et-eo-new dup ok? 0= if nip et-failed exit then drop
  dup et-rel-root dup ok? 0= if nip et-eo-fail exit then drop
  lf-elab-window{ eo eo-saved ! syn-b@ 0 et-fr ['] et-rel-lhs et-tree-call ;
is et-rel

\ ---- elabType, ensureType, elabTermEnsuringType.
: et-sort-mvar ( -- sort outcome )
  lf-level-mvar-new lf-elab-meta ok-then? 0= if no-result exit then
  lf-term-symbolic-sort if outcome-ok else outcome-full no-result then ;
: et-is-type? ( e -- flag outcome )
  lf-infer lf-elab-meta ok-then? 0= if false swap exit then lf-meta-whnf lf-elab-meta
  ok-then? if lf-term-tag@ lf-tag-sort = outcome-ok else false swap then ;
: et-not-sort ( -- outcome )   \ coerceToSort?: CoeSort's instances, not ported
  s" CoeSort" lfa-intern lf-menv-find nip ok?
  if lfa-e-elab-coercion else lfa-e-elab-type then lf-elab-fail ;
: et-sorted ( e -- e outcome )
  dup lf-infer lf-elab-meta ok-then? 0= if exit then
  et-sort-mvar ok-then? 0= if nip exit then
  lf-elab-defeq lf-elab-meta ok-then? if if outcome-ok else et-not-sort then then ;
: et-ensure-type ( e -- e outcome )
  dup et-is-type? ok-then? 0= if exit then if outcome-ok else et-sorted then ;
: lf-elab-type ( node -- type outcome )
  dup et-at! et-sort-mvar ok-then? 0= if nip no-result exit then
  lf-elab-term ok-then? if et-ensure-type else no-result then ;
: lf-elab-ensuring ( node expected -- term outcome )
  tuck lf-elab-term ok-then? if swap lf-elab-ensure else nip no-result then ;
: lf-elab-term-reset ( -- ) et-tree slab-clear et-ops slab-clear ;

base !   \ the BASE this file was loaded with
