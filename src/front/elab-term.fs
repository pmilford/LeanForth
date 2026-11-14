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
\ et-ops (the binop% and binrel% in progress), et-vars and the record
\ et-am (mkAppM's walk, one at a time), in the checker context (ADR
\ 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/literals.fs
require ../core/tagged-sort-boundary.fs
require ../core/mvar-leaves.fs
require ../present/binder-table.fs
require ../author/errors.fs
require ../author/declarations.fs
require ../author/constants.fs
require ./syntax.fs
require ./mvars.fs
require ./lctx-views.fs
require ./meta-env.fs
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

: et-at! ( node -- ) syn-at@ lf-elab-at! ;
: et-app1 ( f a -- t outcome ) lf-term-app if outcome-ok else outcome-full no-result then ;
: et-app2 ( f a b -- t outcome ) >r et-app1 ok-then? if r> et-app1 else r> drop no-result then ;
: et-resolve ( name -- d outcome )
  lf-menv-find dup outcome-invalid = if drop lfa-e-unknown-constant lf-elab-fail exit then
  lf-elab-meta ;
: et-const-at ( level c-addr u -- c outcome )
  lfa-intern et-resolve ok-then? if swap lf-elab-const-at else nip no-result then ;

\ ---- The declaration's variables.
: lf-elab-vars-reset ( -- ) et-vars slab-clear ;
: lf-elab-var+ ( fvar -- outcome ) et-vars slab-push ;

\ ---- Heads: a constant, a variable, a hypothesis.
: et-const ( decl -- f outcome )
  lfa-decl-name et-resolve ok-then? if lf-elab-const else no-result then ;
: et-var ( slot -- f outcome )
  dup et-vars slab-count < if et-vars slab-at @ outcome-ok else drop -1 outcome-invalid then ;
: et-hyp ( name -- f outcome )
  lf-mctx-view swap lf-view-named 0= if -1 outcome-invalid exit then
  lf-mctx-view swap lf-view-local lf-local-fvar outcome-ok ;
: et-head ( node -- f outcome )
  dup syn-kind@ case
    syn-k-const of syn-a@ et-const endof
    syn-k-var of syn-a@ et-var endof
    syn-k-hyp of syn-a@ et-hyp endof
    >r drop -1 outcome-invalid r> endcase ;

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
  >r lf-meta-dec-level dup outcome-invalid = if 2drop r> et-numeral-error no-result exit then
  r> drop lf-elab-meta ;
: et-lit ( n -- lit outcome ) lf-hterm-cell if drop outcome-ok else outcome-full no-result then ;
: et-two-consts ( u -- c1 c2 outcome )   \ OfNat.{u} and OfNat.ofNat.{u}
  dup s" OfNat" et-const-at ok-then? 0= if nip -1 -1 rot exit then
  swap s" OfNat.ofNat" et-const-at ;
: et-of-nat-mvar ( T lit c1 -- i outcome )
  -rot et-app2 ok-then? if lf-elab-inst-mvar else no-result then ;
: et-of-nat-value ( i c2 T lit -- term outcome )
  et-app2 ok-then? 0= if nip no-result exit then swap et-app1 ;
: et-of-nat ( T lit u -- term outcome )
  et-two-consts ok-then2? 0= if nip nip no-result exit then
  >r >r 2dup r> et-of-nat-mvar ok-then? 0= if r> drop nip nip no-result exit then
  r> 2swap et-of-nat-value ;
: et-num. ( node -- node ) s" num " lf-elab-note dup syn-a@ lf-elab-n. lf-elab-nl ;
: et-numeral ( node expected -- term outcome )
  over et-num. drop dup et-type-for ok-then? 0= if nip nip no-result exit then
  tuck swap et-dec-level ok-then? 0= if nip nip no-result exit then
  rot syn-a@ et-lit ok-then? 0= if nip nip no-result exit then swap et-of-nat ;

\ ---- elabTerm: the position (Lean's withRef) set for the visit and put
\ back at its end; the implicit-lambda test; the elaborator by kind.
: et-at-back ( result outcome frames -- result outcome frames 0 )
  dup frame-restore lf-elab-at! 0 ;
: et-at-scope ( node frames -- node frames )
  lf-elab-at over frame-save ['] et-at-back over frame-save over et-at! ;
: et-lambda? ( expected -- outcome )
  dup 0< if drop outcome-ok exit then lf-meta-whnf-forall lf-elab-meta ok-then? 0= if exit then
  lf-term-pi? if lfa-e-elab-lambda lf-elab-fail else outcome-ok then ;
: et-failed ( outcome frames -- -1 outcome frames 0 ) >r no-result r> 0 ;
: et-num ( node expected frames -- term outcome frames 0 ) >r et-numeral r> 0 ;
: et-atom ( node expected frames -- ... frames next )
  >r swap et-head dup ok? 0= if nip nip r> et-failed exit then drop
  swap lf-elab-app-new dup ok? 0= if r> et-failed exit then drop
  0 0 r> ['] frame-return lf-elab-app-call ;
: et-app ( node expected frames -- ... frames next )
  >r swap dup syn-a@ et-head ok-then? 0= if nip nip r> et-failed exit then
  rot lf-elab-app-new dup ok? 0= if nip r> et-failed exit then drop
  lf-elab-app-syntax! 0 0 r> ['] frame-return lf-elab-app-call ;
defer et-op ( node expected frames -- ... frames next )
defer et-rel ( node expected frames -- ... frames next )
: et-dispatch ( node expected frames -- ... frames next )
  >r over syn-kind@ r> swap case
    syn-k-num of et-num endof
    syn-k-app of et-app endof
    syn-k-binop of et-op endof
    syn-k-binrel of et-rel endof
    >r et-atom r> endcase ;
: et-visit ( node expected frames -- ... frames next )
  >r swap r> et-at-scope >r swap dup et-lambda? dup ok? 0= if nip nip r> et-failed exit then
  drop r> et-dispatch ;
:noname ( node expected frames cont -- ... frames next ) ['] et-visit lf-elab-open ;
is lf-elab-term-call
: et-term-call ( node expected frames cont -- ... frames next ) lf-elab-term-call ;
: lf-elab-term ( node expected -- term outcome ) ['] et-term-call lf-elab-visit ;

\ ---- binop% trees: toTree's go, a node per operator (pre-order) and per
\ leaf (its term elaborated with no expected type).
: tn ( i -- addr ) et-tree slab-at ;
: et-tn-new ( node f -- i outcome )
  1 et-tree slab-claim ok-then? 0= if nip nip no-result exit then
  dup >r tn dup /tn erase tuck tn-f ! tuck tn-node ! -1 swap tn-up ! r> outcome-ok ;
: et-leaf? ( i -- flag ) tn tn-f @ 0< ;
: et-leaf. ( term -- term ) s" leaf " lf-elab-note dup lf-elab-term. lf-elab-nl ;
: et-leaf-new ( term node -- i outcome )
  -1 et-tn-new ok-then? if tuck tn tn-val ! outcome-ok else nip no-result then ;
: et-leafed ( term outcome frames -- i outcome frames 0 )
  dup frame-restore swap >r over ok? if nip swap et-leaf. swap et-leaf-new
  else drop nip no-result then r> 0 ;
: et-go-leaf ( node frames -- ... frames next )
  2dup frame-save -1 swap ['] et-leafed lf-elab-term-call ;
: et-up! ( child parent -- ) tn tn-f @ swap tn tn-up ! ;
: et-lhs! ( child parent -- ) 2dup tn tn-lhs ! over tn true swap tn-left ! et-up! ;
: et-rhs! ( child parent -- ) 2dup tn tn-rhs ! et-up! ;
: et-op-fail ( x outcome frames -- -1 outcome frames 0 ) 1 over frame-drop >r nip no-result r> 0 ;
defer et-go-call ( node x frames cont -- ... frames next )
: et-op-rhs ( i outcome frames -- i outcome frames 0 )
  over ok? 0= if et-op-fail exit then nip dup frame-restore rot over et-rhs!
  swap outcome-ok swap 0 ;
: et-op-lhs ( i outcome frames -- ... frames next )
  over ok? 0= if et-op-fail exit then nip 0 over frame-pick rot swap et-lhs!
  0 over frame-pick tn tn-node @ syn-c@ 0 rot ['] et-op-rhs et-go-call ;
: et-op. ( f -- f ) s" binop " lf-elab-note dup lf-elab-term. lf-elab-nl ;
: et-op-f ( node -- f outcome ) syn-a@ et-resolve ok-then? if lf-elab-const else no-result then ;
: et-go-op ( node frames -- ... frames next )
  >r dup et-op-f ok-then? 0= if nip r> et-failed exit then et-op.
  over swap et-tn-new ok-then? 0= if nip r> et-failed exit then
  r> tuck frame-save swap syn-b@ 0 rot ['] et-op-lhs et-go-call ;
: et-go ( node x frames -- ... frames next )
  nip over syn-kind@ syn-k-binop = if et-go-op else et-go-leaf then ;
:noname ( node x frames cont -- ... frames next ) ['] et-go lf-elab-open ; is et-go-call
\ toTree: go, then synthesizeSyntheticMVars (postponing).
: et-tree-end ( i outcome frames -- i outcome frames 0 )
  >r dup ok? if drop lf-postpone-yes lf-elab-synthesize then r> 0 ;
: et-tree-call ( node x frames cont -- ... frames next )
  over frame-save ['] et-tree-end et-go-call ;

\ ---- analyze (Extra.lean:256): the max type over the leaves, oldest first.
: eo ( -- addr ) et-ops slab-last ;
: et-unknown? ( t -- flag ) begin dup lf-term-app? while lf-term-first@ repeat lf-mvar? ;
: et-leaf-type ( i -- type outcome )
  tn tn-val @ lf-infer lf-elab-meta ok-then? if lf-instantiate-mvars lf-elab-meta
  else no-result then ;
: et-max-start ( expected -- outcome )
  -1 eo eo-max ! false eo eo-unknown ! false eo eo-uncomp !
  dup 0< if drop outcome-ok exit then lf-instantiate-mvars lf-elab-meta ok-then? 0= if exit then
  dup et-unknown? if drop else eo eo-max ! then outcome-ok ;
: et-stuck-guarded ( t s -- flag outcome )
  lf-defeq-flags dup >r lf-defeq-stuck or lf-defeq-flags! lf-elab-guarded r> lf-defeq-flags! ;
: et-deep-guarded ( t s -- flag outcome )
  false lf-mctx-depth{ ok-then? 0= if nip nip false swap exit then
  >r et-stuck-guarded r> }lf-mctx-depth outcome-and lf-elab-meta ;
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
: et-analyze-at ( i -- outcome ) dup et-leaf? if et-analyze-leaf else drop outcome-ok then ;
: et-analyzing? ( i -- flag ) et-tree slab-count < eo eo-uncomp @ 0= and ;
: et-analyze. ( -- )
  s" analyze max " lf-elab-note eo eo-max @ dup 0< if drop s" none" lf-elab-note
  else lf-elab-term. then lf-elab-nl ;
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
: et-am-put ( x -- outcome )
  et-am am-app @ over lf-term-app 0= if drop outcome-full exit then et-am am-app !
  et-am am-type @ lf-term-second@ swap lf-meta-instantiate1 lf-elab-meta
  ok-then? if et-am am-type ! 1 et-am am-k +! outcome-ok then ;
: et-am-hole ( kind -- outcome ) et-am-dom swap lf-mvar-new lf-elab-meta ok-then? if et-am-put then ;
: et-am-fits ( flag -- outcome )
  if 1 et-am am-xs +! et-am am-max @ et-am-put else et-am-none then ;
: et-am-explicit ( -- outcome )
  et-am am-max @ lf-infer lf-elab-meta ok-then? 0= if exit then
  et-am-dom swap lf-elab-defeq lf-elab-meta ok-then? if et-am-fits then ;
: et-am-binder ( kind -- outcome )
  case lf-binder-default of et-am-explicit endof
    lf-binder-instance of lfa-e-elab-step lf-elab-fail endof
    >r mv-natural et-am-hole r> endcase ;
: et-am-kind ( -- kind true | false )
  et-am am-d @ lf-menv-kinds et-am am-k @ tuck > if cells + @ true else 2drop false then ;
: et-am-reduce ( -- outcome )
  et-am am-type @ lf-meta-whnf lf-elab-meta ok-then? 0= if exit then
  lf-term-pi? if lfa-e-elab-binder lf-elab-fail else et-am-none then ;
: et-am-step ( -- outcome )
  et-am am-type @ lf-term-pi? 0= if et-am-reduce exit then
  et-am-kind if et-am-binder else lfa-e-elab-binder lf-elab-fail then ;
: et-am-going? ( -- flag ) et-am am-xs @ 3 < et-am am-app @ 0< 0= and ;
: et-am-closed ( t -- t outcome )
  dup lf-elab-holes? ok-then? 0= if exit then if lfa-e-elab-step lf-elab-fail else outcome-ok then ;
: et-am-final ( -- type outcome )
  et-am am-app @ dup 0< if outcome-ok exit then lf-instantiate-mvars lf-elab-meta
  ok-then? if et-am-closed dup ok? 0= if nip no-result then else no-result then ;
: et-am-start ( d max -- outcome )
  et-am /am erase et-am am-max ! dup et-am am-d ! lf-elab-const ok-then? 0= if exit then
  dup et-am am-app ! lf-infer lf-elab-meta ok-then? if et-am am-type ! outcome-ok then ;
: et-am-run ( d max -- type outcome )
  et-am-start dup ok? 0= if no-result exit then drop
  begin et-am-going? while et-am-step dup ok? 0= if no-result exit then drop repeat
  et-am-final ;
: et-app-m ( d max -- type outcome )
  false lf-mctx-depth{ ok-then? 0= if nip nip no-result exit then
  >r et-am-run r> }lf-mctx-depth outcome-and ;

\ ---- hasHomogeneousInstance (Extra.lean:387): the operator's class (its
\ name's prefix; none: false) at the max type, synthesized.
: et-class-of ( f -- d true outcome | false outcome )
  lf-elab-const-name lf-name-prefix@ lf-menv-find dup outcome-invalid =
  if 2drop false outcome-ok exit then lf-elab-meta ok-then? if true outcome-ok else false swap then ;
: et-synthesized ( type -- flag outcome )
  dup 0< if drop false outcome-ok exit then
  lf-elab-try-synth ok-then2? if nip 1 = outcome-ok else false swap then ;
: et-homogeneous ( f -- flag outcome )
  et-class-of ok-then? 0= if false swap exit then 0= if false outcome-ok exit then
  eo eo-max @ et-app-m ok-then? if et-synthesized else false swap then ;

\ ---- hasHeterogeneousDefaultInstances (Extra.lean:367): the operator's
\ class has two or more default instances and one's type ends in
\ C a b c with b (a left leaf) or a (a right one) headed by the max
\ type's head constant.
: et-head-name ( t -- name true | false )
  begin dup lf-term-app? while lf-term-first@ repeat
  dup lf-term-const? if lf-elab-const-name true else drop false then ;
: et-body ( t -- body ) begin dup lf-term-pi? while lf-term-second@ repeat ;
: et-args3 ( t -- a b true | false )
  dup lf-term-app? 0= if drop false exit then lf-term-first@
  dup lf-term-app? 0= if drop false exit then dup lf-term-second@ swap lf-term-first@
  dup lf-term-app? 0= if 2drop false exit then lf-term-second@ swap true ;
: et-def-hit? ( name left? v -- flag )
  elab-default@ drop nip lf-menv-type et-body et-args3 0= if 2drop false exit then
  rot if nip else drop then et-head-name if = else drop false then ;
: et-scan-one ( name left? v -- name left? flag outcome )
  dup 0< if drop false lfa-e-elab-step lf-elab-fail exit then >r 2dup r> et-def-hit? outcome-ok ;
: et-hetero-scan ( name left? addr n -- flag outcome )
  dup 2 < if 2drop 2drop false outcome-ok exit then cells over + swap ?do
    i @ et-scan-one lf-elab-settled? if 2swap 2drop unloop exit then 2drop
  cell +loop 2drop false outcome-ok ;
: et-hetero-of ( name left? f -- flag outcome )
  et-class-of ok-then? 0= if nip nip false swap exit then 0= if 2drop false outcome-ok exit then
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
  dup et-pred? if drop outcome-ok exit then tn tn-f @ et-homogeneous ok-then? 0= if exit then
  if outcome-ok else lfa-e-elab-step lf-elab-fail then ;
: et-fits ( flag outcome -- outcome )
  ok-then? if if outcome-ok else lfa-e-elab-coercion lf-elab-fail then then ;
: et-coe-check ( type -- outcome ) eo eo-max @ swap lf-elab-guarded lf-elab-meta et-fits ;
: et-kept? ( i type -- flag outcome )
  et-unknown? 0= if drop false outcome-ok exit then
  dup tn tn-up @ 0< if drop false outcome-ok else et-hetero then ;
: et-coe-leaf ( i -- outcome )
  dup et-leaf-type ok-then? 0= if nip exit then 2dup et-kept? ok-then? 0= if nip nip exit then
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
: et-x-operands ( rhs frames -- lhs rhs f frames )
  dup frame-restore swap dup frame-restore tn tn-f @ swap >r >r swap r> r> ;
: et-x-rhs ( term outcome frames -- ... frames next )
  over ok? 0= if 2 over frame-drop >r nip r> et-failed exit then
  nip et-x-operands >r et-binop-new dup ok? 0= if r> et-failed exit then drop
  0 0 r> ['] frame-return lf-elab-app-call ;
: et-x-lhs ( term outcome frames -- ... frames next )
  over ok? 0= if et-op-fail exit then nip tuck frame-save
  1 over frame-pick tn tn-rhs @ 0 rot ['] et-x-rhs et-x-call ;
: et-x-visit ( i x frames -- ... frames next )
  nip over et-leaf? if >r tn tn-val @ outcome-ok r> 0 exit then
  2dup frame-save swap tn tn-lhs @ 0 rot ['] et-x-lhs et-x-call ;
:noname ( i x frames cont -- ... frames next ) ['] et-x-visit lf-elab-open ; is et-x-call

\ ---- elabOp and elabBinRelCore, a record each on et-ops.
: et-tree-cut ( first -- ) et-tree slab-count - et-tree slab-commit ;
: et-eo-new ( expected rel? -- outcome )
  1 et-ops slab-claim ok-then? 0= if nip nip exit then et-ops slab-at dup /eo erase
  tuck eo-rel ! tuck eo-expected ! et-tree slab-count swap eo-root ! outcome-ok ;
: et-eo-end ( term outcome frames -- term outcome frames 0 )
  eo eo-root @ et-tree-cut et-ops slab-drop 0 ;
: et-eo-fail ( outcome frames -- -1 outcome frames 0 ) >r no-result r> et-eo-end ;
: et-record-max ( term -- term outcome )
  eo eo-unknown @ if outcome-ok exit then dup lf-infer lf-elab-meta ok-then? 0= if exit then
  eo eo-max @ lf-elab-guarded lf-elab-meta nip ;
: et-op-finish ( term -- term outcome )
  et-record-max ok-then? if eo eo-expected @ lf-elab-ensure else no-result then ;
: et-op-maxed ( term outcome frames -- term outcome frames 0 )
  >r ok-then? if et-op-finish else no-result then r> et-eo-end ;
: et-op-ensure ( term outcome frames -- term outcome frames 0 )
  >r ok-then? if eo eo-expected @ lf-elab-ensure else no-result then r> et-eo-end ;
: et-op-tree ( i outcome frames -- ... frames next )
  over ok? 0= if rot drop et-eo-fail exit then nip >r drop eo eo-expected @ et-analyze
  dup ok? 0= if r> et-eo-fail exit then drop
  et-no-max? if eo eo-root @ 0 r> ['] et-op-ensure et-x-call exit then
  et-apply-coe dup ok? 0= if r> et-eo-fail exit then drop
  eo eo-root @ 0 r> ['] et-op-maxed et-x-call ;
:noname ( node expected frames -- ... frames next )
  >r false et-eo-new dup ok? 0= if nip r> et-failed exit then drop
  0 r> ['] et-op-tree et-tree-call ;
is et-op
\ binrel%: the root an operator node of the relation; both sides' trees
\ inside withSynthesizeLight (the pending list set aside, back at the end).
: et-rel-fail ( x outcome frames -- -1 outcome frames 0 )
  eo eo-saved @ }lf-elab-window >r nip r> et-eo-fail ;
: et-rel-done ( term outcome frames -- term outcome frames 0 )
  >r dup ok? if drop lf-postpone-yes lf-elab-synthesize then eo eo-saved @ }lf-elab-window
  dup ok? 0= if nip no-result then r> et-eo-end ;
: et-rel-ensure ( rhs -- rhs' outcome )
  eo eo-lhs @ lf-infer lf-elab-meta ok-then? if lf-elab-ensure else nip no-result then ;
: et-rel-app ( rhs -- outcome )
  eo eo-root @ tn tn-f @ eo eo-expected @ lf-elab-app-new dup ok? 0= if nip exit then drop
  lf-elab-app-plain eo eo-lhs @ lf-elab-app-term+ dup ok? 0= if nip exit then drop
  lf-elab-app-term+ ;
: et-rel-r ( term outcome frames -- ... frames next )
  over ok? 0= if et-rel-fail exit then nip >r et-rel-ensure ok-then? if et-rel-app then
  dup ok? 0= if 0 swap r> et-rel-fail exit then drop 0 0 r> ['] et-rel-done lf-elab-app-call ;
: et-rel-l ( term outcome frames -- ... frames next )
  over ok? 0= if et-rel-fail exit then nip >r eo eo-lhs !
  eo eo-root @ tn tn-rhs @ 0 r> ['] et-rel-r et-x-call ;
: et-rel-rhs ( i outcome frames -- ... frames next )
  over ok? 0= if et-rel-fail exit then nip >r eo eo-root @ et-rhs!
  -1 et-analyze dup ok? 0= if 0 swap r> et-rel-fail exit then drop
  et-no-max? if eo eo-root @ tn tn-lhs @ 0 r> ['] et-rel-l et-x-call exit then
  et-apply-coe dup ok? 0= if 0 swap r> et-rel-fail exit then drop
  eo eo-root @ 0 r> ['] et-rel-done et-x-call ;
: et-rel-lhs ( i outcome frames -- ... frames next )
  over ok? 0= if et-rel-fail exit then nip >r eo eo-root @ et-lhs!
  eo eo-root @ tn tn-node @ syn-c@ 0 r> ['] et-rel-rhs et-tree-call ;
: et-rel. ( f -- f ) s" binrel " lf-elab-note dup lf-elab-term. lf-elab-nl ;
: et-rel-root ( node -- outcome )
  dup et-op-f ok-then? 0= if nip exit then et-rel. et-tn-new nip ;
:noname ( node expected frames -- ... frames next )
  >r true et-eo-new dup ok? 0= if nip r> et-failed exit then drop
  dup et-rel-root dup ok? 0= if nip r> et-eo-fail exit then drop
  lf-elab-window{ eo eo-saved ! syn-b@ 0 r> ['] et-rel-lhs et-tree-call ;
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
  dup lf-infer lf-elab-meta ok-then? 0= if exit then et-sort-mvar ok-then? 0= if nip exit then
  lf-elab-defeq lf-elab-meta ok-then? if if outcome-ok else et-not-sort then then ;
: et-ensure-type ( e -- e outcome )
  dup et-is-type? ok-then? 0= if exit then if outcome-ok else et-sorted then ;
: lf-elab-type ( node -- type outcome )
  dup et-at! et-sort-mvar ok-then? 0= if nip no-result exit then
  lf-elab-term ok-then? if et-ensure-type else no-result then ;
: lf-elab-ensuring ( node expected -- term outcome )
  dup >r lf-elab-term ok-then? if r> lf-elab-ensure else r> drop no-result then ;
: lf-elab-term-reset ( -- ) et-tree slab-clear et-ops slab-clear ;

base !   \ the BASE this file was loaded with

