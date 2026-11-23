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
\   and binrel% are Extra.lean's, their operator resolved at the root; a
\   hole (_, ?_, ?: NAME; plan row TB2, batch 3b) is elabHole or
\   elabSyntheticHole (see there), with no implicit-lambda test (Lean's
\   blockImplicitLambda). An
\   expected type whose whnfForall is a pi is unsupported (133: Lean's
\   implicit lambda reads its binder's kind, plan FE2), but for an
\   application's explicit argument whose binder's declared kind is
\   explicit or strict implicit (lf-elab-arg-call, elab-app.fs).
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
\   was unknown, and ensureHasType. rightact% (x ^ n) is an operator of
\   the same tree whose right operand is always a leaf, elaborated apart,
\   that analyze and applyCoe skip, its left operand coerced as if no
\   operator were above it, and no homogeneous instance asked of it
\   (Extra.lean:203, 269, 420). binrel% (elabBinRelCore): inside
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
\   next slot. A var node means the newest local of its binder's name in
\   the goal's context, as Lean resolves names; a name the context lacks
\   is refused (invalid, 76), as a hypothesis' name is.
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
require ../core/generation-handles.fs
require ../lib/bounds.fs
require ../lib/find.fs
require ../lib/decimal.fs
require ../core/input.fs
require ../present/binder-table.fs
require ../present/print-job.fs
require ../present/print-names.fs
require ../author/errors.fs
require ../author/declarations.fs
require ../author/constants.fs
require ./syntax.fs
require ./mvars.fs
require ./meta-config.fs
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
require ./meta-spine.fs
require ./meta-must.fs
require ./app-builder.fs

begin-structure /tn      \ a node of a binop% tree
  field: tn-f            \ an operator's function, or -1 for a leaf
  field: tn-lhs          \ an operator's operands
  field: tn-rhs
  field: tn-val          \ a leaf's term
  field: tn-node         \ the syntax
  field: tn-up           \ the operator above's function (applyCoe's f?), or -1
  field: tn-left         \ true: the left operand of the operator above
  field: tn-act          \ true: a rightact% operator, or its right operand
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
1 cells context-record: et-u   \ a numeral's level u, for OfNat.{u} and OfNat.ofNat.{u}

: et-at! ( node -- ) syn-at@ lf-elab-at! ;
: et-app2 ( f a b -- t outcome )   \ mkApp2 (meta-spine.fs's lf-meta-app, mkApp)
  -rot lf-meta-app ok-then? if swap lf-meta-app else nip no-result then ;
: et-resolve ( name -- d outcome )
  lf-menv-find dup outcome-invalid = if drop lfa-e-unknown-constant lf-elab-fail exit then
  lf-elab-meta ;
: et-name-gen ( d -- name gen ) lf-menv-name lf-name-generation @ ;
\ The constant of that name at the numeral's level (Lean's mkConst n [u]).
: et-at-u ( c-addr u -- c outcome )
  lfa-intern et-resolve ok-then? 0= if no-result exit then
  et-name-gen et-u 1 lf-meta-const-at ;
\ Every visit here runs on the elaborator's frames (elab-app.fs): a step
\ drops the record it is given and names it again where it hands it on.
: et-fr ( -- frames ) lf-elab-frames ;
: et-failed ( outcome -- -1 outcome frames 0 ) no-result et-fr 0 ;

\ ---- The declaration's variables.
: lf-elab-vars-reset ( -- ) et-vars slab-clear ;
: lf-elab-var+ ( fvar -- outcome ) et-vars slab-push ;

\ ---- Heads: a constant, a variable, a hypothesis.
: et-const ( decl -- f outcome )
  lfa-decl-name et-resolve ['] lf-meta-const-fresh ok-apply ;
\ A hypothesis, and a variable by its binder's name, is the newest
\ accessible local of that name in the goal's context, as Lean looks
\ every name up there (resolveLocalName): after specialize, or revert and
\ an intro, the local introduced again. A name the context lacks
\ (cleared, reverted, inaccessible) is refused, invalid (Lean's "Unknown
\ identifier"), never taken as the binder's own free variable.
: et-hyp ( name -- f outcome )
  lf-mctx-view swap lf-view-named-fvar if outcome-ok else -1 outcome-invalid then ;
: et-var ( slot -- f outcome )
  dup et-vars slab-count index? 0= if drop -1 outcome-invalid exit then
  lfa-binder lfa-binder-name @ et-hyp ;
: et-head ( node -- f outcome )
  dup syn-a@ swap syn-kind@ case syn-k-const of et-const endof syn-k-var of et-var endof
    syn-k-hyp of et-hyp endof nip -1 outcome-invalid rot endcase ;
\ Lean's Term.resolveId? for an identifier (Elab/Tactic/ElabTerm.lean's
\ elabTermForApply): a constant at new level metavariables with no
\ argument inserted, a variable or a hypothesis; lf-elab-ident? says
\ whether a node is one.
: lf-elab-ident? ( node -- flag )
  syn-kind@ syn-k-const syn-k-var syn-k-hyp one-of3? ;
: lf-elab-ident ( node -- e outcome ) et-head ;

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
  lf-hterm-cell lf-made-term ;
\ OfNat.{u} ?T lit, the instance's type; @OfNat.ofNat.{u} ?T lit ?i
\ from it and the instance metavariable.
: et-of-nat-type ( T lit -- type outcome )
  s" OfNat" et-at-u ok-then? if -rot et-app2 else nip nip no-result then ;
: et-app-to ( i f -- term outcome ) swap lf-meta-app ;
: et-of-nat-args ( type i c -- term outcome )
  rot lf-meta-args2 et-app2 ['] et-app-to ok-apply2 ;
: et-of-nat-value ( type i -- term outcome )
  s" OfNat.ofNat" et-at-u ['] et-of-nat-args ok-apply3 ;
: et-of-nat ( T lit -- term outcome )
  et-of-nat-type ok-then? 0= if no-result exit then
  dup lf-elab-inst-mvar ['] et-of-nat-value ok-apply2 ;
: et-num. ( node -- node ) s" num " lf-elab-note dup syn-a@ lf-elab-n. lf-elab-nl ;
: et-numeral ( node expected -- term outcome )
  over et-num. drop dup et-type-for ok-then? 0= if nip nip no-result exit then
  tuck swap et-dec-level ok-then? 0= if nip nip no-result exit then
  et-u ! swap syn-a@ et-lit ['] et-of-nat ok-apply2 ;

\ ---- elabHole and elabSyntheticHole (Elab/BuiltinTerm.lean:64-109; plan
\ row TB2, batch 3b): mkFreshExprMVar of the expected type (none: a
\ natural ?T : Sort ?u), natural for _ unless holes are synthetic opaque
\ (meta-config.fs's lf-holes-opaque?: refine', specialize), synthetic
\ opaque for ?_ and ?: NAME, that one tagged NAME, then recorded for its
\ error (registerMVarErrorHoleInfo: elab-app.fs's lf-elab-hole+). A NAME
\ some metavariable has already (findUserName?, which Lean reuses,
\ assigns or refuses by the contexts) is not ported (139), nor a hole
\ applied to arguments (139).
: et-sort-mvar ( -- sort outcome )   \ Sort ?u, a new level metavariable
  lf-level-mvar-new lf-elab-meta ok-then? 0= if no-result exit then
  lf-term-symbolic-sort room-result ;
: et-hole-type ( expected -- type outcome )
  dup 0< 0= if outcome-ok exit then
  drop et-sort-mvar ok-then? if mv-natural lf-mvar-new lf-elab-meta else no-result then ;
: et-natural? ( node -- flag ) syn-kind@ syn-k-hole = lf-holes-opaque? 0= and ;
: et-hole-kind ( node -- kind ) et-natural? if mv-natural else mv-opaque then ;
: et-hole-new ( node expected -- node mvar outcome )
  et-hole-type ok-then? 0= if no-result exit then
  over et-hole-kind lf-mvar-new lf-elab-meta ;
\ (The metavariable just made is live, so its tag is never refused:
\ lf-must throws only on a fault.)
: et-tagged ( node mvar -- node mvar )
  over syn-a@ ?dup if over swap lf-mvar-tag! lf-must then ;
: et-recorded ( node mvar -- mvar outcome ) tuck swap syn-at@ lf-elab-hole+ ;
: et-hole-made ( node expected -- mvar outcome )
  et-hole-new ok-then? 0= if nip no-result exit then et-tagged et-recorded ;
: et-taken? ( name -- flag ) ?dup if lf-mvar-named dup if nip then else false then ;
: et-unported ( -- -1 outcome ) lfa-e-elab-step lf-elab-fail no-result ;
: et-hole ( node expected -- mvar outcome )
  over syn-a@ et-taken? if 2drop et-unported exit then et-hole-made ;
: et-holed ( node expected -- mvar outcome frames 0 ) et-hole et-fr 0 ;
: et-fn ( app -- f outcome )
  syn-a@ dup syn-hole? if drop et-unported else et-head then ;

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
\ f applied to node's arguments against the expected type (elabApp).
: et-app-with ( node f expected -- ... frames next )
  lf-elab-app-new dup ok? 0= if nip et-failed exit then drop
  lf-elab-app-syntax! et-app-call ;
: et-app ( node expected -- ... frames next )
  over et-fn ok-then? 0= if nip nip et-failed exit then swap et-app-with ;
\ ---- elabAnonymousConstructor (Elab/BuiltinNotation.lean:43-102; plan
\ row TB2, tactic batch 3c), Lean's ⟨a, b⟩, reader.fs's << a b >>: the
\ expected type known (none, or one whose whnfR is a metavariable's
\ application: Lean postpones, which is not ported, 132; lf-elab-final
\ gives Lean's error 462 where the term would be resumed at once with its
\ type still unknown), its whnf headed by no metavariable (462), by an
\ inductive type's constant (matchConstInduct; else 463) with exactly one
\ constructor (none 464, more 465; a private one, whose accessibility
\ Lean checks, not ported: 139). Its explicit fields after its
\ parameters (numExplicitFields: the declared type's binder kinds,
\ lf-menv-kinds) take the items: fewer items 466, items where it has
\ none 467; as many, the constructor (mkCIdentFrom: new level
\ metavariables) applied to them (elabApp) against the expected type as
\ given; more, the last field takes the rest as a nested ⟨ ⟩ (newStx:
\ new nodes at the bracket's place, where Lean reports their errors).
\ The messages are Lean's, the type shown as inlineExpr shows a short one
\ (Lean indents one longer than 30 characters: not ported, the message
\ differs).
462 lfa-lean
  s" Invalid `⟨...⟩` notation: The expected type of this term could not be determined"
  lfa-code: lfa-e-anon-unknown
463 lfa-lean s" Invalid `⟨...⟩` notation: The expected type"
  lfa-code: lfa-e-anon-type
464 lfa-lean s" Invalid `⟨...⟩` notation: The expected type"
  lfa-code: lfa-e-anon-none
465 lfa-lean s" Invalid `⟨...⟩` notation: The expected type"
  lfa-code: lfa-e-anon-ctors
466 lfa-lean s" Insufficient number of fields for `⟨...⟩` constructor: Constructor"
  lfa-code: lfa-e-anon-few
467 lfa-lean s" Insufficient number of fields for `⟨...⟩` constructor: Constructor"
  lfa-code: lfa-e-anon-fields
: et-usage. ( -- outcome )
  s\" \nNote: This notation can only be used when the expected type is an " lf-pp-emit
  s" inductive type with a single constructor" lf-pp-emit outcome-ok ;
\ The expected type (tryPostponeIfNoneOrMVar's test): none, or one whose
\ whnfR is headed by a metavariable, is unknown; t is it instantiated.
: et-type? ( expected -- t unknown? outcome )
  dup 0< if true outcome-ok exit then
  lf-instantiate-mvars lf-elab-meta ok-then? 0= if no-result-flag exit then
  dup lf-elab-whnf-r-mvar? ;
\ Known, else Lean postpones (132).
: et-postponed ( -- -1 outcome ) lfa-e-elab-postpone lf-elab-fail no-result ;
: et-known ( expected -- t outcome )
  et-type? ok-then2? 0= if no-result exit then if drop et-postponed else outcome-ok then ;
: et-anon-whnf ( t -- t' outcome )
  lf-meta-whnf lf-elab-meta ok-then? 0= if no-result exit then
  dup lf-meta-head lf-mvar? 0= if outcome-ok exit then
  drop lfa-e-anon-unknown lf-elab-fail no-result ;
\ Its inductive type's one constructor.
: et-type-error ( t code -- -1 outcome ) lf-elab-fail-term no-result ;
: et-noted ( t code c-addr u -- -1 outcome )
  lf-elab-rest+ ['] et-usage. lf-elab-below! et-type-error ;
: et-not-inductive ( t -- -1 outcome )
  lfa-e-anon-type s" is not an inductive type" et-noted ;
: et-ctors-error ( t -- -1 outcome )
  lfa-e-anon-ctors s" has more than one constructor" et-noted ;
: et-no-ctor ( t -- -1 outcome )
  s" has no constructors" lf-elab-rest+ lfa-e-anon-none et-type-error ;
: et-ctor-of ( t items n -- name outcome )
  dup 1 = if drop nip @ outcome-ok exit then
  nip 0= if et-no-ctor else et-ctors-error then ;
: et-ctors ( t d -- name outcome )
  lf-menv-data ?dup 0= if drop et-unported exit then lf-ity-ctors@ et-ctor-of ;
: et-anon-name ( t -- name outcome )
  dup lf-meta-head lf-match-const-induct if et-ctors else et-not-inductive then ;
: et-private? ( name -- flag ) lf-name-root s" _private" lf-name-str-is? ;
: et-ctor-decl ( name -- c outcome )
  dup et-private? if drop et-unported exit then lf-menv-find lf-elab-meta ;
\ The steps in turn, each on the result of the one before (the type, then
\ its whnf, the constructor's name, its declaration).
: et-anon-ctor ( expected -- c outcome )
  et-known ['] et-anon-whnf ok-apply
  ['] et-anon-name ok-apply ['] et-ctor-decl ok-apply ;
\ numExplicitFields.
: et-params ( c -- p outcome )
  lf-menv-data ?dup if lf-ict-params lf-more-field outcome-ok else et-unported then ;
: et-past ( addr n k -- addr' n' ) tuck - -rot cells + swap ;
: et-explicit? ( addr k -- addr flag ) over cell-at@ lf-binder-default = ;
: et-fields-past ( c p -- n outcome )
  swap lf-menv-kinds rot 2dup < if 2drop drop et-unported exit then
  et-past ['] et-explicit? count-index outcome-ok ;
: et-fields ( c -- n outcome )
  dup et-params ok-then? if et-fields-past else nip no-result then ;
\ The messages of too few items: Lean's words, its plural as it writes it
\ (fieldsStr "fields" for one field, else "field": BuiltinNotation.lean:72).
: et-name+ ( name -- )
  s"  `" lf-elab-rest+ ['] lf-elab-rest+ lf-pp-name-to s" ` " lf-elab-rest+ ;
: et-n+ ( n -- ) u>decimal lf-elab-rest+ ;
: et-field-word ( n -- c-addr u ) 1 = if s" fields" else s" field" then ;
: et-has ( n -- )
  s" has " lf-elab-rest+ dup et-n+ s"  explicit " lf-elab-rest+
  et-field-word lf-elab-rest+ ;
: et-provided ( k -- )
  case 0 of s" none were" lf-elab-rest+ endof 1 of s" only 1 was" lf-elab-rest+ endof
    s" only " lf-elab-rest+ dup et-n+ s"  were" lf-elab-rest+ endcase ;
: et-few-error ( -- -1 outcome )
  s"  provided" lf-elab-rest+ lfa-e-anon-few lf-elab-fail no-result ;
: et-too-few ( c n k -- -1 outcome )
  rot lf-menv-name et-name+ swap et-has s" , but " lf-elab-rest+ et-provided
  et-few-error ;
: et-was ( k -- c-addr u ) 1 = if s"  was" else s"  were" then ;
: et-none-error ( k -- -1 outcome )
  dup et-n+ et-was lf-elab-rest+ s"  provided" lf-elab-rest+
  lfa-e-anon-fields lf-elab-fail no-result ;
: et-no-fields ( c k -- -1 outcome )
  swap lf-menv-name et-name+ s" does not have explicit fields, but " lf-elab-rest+
  et-none-error ;
\ The items as the constructor's arguments: new ⟨ ⟩ nodes of m slots at
\ the place of node (an argument node's place is its node's), filled
\ from from', a node whose item i is the one wanted, i from 0.
: et-anon-like ( node m -- new outcome )
  swap syn-k-anon swap syn-at@ syn-node-new room-result ;
: et-copy ( from' m to -- to ) swap 0 ?do 2dup swap i syn-arg i swap syn-arg! loop nip ;
: et-anon-of ( from' m -- new outcome )
  2dup et-anon-like ok-then? if et-copy outcome-ok else nip nip no-result then ;
: et-rest# ( node n -- m ) swap syn-b@ swap - 1+ ;
: et-from ( node n -- from' m ) 2dup + 1- -rot et-rest# ;
\ The rest from item n-1 on, nested; the node's first n items (the last
\ then the nested one).
: et-outer ( nested node n -- stx outcome )
  et-anon-of ok-then? if swap syn-last! outcome-ok else nip no-result then ;
: et-split ( node n -- stx outcome )
  2dup et-from et-anon-of ok-then? if -rot et-outer else nip nip no-result then ;
: et-exact? ( node n -- flag ) swap syn-b@ = ;
: et-few? ( node n -- flag ) swap syn-b@ > ;
: et-more ( c node n -- stx outcome )
  dup 0= if drop syn-b@ et-no-fields else rot drop et-split then ;
: et-anon-stx ( c node n -- stx outcome )
  2dup et-exact? if drop nip outcome-ok exit then
  2dup et-few? if swap syn-b@ et-too-few else et-more then ;
: et-anon-built ( node c -- stx outcome )
  dup et-fields ok-then? if rot swap et-anon-stx else nip nip no-result then ;
\ The constructor applied to the items (elabApp), against the expected type.
: et-anon-app ( stx expected c -- ... frames next )
  lf-meta-const-fresh ok-then? 0= if nip nip et-failed exit then swap et-app-with ;
: et-anon ( node expected -- ... frames next )
  tuck et-anon-ctor ok-then? 0= if nip nip et-failed exit then
  tuck et-anon-built ok-then? 0= if nip nip et-failed exit then -rot et-anon-app ;
defer et-op ( node expected -- ... frames next )
defer et-rel ( node expected -- ... frames next )
\ binop% and rightact% are elabOp's (Extra.lean:182).
: et-op-kind? ( node -- flag ) syn-kind@ syn-k-binop syn-k-rightact one-of2? ;
: et-dispatch ( node expected -- ... frames next )
  over syn-hole? if et-holed exit then over et-op-kind? if et-op exit then
  over syn-kind@ case syn-k-num of et-num endof syn-k-app of et-app endof
    syn-k-binrel of et-rel endof syn-k-anon of et-anon endof >r et-atom r> endcase ;
: et-scoped ( node expected frames -- node expected ) drop swap et-at-scope swap ;
\ (blockImplicitLambda: never for a hole, TermElabM.lean:1744.)
: et-visit ( node expected frames -- ... frames next )
  et-scoped over syn-hole? if et-dispatch exit then
  dup et-lambda? dup ok? 0= if nip nip et-failed exit then drop et-dispatch ;
:noname ( node expected frames cont -- ... frames next ) ['] et-visit lf-elab-open ;
is lf-elab-term-call
\ An argument whose binder's declared kind makes no implicit lambda
\ (elab-app.fs's ea-arg-call): the visit without the test.
: et-visit-known ( node expected frames -- ... frames next ) et-scoped et-dispatch ;
:noname ( node expected frames cont -- ... frames next ) ['] et-visit-known lf-elab-open ;
is lf-elab-arg-call
: et-term-call ( node expected frames cont -- ... frames next ) lf-elab-term-call ;
: lf-elab-term ( node expected -- term outcome ) ['] et-term-call lf-elab-visit ;
\ Term.elabTerm where synthesis with no postponing follows at once (a
\ tactic's term with mayPostpone false, #check): a ⟨ ⟩ at the root whose
\ expected type is unknown (none, or its whnfR a metavariable's
\ application) is postponed by Lean and resumed there with its type
\ still unknown: Lean's error 462 at it; anything else lf-elab-term.
: et-type-unknown? ( expected -- flag outcome )
  et-type? ok-then2? if nip outcome-ok else false swap then ;
: et-root-unknown? ( node expected -- flag outcome )
  over syn-kind@ syn-k-anon = if nip et-type-unknown? else 2drop false outcome-ok then ;
: et-root-unknown ( node -- -1 outcome )
  et-at! lfa-e-anon-unknown lf-elab-fail no-result ;
: lf-elab-final ( node expected -- term outcome )
  2dup et-root-unknown? ok-then? 0= if nip nip no-result exit then
  if drop et-root-unknown else lf-elab-term then ;

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
\ rightact% (toTree's processBinOp .rightact; applyCoe, Extra.lean:420):
\ its right operand is a leaf of its own, acting (analyze and applyCoe
\ skip it), and its left one has no operator above (go lhs none).
: et-act? ( i -- flag ) tn tn-act @ ;
: et-act-op! ( node i -- node i ) over syn-kind@ syn-k-rightact = over tn tn-act ! ;
: et-acting! ( child parent -- ) et-act? if true swap tn tn-act ! else drop then ;
: et-up! ( child parent -- ) dup et-act? if 2drop exit then tn tn-f @ swap tn tn-up ! ;
: et-lhs! ( child parent -- ) 2dup tn tn-lhs ! over tn true swap tn-left ! et-up! ;
: et-rhs! ( child parent -- ) 2dup tn tn-rhs ! 2dup et-acting! et-up! ;
: et-op-fail ( x outcome frames -- -1 outcome frames 0 ) 1 swap frame-drop nip et-failed ;
: et-parent ( -- i ) 0 et-fr frame-pick ;
defer et-go-call ( node x frames cont -- ... frames next )
: et-op-rhs ( i outcome frames -- i outcome frames 0 )
  over ok? 0= if et-op-fail exit then frame-restore rot over et-rhs! swap et-fr 0 ;
: et-op-lhs ( i outcome frames -- ... frames next )
  over ok? 0= if et-op-fail exit then 2drop et-parent et-lhs!
  et-parent tn tn-node @ syn-c@ et-parent et-act? et-fr ['] et-op-rhs et-go-call ;
: et-op. ( f -- f ) s" binop " lf-elab-note dup lf-elab-term. lf-elab-nl ;
: et-op-f ( node -- f outcome )
  syn-a@ et-resolve ['] lf-meta-const-fresh ok-apply ;
: et-go-op ( node -- ... frames next )
  dup et-op-f ok-then? 0= if nip et-failed exit then et-op.
  over swap et-tn-new ok-then? 0= if nip et-failed exit then
  et-act-op! et-fr frame-save syn-b@ 0 et-fr ['] et-op-lhs et-go-call ;
\ An operator is entered, unless it is a rightact%'s right operand (leaf?).
: et-go ( node leaf? frames -- ... frames next )
  drop 0= over et-op-kind? and if et-go-op else et-go-leaf then ;
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
: et-counted? ( i -- flag ) dup et-leaf? swap et-act? 0= and ;
: et-analyze-at ( i -- outcome )
  dup et-counted? if et-analyze-leaf else drop outcome-ok then ;
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

\ ---- mkAppM className #[max, max, max] (Extra.lean:391; the tactic
\ library's lf-mk-app-m-of, app-builder.fs): -1 (ok) where Lean's app
\ builder throws (rejected: an argument whose type does not fit, too
\ many arguments, no instance, a metavariable of the new depth left),
\ which hasHomogeneousInstance catches; anything else recorded (139 for
\ unsupported).
: et-mk-app-m ( d max -- e ) dup dup 3 lf-mk-app-m-of ;
: et-app-m ( d max -- type outcome )
  ['] et-mk-app-m 2 1 lf-meta-catch
  dup outcome-rejected = if 2drop -1 outcome-ok exit then
  lf-elab-meta ;

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
  rot et-side lf-meta-head-name if = else drop false then ;
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
  eo eo-max @ lf-meta-head-name 0= if drop false outcome-ok exit then
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
: et-coe-at ( i -- outcome )
  dup et-act? if drop outcome-ok exit then
  dup et-leaf? if et-coe-leaf else et-coe-op then ;
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
: et-eo-new ( expected rel? -- outcome ) et-ops ['] et-eo-fill lf-elab-record+ ;
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
  et-record-max ['] et-expected ok-apply ;
: et-op-done ( term outcome frames -- term outcome frames 0 )
  drop ['] et-op-finish ok-apply et-eo-end ;
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
  ok-or-none et-eo-end ;
: et-rel-ensure ( rhs -- rhs' outcome )
  eo eo-lhs @ lf-infer lf-elab-meta ['] lf-elab-ensure ok-apply2 ;
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
: et-is-type? ( e -- flag outcome )
  lf-infer lf-elab-meta ok-then? 0= if false swap exit then lf-meta-whnf lf-elab-meta
  ok-then? if lf-sort? outcome-ok else false swap then ;
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
  lf-elab-term ['] et-ensure-type ok-apply ;
\ The ensureHasType at the term's own syntax (Lean's withRef stx).
: lf-elab-ensuring ( node expected -- term outcome )
  over et-at! tuck lf-elab-term ok-then? if swap lf-elab-ensure else nip no-result then ;
: lf-elab-term-reset ( -- ) et-tree slab-clear et-ops slab-clear ;

base !   \ the BASE this file was loaded with
