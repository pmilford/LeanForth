\ Binders and telescopes of the tactic library (docs/design/
\ TACTIC_PLUGINS.md 2.3; plan slice a2-i), after Lean 4.35.0's
\ Meta/Basic.lean and MetavarContext.lean. Every word but the two kind
\ lookups throws on failure (meta-must.fs).
\ Public words (stack effect; the Lean function ported):
\   lf-binder-of ( pi -- name kind true | false )  a binder node's own
\       name and kind as recorded (present/binder-table.fs's
\       lf-pres-binder@: an input binder's record, else the presentation
\       table's), false when none is
\   lf-binder-name ( pi -- name ) its recorded name, else 0 (anonymous)
\   lf-binder-kind! ( pi d k -- kind ) lf-binder-kind-at, unknown thrown
\       unsupported; lf-walk-kind ( pi addr -- kind ) the same of d and k
\       kept in two cells at addr (a walk's frame)
\   lf-binder-mvar ( pi kind -- mvar ) mkFreshExprMVar of the binder's type,
\       synthetic for an instance binder, else natural, named as the binder
\   lf-binder-kind-at ( pi d k -- kind true | false )  the kind of binder
\       pi, the k-th (from 0) of declaration d's type: THE source of
\       binder kinds for a telescope; see below
\   lf-with-local-decl ( i*x type name bi xt -- j*x )  withLocalDecl
\       (Basic.lean:1835): xt ( i*x fvar -- j*x ) runs with a new free
\       variable of type in a new local whose view is current; the view
\       and the local context put back on both paths. lf-lctx-drop drops
\       every local made inside xt, not only this one: nothing made
\       inside may escape (a metavariable made there and kept would name
\       a dead local, which lf-fvar-live? tells; Lean's keeps its context)
\   lf-local-decl-new ( type name bi -- fvar view' )  mkFreshFVarId and
\       LocalContext.mkLocalDecl: a new free variable of type and its local,
\       named name, of kind bi, pushed on the current view (view' the
\       result, not made current)
\   lf-forall-meta-telescope-reducing ( acc type d xt -- acc' body )
\       forallMetaTelescopeReducing (Basic.lean:1751-1791, maxMVars?
\       none, kind natural): a new metavariable per binder, synthetic for
\       an instance binder, named as the binder (Lean's userName), each
\       given to xt ( acc mvar kind -- acc' ) in order; a body that is no
\       pi is put through whnf (the transparency in force) and walked on
\       when that gives a pi, else returned as it was before whnf
\   lf-let-decl-new ( type val name nondep -- fvar view' )  mkFreshFVarId
\       and LocalContext.mkLetDecl: a new let variable of type and value
\       val (with nondep a have, its value hidden: Lean's nondep := true),
\       its local named name, explicit, pushed on the current view (view'
\       not made current)
\   lf-mk-lambda-fvars ( e fvars n -- e' ), lf-mk-forall-fvars  mkLambdaFVars
\       and mkForallFVars (Basic.lean:1174-1180; MetavarContext.lean's
\       mkBinding and elimMVar): fvars the address of n free variables,
\       oldest first, each a local of the current view
\   lf-mk-let-fvars ( e fvars n -- e' )  mkLetFVars (Basic.lean:1183,
\       usedLetOnly and generalizeNondepLet false) as elabLetDeclAux
\       (Elab/Binders.lean:832) calls it: the same, a
\       let or have variable bound by let x : T := v (nondep kept), every
\       one whether e uses it or not
\ Binder kinds: lf-binder-kind-at reads declaration d's own kinds
\ (meta-env.fs's lf-menv-kind@, the tier's or the text's binder tags)
\ while k is one of its type's binders, else the node's record
\ (lf-binder-of); d -1 means no declaration. A telescope walks d's kinds
\ only until whnf first makes a pi (whnf's pis are no binder of d's
\ type), and refuses a binder whose kind is unknown (unsupported: Lean
\ reads binderInfo from the node, which a shared node may hide here,
\ review C4 of 2026-11-18).
\ mkBinding, as Lean's: e instantiated; each binder's type instantiated,
\ head-beta reduced and abstracted over the variables before it; each
\ binder named and of the kind of its local. elimMVar's case is ported
\ for e itself an unassigned metavariable whose context ends with the
\ variables (intro's fun x => ?n x): a new metavariable ?n of type
\ (xs : types) -> e's type in the context before them (synthetic opaque
\ when e's is not assignable, else e's kind) and e := ?n xs, delayed
\ when e is synthetic opaque, else assigned; with a let variable among
\ the xs (mkLetFVars only) ?n's type as mkAuxMVarType makes it for a
\ synthetic opaque ?n (a let past the first variable, or another kind of
\ ?n, unsupported). Not ported: a let variable among mkLambdaFVars' or
\ mkForallFVars' xs, a context where locals follow the xs or that holds only
\ some of them, and any other metavariable left in e (delayed-assigned,
\ or inside e) whose context holds one of the xs: all unsupported
\ (Lean's elimMVarDeps would revert it).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: tl-frames (a telescope's frame, one per telescope open,
\ meta-must.fs's lf-with-record, in the checker context, ADR 0009) and
\ tlb (the binding loop's fields: not re-entrant within one binding,
\ whose loop builds no other binding).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../lib/slab.fs
require ../lib/find.fs
require ../core/terms.fs
require ../core/let-terms.fs
require ../core/local-context.fs
require ../present/binder-table.fs
require ./mvars.fs
require ./lctx-views.fs
require ./instantiate.fs
require ./meta-env.fs
require ./term-eqv.fs
require ./meta-must.fs

\ ---- Binder kinds: the declaration's, else the node's.
: lf-binder-of ( pi -- name kind true | false ) lf-pres-binder@ ;
: tl-decl-kind ( d k -- kind true | false )
  over 0< if 2drop false else lf-menv-kind@ then ;
: tl-node-kind ( pi -- kind true | false ) lf-binder-of dup if >r nip r> then ;
: lf-binder-kind-at ( pi d k -- kind true | false )
  tl-decl-kind if nip true else tl-node-kind then ;
: lf-binder-kind! ( pi d k -- kind )
  lf-binder-kind-at 0= if outcome-unsupported lf-must then ;
\ A walk's binder kind: d and k in two cells at addr (d first).
: lf-walk-kind ( pi addr -- kind ) cell-pair@ lf-binder-kind! ;
: lf-binder-name ( pi -- name ) lf-binder-of if drop else 0 then ;

\ ---- withLocalDecl.
: tl-mark ( -- mark ) lf-term-base lf-term-count @ + ;   \ lf-lctx-drop's
\ The local of fvar, named name, of kind flags, pushed on the current view.
: tl-pushed ( fvar name flags -- fvar view' )
  2>r dup 2r> lf-local-new lf-must lf-mctx-view swap lf-view-push lf-must ;
: lf-local-decl-new ( type name bi -- fvar view' )
  rot lf-lctx-local lf-must -rot tl-pushed ;
\ mkLetDecl: a let variable, or with nondep a have (its value hidden).
: tl-let-fvar ( type val nondep -- fvar ) if lf-lctx-have else lf-lctx-let then lf-must ;
: lf-let-decl-new ( type val name nondep -- fvar view' )
  swap >r tl-let-fvar r> lf-binder-default tl-pushed ;
: tl-opened ( i*x type name bi xt -- j*x ) >r lf-local-decl-new r> swap lf-with-view ;
: lf-with-local-decl ( i*x type name bi xt -- j*x )
  tl-mark >r ['] tl-opened catch r> lf-lctx-drop throw ;

\ ---- forallMetaTelescopeReducing: a frame per telescope open.
begin-structure /tlf
  field: tlf-acc         \ the caller's cell
  field: tlf-type        \ the rest of the type
  field: tlf-d           \ the declaration whose kinds are read, or -1
  field: tlf-k           \ binders passed
  field: tlf-xt          \ ( acc mvar kind -- acc' )
  field: tlf-max         \ Lean's maxMVars?: the binders to pass at most, -1 none
end-structure
/tlf context-slab: tl-frames
: tl ( -- addr ) tl-frames slab-last ;
: tl-fill ( acc type d max xt frame -- )
  tuck tlf-xt ! tuck tlf-max ! tlf-acc cell-triple! ;
: tl-kind ( pi -- kind ) tl tlf-d lf-walk-kind ;
: tl-mv-kind ( kind -- mvkind )
  lf-binder-instance = if mv-synthetic else mv-natural then ;
: lf-binder-mvar ( pi kind -- mvar )
  tl-mv-kind over lf-term-first@ swap lf-mvar-new lf-must
  dup rot lf-binder-name lf-mvar-tag! lf-must ;
: tl-call ( mvar kind -- ) tl tlf-acc @ -rot tl tlf-xt @ execute tl tlf-acc ! ;
: tl-binder ( pi -- )
  dup tl-kind 2dup lf-binder-mvar tuck swap tl-call lf-meta-open lf-must tl tlf-type !
  1 tl tlf-k +! ;
: tl-reduced ( -- more? )
  tl tlf-type @ lf-whnf! dup lf-term-pi? 0= if drop false exit then
  tl tlf-type ! -1 tl tlf-d ! true ;
: tl-full? ( -- flag ) tl dup tlf-k @ swap tlf-max @ = ;   \ maxMVars reached
: tl-step ( -- more? )
  tl-full? if false exit then
  tl tlf-type @ lf-term-pi? if tl tlf-type @ tl-binder true else tl-reduced then ;
: tl-walk ( -- ) begin tl-step 0= until ;
: tl-run ( -- acc body ) tl-walk tl dup tlf-acc @ swap tlf-type @ ;
: tl-framed ( acc type d max xt -- acc' body ) tl tl-fill tl-run ;
\ With maxMVars? some max (Basic.lean:1755): at most max binders, the
\ rest of the type returned as it is once max are passed; -1 for none.
: lf-forall-meta-bounded-telescope ( acc type d max xt -- acc' body )
  tl-frames ['] tl-framed lf-with-record ;
: lf-forall-meta-telescope-reducing ( acc type d xt -- acc' body )
  -1 swap lf-forall-meta-bounded-telescope ;

\ ---- getExpectedNumArgsAux (Meta/Tactic/Apply.lean:21): the binders of
\ e under forallTelescopeReducing at default transparency, and whether the
\ body's head is a metavariable. The telescope is walked with new
\ metavariables in place of Lean's free variables and rolled back
\ (commitWhen false); a head among those new ones is a bound variable of
\ e, no metavariable.
: tl-count ( n mvar kind -- n' ) 2drop 1+ ;
: tl-older-mvar? ( e mark -- flag )
  >r lf-meta-head dup lf-mvar? if lf-term-first@ r> < else r> 2drop false then ;
: tl-expected ( e -- n mvar-head? false )
  lf-mvar-count >r 0 swap -1 ['] tl-count lf-forall-meta-telescope-reducing
  r> tl-older-mvar? false ;
: tl-expected-at ( e -- n mvar-head? false ) ['] tl-expected lf-tr-default lf-meta-at ;
: lf-expected-num-args ( e -- n mvar-head? ) ['] tl-expected-at lf-commit-when drop ;

\ ---- mkBinding (mkLambdaFVars, mkForallFVars, mkLetFVars).
begin-structure /tlb
  field: tlb-xs          \ the variables' address
  field: tlb-view        \ the context their locals are read in
  field: tlb-mode        \ the binding's mode (tl-mode, below)
end-structure
/tlb context-record: tlb
: tl-cell ( addr i -- x ) cells + @ ;
: tl-x ( i -- x ) tlb tlb-xs @ swap tl-cell ;
: tl-local-of ( fvar view -- local ) dup rot lf-view-find lf-found lf-view-local ;
\ Binder i's domain: x_i's type instantiated, head-beta reduced and
\ abstracted over x_0 .. x_i-1 (tl-abstract).
: tl-abstract ( t i -- t' ) tlb tlb-xs @ swap lf-meta-abstract lf-must ;
: tl-domain ( i -- dom )
  dup tl-x lf-fvar-type lf-instantiate! lf-meta-head-beta lf-must swap tl-abstract ;
: tl-named ( t local -- t )
  over swap dup lf-local-name swap lf-local-binder lf-pres-binder! lf-must ;
\ x_i's binder over body (the mode's lambda or pi), named as its local.
: tl-wrapped ( body i -- t )
  dup tl-x tlb tlb-view @ tl-local-of >r tl-domain swap tlb tlb-mode @ @ execute
  lf-made! r> tl-named ;
: tl-let ( body i -- t ) tlb tlb-mode @ cell+ @ execute ;
: tl-wrap ( body i -- t ) dup tl-x lf-fvar-ldecl? if tl-let else tl-wrapped then ;
: tl-binders ( e n -- e' ) begin dup while 1- tuck tl-wrap swap repeat drop ;
: tl-bound ( e addr n view mode -- e' )   \ e instantiated, elimMVar's case done
  tlb tlb-mode ! tlb tlb-view ! over tlb tlb-xs ! dup >r lf-meta-abstract lf-must r>
  tl-binders ;

\ A let variable x_i (a let, or a have: Lean's ldecl, nondep or not),
\ mkBinding's ldecl case with usedLetOnly false: let x : T := v; body, T
\ as a binder's domain, v instantiated and abstracted over x_0 .. x_i-1,
\ nondep kept (the let's binder named as x_i's local). In ?n's type
\ (mkAuxMVarType) for a synthetic opaque ?n, a have is a pi as a variable
\ is and a let is (x : T) -> let x : T := v; body (Lean's "gruesome
\ details", MetavarContext.lean), for x_0 only, whose let needs no lift
\ (else unsupported). mkLambdaFVars' and mkForallFVars' callers give none:
\ unsupported, as for ?n of any other kind.
: tl-unported ( body i -- t ) outcome-unsupported lf-must ;
: tl-value ( i -- v ) dup tl-x lf-fvar-value lf-instantiate! swap tl-abstract ;
: tl-let-of ( i lam -- let )
  swap dup tl-x lf-fvar-nondep? swap tl-value -rot lf-let-make lf-made! ;
: tl-let-bound ( body i -- t ) tuck tl-wrapped tl-let-of ;
: tl-relam ( pi -- lam ) dup lf-term-first@ swap lf-term-second@ lf-term-lam lf-made! ;
: tl-over ( pi t -- pi' ) swap lf-term-first@ swap lf-term-pi lf-made! ;
: tl-pi-let ( body i -- t ) tuck tl-wrapped tuck tl-relam tl-let-of tl-over ;
: tl-aux-let ( body i -- t )
  dup tl-x lf-fvar-nondep? if tl-wrapped exit then dup if tl-unported then tl-pi-let ;
\ Modes: a variable's binder ( dom body -- t flag ) and a let's ( body i -- t ).
: tl-mode ( binder let -- mode ) align here 2 cells allot tuck cell+ ! tuck ! ;
' lf-term-lam ' tl-unported tl-mode constant tl-lambdas
' lf-term-pi ' tl-unported tl-mode constant tl-foralls
' lf-term-lam ' tl-let-bound tl-mode constant tl-lets
' lf-term-pi ' tl-aux-let tl-mode constant tl-auxes

\ elimMVar's case: e an unassigned metavariable whose context holds some
\ of the n variables, all at its end (else unsupported).
begin-structure /tle
  field: tle-mvar        \ e
  field: tle-n           \ the variables' count
  field: tle-xs          \ and address (2! stores the pair)
end-structure
/tle context-record: tle
: tle! ( mvar addr n -- ) tle tle-n 2! tle tle-mvar ! ;
: tle-x ( i -- x ) tle tle-xs @ swap tl-cell ;
: tle-view ( -- view ) tle tle-mvar @ lf-goal-view ;
: tle-index ( i -- k true | false ) tle-view swap tle-x lf-view-find ;
: tle-placed? ( i -- flag )
  dup tle-index 0= if drop false exit then swap tle-view lf-view-count tle tle-n @ - + = ;
\ Whether a context holds one of the variables.
: tle-holds? ( view i -- view flag ) tle-x over swap lf-view-has? ;
: tle-sees? ( view -- flag ) tle tle-n @ ['] tle-holds? find-index dup if nip then ;
: tle-tail? ( -- flag ) tle tle-n @ ['] tle-placed? all? ;
\ ?n's type, kind and context; ?n xs; e delayed-assigned or assigned.
: tl-aux-kind ( -- kind )
  tle tle-mvar @ dup lf-mvar-assignable? if lf-mvar-kind drop else drop mv-opaque then ;
: tl-aux-view ( -- view ) tle-view dup lf-view-count tle tle-n @ - run-take lf-must ;
: tl-aux ( type -- aux ) tl-aux-kind tl-aux-view lf-mvar-new-at lf-must ;
: tl-applied ( aux -- r ) tle tle-n @ 0 ?do i tle-x lf-term-app lf-made! loop ;
: tl-delayed ( aux -- )
  tle tle-n @ 0 ?do i tle-x lf-delay-fvar lf-must loop
  tle tle-mvar @ tle tle-n @ lf-mvar-delay lf-must ;
: tl-assigned ( r -- r ) tle tle-mvar @ over lf-mvar-assign lf-must ;
: tl-settle ( aux r -- r )
  tle tle-mvar @ lf-mvar-kind drop mv-opaque =
  if swap tl-delayed else nip tl-assigned then ;
defer tl-bind-in ( e addr n view mode -- e' )
: tl-aux-mode ( -- mode ) tl-aux-kind mv-opaque = if tl-auxes else tl-foralls then ;
: tl-aux-type ( mvar addr n -- type )
  >r >r dup lf-goal-type swap lf-goal-view r> r> rot tl-aux-mode tl-bind-in ;
: tl-revert ( mvar addr n -- r )
  2>r dup 2r@ tl-aux-type swap 2r> tle! tl-aux dup tl-applied tl-settle ;
: tl-elim ( e addr n -- e' )
  >r over swap r> tle! dup lf-mvar-open? 0= if exit then
  tle-view tle-sees? 0= if exit then
  tle-tail? 0= if outcome-unsupported lf-must then tle tle-xs @ tle tle-n @ tl-revert ;
\ elimMVarDeps beyond that case: a metavariable left in e (delayed-
\ assigned, or inside e) that sees one of the variables, or has no
\ context, is refused (unsupported; Lean would revert it). The test
\ throws nothing and writes nothing (it runs inside lf-term-holds-with?'s
\ walk); its context is unused.
: tl-sees-xs? ( x leaf -- x flag )
  dup lf-mvar? 0= if drop false exit then lf-mvar-view 0= if true exit then tle-sees? ;
: tl-closed ( e -- e )
  dup 0 ['] tl-sees-xs? lf-term-holds-with? lf-must if outcome-unsupported lf-must then ;
: tl-binding ( e addr n view mode -- e' )
  2>r 2>r lf-instantiate! 2r@ tl-elim tl-closed 2r> 2r> tl-bound ;
' tl-binding is tl-bind-in
\ (Lean's mkLambdaFVars, mkForallFVars and mkLetFVars give e as it is
\ for no variable.)
: tl-made ( e fvars n mode -- e' )
  over 0= if drop 2drop exit then lf-mctx-view swap tl-binding ;
: lf-mk-lambda-fvars ( e fvars n -- e' ) tl-lambdas tl-made ;
: lf-mk-forall-fvars ( e fvars n -- e' ) tl-foralls tl-made ;
: lf-mk-let-fvars ( e fvars n -- e' ) tl-lets tl-made ;
base !   \ the BASE this file was loaded with
