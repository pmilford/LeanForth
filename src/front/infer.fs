\ The front end's type inference, first cases (plan FE1c; ADR 0021 D6): a
\ port of Lean 4.35.0's Meta.inferType (Lean/Meta/InferType.lean,
\ inferTypeImp) over the term store, with no use of src/kernel/. Like
\ Lean's, it infers without checking: an ill-typed term may get a type.
\ lf-infer ( term -- type outcome ):
\ - a constant: its declaration's type with the universe parameters
\   instantiated (inferConstType; another number of levels is invalid, as
\   Lean throws); a free variable: its local declaration's type; a
\   metavariable: its declaration's type; Sort u: Sort (u + 1);
\ - an application f a1 .. an whose head is one of those (inferAppType):
\   the head's type with each pi's bound variable instantiated by the
\   next argument, with beta where a bound variable heads an application
\   (instantiateBetaRevRange); a type that is no pi is reduced by whnfCore
\   (front/whnf.fs) and must then be one (Lean's whnf: a result whnf could
\   unfold further, its head a definition or unknown, answers unsupported;
\   one with a free variable, metavariable, sort, lambda or any other
\   constant at the head is invalid, as Lean throws "function expected").
\ - a lambda (inferLambdaType): its binders opened with new free
\   variables, the body's type (one of the above) inferred and closed
\   into pis over them (mkForallFVars), each with its lambda's name and
\   kind.
\ - a pi (inferForallType): its binders opened, the body's level and the
\   domains' (getLevel) combined with mkLevelIMax' and normalized.
\ - a projection e.i, alone or at an application's head (inferProjType,
\   S2 merge B: n + 0 unfolds to instAddNat.1 n 0): e's type, whnf'd,
\   must be the inductive type S with one constructor applied to its
\   parameters (invalid otherwise, Lean's "invalid projection"); the
\   constructor's type at those, its fields before i put in as e.j, then
\   field i's domain with its parameter annotations consumed.
\ A number literal's type is Nat (Lean's Literal.type).
\ Never a guess: unsupported for a let or string literal, an
\ application with any other head, a lambda or pi whose body or domain
\ is itself a lambda or pi or none of the above (nested telescopes, let
\ telescopes: plan FE1c), a projection of a structure with indices or
\ of a term that is or is headed by a projection, lambda, pi or let (a
\ nested inference: plan FE1c), a lambda's type holding a
\ metavariable (mkForallFVars's elimMVarDeps), a level Lean would get by
\ assigning a metavariable Sort ?u, a beta step under a binder of the
\ type (front/beta-inst.fs), and Sort's legacy numeric form.
\ Outcomes: ok; invalid for no term, a loose bound variable, a stale
\ leaf, an unknown constant, a wrong number of levels, a function
\ expected; unsupported as above; full when a store or slab has no room;
\ exhausted when whnfCore's fuel runs out (the fuel is per lf-whnf-core
\ call, so one inference may spend it once per argument and binder). A
\ failure gives -1.
\ lf-get-level ( type -- level outcome ): Lean's getLevel, the level u of
\ the type's inferred type once whnfCore makes it Sort u, with the same
\ outcomes (FE1g-3's by-sorry uses it, as Lean's mkSorry does);
\ lf-whnf-firm? ( term -- flag outcome ): whether whnf's delta could go
\ further than whnfCore's result (FE1g-4's by-intro asks); a refused
\ decode of the head's declaration passed on.
\ lf-meta-dec-level ( type -- level outcome ): Lean's getDecLevel
\ (Meta/DecLevel.lean:57-76): the type's level (getLevel), its level
\ metavariables instantiated and normalized (normalizeLevel), then
\ decremented (decLevel): succ u gives u; a max or imax whose two sides
\ both decrement gives mkLevelMax' of the two (no assignment below the
\ root, processMax); an assignable level metavariable at the root is
\ assigned succ ?w for a fresh ?w, the answer (one of an outer depth,
\ levelAssignDepth, is read-only); zero, a parameter or anything else is
\ Lean's "invalid universe level" (invalid; error 100 where a user sees
\ it). Full when a store has no room (a fresh ?w may then stay, unassigned
\ and named by no term: Lean's assignment cannot fail, so it has nothing
\ to restore).
\ Not re-entrant: one inference at a time per context uses the slabs
\ below (whnfCore and the instantiations it calls keep their own). Each
\ lambda or pi inferred adds its binders' free variables to the local
\ context, which only grows while a declaration is elaborated
\ (core/local-context.fs): the context is emptied with the declaration.
\ Untrusted: only the kernel's check of a finished term decides anything.
\ State: the record if-state (inferAppType's j, inferProjType's
\ projection) and the slabs if-args (the arguments, last first), if-levels (a
\ constant's universe arguments), if-xs and if-lams (a lambda's free
\ variables and binders), in the checker context. Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/generation-handles.fs
require ../core/local-context.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/input.fs
require ../core/projections.fs
require ../core/name-equal.fs
require ./mvars.fs
require ./instantiate.fs
require ./level-params.fs
require ../present/binder-table.fs
require ./level-simp.fs
require ./level-normalize.fs
require ./meta-spine.fs
require ./whnf.fs
require ./term-eqv.fs
require ./beta-inst.fs
require ./nat-offset.fs

begin-structure /if
  field: if-from    \ inferAppType's j: the first argument not put in yet
  field: if-proj    \ inferProjType's projection
end-structure
/if context-record: if-state
1 cells context-slab: if-args     \ the application's arguments, last first
1 cells context-slab: if-levels   \ a constant's universe arguments

: if-tag ( term -- tag ) lf-term-tag@ ;
: if-fail ( x outcome -- -1 outcome ) nip no-result ;
: if-bad ( x -- -1 outcome ) outcome-invalid if-fail ;

\ ---- Leaves.
: if-const-type ( const d -- type outcome )
  swap if-levels lf-meta-levels-fill ok-then? 0= if no-result exit then
  dup lf-menv-type swap lf-menv-params >r 0 if-levels slab-at r>
  lf-meta-instantiate-level-params ;
\ d's type at const's universe arguments, another number of them invalid.
: if-at-levels ( const d -- type outcome )
  2dup swap lf-meta-arity? 0= if 2drop -1 outcome-invalid exit then
  if-const-type ;
: if-const ( const -- type outcome )
  dup lf-meta-const-decl ok-then? if if-at-levels else if-fail then ;
: if-fvar ( fvar -- type outcome )
  dup lf-fvar-live? if lf-fvar-type outcome-ok else outcome-invalid if-fail then ;
: if-mvar ( mvar -- type outcome )
  lf-mvar-type if outcome-ok else -1 outcome-invalid then ;
: if-sort-new ( level -- type outcome )
  dup lf-level-identity 0= if drop -1 outcome-full exit then
  lf-hterm-sort if drop outcome-ok else -1 outcome-full then ;
: if-sort ( sort -- type outcome )
  lf-term-first@ lf-level-succ if if-sort-new else -1 outcome-full then ;
\ A number's type (Lean's Literal.type; branch s2-tactics: Meta.check of
\ rewriting's motive meets OfNat.ofNat Nat 1 (instOfNatNat 1)).
: if-lit ( lit -- type outcome ) drop lf-meta-nat ;
: if-leaf ( term tag -- type outcome )
  case lf-tag-constant of if-const endof  lf-tag-fvar of if-fvar endof
    lf-tag-mvar of if-mvar endof  lf-tag-symbolic-sort of if-sort endof
    lf-tag-lit of if-lit endof  lf-tag-bvar of outcome-invalid if-fail endof
    >r outcome-unsupported if-fail r> endcase ;

\ ---- Applications (inferAppType): the arguments in if-args. As Lean's,
\ the pis of the head's type are entered without putting the arguments
\ in; at a type that is no pi, and at the end, the arguments since the
\ last such point, j to i - 1, are put in at once, with beta
\ (instantiateBetaRevRange, front/beta-inst.fs). In if-args, last first,
\ they are the m = i - j cells from n - i on, the last one first, as
\ instantiateRev takes them.
: if-spine ( term -- head outcome ) if-args lf-meta-spine ;
: if-lam? ( term -- flag ) if-tag lf-tag-lam = ;
: if-pi? ( term -- flag ) if-tag lf-tag-pi = ;
\ A type that is no pi: whnfCore's result must be one; an inert head
\ (no pi whnf could make) is "function expected", anything else needs
\ whnf's delta.
: if-inert-tag? ( tag -- flag )
  dup lf-tag-fvar = over lf-tag-mvar = or
  over lf-tag-symbolic-sort = or swap lf-tag-lam = or ;
: if-inert? ( term -- flag ) if-tag if-inert-tag? ;
: if-head ( term -- head ) begin dup lf-meta-app? while lf-term-first@ repeat ;
\ A constant no declaration has is not firm; one whose declaration could
\ not be decoded passes that outcome on (full as full): lf-meta-firm-const?.
: if-firm ( head -- flag outcome )
  dup if-tag lf-tag-constant = if lf-meta-firm-const? else if-inert? outcome-ok then ;
\ Invalid where whnf leaves the head (Lean throws), unsupported where its
\ delta might go on, a refused decode passed on.
: if-firm-or ( head -- outcome )
  if-firm ok-then? if if outcome-invalid else outcome-unsupported then then ;
: if-no-pi ( type -- outcome ) if-head if-firm-or ;
\ Where whnfCore leaves a definition at the head, Lean's whnfD unfolds it
\ (inferAppType's whnf, getLevel's whnfD: outParam (Type) in HAdd.hAdd's
\ binders; branch s2-tactics, with merge A's delta).
\ (A declaration that could not be decoded passes its outcome on.)
: if-unfolds? ( type -- flag outcome )
  if-head dup if-tag lf-tag-constant = 0= if drop false outcome-ok exit then
  lf-meta-firm-const? ok-then? if 0= outcome-ok else false swap then ;
\ At least default transparency (withAtLeastTransparency .default,
\ InferType.lean:229): all stays all.
: if-whnf-d ( type -- type' outcome )
  lf-defeq-mode lf-tr-all = if lf-meta-whnf else lf-meta-whnf-d then ;
: if-delta ( type -- type' outcome )
  dup if-unfolds? ok-then? 0= if nip no-result exit then
  if if-whnf-d else outcome-ok then ;
: if-pi-of ( type -- pi outcome )
  dup if-pi? if outcome-ok else dup if-no-pi if-fail then ;
: if-to-pi ( type -- pi outcome )
  lf-whnf-core ok-then? 0= if no-result exit then
  if-delta ok-then? if if-pi-of else no-result then ;
: if-n ( -- n ) if-args slab-count ;
: if-j ( -- addr ) if-state if-from ;
: if-rev ( i -- addr m ) dup if-n swap - if-args slab-at swap if-j @ - ;
: if-flush ( type i -- type' outcome ) if-rev lf-meta-instantiate-rev-beta ;
: if-enter ( type i -- type' outcome )
  over if-pi? if drop lf-term-second@ outcome-ok exit then
  tuck if-flush ok-then? 0= if nip no-result exit then
  if-to-pi ok-then? 0= if nip no-result exit then
  swap if-j ! lf-term-second@ outcome-ok ;
: if-args-in ( type -- type' outcome )
  0 if-j ! if-n 0 ?do i if-enter dup ok? 0= if unloop exit then drop loop
  if-n if-flush ;
\ A spine's head is no application; a lambda, pi or let there answers
\ unsupported (if-leaf), a projection is inferred below. The head's type
\ comes first, then the arguments fill if-args: inferring a projection's
\ structure uses if-args too.
: if-leaf-type ( head -- type outcome ) dup if-tag if-leaf ;
: if-app-of ( term type -- type' outcome )
  swap if-spine ok-then? if drop if-args-in else nip no-result then ;
\ A term, its head's type by xt ( head -- type outcome ).
: if-body-by ( term xt -- type outcome )
  over lf-meta-app? 0= if execute exit then
  over if-head swap execute ok-then? if if-app-of else nip no-result then ;

\ ---- Projections (inferProjType, InferType.lean:128): e.i of the
\ structure S has the type of field i of S's one constructor applied to
\ the parameters of e's type (whnf'd), each earlier field j put in as
\ e.j, the field's type whnf'd to a pi whose domain is the answer, its
\ optParam, autoParam, outParam and semiOutParam annotations consumed.
\ Invalid (Lean's "invalid projection") when e's type is not an
\ application of the inductive type S with one constructor and
\ parameters plus indices arguments, or a field type is no pi.
\ Unsupported: S with indices (no structure has them), and e itself a
\ projection, lambda, pi or let or headed by one (inferring it would
\ nest this inference: plan FE1c, nested telescopes).
: if-p ( -- addr ) if-state if-proj ;
: if-s ( -- name ) if-p @ lf-proj-leaf lf-proj-name ;
: if-e ( -- e ) if-p @ lf-proj-struct ;
: if-e-type ( -- type outcome )
  if-e ['] if-leaf-type if-body-by ok-then? if if-whnf-d else no-result then ;
: if-named? ( d -- flag ) lf-menv-name if-s lf-name-same? ;
: if-induct? ( d -- flag ) dup lf-menv-kind lf-kind-inductive = swap if-named? and ;
: if-one-ctor ( data -- name true | false )
  lf-ity-ctors@ 1 = if @ true else drop false then ;
: if-arity ( data -- params indices ) dup lf-ity-params lf-more-field
  swap lf-ity-indices lf-more-field ;
\ S's data, after the head was found S: its constructor's name.
: if-shape ( data -- ctor outcome )
  dup if-arity tuck + if-n <> if drop if-bad exit then
  if outcome-unsupported if-fail exit then
  if-one-ctor if outcome-ok else -1 outcome-invalid then ;
: if-ctor ( name -- d outcome )
  lf-menv-find ok-then? 0= if no-result exit then
  dup lf-menv-kind lf-kind-constructor = if outcome-ok else if-bad then ;
\ e's type's head, a constant naming S: S's constructor's declaration.
: if-data ( d -- data outcome ) lf-menv-data dup if outcome-ok else if-bad then ;
: if-struct ( head -- d outcome )
  lf-meta-const-decl ok-then? 0= if no-result exit then
  dup if-induct? 0= if if-bad exit then
  if-data ok-then? 0= if no-result exit then
  if-shape ok-then? if if-ctor else no-result then ;
: if-ctor-type ( head -- type outcome )
  dup if-tag lf-tag-constant <> if if-bad exit then
  dup if-struct ok-then? 0= if if-fail exit then if-at-levels ;
\ The constructor's type applied to the parameters, which if-args holds.
: if-params-in ( type -- type' outcome )
  if-spine ok-then? 0= if no-result exit then
  if-ctor-type ok-then? if if-args-in else no-result then ;
: if-pi-whnf ( type -- pi outcome )
  if-whnf-d ok-then? 0= if no-result exit then dup if-pi? if outcome-ok else if-bad then ;
: if-field ( j -- proj outcome ) if-e swap if-s swap lf-proj-of ;
: if-skip ( type j -- type' outcome )
  swap if-pi-whnf ok-then? 0= if nip no-result exit then lf-term-second@
  swap if-field ok-then? if lf-meta-instantiate1 else nip no-result then ;
: if-fields ( type -- type' outcome )
  if-p @ lf-proj-leaf lf-proj-idx 0 ?do
    i if-skip dup ok? 0= if unloop exit then drop
  loop outcome-ok ;
: if-domain ( type -- type' outcome )
  if-pi-whnf ok-then? if lf-term-first@ lf-meta-consume-annotations outcome-ok
  else no-result then ;
: if-proj-type ( p -- type outcome )
  if-p ! if-e-type ok-then? 0= if no-result exit then
  if-params-in ok-then? 0= if no-result exit then
  if-fields ok-then? if if-domain else no-result then ;
: if-head-type ( head -- type outcome )
  dup lf-proj? if if-proj-type else if-leaf-type then ;
: if-app ( term -- type outcome ) ['] if-head-type if-body-by ;

\ ---- Lambdas (inferLambdaType, with mkForallFVars): each binder opened
\ with a new free variable of its domain (lambdaTelescope; the local
\ context keeps them, as it only grows while a declaration is
\ elaborated), the body's type inferred, then closed again into pis over
\ the variables, each with its lambda's name and kind. A type holding a
\ metavariable (Lean's elimMVarDeps) answers unsupported.
1 cells context-slab: if-xs     \ the telescope's free variables, first first
1 cells context-slab: if-lams   \ and the lambdas they opened
: if-x ( i -- fvar ) if-xs slab-at @ ;
: if-xs-at ( -- addr ) 0 if-xs slab-at ;
: if-holes? ( term -- flag ) lf-meta-mvar-free? 0= ;
: if-open ( lam -- body outcome )
  dup if-lams lf-meta-push ok-then? 0= if no-result exit then
  dup lf-term-first@ lf-lctx-local ok-then? 0= if if-fail exit then
  dup if-xs lf-meta-push ok-then? 0= if if-fail exit then
  lf-meta-open ;
: if-telescope ( term -- body outcome )
  if-xs slab-clear if-lams slab-clear
  begin dup if-lam? while if-open ok-then? 0= if no-result exit then repeat outcome-ok ;
: if-abstract ( term n -- term' outcome )
  over if-holes? if 2drop -1 outcome-unsupported exit then
  if-xs-at swap lf-meta-abstract ;
: if-pi ( body i -- pi outcome )
  dup if-x lf-fvar-type over if-abstract ok-then? 0= if nip nip no-result exit then
  rot lf-term-pi 0= if drop -1 outcome-full exit then
  swap if-lams slab-at @ lf-meta-named ;
: if-close ( type -- type' outcome )
  if-xs slab-count tuck if-abstract ok-then? 0= if nip no-result exit then
  swap begin dup 0> while 1- tuck if-pi ok-then? 0= if nip no-result exit then swap repeat
  drop outcome-ok ;
: if-body ( term -- type outcome ) if-app ;
: if-lambda ( lam -- type outcome )
  if-telescope ok-then? 0= if no-result exit then
  if-body ok-then? if if-close else no-result then ;

\ ---- Pis (inferForallType): the binders opened (forallTelescope), the
\ body's level and each domain's (getLevel: the type of the type, by
\ whnfCore a sort), combined from the last binder to the first with
\ mkLevelIMax' (front/level-simp.fs) and normalized
\ (front/level-normalize.fs): Sort of that. A type of a type that is no
\ sort is invalid (Lean: type expected) when whnf could not make one,
\ unsupported when it might (a definition) or when Lean would assign a
\ metavariable Sort ?u.
: if-sort? ( term -- flag ) if-tag lf-tag-symbolic-sort = ;
: if-no-sort ( type -- outcome )
  if-head dup if-tag lf-tag-mvar = if drop outcome-unsupported exit then if-firm-or ;
: if-sort-of ( T -- level outcome )
  dup if-sort? if lf-term-first@ outcome-ok else dup if-no-sort if-fail then ;
: if-sort-level ( T -- level outcome )
  dup if-sort? if lf-term-first@ outcome-ok exit then
  lf-whnf-core ok-then? 0= if no-result exit then
  if-delta ok-then? if if-sort-of else no-result then ;
: if-get-level ( type -- level outcome )
  if-body ok-then? if if-sort-level else no-result then ;
: if-pi-telescope ( term -- body outcome )
  if-xs slab-clear if-lams slab-clear
  begin dup if-pi? while if-open ok-then? 0= if no-result exit then repeat outcome-ok ;
: if-imax-step ( lvl i -- lvl' outcome )
  if-x lf-fvar-type if-get-level ok-then? 0= if nip no-result exit then
  swap lf-meta-imax ;
: if-imaxes ( lvl -- lvl' outcome )
  if-xs slab-count begin dup 0> while
    1- tuck if-imax-step ok-then? 0= if nip no-result exit then swap
  repeat drop outcome-ok ;
: if-forall ( pi -- type outcome )
  if-pi-telescope ok-then? 0= if no-result exit then
  if-get-level ok-then? 0= if no-result exit then
  if-imaxes ok-then? 0= if no-result exit then
  lf-meta-level-normalize ok-then? if if-sort-new else no-result then ;

: lf-infer ( term -- type outcome )
  dup lf-term-root? 0= if outcome-invalid if-fail exit then
  dup if-lam? if if-lambda exit then
  dup if-pi? if if-forall else if-body then ;
\ Whether Lean's whnf would leave a term whnfCore made as it is: its head
\ inert (a free variable, metavariable, sort or lambda) or a constant of
\ the input that is no definition; false where delta might go on (a
\ definition, or a constant the input does not hold); a head whose
\ declaration could not be decoded passes that outcome on.
: lf-whnf-firm? ( term -- flag outcome ) if-head if-firm ;
\ Lean's getLevel (Meta/InferType.lean): the level u of a type's type,
\ which whnf must make Sort u; the cases as inferForallType's above.
: lf-get-level ( type -- level outcome )
  lf-infer ok-then? if if-sort-level else no-result then ;

\ ---- getDecLevel. Below the root a bottom-up walk (dag-walk.fs) whose
\ image is the decrement + 1, 0 for none (a walk's images are not
\ negative); the root may assign.
begin-structure /idl
  /dw +field idl-walk
end-structure
/idl context-record: idl
: idl-walk@ ( -- walk ) idl idl-walk ;
: idl-max? ( l -- flag )
  lf-level-tag@ dup lf-level-tag-max = swap lf-level-tag-imax = or ;
: idl-pending ( l walk -- child true | false )
  over idl-max? 0= if 2drop false exit then
  >r dup lf-level-first@ swap lf-level-second@ r> dw-want2 ;
: idl-img ( l -- image ) idl-walk@ dw-image ;
: idl-both ( l -- a b ) dup lf-level-first@ idl-img swap lf-level-second@ idl-img ;
: idl-max ( l walk -- image )
  >r idl-both 2dup 0= swap 0= or if 2drop r> drop 0 exit then
  1- swap 1- swap lf-meta-max dup ok? if drop r> drop 1+ else r> dw-refuse drop 0 then ;
: idl-build ( l walk -- image )
  over lf-level-tag@ lf-level-tag-succ = if drop lf-level-first@ 1+ exit then
  over idl-max? if idl-max else 2drop 0 then ;
:noname ( -- ) ['] idl-pending idl-walk@ dw-pending ! ['] idl-build idl-walk@ dw-build ! ;
  context-setup
: idl-answer ( image -- level outcome ) ?dup if 1- outcome-ok else -1 outcome-invalid
  then ;
: idl-dec ( level -- level' outcome )
  lf-level-count @ idl-walk@ dw-size ! idl-walk@ dw-run ok-then? if idl-answer else
    no-result then ;
\ An assignable ?u at the root: ?u := succ ?w for a fresh ?w, the answer.
\ Lean's assignment cannot fail; here the stores may have no room (full),
\ and then ?w, made already, stays unassigned and named by no term.
: idl-assign ( mvar w succ -- w outcome )
  rot swap lf-level-mvar-assign dup ok? 0= if nip no-result then ;
: idl-succ-of ( mvar w -- w outcome )
  dup lf-level-succ if idl-assign else 2drop -1 outcome-full then ;
: idl-fresh ( mvar -- w outcome )
  lf-level-mvar-new ok-then? if idl-succ-of else nip no-result then ;
: idl-open? ( level -- flag outcome )
  dup lf-level-mvar? if lf-level-assignable-mvar? else drop false outcome-ok then ;
: idl-decrement ( level -- level' outcome )
  dup idl-open? ok-then? 0= if nip no-result exit then if idl-fresh else idl-dec then ;
: lf-meta-dec-level ( type -- level outcome )
  lf-get-level ok-then? 0= if no-result exit then
  lf-level-instantiate-mvars ok-then? 0= if no-result exit then
  lf-meta-level-normalize ok-then? if idl-decrement else no-result then ;

base !   \ the BASE this file was loaded with
