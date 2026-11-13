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
\ Never a guess: unsupported for a let, projection or literal, an
\ application with any other head, a lambda or pi whose body or domain
\ is itself a lambda or pi or none of the above (nested telescopes, let
\ telescopes, inferProjType: plan FE1c), a lambda's type holding a
\ metavariable (mkForallFVars's elimMVarDeps), a level Lean would get by
\ assigning a metavariable Sort ?u, a beta step under a binder of the
\ type (front/beta-inst.fs), and Sort's legacy numeric form.
\ Outcomes: ok; invalid for no term, a loose bound variable, a stale
\ leaf, an unknown constant, a wrong number of levels, a function
\ expected; unsupported as above; full when a store or slab has no room;
\ exhausted when whnfCore's fuel runs out (the fuel is per lf-whnf-core
\ call, so one inference may spend it once per argument and binder). A
\ failure gives -1.
\ Not re-entrant: one inference at a time per context uses the slabs
\ below (whnfCore and the instantiations it calls keep their own). Each
\ lambda or pi inferred adds its binders' free variables to the local
\ context, which only grows while a declaration is elaborated
\ (core/local-context.fs): the context is emptied with the declaration.
\ Untrusted: only the kernel's check of a finished term decides anything.
\ State: the record if-state (inferAppType's j) and the slabs if-args
\ (the arguments, last first), if-levels (a
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
require ./mvars.fs
require ./instantiate.fs
require ./level-params.fs
require ../present/binder-table.fs
require ./level-simp.fs
require ./level-normalize.fs
require ./meta-spine.fs
require ./whnf.fs
require ./beta-inst.fs

begin-structure /if
  field: if-from    \ inferAppType's j: the first argument not put in yet
end-structure
/if context-record: if-state
1 cells context-slab: if-args     \ the application's arguments, last first
1 cells context-slab: if-levels   \ a constant's universe arguments

: if-tag ( term -- tag ) lf-term-tag@ ;
: if-fail ( x outcome -- -1 outcome ) nip no-result ;

\ ---- Leaves.
: if-levels-fill ( slot -- outcome ) if-levels lf-meta-levels-fill ;
: if-levels-ok? ( slot d -- flag ) lf-input-params nip swap lf-cref-pairs nip = ;
: if-const-type ( slot d -- type outcome )
  over if-levels-fill dup ok? 0= if nip if-fail exit then drop nip
  dup lf-input-decl lf-idecl-type @ swap lf-input-params >r 0 if-levels slab-at r>
  lf-meta-instantiate-level-params ;
: if-slot ( const -- slot ) lf-term-first@ lf-cref-slot ;
: if-const ( const -- type outcome )
  dup lf-meta-const-decl 0= if outcome-invalid if-fail exit then
  swap if-slot swap 2dup if-levels-ok? 0= if 2drop -1 outcome-invalid exit then
  if-const-type ;
: if-fvar ( fvar -- type outcome )
  dup lf-fvar-live? if lf-fvar-type outcome-ok else outcome-invalid if-fail then ;
: if-mvar ( mvar -- type outcome )
  lf-mvar-type if outcome-ok else -1 outcome-invalid then ;
: if-sort-new ( level -- type outcome )
  dup lf-level-identity 0= if drop -1 outcome-full exit then
  lf-hterm-sort if drop outcome-ok else -1 outcome-full then ;
: if-sort ( sort -- type outcome )
  lf-term-first@ lf-level-succ if if-sort-new else -1 outcome-full then ;
: if-leaf ( term tag -- type outcome )
  case lf-tag-constant of if-const endof  lf-tag-fvar of if-fvar endof
    lf-tag-mvar of if-mvar endof  lf-tag-symbolic-sort of if-sort endof
    lf-tag-bvar of outcome-invalid if-fail endof
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
: if-firm-const? ( const -- flag )
  lf-meta-const-decl if lf-menv-kind lf-kind-definition <> else false then ;
: if-firm? ( head -- flag )
  dup if-tag lf-tag-constant = if if-firm-const? else if-inert? then ;
: if-no-pi ( type -- outcome )
  if-head if-firm? if outcome-invalid else outcome-unsupported then ;
: if-to-pi ( type -- pi outcome )
  lf-whnf-core ok-then? 0= if no-result exit then
  dup if-pi? if outcome-ok else dup if-no-pi if-fail then ;
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
\ A spine's head is no application; a lambda, pi, let or projection
\ there answers unsupported (if-leaf).
: if-head-type ( head -- type outcome ) dup if-tag if-leaf ;
: if-app ( term -- type outcome )
  if-spine ok-then? 0= if no-result exit then
  if-head-type ok-then? if if-args-in else no-result then ;

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
  swap lf-term-second@ swap lf-meta-instantiate1 ;
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
: if-body ( term -- type outcome )
  dup lf-meta-app? if if-app else dup if-tag if-leaf then ;
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
  if-head dup if-tag lf-tag-mvar = if drop outcome-unsupported exit then
  if-firm? if outcome-invalid else outcome-unsupported then ;
: if-sort-level ( T -- level outcome )
  dup if-sort? if lf-term-first@ outcome-ok exit then
  lf-whnf-core ok-then? 0= if no-result exit then
  dup if-sort? if lf-term-first@ outcome-ok else dup if-no-sort if-fail then ;
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

base !   \ the BASE this file was loaded with
