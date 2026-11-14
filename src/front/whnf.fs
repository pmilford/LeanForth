\ The front end's whnfCore and whnf (plan FE1c, S1 appendix D, S2 merge A;
\ ADR 0021 D6): ports of Lean 4.35.0's Meta.whnfCore (Lean/Meta/WHNF.lean,
\ with whnfEasyCases, reduceRec and projectCore?) under Meta's default
\ configuration (beta, zeta, zetaDelta, zetaHave, iota and proj :=
\ yesWithDelta on), of whnf (whnfImp, 1060) and of unfoldDefinition? (844),
\ over the term store, with no use of src/kernel/.
\ lf-whnf-core ( term -- term' outcome ) repeats one step on the term
\ until none applies:
\ - a sort, binder, literal or constant is itself; a loose bound variable
\   is invalid (Lean panics);
\ - an assigned metavariable is its value; a let variable of the local
\   context its value (zetaDelta); a let is its body with the value put in;
\ - a projection reduces its structure with whnf first (a frame, below);
\   when that is a constructor applied to more than its parameters and the
\   field's index, it is that argument; else the projection stays;
\ - an application f a1 .. an: a lambda head takes the arguments
\   (lf-meta-head-beta); an assigned metavariable, a let variable, a let
\   or a projection at the head is replaced as above, the arguments kept;
\   a recursor at the head reduces its major premise with whnf first (at
\   transparency all for Acc.rec and WellFounded.rec at default, isWFRec),
\   then, when that is a constructor application, fires the constructor's
\   rule (iota: the rule's right side, its universe parameters
\   instantiated, applied to the parameters, motives and minor premises,
\   the constructor's fields and the arguments after the major premise);
\   any other major premise leaves it; any other head, an unassigned
\   metavariable included, ends the reduction.
\ lf-whnf-core-at-defeq ( term -- term' outcome ) is whnfCoreAtDefEq
\ (ExprDefEq.lean, backward.isDefEq.lazyWhnfCore true: proj :=
\ yesWithDeltaI): a projection's structure, and everything inside that
\ reduction, by whnfAtMostI (instances transparency in place of all,
\ default or implicit).
\ lf-meta-whnf ( e -- e' outcome ) is whnf at the configured transparency
\ (meta-config.fs): whnfCore, then reduceNat? (answered unsupported where
\ it might fold: a constant of Nat's namespace with one or two arguments,
\ except Nat.succ of a term whnf leaves; plan S2 merge B), then
\ unfoldDefinition? (front/unfold.fs, lf-unfold-step): when it unfolds,
\ whnf again on the result. lf-meta-unfold ( e -- e' flag outcome ) is
\ unfoldDefinition? alone: the result and true, or e and false (none).
\ Where unfold.fs asks for a class field (reduceProj? at instances
\ transparency), the structure's whnf runs at instances and, when it is a
\ constructor, the field applied to the unfolded term's arguments with
\ head beta is the result; else unfoldDefault's result stands (ask-keep)
\ or nothing unfolds (ask-none, unfoldProjInst?).
\ Machine: an activation is whnfCore (lf-whnf-core's), whnf (every part:
\ a projection's structure, a recursor's major premise, a class field's
\ structure; lf-meta-whnf's) or unfoldDefinition? (lf-meta-unfold's).
\ Where Lean calls whnf on a part, the step keeps (term, aux, kind, the
\ activation, the transparency) on the heap stack wc-frames and goes on
\ with the part in a whnf activation; when the part is done the frame
\ resumes with it, its activation and transparency restored. No host
\ recursion (plan task 6.2.0 (b)); the transparency on entry is restored
\ on every exit.
\ Never a guess: unsupported for what Lean decides with a fact or a step
\ not ported yet -- a matcher or an auxiliary recursor at a definition's
\ head (whnfCore's matcher and deltaBetaDefinition steps, S2 merge B; a
\ definition that is neither stays), a definition with a `_sunfold` or not
\ known to have none (unfold.fs), a quotient's lift or ind, a
\ delayed-assigned metavariable at the head, a literal where Lean turns it
\ into constructors (toCtorIfLit), and, for a recursor: K-like ones
\ (toCtorWhenK infers the major premise's type), a major premise
\ Nat.succ of a term reduceNat? might fold (cleanupNatOffsetMajor), a
\ stuck major premise of a structure-like type (toCtorWhenStructure
\ eta-expands it), and a recursor of a mutual or nested block.
\ Let variables: Lean unfolds a let variable only when it is no "have"
\ (nondep) declaration; lf-fvar-let? is false for a have
\ (core/local-context.fs, lf-lctx-have, plan FE1g-1), which therefore
\ stays as it is, as Lean's whnfEasyCases leaves it.
\ Fuel: each step spends one; lf-whnf-fuel! sets the steps a call may
\ take (0: lf-whnf-default-fuel); none left is exhausted, never a term.
\ Each unfolding attempt (at least one per whnf, and one per part) also
\ spends one step of meta-config.fs's budget (none left: exhausted).
\ Outcomes: ok; invalid for a term or leaf that is not live, a loose
\ bound variable, a malformed let or an unknown constant whnf would
\ unfold; unsupported as above; full when a store or slab has no room;
\ exhausted. A failure gives -1 for the term.
\ lf-whnf-stuck ( term -- mvar true outcome | false outcome ), Lean's
\ getStuckMVar? for the same cases: the unassigned metavariable at the
\ head, a recursor's major premise or a projection's structure that is
\ one; unsupported where it would need whnf or a definition's facts.
\ lf-meta-whnf-r is whnfR (reducible), lf-meta-whnf-d whnfD (default), each
\ at its transparency whatever the configured one, which it gives back;
\ lf-meta-whnf-forall ( e -- e' outcome ) whnfForall (whnf's result when
\ it is a pi, else e); lf-meta-instantiate-forall ( e addr n -- e'
\ outcome ) instantiateForall (Basic.lean:2186): e's first n pis, each
\ made a pi by whnf when it is none, instantiated with the n terms at
\ addr; invalid when one is still no pi (Lean: too many parameters) or
\ n is negative.
\ Untrusted: only the kernel's check of a finished term decides anything.
\ State: the record wc (fuel, whether facts are asked, the activation,
\ the projection mode, lf-meta-unfold's answer, the transparency on
\ entry, the recursor step's term, head, data and declaration) and the
\ slabs wc-args, wc-margs, wc-levels and wc-frames, in the checker
\ context. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/local-context.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/let-terms.fs
require ../core/literals.fs
require ../core/projections.fs
require ../core/mvar-leaves.fs
require ../core/input.fs
require ./mvars.fs
require ./instantiate.fs
require ./level-params.fs
require ./meta-config.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./term-eqv.fs
require ./unfold.fs

100000 constant lf-whnf-default-fuel
begin-structure /wc
  field: wc-limit    \ steps a call may take; 0: the default
  field: wc-fuel     \ steps left in this call
  field: wc-facts    \ true: a definition head asks meta-env.fs's facts
  field: wc-act      \ the running activation: wc-core-act, -full- or -unfold-
  field: wc-proj-i   \ true: projections' structures by whnfAtMostI
  field: wc-unfolded \ lf-meta-unfold's answer: whether its term unfolded
  field: wc-mode0    \ the transparency on entry
  field: wc-src      \ the slab wc-apply reads arguments from (set just
                     \ before each use: wc-from; one step's register)
  field: wc-e        \ the recursor step's term,
  field: wc-head     \ its head constant,
  field: wc-data     \ the recursor's inductive data
  field: wc-aux      \ a frame's third cell: the recursor's declaration,
                     \ or a class field's unfolded term
  field: wc-fault    \ the first declaration that could not be decoded:
                     \ its outcome (full, unsupported), else ok
end-structure
/wc context-record: wc
1 cells context-slab: wc-args     \ the term's arguments, last first
1 cells context-slab: wc-margs    \ the major premise's arguments, last first
1 cells context-slab: wc-levels   \ the recursor's universe arguments
begin-structure /wcf
  field: wcf-kind    \ wc-proj-kind, wc-rec-kind or unfold.fs's ask code
  field: wcf-term    \ the step's term
  field: wcf-aux     \ a recursor's declaration, a class field's unfolded term
  field: wcf-act     \ the activation the frame resumes
  field: wcf-mode    \ the transparency it resumes at
end-structure
/wcf context-slab: wc-frames      \ the frames, the newest last
0 constant wc-core-act   1 constant wc-full-act   2 constant wc-unfold-act
: lf-whnf-fuel! ( n -- ) wc wc-limit ! ;
: wc-start ( -- )
  wc-frames slab-clear wc wc-limit @ ?dup 0= if lf-whnf-default-fuel then wc wc-fuel !
  outcome-ok wc wc-fault ! ;
: wc-full? ( -- flag ) wc wc-act @ wc-full-act = ;

\ ---- Results of a step ( -- term flag outcome ): flag true goes on.
: wc-done ( term -- term false outcome ) false outcome-ok ;
: wc-fail ( outcome -- -1 false outcome ) -1 false rot ;
: wc-go ( term outcome -- term flag outcome )
  ok-then? if true outcome-ok else wc-fail then ;
: wc-drop-fail ( x outcome -- -1 false outcome ) nip wc-fail ;
: wc-2drop-fail ( x y outcome -- -1 false outcome ) nip nip wc-fail ;

\ ---- Spines: the arguments of f a1 .. an in a slab, an first.
: wc-nth ( i -- term ) wc wc-src @ lf-meta-arg ;
\ f applied to arguments from to to-1 of the slab wc-src names.
: wc-app-at ( f k from -- f' outcome ) + wc-nth lf-meta-app ;
: wc-apply ( f from to -- f' outcome ) over - swap ['] wc-app-at ok-fold ;
: wc-from ( slab -- ) wc wc-src ! ;
: wc-rebuild ( head -- term outcome ) wc-args lf-meta-apply-all ;

\ ---- Frames: a step that needs the whnf of a part keeps (term, aux,
\ kind, activation, transparency) on wc-frames and goes on with the part
\ in a whnf activation; when the part is done, the frame resumes with it
\ (wc-resume), as Lean's call of whnf returns.
0 constant wc-proj-kind   1 constant wc-rec-kind
: wc-top ( -- frame ) wc-frames slab-last ;
: wc-keep ( frame -- ) wc wc-act @ over wcf-act ! lf-defeq-mode swap wcf-mode ! ;
\ One frame claimed whole, or none (full); the part's activation is whnf.
: wc-frame ( e aux kind -- outcome )
  1 wc-frames slab-claim nip dup ok? 0= if nip nip nip exit then drop
  wc-top tuck wcf-kind ! tuck wcf-aux ! tuck wcf-term ! wc-keep
  wc-full-act wc wc-act ! outcome-ok ;
: wc-restore ( frame -- ) dup wcf-act @ wc wc-act ! wcf-mode @ lf-defeq-mode! ;
: wc-pop ( -- kind )
  wc-top dup wc-restore dup wcf-aux @ wc wc-aux ! dup wcf-term @ wc wc-e ! wcf-kind @
  wc-frames slab-drop ;
: wc-framed? ( -- flag ) wc-frames slab-count 0> ;

\ ---- Leaves: metavariables, let variables, lets.
: wc-delayed? ( mvar -- flag ) lf-mvar-delayed dup if nip nip nip then ;
: wc-let-value ( fvar -- value true | false )
  dup lf-fvar-let? if lf-fvar-value true else drop false then ;
: wc-zeta ( let -- term outcome )
  dup lf-let-well? if dup lf-let-body swap lf-let-value lf-meta-instantiate1
  else drop -1 outcome-invalid then ;
: wc-mvar ( e -- e' flag outcome )
  dup lf-mvar-live? 0= if outcome-invalid wc-drop-fail exit then
  dup lf-mvar-value if nip true outcome-ok else wc-done then ;
: wc-fvar ( e -- e' flag outcome )
  dup lf-fvar-live? 0= if outcome-invalid wc-drop-fail exit then
  dup wc-let-value if nip true outcome-ok else wc-done then ;

\ ---- Heads of applications ( e head -- e' flag outcome ).
: wc-mvar-head ( e head -- e' flag outcome )
  dup lf-mvar-live? 0= if outcome-invalid wc-2drop-fail exit then
  dup lf-mvar-value if nip nip wc-rebuild wc-go exit then
  wc-delayed? if outcome-unsupported wc-drop-fail else wc-done then ;
: wc-fvar-head ( e head -- e' flag outcome )
  dup lf-fvar-live? 0= if outcome-invalid wc-2drop-fail exit then
  wc-let-value if nip wc-rebuild wc-go else wc-done then ;
: wc-let-head ( e head -- e' flag outcome )
  nip wc-zeta ok-then? if wc-rebuild else no-result then wc-go ;
: wc-unsupported ( e head -- e' flag outcome ) outcome-unsupported wc-2drop-fail ;
: wc-invalid ( e head -- e' flag outcome ) outcome-invalid wc-2drop-fail ;

\ ---- Constants: the input's declaration of the name (Lean's find?). A
\ declaration that could not be decoded is no unknown constant: wc-kind
\ keeps its outcome as the call's fault, which ends the call (wc-checked).
: wc-name ( const -- name ) lf-term-first@ lf-cref-slot lf-cref-name@ drop ;
: wc-levels# ( const -- n ) lf-term-first@ lf-cref-slot lf-cref-pairs nip ;
0 constant wc-no-kind   \ not a constant, or one no declaration has
: wc-fault! ( d outcome -- )
  nip dup outcome-invalid = if drop else wc wc-fault outcome-first! then ;
: wc-const-kind ( const -- kind )
  lf-meta-const-decl ok-then? if lf-menv-kind else -1 swap wc-fault! wc-no-kind then ;
: wc-kind ( term -- kind )
  dup lf-term-const? if wc-const-kind else drop wc-no-kind then ;
: wc-faulted ( -- outcome ) wc wc-fault @ ;

\ ---- Recursors (reduceRec). The step's term, head and inductive data
\ are kept in wc; the arguments in wc-args, the major premise's in
\ wc-margs.
: wc-irc ( k -- x ) wc wc-data @ swap lf-more-field ;
: wc-prefix ( -- n ) lf-irc-params wc-irc lf-irc-motives wc-irc + lf-irc-minors wc-irc + ;
: wc-major-at ( -- k ) wc-prefix lf-irc-indices wc-irc + ;
: wc-k? ( -- flag ) lf-irc-k wc-irc 0<> ;
\ One motive: neither mutual nor nested, so the major premise's type is
\ the block's one type.
: wc-single? ( -- flag ) lf-irc-motives wc-irc 1 = ;
: wc-term ( -- e ) wc wc-e @ ;
: wc-stay ( -- e false outcome ) wc-term wc-done ;
: wc-short? ( -- flag ) wc-args slab-count wc-major-at > 0= ;
: wc-major ( -- term ) wc-major-at wc-args lf-meta-arg ;

\ The rule of a constructor: its right side and fields, or none.
: wc-rule? ( name rule -- flag ) lf-irule-ctor = ;
: wc-rule ( name -- rule true | false )
  wc wc-data @ lf-irc-rules@ 0 ?do
    2dup i lf-irc-rule wc-rule? if i lf-irc-rule nip true unloop exit then
  loop 2drop false ;

\ A major premise's argument that whnf leaves as it is, and is a literal
\ only if it is one: Nat.succ of it is not folded differently.
: wc-unassigned? ( term -- flag )
  dup lf-mvar-live? if lf-mvar-value dup if nip then 0= else drop false then ;
: wc-plain-mvar? ( term -- flag )
  dup wc-unassigned? if wc-delayed? 0= else drop false then ;
: wc-plain-fvar? ( term -- flag )
  dup lf-fvar-live? if lf-fvar-let? 0= else drop false then ;
: wc-sort? ( term -- flag )
  lf-term-tag@ dup lf-tag-sort = swap lf-tag-symbolic-sort = or ;
: wc-inert? ( term -- flag )
  dup wc-plain-fvar? over wc-plain-mvar? or over lf-term-binder? or swap wc-sort? or ;
\ Nat.succ applied to one argument that whnf might fold (reduceNat?).
: wc-succ? ( head -- flag )
  dup lf-term-const? if wc-name lf-menv-nat-succ? wc-margs slab-count 1 = and
  else drop false then ;
: wc-foldable? ( head -- flag )
  wc-succ? 0= if false exit then
  0 wc-margs lf-meta-arg dup wc-inert? swap lf-lit-leaf? or 0= ;

\ The universe arguments of the recursor's constant, as levels.
: wc-levels-fill ( const -- outcome )
  lf-term-first@ lf-cref-slot wc-levels lf-meta-levels-fill ;
: wc-levels-at ( -- addr ) 0 wc-levels slab-at ;
: wc-rec-params ( -- names n ) wc wc-head @ lf-meta-const-decl drop lf-menv-params ;
: wc-levels-ok? ( -- flag ) wc-rec-params nip wc wc-head @ wc-levels# = ;
: wc-rhs-levels ( rhs -- rhs' outcome )
  wc wc-head @ wc-levels-fill dup ok? 0= if nip no-result exit then drop
  wc-rec-params >r wc-levels-at r> lf-meta-instantiate-level-params ;

\ rhs applied to the prefix, the constructor's fields (the last nfields
\ of its arguments, all when it has fewer) and the rest.
: wc-fields ( rhs nfields -- rhs' outcome )
  wc-margs wc-from wc-margs slab-count tuck swap - 0 max swap wc-apply ;
: wc-rest ( rhs -- rhs' outcome )
  wc-args wc-from wc-major-at 1+ wc-args slab-count wc-apply ;
: wc-prefixed ( rhs -- rhs' outcome ) wc-args wc-from 0 wc-prefix wc-apply ;
: wc-fire ( rule -- term outcome )
  dup lf-irule-nfields swap lf-irule-rhs wc-rhs-levels
  ok-then? 0= if nip no-result exit then
  wc-prefixed ok-then? 0= if nip no-result exit then
  swap wc-fields ok-then? if wc-rest else no-result then ;
: wc-ctor-major ( mhead -- e' flag outcome )
  dup wc-foldable? if drop outcome-unsupported wc-fail exit then
  wc-name wc-rule 0= if wc-stay exit then
  wc-levels-ok? 0= if drop wc-stay exit then wc-fire wc-go ;

\ The block's one type (toCtorWhenStructure): when it is structure-like,
\ a major premise that is not a constructor applied to exactly its
\ parameters and fields is eta-expanded with its inferred type. Its data,
\ or 0 and unsupported when no declaration has its name; a declaration
\ that could not be decoded passes its outcome on (full as full).
: wc-induct-data ( -- data outcome )
  wc wc-data @ lf-irc-all@ drop @ lf-menv-find
  ok-then? if lf-menv-data outcome-ok exit then
  dup outcome-invalid = if drop outcome-unsupported then 0 swap ;
: wc-structure-like? ( data -- flag )
  dup lf-ity-indices lf-more-field 0= over lf-ity-ctors@ nip 1 = and
  swap lf-ity-flags lf-more-field lf-ity-rec-bit and 0= and ;
: wc-ctor? ( mhead -- flag ) wc-kind lf-kind-constructor = ;
: wc-ctor-arity ( mhead -- n )
  lf-meta-const-decl drop lf-menv-data dup lf-ict-params lf-more-field
  swap lf-ict-fields lf-more-field + ;
: wc-exact? ( mhead -- flag )
  dup wc-ctor? if wc-ctor-arity wc-margs slab-count = else drop false then ;
: wc-eta? ( mhead data -- flag ) wc-structure-like? if wc-exact? 0= else drop false then ;
\ Heads whose application whnf leaves as it is and no rule matches
\ (getStuckMVar? below asks them).
: wc-head-inert? ( mhead -- flag )
  dup wc-plain-fvar? over wc-plain-mvar? or swap wc-sort? or ;
: wc-leaf-inert? ( mhead -- flag )
  wc-margs slab-count 0= if lf-term-binder? else drop false then ;
: wc-const-inert? ( mhead -- flag )
  wc-kind dup lf-kind-inductive = over lf-kind-axiom = or swap lf-kind-theorem = or ;
: wc-inert-major? ( mhead -- flag )
  dup wc-head-inert? over wc-leaf-inert? or swap wc-const-inert? or ;
\ The major premise's whnf: a constructor fires its rule, a literal
\ (toCtorIfLit) answers unsupported, any other head leaves the recursor.
: wc-major-head ( mhead -- e' flag outcome )
  wc-induct-data ok-then? 0= if nip wc-fail exit then
  over swap wc-eta? if drop outcome-unsupported wc-fail exit then
  dup wc-ctor? if wc-ctor-major exit then
  lf-lit-leaf? if outcome-unsupported wc-fail else wc-stay then ;
\ isWFRec: Acc.rec and WellFounded.rec reduce their major premise at
\ transparency all when it is default.
: wc-wf-bump ( -- )
  wc wc-head @ wc-name lf-menv-wf-rec? lf-defeq-mode lf-tr-default = and
  if lf-tr-all lf-defeq-mode! then ;
: wc-reduce-rec ( -- e' flag outcome )
  wc-short? if wc-stay exit then
  wc-k? wc-single? 0= or if outcome-unsupported wc-fail exit then
  wc-major wc-term wc wc-aux @ wc-rec-kind wc-frame ok-then? 0= if wc-fail exit then
  wc-wf-bump true outcome-ok ;
: wc-iota ( e head d -- e' flag outcome )
  dup wc wc-aux ! lf-menv-data wc wc-data ! wc wc-head ! wc wc-e !
  wc-reduce-rec ;
\ Resumed with the major premise's whnf r: the step's state again, then
\ r's head decides.
: wc-rec-frame ( -- outcome )
  wc wc-aux @ lf-menv-data wc wc-data !
  wc-term wc-args lf-meta-spine ok-then? if wc wc-head ! outcome-ok then ;
: wc-rec-resume ( r -- e' flag outcome )
  wc-rec-frame dup ok? 0= if wc-drop-fail exit then drop
  wc-margs lf-meta-spine ok-then? if wc-major-head else wc-fail then ;

\ ---- Projections (projectCore?): the structure's whnf r, a constructor
\ applied to more than its parameters and the field's index, gives that
\ argument; any other r leaves the projection; a literal, which
\ toCtorIfLit turns into constructors, answers unsupported.
\ whnfAtMostI (proj := yesWithDeltaI): all, default and implicit become
\ instances.
: wc-at-most-i ( mode -- mode' )
  dup lf-tr-all = over lf-tr-default = or over lf-tr-implicit = or
  if drop lf-tr-instances then ;
: wc-lower ( -- ) wc wc-proj-i @ if lf-defeq-mode wc-at-most-i lf-defeq-mode! then ;
: wc-proj-at ( p -- k ) lf-proj-leaf lf-proj-idx ;
: wc-ctor-params ( ctor -- n )
  lf-meta-const-decl drop lf-menv-data lf-ict-params lf-more-field ;
: wc-field ( rhead p -- x true | false )
  wc-proj-at swap wc-ctor-params + dup wc-margs slab-count <
  if wc-margs lf-meta-arg true else drop false then ;
: wc-project ( rhead p -- x true | false )
  over wc-ctor? if wc-field else 2drop false then ;
: wc-proj-frame ( -- p outcome ) wc-term wc-args lf-meta-spine ;
: wc-proj-resume ( r -- e' flag outcome )
  wc-margs lf-meta-spine ok-then? 0= if wc-fail exit then
  dup lf-lit-leaf? if drop outcome-unsupported wc-fail exit then
  wc-proj-frame ok-then? 0= if wc-drop-fail exit then
  wc-project if wc-rebuild wc-go else wc-stay then ;
: wc-proj-head ( e head -- e' flag outcome )
  lf-proj-struct swap 0 wc-proj-kind wc-frame ok-then? 0= if wc-fail exit then
  wc-lower true outcome-ok ;

: wc-blocked? ( d -- flag )
  lf-menv-kind dup lf-kind-definition = swap lf-kind-quotient = or ;
: wc-recursor? ( d -- flag ) lf-menv-kind lf-kind-recursor = ;
\ With facts asked, a definition that is certainly no matcher and no
\ auxiliary recursor stays (Lean's whnfCore returns e).
: wc-fact-no? ( d xt -- flag ) execute ok? swap 0= and ;
: wc-inert-defn? ( d -- flag )
  wc wc-facts @ 0= if drop false exit then dup lf-menv-kind lf-kind-definition <>
  if drop false exit then
  dup ['] lf-menv-matcher? wc-fact-no? swap ['] lf-menv-aux-recursor? wc-fact-no? and ;
: wc-decl-head ( e head d -- e' flag outcome )
  dup wc-inert-defn? if 2drop wc-done exit then
  dup wc-blocked? if drop wc-unsupported exit then
  dup wc-recursor? if wc-iota else 2drop wc-done then ;
\ A constant no declaration has stays; one that could not be decoded fails.
: wc-unknown-head ( e head outcome -- e' flag outcome )
  dup outcome-invalid = if 2drop wc-done else nip nip wc-fail then ;
: wc-const-head ( e head -- e' flag outcome )
  dup lf-meta-const-decl ok-then? if wc-decl-head else wc-unknown-head then ;

\ ---- One step of whnfCore.
: wc-head-tag ( e head tag -- e' flag outcome )
  case lf-tag-mvar of wc-mvar-head endof  lf-tag-fvar of wc-fvar-head endof
    lf-tag-constant of wc-const-head endof  lf-tag-projection of wc-proj-head endof
    lf-tag-bvar of wc-invalid endof  >r drop wc-done r> endcase ;
: wc-head-step ( e head -- e' flag outcome )
  dup lf-term-lam? if drop lf-meta-head-beta wc-go exit then
  dup lf-let? if wc-let-head else dup lf-term-tag@ wc-head-tag then ;
: wc-app ( e -- e' flag outcome )
  dup wc-args lf-meta-spine ok-then? if wc-head-step else wc-drop-fail then ;
: wc-leaf-step ( e tag -- e' flag outcome )
  case lf-tag-mvar of wc-mvar endof  lf-tag-fvar of wc-fvar endof
    lf-tag-projection of dup wc-proj-head endof
    lf-tag-bvar of outcome-invalid wc-drop-fail endof  >r wc-done r> endcase ;
: wc-core-step ( e -- e' flag outcome )
  dup lf-let? if wc-zeta wc-go exit then
  dup lf-meta-app? if wc-app else dup lf-term-tag@ wc-leaf-step then ;

\ ---- reduceNat?: a constant of Nat's namespace with one or two arguments
\ (Lean's list, taken widely), except Nat.succ of a term whnf leaves.
: wm-head-named? ( e xt -- flag )
  swap lf-meta-head dup lf-term-const? if wc-name swap execute else 2drop false then ;
: wm-succ-inert? ( e -- flag )
  dup ['] lf-menv-nat-succ? wm-head-named?
  if lf-term-second@ wc-inert? else drop false then ;
: wm-nat? ( e -- flag )
  dup lf-meta-args# 1 3 within over ['] lf-menv-nat-name? wm-head-named? and
  if wm-succ-inert? 0= else drop false then ;

\ ---- Delta: whnf's step once whnfCore ends (reduceNat?, then
\ unfoldDefinition?), and lf-meta-unfold's one step. An unfolding goes on
\ in a whnf activation and ends lf-meta-unfold's (wc-unfolded); a class
\ field's structure goes on as a part at instances transparency.
: wc-advance ( e' -- e' flag outcome )
  wc-full? if true else true wc wc-unfolded ! false then outcome-ok ;
: wc-field-of ( -- s ) wc-top wcf-aux @ lf-meta-head lf-proj-struct ;
: wc-ask ( e e' code -- s flag outcome )
  wc-frame dup ok? 0= if wc-fail exit then drop
  lf-tr-instances lf-defeq-mode! wc-field-of true outcome-ok ;
: wc-unfold-code ( e e' code -- e'' flag outcome )
  dup lf-unfold-none = if 2drop wc-done exit then
  dup lf-unfold-made = if drop nip wc-advance else wc-ask then ;
: wc-unfold ( e -- e' flag outcome )
  dup lf-unfold-step ok-then2? if wc-unfold-code else wc-drop-fail then ;
: wc-delta ( e -- e' flag outcome )
  wc-full? if dup wm-nat? if outcome-unsupported wc-drop-fail exit then then
  lf-meta-spend? if wc-unfold else outcome-exhausted wc-drop-fail then ;
\ After a whnfCore step: when it ends, a whnf activation tries delta.
: wc-then-delta ( e flag outcome -- e' flag' outcome )
  dup ok? 0= if exit then drop dup if outcome-ok exit then
  drop wc-full? if wc-delta else false outcome-ok then ;
: wc-step ( e -- e' flag outcome ) wc-core-step wc-then-delta ;

\ ---- Resuming a frame with its part's whnf r. A class field: the field
\ applied to the unfolded term's arguments with head beta, else the
\ unfolded term (ask-keep) or nothing (ask-none).
: wc-field-arg ( r -- x flag outcome )
  wc-margs lf-meta-spine ok-then? 0= if wc-fail exit then
  dup lf-lit-leaf? if drop outcome-unsupported wc-fail exit then
  wc wc-aux @ lf-meta-head wc-project if true else -1 false then outcome-ok ;
: wc-field-apply ( x -- y outcome )
  wc wc-aux @ wc-args lf-meta-spine ok-then? 0= if nip no-result exit then drop
  wc-rebuild ok-then? if lf-meta-head-beta else no-result then ;
: wc-field-none ( kind -- e' flag outcome )
  lf-unfold-ask-keep = if wc wc-aux @ wc-advance else wc-stay then ;
: wc-field-got ( kind x flag -- e' flag outcome )
  if nip wc-field-apply ok-then? if wc-advance else wc-fail then
  else drop wc-field-none then ;
: wc-field-resume ( r kind -- e' flag outcome )
  swap wc-field-arg ok-then2? if wc-field-got else nip wc-fail then ;
: wc-core-resume ( r kind -- e' flag outcome )
  wc-rec-kind = if wc-rec-resume else wc-proj-resume then wc-then-delta ;
: wc-resume ( r -- e' flag outcome )
  wc-pop dup lf-unfold-ask-keep < if wc-core-resume else wc-field-resume then ;

\ ---- The loop.
: wc-spend ( -- flag ) wc wc-fuel @ dup 0> if 1- wc wc-fuel ! true else drop false then ;
: wc-next ( e flag -- e' flag' outcome )
  begin dup 0= wc-framed? and while drop wc-resume dup ok? 0= if exit then drop repeat
  outcome-ok ;
\ After a step, a fault (wc-kind's, the first failure) ends the call with
\ its outcome, whatever the step gave.
: wc-checked ( e flag outcome -- e' flag outcome )
  wc-faulted dup ok? if drop else nip nip nip wc-fail then ;
: wc-turn ( e -- e' flag outcome ) wc-step dup ok? if drop wc-next then wc-checked ;
: wc-loop ( e -- e' outcome )
  begin wc-spend 0= if drop -1 outcome-exhausted exit then
    wc-turn dup ok? 0= if nip exit then drop
  0= until outcome-ok ;
\ A call: the activation, the projection mode and the facts flag set, the
\ transparency on entry restored at the end.
: wc-enter ( act proj-i -- )
  wc wc-proj-i ! wc wc-act ! false wc wc-unfolded ! lf-defeq-mode wc wc-mode0 ! wc-start ;
: wc-leave ( -- ) wc wc-mode0 @ lf-defeq-mode! ;
: wc-run ( e act proj-i -- e' outcome )
  wc-enter dup lf-term-root? if wc-loop else drop -1 outcome-invalid then wc-leave ;
: wc-core ( term facts -- term' outcome ) wc wc-facts ! wc-core-act false wc-run ;
: lf-whnf-core ( term -- term' outcome ) true wc-core ;
: lf-whnf-core-at-defeq ( term -- term' outcome )
  true wc wc-facts ! wc-core-act true wc-run ;

\ ---- whnf (lf-meta-whnf) and unfoldDefinition? (lf-meta-unfold).
: lf-meta-whnf ( e -- e' outcome ) true wc wc-facts ! wc-full-act false wc-run ;
: wc-unfold-run ( e -- e' outcome )
  wc-delta ok-then2? 0= if no-result exit then if wc-loop else outcome-ok then ;
: wc-answer ( e' outcome -- e' flag outcome )
  dup ok? if wc wc-unfolded @ else false then swap ;
: lf-meta-unfold ( e -- e' flag outcome )
  dup lf-term-root? 0= if drop -1 false outcome-invalid exit then
  true wc wc-facts ! wc-unfold-act false wc-enter wc-unfold-run wc-leave wc-answer ;
\ whnfR and whnfD: whnf at reducible or default transparency, the
\ configured one restored.
: wm-at ( e mode -- e' outcome ) ['] lf-meta-whnf swap lf-meta-at ;
: lf-meta-whnf-r ( e -- e' outcome ) lf-tr-reducible wm-at ;
: lf-meta-whnf-d ( e -- e' outcome ) lf-tr-default wm-at ;
: lf-meta-whnf-forall ( e -- e' outcome )
  dup lf-meta-whnf ok-then? 0= if nip no-result exit then
  dup lf-term-pi? if nip else drop then outcome-ok ;
\ instantiateForall's step: e made a pi (whnf when it is none), its body
\ instantiated with p.
: wm-to-pi ( e -- pi outcome )
  dup lf-term-pi? if outcome-ok else drop -1 outcome-invalid then ;
: wm-pi ( e -- pi outcome )
  dup lf-term-pi? if outcome-ok exit then
  lf-meta-whnf ok-then? if wm-to-pi else no-result then ;
: wm-inst ( e p -- e' outcome )
  swap wm-pi ok-then? 0= if nip no-result exit then
  lf-term-second@ swap lf-meta-instantiate1 ;
: wm-inst-at ( e k addr -- e' outcome ) swap cells + @ wm-inst ;
: lf-meta-instantiate-forall ( e addr n -- e' outcome )
  dup 0< if drop 2drop outcome-invalid no-result exit then
  swap ['] wm-inst-at ok-fold ok-then? if outcome-ok else no-result then ;

\ ---- getStuckMVar?: the unassigned metavariable at the head, or one
\ that is a recursor's major premise (isRecStuck?: none for a K-like
\ recursor); a definition's application without metavariables has none
\ (its data word is known), one with them needs its projection facts.
: ws-mvar ( mvar -- mvar true outcome | false outcome )
  dup lf-mvar-live? 0= if drop false outcome-invalid exit then
  dup wc-plain-mvar? if true outcome-ok else drop false outcome-unsupported then ;
: ws-none? ( flag -- false outcome )
  false swap if outcome-ok else outcome-unsupported then ;
: ws-major-head ( mhead -- mvar true outcome | false outcome )
  dup wc-plain-mvar? if true outcome-ok exit then
  dup wc-foldable? if drop false outcome-unsupported exit then
  dup wc-ctor? swap wc-inert-major? or ws-none? ;
: ws-major ( -- mvar true outcome | false outcome )
  wc-k? wc-short? or if false outcome-ok exit then
  wc-major wc-margs lf-meta-spine ok-then? if ws-major-head else false swap then ;
: ws-rec ( head d -- mvar true outcome | false outcome )
  lf-menv-data wc wc-data ! drop ws-major ;
\ A binary node's data word is known only when no metavariable is in it
\ (core/terms.fs): Lean's hasExprMVar is false.
: ws-kind ( e d -- false outcome )
  lf-menv-kind dup lf-kind-quotient = if 2drop false outcome-unsupported exit then
  lf-kind-definition = if lf-meta-mvar-free? ws-none? else drop false outcome-ok then ;
: ws-unknown ( e head outcome -- false outcome )
  nip nip dup outcome-invalid = if drop outcome-ok then false swap ;
: ws-const ( e head -- mvar true outcome | false outcome )
  dup lf-meta-const-decl ok-then? 0= if ws-unknown exit then
  dup wc-recursor? if rot drop ws-rec else nip ws-kind then ;
\ A projection (Lean: getStuckMVar? of its structure's whnf): a structure
\ whose head is a plain metavariable is stuck on it, as whnf leaves it;
\ any other would need whnf first.
: ws-proj ( proj -- mvar true outcome | false outcome )
  lf-proj-struct wc-margs lf-meta-spine ok-then? 0= if false swap exit then
  dup wc-plain-mvar? if true outcome-ok else drop false outcome-unsupported then ;
: ws-app ( e -- mvar true outcome | false outcome )
  dup wc-args lf-meta-spine ok-then? 0= if nip false swap exit then
  dup lf-term-tag@ case
    lf-tag-mvar of nip ws-mvar endof  lf-tag-constant of ws-const endof
    lf-tag-projection of nip ws-proj endof  >r 2drop false outcome-ok r> endcase ;
\ A fault (wc-kind's, the first failure) replaces the answer.
: ws-checked ( mvar true outcome | false outcome -- mvar true outcome | false outcome )
  wc-faulted dup ok? if drop exit then nip swap if nip then false swap ;
: ws-run ( term -- mvar true outcome | false outcome )
  dup lf-term-tag@ case lf-tag-mvar of ws-mvar endof  lf-tag-app of ws-app endof
    lf-tag-projection of ws-proj endof  >r drop true ws-none? r> endcase ;
: lf-whnf-stuck ( term -- mvar true outcome | false outcome )
  dup lf-term-root? 0= if drop false outcome-invalid exit then
  outcome-ok wc wc-fault ! ws-run ws-checked ;

base !   \ the BASE this file was loaded with
