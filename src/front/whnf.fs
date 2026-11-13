\ The front end's whnfCore (plan FE1c; ADR 0021 D6): a port of Lean
\ 4.35.0's Meta.whnfCore (Lean/Meta/WHNF.lean, with whnfEasyCases,
\ reduceRec and projectCore?) under Meta's default configuration (beta,
\ zeta, zetaDelta, zetaHave, iota and proj := yesWithDelta on), over the
\ term store, with no use of src/kernel/.
\ lf-whnf-core ( term -- term' outcome ) repeats one step on the term
\ until none applies:
\ - a sort, binder, literal or constant is itself; a loose bound variable
\   is invalid (Lean panics);
\ - an assigned metavariable is its value; a let variable of the local
\   context its value (zetaDelta); a let is its body with the value put in;
\ - a projection reduces its structure first (a frame, below); when that
\   is a constructor applied to more than its parameters and the field's
\   index, it is that argument; else the projection stays;
\ - an application f a1 .. an: a lambda head takes the arguments
\   (lf-meta-head-beta); an assigned metavariable, a let variable, a let
\   or a projection at the head is replaced as above, the arguments kept;
\   a recursor at the head reduces its major premise first, then, when
\   that is a constructor application, fires the constructor's rule
\   (iota: the rule's right side, its universe parameters instantiated,
\   applied to the parameters, motives and minor premises, the
\   constructor's fields and the arguments after the major premise); any
\   other head, an unassigned metavariable included, ends the reduction.
\ Frames: where Lean calls whnf on a part (a projection's structure, a
\ recursor's major premise), the step keeps (kind, term, aux) on the heap
\ stack wc-frames and goes on with the part; when the part is done the
\ frame resumes with it. Lean's whnf adds delta and Nat literal folding to
\ whnfCore; a part whose whnfCore ends where whnf would do more (a
\ definition, an unknown constant, a literal, Nat.succ of what reduceNat?
\ or the Nat offsets would change) answers unsupported.
\ Never a guess: unsupported for what Lean decides with a fact or a step
\ not ported yet -- a definition at the head (Lean first asks whether it
\ is a matcher, then whether it is an auxiliary recursor: facts the
\ export lacks, front/meta-env.fs, plan FE1d2), a quotient's lift or ind,
\ a delayed-assigned metavariable at the head, and, for a recursor:
\ K-like ones (toCtorWhenK infers the major premise's type), a stuck
\ major premise of a structure-like type (toCtorWhenStructure
\ eta-expands it), and a recursor of a mutual or nested block.
\ Let variables: Lean unfolds a let variable only when it is no "have"
\ (nondep) declaration; core/local-context.fs has no such flag, and every
\ let variable it holds is a let, so each is unfolded (the flag comes with
\ the let telescopes of plan FE1c).
\ Fuel: each step spends one; lf-whnf-fuel! sets the steps a call may
\ take (0: lf-whnf-default-fuel); none left is exhausted, never a term.
\ Outcomes: ok; invalid for a term or leaf that is not live, a loose
\ bound variable or a malformed let; unsupported as above; full when a
\ store or slab has no room; exhausted. A failure gives -1 for the term.
\ lf-whnf-stuck ( term -- mvar true outcome | false outcome ), Lean's
\ getStuckMVar? for the same cases: the unassigned metavariable at the
\ head, a recursor's major premise or a projection's structure that is
\ one; unsupported where it would need whnf or a definition's facts.
\ Untrusted: only the kernel's check of a finished term decides anything.
\ State: the record wc (fuel, the recursor step's term, head, data and
\ declaration) and the slabs wc-args, wc-margs, wc-levels and wc-frames,
\ in the checker context. Loads in decimal whatever BASE is, then
\ restores it.

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
require ./meta-env.fs
require ./meta-spine.fs

100000 constant lf-whnf-default-fuel
begin-structure /wc
  field: wc-limit    \ steps a call may take; 0: the default
  field: wc-fuel     \ steps left in this call
  field: wc-src      \ the slab wc-apply reads arguments from (set just
                     \ before each use: wc-from; one step's register)
  field: wc-e        \ the recursor step's term,
  field: wc-head     \ its head constant,
  field: wc-data     \ the recursor's inductive data
  field: wc-aux      \ a frame's third cell: the recursor's declaration
end-structure
/wc context-record: wc
1 cells context-slab: wc-args     \ the term's arguments, last first
1 cells context-slab: wc-margs    \ the major premise's arguments, last first
1 cells context-slab: wc-levels   \ the recursor's universe arguments
begin-structure /wcf
  field: wcf-kind    \ wc-proj-kind or wc-rec-kind
  field: wcf-term    \ the step's term
  field: wcf-aux     \ a recursor step's declaration
end-structure
/wcf context-slab: wc-frames      \ the frames, the newest last
: lf-whnf-fuel! ( n -- ) wc wc-limit ! ;
: wc-start ( -- )
  wc-frames slab-clear wc wc-limit @ ?dup 0= if lf-whnf-default-fuel then wc wc-fuel ! ;

\ ---- Results of a step ( -- term flag outcome ): flag true goes on.
: wc-done ( term -- term false outcome ) false outcome-ok ;
: wc-fail ( outcome -- -1 false outcome ) -1 false rot ;
: wc-go ( term outcome -- term flag outcome )
  ok-then? if true outcome-ok else wc-fail then ;
: wc-drop-fail ( x outcome -- -1 false outcome ) nip wc-fail ;
: wc-2drop-fail ( x y outcome -- -1 false outcome ) nip nip wc-fail ;

\ ---- Spines: the arguments of f a1 .. an in a slab, an first.
: wc-nth ( i -- term ) wc wc-src @ lf-meta-arg ;
: wc-app1 ( f a -- f' outcome ) lf-term-app if outcome-ok else -1 outcome-full then ;
\ f applied to arguments from to to-1 of the slab wc-src names.
: wc-apply ( f from to -- f' outcome )
  swap ?do i wc-nth wc-app1 ok-then? 0= if -1 swap unloop exit then loop outcome-ok ;
: wc-from ( slab -- ) wc wc-src ! ;
: wc-rebuild ( head -- term outcome ) wc-args wc-from 0 wc-args slab-count wc-apply ;

\ ---- Frames: a step that needs the whnf of a part (a projection's
\ structure, a recursor's major premise) keeps (kind, term, aux) on
\ wc-frames and goes on with the part; when the part is done, the frame
\ resumes with it (wc-resume), as Lean's call of whnf returns.
0 constant wc-proj-kind   1 constant wc-rec-kind
: wc-top ( -- frame ) wc-frames dup slab-count 1- swap slab-at ;
\ One frame claimed whole, or none (full).
: wc-frame ( kind e aux -- outcome )
  1 wc-frames slab-claim nip dup ok? 0= if >r 2drop drop r> exit then drop
  wc-top tuck wcf-aux ! tuck wcf-term ! wcf-kind ! outcome-ok ;
: wc-pop ( -- kind )
  wc-top dup wcf-aux @ wc wc-aux ! dup wcf-term @ wc wc-e ! wcf-kind @
  -1 wc-frames slab-commit ;
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

\ ---- Constants: the input's declaration of the name (Lean's find?).
: wc-name ( const -- name ) lf-term-first@ lf-cref-slot lf-cref-name@ drop ;
: wc-levels# ( const -- n ) lf-term-first@ lf-cref-slot lf-cref-pairs nip ;
0 constant wc-no-kind   \ not a constant, or one no declaration has
: wc-kind ( term -- kind ) dup lf-term-tag@ lf-tag-constant = if
    lf-meta-const-decl if lf-menv-kind exit then wc-no-kind exit then drop wc-no-kind ;

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
: wc-binder? ( term -- flag ) lf-term-tag@ lf-term-binder-tag? ;
: wc-sort? ( term -- flag )
  lf-term-tag@ dup lf-tag-sort = swap lf-tag-symbolic-sort = or ;
: wc-inert? ( term -- flag )
  dup wc-plain-fvar? over wc-plain-mvar? or over wc-binder? or swap wc-sort? or ;
: wc-lit? ( term -- flag ) lf-term-tag@ lf-tag-lit = ;
\ Nat.succ applied to one argument that whnf might fold (reduceNat?).
: wc-const? ( term -- flag ) lf-term-tag@ lf-tag-constant = ;
: wc-succ? ( head -- flag )
  dup wc-const? if wc-name lf-menv-nat-succ? wc-margs slab-count 1 = and
  else drop false then ;
: wc-foldable? ( head -- flag )
  wc-succ? if 0 wc-margs lf-meta-arg dup wc-inert? swap wc-lit? or 0= else false then ;

\ The universe arguments of the recursor's constant, as levels.
: wc-levels-fill ( const -- outcome )
  lf-term-first@ lf-cref-slot wc-levels lf-meta-levels-fill ;
: wc-levels-at ( -- addr ) 0 wc-levels slab-at ;
: wc-rec-params ( -- names n ) wc wc-head @ lf-meta-const-decl drop lf-input-params ;
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
\ parameters and fields is eta-expanded with its inferred type.
: wc-induct-data ( -- data|0 )
  wc wc-data @ lf-irc-all@ drop @ lf-input-newest dup 0< if drop 0 exit then
  lf-input-decl lf-idecl-data ;
: wc-structure-like? ( data -- flag )
  dup lf-ity-indices lf-more-field 0= over lf-ity-ctors@ nip 1 = and
  swap lf-ity-flags lf-more-field lf-ity-rec-bit and 0= and ;
: wc-ctor? ( mhead -- flag ) wc-kind lf-kind-constructor = ;
: wc-ctor-arity ( mhead -- n )
  lf-meta-const-decl drop lf-input-decl lf-idecl-data dup lf-ict-params lf-more-field
  swap lf-ict-fields lf-more-field + ;
: wc-exact? ( mhead -- flag )
  dup wc-ctor? if wc-ctor-arity wc-margs slab-count = else drop false then ;
: wc-eta? ( mhead data -- flag ) wc-structure-like? if wc-exact? 0= else drop false then ;
\ Heads whose application whnf leaves as it is and no rule matches.
: wc-head-inert? ( mhead -- flag )
  dup wc-plain-fvar? over wc-plain-mvar? or swap wc-sort? or ;
: wc-leaf-inert? ( mhead -- flag )
  wc-margs slab-count 0= if wc-binder? else drop false then ;
: wc-const-inert? ( mhead -- flag )
  wc-kind dup lf-kind-inductive = over lf-kind-axiom = or swap lf-kind-theorem = or ;
: wc-inert-major? ( mhead -- flag )
  dup wc-head-inert? over wc-leaf-inert? or swap wc-const-inert? or ;
: wc-major-head ( mhead -- e' flag outcome )
  wc-induct-data dup 0= if 2drop outcome-unsupported wc-fail exit then
  over swap wc-eta? if drop outcome-unsupported wc-fail exit then
  dup wc-ctor? if wc-ctor-major exit then
  wc-inert-major? if wc-stay else outcome-unsupported wc-fail then ;
: wc-reduce-rec ( -- e' flag outcome )
  wc-short? if wc-stay exit then
  wc-k? wc-single? 0= or if outcome-unsupported wc-fail exit then
  wc-major wc-rec-kind wc-term wc wc-aux @ wc-frame wc-go ;
: wc-iota ( e head d -- e' flag outcome )
  dup wc wc-aux ! lf-input-decl lf-idecl-data wc wc-data ! wc wc-head ! wc wc-e !
  wc-reduce-rec ;
\ Resumed with the major premise's whnf r: the step's state again, then
\ r's head decides.
: wc-rec-frame ( -- outcome )
  wc wc-aux @ lf-input-decl lf-idecl-data wc wc-data !
  wc-term wc-args lf-meta-spine ok-then? if wc wc-head ! outcome-ok then ;
: wc-rec-resume ( r -- e' flag outcome )
  wc-rec-frame dup ok? 0= if wc-drop-fail exit then drop
  wc-margs lf-meta-spine ok-then? if wc-major-head else wc-fail then ;

\ ---- Projections (projectCore?): the structure's whnf r, a constructor
\ applied to more than its parameters and the field's index, gives that
\ argument; any other r leaves the projection. An r whnf would reduce
\ further (a definition, an unknown constant, Nat.succ it folds, a
\ literal, which toCtorIfLit turns into Nat's constructors) answers
\ unsupported.
: wc-const-unfinal? ( rhead -- flag )
  dup wc-kind dup lf-kind-definition = swap 0= or swap wc-foldable? or ;
: wc-unfinal? ( rhead -- flag ) dup wc-const? if wc-const-unfinal? else wc-lit? then ;
: wc-proj-at ( p -- k ) lf-proj-leaf lf-proj-idx ;
: wc-ctor-params ( ctor -- n )
  lf-meta-const-decl drop lf-input-decl lf-idecl-data lf-ict-params lf-more-field ;
: wc-field ( rhead p -- x true | false )
  wc-proj-at swap wc-ctor-params + dup wc-margs slab-count <
  if wc-margs lf-meta-arg true else drop false then ;
: wc-project ( rhead p -- x true | false )
  over wc-ctor? if wc-field else 2drop false then ;
: wc-proj-frame ( -- p outcome ) wc-term wc-args lf-meta-spine ;
: wc-proj-resume ( r -- e' flag outcome )
  wc-margs lf-meta-spine ok-then? 0= if wc-fail exit then
  dup wc-unfinal? if drop outcome-unsupported wc-fail exit then
  wc-proj-frame ok-then? 0= if wc-drop-fail exit then
  wc-project if wc-rebuild wc-go else wc-stay then ;
: wc-proj-head ( e head -- e' flag outcome )
  lf-proj-struct wc-proj-kind rot 0 wc-frame wc-go ;
: wc-resume ( r -- e' flag outcome )
  wc-pop wc-rec-kind = if wc-rec-resume else wc-proj-resume then ;

: wc-blocked? ( d -- flag )
  lf-menv-kind dup lf-kind-definition = swap lf-kind-quotient = or ;
: wc-recursor? ( d -- flag ) lf-menv-kind lf-kind-recursor = ;
: wc-const-head ( e head -- e' flag outcome )
  dup lf-meta-const-decl 0= if drop wc-done exit then
  dup wc-blocked? if drop wc-unsupported exit then
  dup wc-recursor? if wc-iota else 2drop wc-done then ;

\ ---- One step.
: wc-head-tag ( e head tag -- e' flag outcome )
  case lf-tag-mvar of wc-mvar-head endof  lf-tag-fvar of wc-fvar-head endof
    lf-tag-constant of wc-const-head endof  lf-tag-projection of wc-proj-head endof
    lf-tag-bvar of wc-invalid endof  >r drop wc-done r> endcase ;
: wc-lam? ( term -- flag ) lf-term-tag@ lf-tag-lam = ;
: wc-head-step ( e head -- e' flag outcome )
  dup wc-lam? if drop lf-meta-head-beta wc-go exit then
  dup lf-let? if wc-let-head else dup lf-term-tag@ wc-head-tag then ;
: wc-app ( e -- e' flag outcome )
  dup wc-args lf-meta-spine ok-then? if wc-head-step else wc-drop-fail then ;
: wc-leaf-step ( e tag -- e' flag outcome )
  case lf-tag-mvar of wc-mvar endof  lf-tag-fvar of wc-fvar endof
    lf-tag-projection of dup wc-proj-head endof
    lf-tag-bvar of outcome-invalid wc-drop-fail endof  >r wc-done r> endcase ;
: wc-step ( e -- e' flag outcome )
  dup lf-let? if wc-zeta wc-go exit then
  dup lf-meta-app? if wc-app else dup lf-term-tag@ wc-leaf-step then ;
: wc-spend ( -- flag ) wc wc-fuel @ dup 0> if 1- wc wc-fuel ! true else drop false then ;
: wc-next ( e flag -- e' flag' outcome )
  begin dup 0= wc-framed? and while drop wc-resume dup ok? 0= if exit then drop repeat
  outcome-ok ;
: wc-turn ( e -- e' flag outcome ) wc-step dup ok? if drop wc-next then ;
: wc-loop ( e -- e' outcome )
  begin wc-spend 0= if drop -1 outcome-exhausted exit then
    wc-turn dup ok? 0= if nip exit then drop
  0= until outcome-ok ;
: lf-whnf-core ( term -- term' outcome )
  dup lf-term-root? 0= if drop -1 outcome-invalid exit then wc-start wc-loop ;

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
  lf-input-decl lf-idecl-data wc wc-data ! drop ws-major ;
\ A binary node's data word is known only when no metavariable is in it
\ (core/terms.fs): Lean's hasExprMVar is false.
: ws-kind ( e d -- false outcome )
  lf-menv-kind dup lf-kind-quotient = if 2drop false outcome-unsupported exit then
  lf-kind-definition = if lf-meta-mvar-free? ws-none? else drop false outcome-ok then ;
: ws-const ( e head -- mvar true outcome | false outcome )
  dup lf-meta-const-decl 0= if 2drop false outcome-ok exit then
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
: lf-whnf-stuck ( term -- mvar true outcome | false outcome )
  dup lf-term-root? 0= if drop false outcome-invalid exit then
  dup lf-term-tag@ case lf-tag-mvar of ws-mvar endof  lf-tag-app of ws-app endof
    lf-tag-projection of ws-proj endof  >r drop true ws-none? r> endcase ;

base !   \ the BASE this file was loaded with
