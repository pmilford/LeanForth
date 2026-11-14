\ Lazy delta reduction of the front end's unification (plan S2, merge A;
\ docs/design/S2_INTERFACE.md §2): a port of Lean 4.35.0's isDefEqDelta
\ and its helpers (Lean/Meta/ExprDefEq.lean:1544-1849), at Lean's place in
\ isExprDefEqExpensive (2410-2421: after whnfCore, isDefEqNat and
\ isDefEqOffset, before structure eta and isDefEqApp), as an activation of
\ front/defeq.fs's machine: it sets defeq.fs's de-delta-x, uses that
\ machine's registers and steps (de-*), and runs under its checkpoints,
\ fuel and the --elab-fuel budget. Every comparison it makes is a call of
\ isExprDefEqAux on the machine's heap stack (no host recursion, plan
\ 6.2.0 (b)); unfolding one side is front/whnf.fs's lf-meta-unfold
\ (unfoldDefinition?), whnfCore lf-whnf-core, both at the activation's
\ transparency. The answer is an LBool:
\ - candidates (isDeltaCandidate?): a side whose head is a constant that
\   getUnfoldableConst? gives (meta-env.fs's lf-menv-unfoldable); none:
\   undef; one: that side unfolded and compared with the other
\   (isDefEqLeft, isDefEqRight), undef when it does not unfold;
\ - two of one name (unfoldBothDefEq, 1697): two constants equal when
\   their universe levels are, else both unfolded; two applications by
\   tryHeuristic (1632: when the head is a non-trivial regular definition
\   (isNonTrivialRegular: height above 2, or a value that is not simple
\   after its lambdas), a matcher, or either side holds a metavariable:
\   arguments then levels under a checkpoint, defeq.fs's isDefEqApp
\   activation), else each side that unfolds; anything else false;
\ - two names (unfoldNonProjFnDefEq, 1807): a class projection unfolded
\   and whnfCore'd until its head is the other side's constant
\   (packedInstanceOf?), first on the left, then on the right; else a
\   projection function on one side only unfolds the other side; else
\   unfoldReducibleDefEq (1769: above reducible transparency a reducible
\   side alone unfolds first), then unfoldDefEq (1748: without
\   metavariables the side of greater definitional height unfolds first,
\   ReducibilityHints.lt), then unfoldComparingHeadsDefEq (1726: a side
\   whose unfolding has the other's head symbol alone, else both).
\ Each fallback runs where Lean's does when a side does not unfold.
\ Untrusted and fail-closed: a fact meta-env.fs does not have
\ (reducibility, projection, matcher, a text declaration's height) or a
\ step whnf.fs answers unsupported aborts the comparison unsupported,
\ never a guess. Outcomes are defeq.fs's.
\ Reuse: defeq.fs's machine for every comparison and checkpoint, whnf.fs
\ for unfolding and whnfCore, meta-env.fs for every fact, lib/walk.fs for
\ isSimple's walk.
\ State: the walk dd-walker (isSimple's pending terms; lib/walk.fs), in
\ the checker context (ADR 0009); the registers x and y of the activation
\ hold the two candidates' declarations (-1: none). Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/projections.fs
require ../core/literals.fs
require ../core/string-literals.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../core/tagged-sort-boundary.fs
require ../core/constant-term-boundary.fs
require ../core/input.fs
require ./meta-config.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./whnf.fs
require ./defeq.fs

lf-walk-room context-walk: dd-walker

\ ---- Unfolding and comparing.
: dd-unfold ( e -- e' flag ) ['] lf-meta-unfold de-mode-at de-must and ;
: dd-core ( e -- e' flag ) ['] lf-whnf-core de-mode-at de-must ;
: dd-compare ( t s -- ) ['] de-pass de-solve ;
: dd-undef ( -- ) lf-lb-undef de-return ;
: dd-flag ( flag outcome -- flag ) de-must and ;
: dd-same-head? ( a b -- flag ) lf-meta-head swap lf-meta-head de-same-const? ;

\ ---- Candidates in x and y.
: dd-candidate ( t -- d flag )
  lf-meta-head dup lf-term-const? 0= if drop -1 false exit then
  lf-const-name df df-mode @ lf-menv-unfoldable dd-flag ;
: dd-cand! ( t addr -- ) swap dd-candidate 0= if drop -1 then swap ! ;
: dd-t? ( -- flag ) de-x 0< 0= ;
: dd-s? ( -- flag ) de-y 0< 0= ;

\ ---- One side unfolds and is compared with the other; when it does not
\ unfold, the step xt (Lean's fallback at that place).
: dd-t-or ( xt -- ) de-t dd-unfold if nip de-s dd-compare else drop execute then ;
: dd-s-or ( xt -- ) de-s dd-unfold if nip de-t swap dd-compare else drop execute then ;
: dd-left ( -- ) ['] dd-undef dd-t-or ;
: dd-right ( -- ) ['] dd-undef dd-s-or ;

\ ---- unfoldComparingHeadsDefEq.
: dd-heads-both ( tNew sNew -- )
  de-t over dd-same-head? if nip de-t swap then dd-compare ;
: dd-heads-new ( tNew -- )
  dup de-s dd-same-head? if de-s dd-compare exit then
  de-s dd-unfold if dd-heads-both else drop de-s dd-compare then ;
: dd-heads ( -- ) de-t dd-unfold if dd-heads-new else drop dd-right then ;

\ ---- unfoldDefEq: without metavariables, ReducibilityHints.lt (abbrev
\ below everything, a greater height below a smaller, regular below
\ opaque) as one key: abbrev max-n, regular its height, opaque -1; the
\ side of the greater key unfolds first.
: dd-rank ( hint height -- key )
  over lf-hint-regular = if nip exit then drop lf-hint-abbrev = if max-n else -1 then ;
: dd-key ( d -- key )
  dup lf-menv-hint-known? if lf-menv-hint dd-rank exit then
  drop outcome-unsupported de-abort 0 ;
: dd-first-t ( -- ) ['] dd-heads dd-t-or ;
: dd-first-s ( -- ) ['] dd-heads dd-s-or ;
: dd-mvars? ( -- flag ) de-t lf-meta-mvar-free? de-s lf-meta-mvar-free? and 0= ;
: dd-by-keys ( kt ks -- )
  2dup > if 2drop dd-first-t exit then < if dd-first-s else dd-heads then ;
: dd-defeq ( -- )
  dd-mvars? if dd-heads exit then
  de-x dd-key de-y dd-key de-aborted? if 2drop else dd-by-keys then ;

\ ---- unfoldReducibleDefEq: above reducible transparency a reducible side
\ alone unfolds first.
: dd-unfold-t ( -- ) ['] dd-defeq dd-t-or ;
: dd-unfold-s ( -- ) ['] dd-defeq dd-s-or ;
: dd-red? ( d -- flag ) lf-menv-reducible? dd-flag ;
: dd-one-of ( t? s? -- )
  de-aborted? if 2drop exit then
  2dup = if 2drop dd-defeq exit then drop if dd-unfold-t else dd-unfold-s then ;
: dd-reducible ( -- )
  df df-mode @ lf-tr-reducible = if dd-defeq exit then
  de-x dd-red? de-y dd-red? dd-one-of ;

\ ---- unfoldNonProjFnDefEq.
\ packedInstanceOf?: while e's head is a class projection function, e
\ unfolded and whnfCore'd, until its head is the constant other.
: dd-class-head? ( e -- flag )
  lf-meta-head dup lf-term-const? 0= if drop false exit then
  de-decl if lf-menv-proj-class? dd-flag else false then ;
: dd-packed-step ( e -- e' flag ) dd-unfold if dd-core else false then ;
: dd-class-more? ( e -- flag ) dd-class-head? dup if drop de-spend? then ;
: dd-packed ( e other -- e' true | false )
  begin over dd-class-more? while
    swap dd-packed-step 0= if 2drop false exit then
    swap 2dup dd-same-head? if drop true exit then
  repeat 2drop false ;
: dd-proj? ( d -- flag ) lf-menv-proj-fn? dd-flag ;
: dd-proj-cases ( -- )
  de-x dd-proj? de-y dd-proj? de-aborted? if 2drop exit then
  2dup = if 2drop dd-reducible exit then drop if dd-unfold-s else dd-unfold-t then ;
: dd-non-proj ( -- )
  de-t de-s dd-packed if de-s dd-compare exit then de-aborted? if exit then
  de-s de-t dd-packed if de-t swap dd-compare exit then de-aborted? if exit then
  dd-proj-cases ;

\ ---- tryHeuristic's test: isNonTrivialRegular, a matcher, or a
\ metavariable on either side.
\ isSimple of the value after its lambdas (consumeDefnPreamble): only
\ applications and projections over bound and free variables,
\ metavariables, sorts and literals.
\ A walk of lib/walk.fs: a visit pushes an application's or projection's
\ parts; a simple leaf is ok; a binder, let or constant is rejected (not
\ simple); any other tag (an unsupported form) unsupported. The walk
\ spends the call's fuel.
lf-tag-bvar lf-tag-bit lf-tag-fvar lf-tag-bit or lf-tag-mvar lf-tag-bit or
  lf-tag-sort lf-tag-bit or lf-tag-symbolic-sort lf-tag-bit or lf-tag-lit lf-tag-bit or
  lf-tag-str lf-tag-bit or constant dd-simple-tags   \ isSimple's leaves
: dd-leaf? ( tag -- flag ) lf-tag-bit dd-simple-tags and 0<> ;
: dd-false? ( tag -- flag )
  dup lf-term-binder-tag? over lf-term-let-tag? or swap lf-tag-constant = or ;
: dd-other ( tag -- outcome )
  dup dd-leaf? if drop outcome-ok exit then
  dd-false? if outcome-rejected else outcome-unsupported then ;
: dd-visit ( walk -- outcome )
  walk-node @ dup lf-term-tag@ case
    lf-tag-app of dup lf-term-first@ swap lf-term-second@ dd-walker walk-push2 endof
    lf-tag-projection of lf-proj-struct dd-walker walk-push-outcome endof
    >r drop r@ dd-other r> endcase ;
: dd-verdict ( outcome -- flag )
  dup outcome-rejected = if drop false exit then
  dup ok? if drop true else de-abort false then ;
: dd-simple? ( e -- flag )
  df df-fuel @ dd-walker walk-budget drop ['] dd-visit dd-walker walk-run
  dd-walker walk-fuel @ df df-fuel ! dd-verdict ;
: dd-preamble ( v -- e ) begin dup lf-term-lam? while lf-term-second@ repeat ;
: dd-regular ( d height -- flag )
  2 > if drop true exit then
  lf-menv-value if dd-preamble dd-simple? 0= else outcome-invalid de-abort false then ;
\ An abbreviation: a class's projection function at reducible
\ transparency (backward.whnf.reducibleClassField, default true).
: dd-abbrev ( d -- flag )
  dup lf-menv-proj-fn? dd-flag 0= if drop false exit then
  lf-menv-proj-class? dd-flag df df-mode @ lf-tr-reducible = and ;
: dd-nontrivial? ( d -- flag )
  dup lf-menv-hint-known? 0= if drop outcome-unsupported de-abort false exit then
  dup lf-menv-hint over lf-hint-regular = if nip dd-regular exit then
  drop lf-hint-abbrev = if dd-abbrev else drop false then ;
: dd-heuristic? ( -- flag )
  dd-mvars? if true exit then de-x dd-nontrivial? dup de-aborted? or if exit then
  drop de-x lf-menv-matcher? dd-flag ;

\ ---- unfoldBothDefEq.
: dd-pair ( -- )
  de-t dd-unfold if de-s dd-unfold drop dd-compare exit then drop dd-right ;
: dd-heur-k ( r -- ) lf-lb-true = if lf-lb-true de-return else dd-pair then ;
: dd-apps ( -- )
  dd-heuristic? de-aborted? if drop exit then
  if ['] dd-heur-k ['] de-app de-call else dd-pair then ;
: dd-consts ( -- )
  de-t de-s de-levels lf-lb-true = if lf-lb-true de-return exit then
  de-t dd-unfold if de-s dd-unfold if dd-compare else 2drop dd-undef then
  else drop dd-undef then ;
: dd-same ( -- )
  de-t lf-term-const? de-s lf-term-const? and if dd-consts exit then
  de-t lf-meta-app? de-s lf-meta-app? and if dd-apps else lf-lb-false de-return then ;

\ ---- isDefEqDelta.
: dd-both ( -- ) de-t de-s dd-same-head? if dd-same else dd-non-proj then ;
: dd-delta ( -- )
  de-t df df-x dd-cand! de-s df df-y dd-cand! de-aborted? if exit then
  dd-t? dd-s? 2dup and if 2drop dd-both exit then
  if drop dd-right exit then if dd-left else dd-undef then ;
' dd-delta is de-delta-x

base !   \ the BASE this file was loaded with
