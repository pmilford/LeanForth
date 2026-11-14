\ Unfolding one definition (plan S2, merge A; docs/design/S2_INTERFACE.md
\ §2): the steps of Lean 4.35.0's unfoldDefinition? (Lean/Meta/WHNF.lean:
\ 844) that need no whnf, over the term store, with no use of src/kernel/.
\ front/whnf.fs runs them: in lf-meta-whnf's delta step and in
\ lf-meta-unfold ( e -- e' flag outcome ), Lean's unfoldDefinition? itself,
\ which is defined there because a class projection needs whnf's machine
\ (reduceProj? below).
\ lf-unfold-step ( e -- e' code outcome ), at the configured transparency
\ (meta-config.fs), in the environment of front/meta-env.fs:
\ - f a1 .. an with a constant f that getUnfoldableConst? gives
\   (GetUnfoldableConst.lean:78: a definition the transparency unfolds;
\   an unknown name is invalid, as Lean throws): none (lf-unfold-none)
\   when f's universe arguments are not as many as its parameters;
\   unsupported when f has a smart-unfolding `f._sunfold` definition (the
\   smart path, plan S2 merge B) or when that is not known
\   (lf-menv-smart?); none for a matcher (whnfCore reduces matchers);
\   else unfoldDefault (821): f's value with f's universe arguments for
\   its parameters, applied to a1 .. an with head beta
\   (deltaBetaDefinition, 423): lf-unfold-made. At reducible transparency,
\   when f is a class's projection function (backward.whnf.reducibleClassField,
\   default true) and that result's head is a projection,
\   lf-unfold-ask-keep: whnf.fs reduces the projection's structure at
\   instances transparency (reduceProj?) and, when it is a constructor,
\   applies the field to the result's arguments with head beta; else the
\   result stands.
\ - f a1 .. an with any other head: unfoldProjInstWhenInstances? (787):
\   at instances or implicit transparency, a constant f that is a class's
\   projection function and that default transparency unfolds (isProjInst
\   and getUnfoldableConst?, unfoldProjInst? 766) is delta-beta reduced as
\   above; when that result's head is a projection, lf-unfold-ask-none:
\   whnf.fs reduces it as above, and none when it does not project. Any
\   other: none.
\ - a constant c: getUnfoldableConstNoEx? (an unknown name, a theorem, an
\   axiom or what the transparency keeps: none); none when c has a
\   `_sunfold` (unsupported when not known); else c's value with its
\   universe arguments (deltaDefinition, 416; none when the counts
\   differ): lf-unfold-made.
\ - any other term: none.
\ None gives e back. Outcomes: ok; invalid for an unknown constant at an
\ application's head or a definition without a value; unsupported as
\ above; full when a store or slab has no room. A failure gives -1 and
\ lf-unfold-none.
\ Reuse: meta-env.fs for every fact, meta-spine.fs for the spine, the
\ universe-argument count and mkAppN, constant-term-boundary.fs for the
\ head's name, level-params.fs for instantiateValueLevelParams, instantiate.fs
\ for head beta, term-eqv.fs for the head.
\ Unchecked: e is a live term (whnf.fs's entries check it). Untrusted: only
\ the kernel's check of a finished term decides anything.
\ State: the slabs uf-args (the application's arguments, last first) and
\ uf-levels (the head's universe arguments), in the checker context (ADR
\ 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/projections.fs
require ./meta-config.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./instantiate.fs
require ./level-params.fs
require ./term-eqv.fs

0 constant lf-unfold-none   1 constant lf-unfold-made
2 constant lf-unfold-ask-keep   3 constant lf-unfold-ask-none
1 cells context-slab: uf-args
1 cells context-slab: uf-levels

\ ---- Results ( -- e' code outcome ).
: uf-none-of ( e -- e code outcome ) lf-unfold-none outcome-ok ;
: uf-fail ( outcome -- -1 code outcome ) -1 lf-unfold-none rot ;

\ ---- deltaDefinition and deltaBetaDefinition: d's value with const's
\ universe arguments for its parameters (instantiateValueLevelParams);
\ applied to the arguments in uf-args, a lambda value with head beta
\ (betaRev), any other as it is.
: uf-value ( d const -- value outcome )
  uf-levels lf-meta-levels-fill ok-then? 0= if no-result exit then
  dup lf-menv-value 0= if drop-invalid no-result exit then
  swap lf-menv-params >r 0 uf-levels slab-at r> lf-meta-instantiate-level-params ;
: uf-beta ( value -- e' outcome )
  dup lf-term-lam? swap uf-args lf-meta-apply-all
  ok-then? 0= if nip no-result exit then swap if lf-meta-head-beta else outcome-ok then ;
: uf-delta-beta ( d const -- e' outcome )
  uf-value ok-then? if uf-beta else no-result then ;

\ ---- unfoldDefault: at reducible transparency a class field whose result
\ has a projection at its head asks whnf.fs for reduceProj?.
: uf-field? ( e' -- flag ) lf-meta-head lf-proj? ;
: uf-reducible? ( -- flag ) lf-defeq-mode lf-tr-reducible = ;
: uf-ask ( e' flag code -- e' code outcome )
  >r over uf-field? and if r> else r> drop lf-unfold-made then outcome-ok ;
: uf-at-field ( e' d -- e' code outcome )
  uf-reducible? 0= if drop lf-unfold-made outcome-ok exit then
  lf-menv-proj-class? ok-then? if lf-unfold-ask-keep uf-ask else nip uf-fail then ;
: uf-default ( d const -- e' code outcome )
  over >r uf-delta-beta ok-then? if r> uf-at-field else r> drop uf-fail then ;

\ Before unfoldDefault: a `_sunfold` (the smart path, merge B) or not
\ knowing whether there is one answers unsupported; a matcher may not
\ unfold (flag false).
: uf-smart-check ( d -- outcome )
  lf-menv-smart? ok-then? if if outcome-unsupported else outcome-ok then then ;
: uf-gate ( d -- flag outcome )
  dup uf-smart-check ok-then? 0= if false swap exit then
  lf-menv-matcher? ok-then? if 0= outcome-ok else false swap then ;
: uf-known ( e d const -- e' code outcome )
  2dup lf-meta-arity? 0= if 2drop uf-none-of exit then
  over uf-gate ok-then? 0= if nip nip nip uf-fail exit then
  if rot drop uf-default else 2drop uf-none-of then ;

\ ---- unfoldProjInstWhenInstances? and unfoldProjInst?: isProjInst, then
\ getUnfoldableConst? at default transparency.
: uf-inst-mode? ( -- flag ) lf-defeq-mode dup lf-tr-instances = swap lf-tr-implicit = or ;
: uf-class-field ( const -- d flag outcome )
  lf-const-name dup lf-menv-find ok-then? 0= if nip -1 false rot exit then
  lf-menv-proj-class? ok-then? 0= if nip -1 false rot exit then
  if lf-tr-default lf-menv-unfoldable else drop -1 false outcome-ok then ;
: uf-ready ( e d const -- e' code outcome )
  2dup lf-meta-arity? 0= if 2drop uf-none-of exit then
  uf-delta-beta ok-then? 0= if nip uf-fail exit then
  dup uf-field? if nip lf-unfold-ask-none outcome-ok else drop uf-none-of then ;
: uf-proj-inst ( e const -- e' code outcome )
  dup uf-class-field ok-then? 0= if nip nip nip uf-fail exit then
  if swap uf-ready else 2drop uf-none-of then ;
: uf-when-instances ( e const -- e' code outcome )
  uf-inst-mode? if uf-proj-inst else drop uf-none-of then ;

\ ---- An application: getUnfoldableConst? at its head.
: uf-app-head ( e const -- e' code outcome )
  dup lf-const-name lf-defeq-mode lf-menv-unfoldable
  ok-then? 0= if nip nip nip uf-fail exit then
  if swap uf-known else drop uf-when-instances then ;
: uf-spine ( e -- e' code outcome )
  dup uf-args lf-meta-spine ok-then? 0= if nip uf-fail exit then
  dup lf-term-const? if uf-app-head else drop uf-none-of then ;

\ ---- A constant: getUnfoldableConstNoEx? (an unknown name: none).
: uf-const-d ( const -- d flag outcome )
  lf-const-name lf-defeq-mode lf-menv-unfoldable
  dup outcome-invalid = if 2drop false outcome-ok then ;
: uf-const-known ( const d -- e' code outcome )
  dup lf-menv-smart? ok-then? 0= if nip nip uf-fail exit then
  if drop uf-none-of exit then
  2dup swap lf-meta-arity? 0= if drop uf-none-of exit then
  swap uf-value ok-then? if lf-unfold-made outcome-ok else uf-fail then ;
: uf-const ( const -- e' code outcome )
  dup uf-const-d ok-then? 0= if nip nip uf-fail exit then
  if uf-const-known else drop uf-none-of then ;

: lf-unfold-step ( e -- e' code outcome )
  dup lf-meta-app? if uf-spine exit then
  dup lf-term-const? if uf-const else uf-none-of then ;

base !   \ the BASE this file was loaded with
