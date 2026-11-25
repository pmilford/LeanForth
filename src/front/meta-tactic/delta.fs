\ Delta expansion of one definition (plan row TB2, tactic batch 1): Lean
\ 4.35.0's deltaExpand and delta? (src/lean/Lean/Meta/Tactic/Delta.lean:
\ 13-26) over Core.transform (Lean/Meta/Transform.lean:44-72).
\ Public word:
\   lf-delta-expand ( e name -- e' )  deltaExpand e (· == name): every
\       application f a1 .. an, f the constant name with as many universe
\       arguments as its parameters, becomes f's value at those universe
\       arguments (instantiateValueLevelParams: unfold.fs's
\       lf-unfold-value) applied to a1 .. an and head-beta reduced
\       (betaRev: instantiate.fs's lf-meta-head-beta); f alone becomes its
\       value; every other node is rebuilt from its parts' images (the
\       same node when none changed, a binder keeping its name and kind:
\       offset-walk.fs's lf-meta-rebuilt). Bound variables stay loose, as
\       Core.transform leaves them. A name that is no definition (an
\       inductive type, an axiom, an opaque one: no value, Lean's hasValue
\       false) leaves e as it is; a theorem, whose value Lean would put in,
\       is not supported yet (thrown unsupported: the runner's 93); an
\       unknown name is invalid (a fault: the
\       tactic gives a constant).
\ The walk is bottom-up (dag-walk.fs: each node's image made once, from
\ its children's), where Lean's is top-down and visits the expansion
\ again (Core.transform's .visit): an application of name has the
\ arguments as its children, so its image puts in the arguments' images,
\ and f's value names no f (a definition's value never names the
\ definition itself). The two give the same term but where an argument is
\ itself name applied (or name alone) and its image a lambda: put in head
\ position by f's value, Lean meets it there with the arguments after it
\ and expands it with them all, beta-reduced, where this walk would leave
\ the redex (@id (N → N) (@id N) s 0: Lean's s 0, here (fun a => a) s 0).
\ Not ported (unsupported, through the walk): that argument, wherever the
\ value puts it; head beta of an argument with loose bound variables under
\ a binder of f's value (instantiate.fs); and the zeta step betaRev's
\ useZeta takes when a let sits between f's lambdas with arguments left
\ over (instantiate.fs's head beta stops at the let: the term would
\ differ from Lean's, so it is refused).
\ Lean call list: delta? -> mdl-head? and mdl-expand; matchConst ->
\ lf-term-const? and lf-const-name; levelParams.length == fLvls.length ->
\ lf-meta-arity? (meta-spine.fs); instantiateValueLevelParams ->
\ lf-unfold-value (unfold.fs); betaRev -> lf-meta-apply-all and
\ lf-meta-head-beta; Core.transform -> dag-walk.fs's dw-run.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the record mdl (the walk and the definition, one expansion at a
\ time: nothing the walk calls expands again) and the slab mdl-args (an
\ application's arguments, last first), in the checker context (ADR
\ 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../core/let-terms.fs
require ../../core/input.fs
require ../../core/name-equal.fs
require ../../core/constant-term-boundary.fs
require ../../core/annotations.fs
require ../dag-walk.fs
require ../meta-env.fs
require ../meta-spine.fs
require ../offset-walk.fs
require ../instantiate.fs
require ../unfold.fs
require ../meta-must.fs

begin-structure /mdl
  /dw +field mdl-walk    \ the walk (dag-walk.fs)
  field: mdl-name        \ the definition's name
  field: mdl-decl        \ and declaration
end-structure
/mdl context-record: mdl
1 cells context-slab: mdl-args
: mdl-dw ( -- walk ) mdl mdl-walk ;
: mdl-made ( image outcome -- image ) dup ok? if drop else mdl-dw dw-refuse then ;

\ ---- delta?'s test: the constant name with as many universe arguments
\ as the definition's parameters, at an application's head or alone.
: mdl-named? ( const -- flag )
  dup lf-const-name mdl mdl-name @ lf-name-same?
  if mdl mdl-decl @ swap lf-meta-arity? else drop false then ;
: mdl-head? ( t -- flag )
  lf-meta-app-head dup lf-term-const? if mdl-named? else drop false then ;

\ ---- The walk's children: the arguments of an application of name; any
\ other binary node's parts.
: mdl-want-arg ( app -- child true | false ) lf-term-second@ mdl-dw dw-want ;
: mdl-want-args ( node -- child true | false )
  begin dup lf-meta-app? while
    dup mdl-want-arg if nip true exit then lf-term-first@
  repeat drop false ;
: mdl-pending ( node walk -- child true | false )
  over mdl-head? if drop mdl-want-args else dw-want-binary then ;

\ ---- The images: the value applied to the arguments' images, head beta;
\ any other binary node over its parts' images; a leaf itself. An
\ argument that is name applied, its image a lambda (under annotations,
\ as headBeta looks), is the revisit not ported: unsupported.
: mdl-revisited? ( arg image -- flag )
  lf-annot-strip lf-term-lam? if mdl-head? else drop false then ;
: mdl-image ( arg -- image outcome )
  dup mdl-dw dw-image tuck mdl-revisited? if outcome-unsupported else outcome-ok then ;
: mdl-image! ( k -- outcome ) mdl-args slab-at dup @ mdl-image >r swap ! r> ;
: mdl-images ( -- outcome ) mdl-args slab-count ['] mdl-image! ok-each ;
: mdl-value ( head -- value outcome )
  mdl mdl-decl @ swap lf-unfold-value ['] mdl-images ok-and ;
\ betaRev's useZeta: a let between the value's lambdas, with arguments
\ left for the lambdas after it, would be zeta-reduced: not ported.
: mdl-zeta ( e -- e outcome )
  dup lf-meta-app? if dup lf-meta-app-head lf-let? if outcome-unsupported exit then then
  outcome-ok ;
: mdl-beta ( value -- e outcome )
  mdl-args lf-meta-apply-all ['] lf-meta-head-beta ok-apply ['] mdl-zeta ok-apply ;
: mdl-expand ( node -- image )
  mdl-args lf-meta-spine ['] mdl-value ok-apply ['] mdl-beta ok-apply mdl-made ;
: mdl-rebuild ( node -- image ) dup mdl-dw dw-part-images rot lf-meta-rebuilt mdl-made ;
: mdl-build ( node walk -- image )
  drop dup mdl-head? if mdl-expand exit then dup lf-term-binary? if mdl-rebuild then ;
' mdl-build ' mdl-pending 2constant mdl-hooks

\ ---- deltaExpand: a definition's applications expanded; another kind's
\ name leaves e (no value), a theorem's is not ported.
: mdl-kind ( name -- kind )
  dup mdl mdl-name ! lf-menv-find lf-must dup mdl mdl-decl ! lf-menv-kind ;
: mdl-theorem ( kind -- kind ) dup lf-kind-theorem = if lf-unported then ;
: mdl-run ( e -- e' ) mdl-hooks mdl-dw dw-on-terms dw-run lf-must ;
: lf-delta-expand ( e name -- e' )
  mdl-kind mdl-theorem lf-kind-definition = if mdl-run then ;
base !   \ the BASE this file was loaded with
