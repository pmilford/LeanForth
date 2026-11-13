\ Parameter facts for the front end's unifier (plan FE1c; ADR 0021 D6):
\ ports of Lean 4.35.0's getFunInfoNArgs (Lean/Meta/FunInfo.lean), as
\ far as isDefEqArgs reads it, and isProp (Lean/Meta/InferType.lean),
\ with the test for a term Lean's whnf leaves as it is.
\ - lf-meta-whnf-final? ( e -- flag ): e, a result of whnfCore
\   (whnf.fs), is one Lean's whnf leaves as it is: its head is a free
\   variable, metavariable, Sort, lambda, pi, literal, projection or a
\   constant that is no definition, and it is no Nat.succ that whnf's
\   reduceNat? might fold (one whose argument is no plain free variable
\   or unassigned metavariable). A definition counts as unfolded,
\   whatever the transparency (its facts come with plan FE1d2), and so
\   does Sort's legacy numeric form.
\ - lf-meta-is-prop ( e -- flag outcome ): isProp: isPropQuick
\   (prop-quick.fs), else e's type, reduced by whnfCore to a Sort, is
\   Prop for every value of its universe parameters.
\ - lf-meta-fun-info ( f n -- m outcome ): getFunInfoNArgs f n: the
\   parameters of f's type (inferType), up to n, entered with new free
\   variables (whnfCore and the test above where the type is no pi:
\   forallBoundedTelescope); for each, lf-meta-param ( i -- kind prop )
\   its binder kind (present/binder-table.fs, explicit when none is
\   recorded) and whether its type is a proposition. Unsupported, never
\   a guess, when a non-explicit parameter's type has a head that might
\   be a class and an argument that is an earlier parameter whose type
\   is or might become a pi: Lean marks such a higher-order
\   out-parameter, which changes isDefEqArgs's order, and class facts
\   come with plan FE1e1.
\ - lf-meta-class-none? ( type -- flag ): Lean's isClassQuick? answers
\   none: past its pis, the head is a free variable, an unassigned
\   metavariable, a Sort, a literal or a bound variable (false: it might
\   be a class, which only class facts decide, plan FE1e1).
\ Binder kinds are those the term store keeps: two binders that differ
\ only in their kind are one node (core/terms.fs), so a kind may be the
\ other binder's (see the plan row FE1c).
\ Outcomes: ok; unsupported as above or where inferType or whnfCore is;
\ invalid for a term that is not live; full when a store or the heap has
\ no room. Untrusted.
\ State: the slab fi-params (kind, prop and free variable per
\ parameter), in the checker context (ADR 0009); valid until the next
\ lf-meta-fun-info.

require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../core/input.fs
require ../core/projections.fs
require ../present/binder-table.fs
require ./mvars.fs
require ./instantiate.fs
require ./meta-spine.fs
require ./meta-env.fs
require ./whnf.fs
require ./infer.fs
require ./term-eqv.fs
require ./prop-quick.fs

3 cells context-slab: fi-params
: fi-tag ( t -- tag ) lf-term-tag@ ;

\ ---- whnf's fixed points.
: fi-bit ( tag -- mask ) 1 swap lshift ;
: fi-final-mask ( -- mask )
  lf-tag-fvar fi-bit lf-tag-mvar fi-bit or lf-tag-symbolic-sort fi-bit or lf-tag-lam fi-bit or
  lf-tag-pi fi-bit or lf-tag-lit fi-bit or lf-tag-projection fi-bit or ;
: fi-defn? ( const -- flag ) lf-meta-const-decl if lf-menv-kind lf-kind-definition = else true then ;
: fi-head-final? ( head -- flag )
  dup fi-tag lf-tag-constant = if fi-defn? 0= exit then fi-tag fi-bit fi-final-mask and 0<> ;
: fi-unassigned? ( mvar -- flag ) lf-mvar-value dup if nip then 0= ;
: fi-inert? ( t -- flag )
  dup fi-tag lf-tag-fvar = if lf-fvar-let? 0= exit then
  dup fi-tag lf-tag-mvar = if fi-unassigned? else drop false then ;
: fi-succ-app? ( e -- flag )
  dup lf-meta-app? if lf-term-first@ s" Nat.succ" lf-meta-const-named? else drop false then ;
: lf-meta-whnf-final? ( e -- flag )
  dup fi-succ-app? if lf-term-second@ fi-inert? else lf-meta-head fi-head-final? then ;

\ ---- isProp.
: fi-sort-prop ( type -- flag outcome )
  dup fi-tag lf-tag-symbolic-sort = if
    lf-term-first@ lf-level-instantiate-mvars ok-then? if lf-meta-always-zero? else false swap then
    exit then
  lf-meta-whnf-final? if false outcome-ok else false outcome-unsupported then ;
: lf-meta-is-prop ( e -- flag outcome )
  dup lf-meta-prop-quick ok-then? 0= if nip false swap exit then
  dup lf-lb-undef <> if nip lf-lb-true = outcome-ok exit then drop
  lf-infer ok-then? 0= if false swap exit then
  lf-whnf-core ok-then? if fi-sort-prop else false swap then ;

\ ---- The telescope: per parameter (kind, prop, free variable).
: lf-meta-param ( i -- kind prop ) fi-params slab-at dup @ swap cell+ @ ;
: fi-x ( i -- x ) fi-params slab-at 2 cells + @ ;
: fi-push ( kind prop x -- outcome )
  1 fi-params slab-claim ok-then? 0= if >r 2drop drop r> exit then
  fi-params slab-at tuck 2 cells + ! tuck cell+ ! ! outcome-ok ;
: fi-kind ( pi -- kind ) lf-pres-binder@ if nip else lf-binder-default then ;
: fi-record ( pi x -- outcome ) swap fi-kind 0 rot fi-push ;
: fi-open ( pi -- body outcome )
  dup lf-term-first@ lf-lctx-local ok-then? 0= if nip no-result exit then
  2dup fi-record dup ok? 0= if nip nip no-result exit then drop
  swap lf-term-second@ swap lf-meta-instantiate1 ;
: fi-pi ( type n -- type' n' go? outcome ) >r fi-open r> 1- swap true swap ;
\ A type that is no pi: whnfCore's pi, or the end when whnf would leave
\ it; anything else would need whnf's delta.
: fi-reduce ( type n -- type' n' go? outcome )
  >r lf-whnf-core ok-then? 0= if -1 swap r> swap false swap exit then
  dup fi-tag lf-tag-pi = if r> true outcome-ok exit then
  dup lf-meta-whnf-final? r> false rot if outcome-ok else outcome-unsupported then ;
: fi-step ( type n -- type' n' go? outcome )
  dup 0= if false outcome-ok exit then over fi-tag lf-tag-pi = if fi-pi else fi-reduce then ;
: fi-telescope ( type n -- outcome )
  begin fi-step ok-then? 0= if nip nip exit then 0= until 2drop outcome-ok ;

\ ---- Higher-order out-parameters (see the header).
: fi-maybe-pi? ( type -- flag outcome )
  dup fi-tag lf-tag-pi = if drop true outcome-ok exit then
  lf-whnf-core ok-then? 0= if false swap exit then
  dup fi-tag lf-tag-pi = if drop true else lf-meta-whnf-final? 0= then outcome-ok ;
: fi-earlier? ( arg i -- flag ) false swap 0 ?do over i fi-x = or loop nip ;
: fi-ho-arg? ( arg i -- flag outcome )
  over swap fi-earlier? if lf-fvar-type fi-maybe-pi? else drop false outcome-ok then ;
: fi-ho-args? ( T i -- flag outcome )
  false -rot begin over lf-meta-app? while
    over lf-term-second@ over fi-ho-arg? ok-then? 0= if >r 2drop drop false r> exit then
    >r rot r> or -rot swap lf-term-first@ swap repeat 2drop outcome-ok ;
: fi-strip ( T -- body ) begin dup fi-tag lf-tag-pi = while lf-term-second@ repeat ;
\ isClassQuick? answers none for these heads: no class.
: fi-not-class? ( head -- flag )
  dup fi-tag lf-tag-mvar = if fi-unassigned? exit then
  fi-tag dup lf-tag-fvar = over lf-tag-symbolic-sort = or over lf-tag-sort = or
  over lf-tag-lit = or swap lf-tag-bvar = or ;
: lf-meta-class-none? ( type -- flag ) fi-strip lf-meta-head fi-not-class? ;
: fi-ho? ( i -- flag outcome )
  dup lf-meta-param drop lf-binder-default = if drop false outcome-ok exit then
  dup fi-x lf-fvar-type fi-strip dup lf-meta-head fi-not-class? if 2drop false outcome-ok exit then
  swap fi-ho-args? ;

\ ---- getFunInfoNArgs.
: fi-prop! ( i -- outcome )
  dup fi-x lf-fvar-type lf-meta-is-prop ok-then? 0= if nip exit then
  swap fi-params slab-at cell+ ! outcome-ok ;
: fi-props ( -- outcome )
  fi-params slab-count 0 ?do i fi-prop! dup ok? 0= if unloop exit then drop
    i fi-ho? ok-then? 0= if unloop exit then if unloop outcome-unsupported exit then loop outcome-ok ;
: lf-meta-fun-info ( f n -- m outcome )
  fi-params slab-clear swap lf-infer ok-then? 0= if nip no-result exit then
  swap fi-telescope dup ok? if drop fi-props then fi-params slab-count swap ;
