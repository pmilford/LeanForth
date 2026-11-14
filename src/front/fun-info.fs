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
\   its binder kind and whether its type is a proposition; the free
\   variables leave the local context at the end. Unsupported, never
\   a guess, when a non-explicit parameter's type has a head that might
\   be a class and an argument that is an earlier parameter whose type
\   is or might become a pi (outParam T and semiOutParam T taken as T,
\   as whnf unfolds them): Lean marks such a higher-order
\   out-parameter, which changes isDefEqArgs's order, and class facts
\   come with plan FE1e1.
\ - lf-meta-class-none? ( type -- flag ): Lean's isClassQuick? answers
\   none: past its pis, the head is a free variable, an unassigned
\   metavariable, a Sort, a literal or a bound variable (false: it might
\   be a class, which only class facts decide, plan FE1e1).
\ - lf-meta-unassigned? ( mvar -- flag ): no plain assignment.
\ Binder kinds: from the head's declared type (a constant's input type,
\ else the type itself), never from a copy: an input binder's from its
\ record; a store binder named in the binder table answers unsupported,
\ since the store shares equal nodes and the name may be another
\ binder's; one not named is explicit. Unsupported too where whnf makes
\ the pis. (The importer also merges input binders that differ only in
\ their kind, core/terms.fs: the plan row FE1c keeps that risk.)
\ Outcomes: ok; unsupported as above or where inferType or whnfCore is;
\ invalid for a term that is not live; full when a store or the heap has
\ no room. Untrusted.
\ State: the slab fi-params (kind, prop and free variable per
\ parameter) and the record fi-state (the kinds' source), in the checker
\ context (ADR 0009); valid until the next lf-meta-fun-info.

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
begin-structure /fi
  field: fi-source   \ the declared type's pi of the next parameter, or -1
end-structure
/fi context-record: fi-state

\ ---- whnf's fixed points.
: fi-final-mask ( -- mask )
  lf-tag-fvar lf-tag-bit lf-tag-mvar lf-tag-bit or lf-tag-symbolic-sort lf-tag-bit or
  lf-tag-lam lf-tag-bit or
  lf-tag-pi lf-tag-bit or lf-tag-lit lf-tag-bit or lf-tag-projection lf-tag-bit or ;
: fi-defn? ( const -- flag )
  lf-meta-const-decl if lf-menv-kind lf-kind-definition = else true then ;
: fi-head-final? ( head -- flag )
  dup lf-term-const? if fi-defn? 0= exit then
  lf-term-tag@ lf-tag-bit fi-final-mask and 0<> ;
: lf-meta-unassigned? ( mvar -- flag ) lf-mvar-value dup if nip then 0= ;
: fi-inert? ( t -- flag )
  dup lf-term-tag@ lf-tag-fvar = if lf-fvar-let? 0= exit then
  dup lf-mvar? if lf-meta-unassigned? else drop false then ;
: lf-meta-whnf-final? ( e -- flag )
  dup 1 s" Nat.succ" lf-meta-app-of? if lf-term-second@ fi-inert? exit then
  lf-meta-head fi-head-final? ;

\ ---- isProp.
: fi-zero-sort? ( sort -- flag outcome )
  lf-term-first@ lf-level-instantiate-mvars ok-then? if lf-meta-always-zero?
  else false swap then ;
: fi-sort-prop ( type -- flag outcome )
  dup lf-tag-symbolic-sort lf-term-tag? if fi-zero-sort? exit then
  lf-meta-whnf-final? if false outcome-ok else false outcome-unsupported then ;
: lf-meta-is-prop ( e -- flag outcome )
  dup lf-meta-prop-quick ok-then? 0= if nip false swap exit then
  dup lf-lb-undef <> if nip lf-lb-true = outcome-ok exit then drop
  lf-infer ok-then? 0= if false swap exit then
  lf-whnf-core ok-then? if fi-sort-prop else false swap then ;

\ ---- The telescope: per parameter (kind, prop, free variable).
: lf-meta-param ( i -- kind prop ) fi-params slab-at dup @ swap cell+ @ ;
: fi-x ( i -- x ) fi-params slab-at 2 cells + @ ;
: fi-push ( x kind prop -- outcome )
  1 fi-params slab-claim ok-then? 0= if >r 2drop drop r> exit then
  fi-params slab-at tuck cell+ ! tuck ! 2 cells + ! outcome-ok ;
\ Binder kinds come from the head's own declared type, walked beside the
\ telescope (fi-src: its pi for the next parameter, -1 once whnf made the
\ pis): an input binder's kind from its record; a store binder that the
\ binder table names may be another binder's of the same node (the store
\ shares equal nodes, binder-table.fs), so its kind is unknown; one it
\ does not name is explicit, as every front-end binder made without a
\ kind (whose copies are refused, not dropped, when the table is full).
: fi-src ( -- addr ) fi-state fi-source ;
: fi-store-kind ( pi -- kind true | false )
  lf-pres-binder@ if 2drop false else lf-binder-default true then ;
: fi-kind ( -- kind true | false )
  fi-src @ dup 0< if drop false exit then
  dup lf-term-input? if lf-term-input-binder@ if nip true else false then exit then
  fi-store-kind ;
: fi-next-src ( -- )
  fi-src @ dup 0< 0= if
    dup lf-term-pi? if lf-term-second@ else drop -1 then then
  fi-src ! ;
: fi-record ( pi x -- outcome )
  nip fi-kind fi-next-src if 0 fi-push else drop outcome-unsupported then ;
: fi-open ( pi -- body outcome )
  dup lf-term-first@ lf-lctx-local ok-then? 0= if nip no-result exit then
  2dup fi-record dup ok? 0= if nip nip no-result exit then drop
  swap lf-term-second@ swap lf-meta-instantiate1 ;
: fi-pi ( type n -- type' n' go? outcome ) >r fi-open r> 1- swap true swap ;
\ A type that is no pi: whnfCore's pi, or the end when whnf would leave
\ it; anything else would need whnf's delta.
: fi-reduce ( type n -- type' n' go? outcome )
  >r lf-whnf-core ok-then? 0= if -1 swap r> swap false swap exit then
  dup lf-term-pi? if -1 fi-src ! r> true outcome-ok exit then
  dup lf-meta-whnf-final? if outcome-ok else outcome-unsupported then r> swap false swap ;
: fi-step ( type n -- type' n' go? outcome )
  dup 0= if false outcome-ok exit then over lf-term-pi? if fi-pi
  else fi-reduce then ;
: fi-telescope ( type n -- outcome )
  begin fi-step ok-then? 0= if nip nip exit then 0= until 2drop outcome-ok ;

\ ---- Higher-order out-parameters (see the header).
\ outParam T and semiOutParam T are T (Init's reducible definitions
\ outParam (α : Sort u) := α, which whnf unfolds at any transparency).
: fi-param-wrapper? ( t -- flag )
  dup lf-term-app? 0= if drop false exit then lf-term-first@
  dup s" outParam" lf-meta-const-named? swap s" semiOutParam" lf-meta-const-named? or ;
: fi-unwrap ( t -- t' ) begin dup fi-param-wrapper? while lf-term-second@ repeat ;
: fi-maybe-pi? ( type -- flag outcome )
  fi-unwrap dup lf-term-pi? if drop true outcome-ok exit then
  lf-whnf-core ok-then? 0= if false swap exit then
  dup lf-term-pi? if drop true else lf-meta-whnf-final? 0= then outcome-ok ;
: fi-earlier? ( arg i -- flag ) false swap 0 ?do over i fi-x = or loop nip ;
: fi-ho-arg? ( arg i -- flag outcome )
  over swap fi-earlier? if lf-fvar-type fi-maybe-pi? else drop false outcome-ok then ;
: fi-ho-args? ( T i -- flag outcome )
  swap begin dup lf-term-app? while
    2dup lf-term-second@ swap fi-ho-arg? ok-then? 0= if nip nip false swap exit then
    if 2drop true outcome-ok exit then lf-term-first@ repeat 2drop false outcome-ok ;
: fi-strip ( T -- body ) begin dup lf-term-pi? while lf-term-second@ repeat ;
\ isClassQuick? answers none for these heads: no class.
: fi-not-class? ( head -- flag )
  dup lf-mvar? if lf-meta-unassigned? exit then
  lf-term-tag@ dup lf-tag-fvar = over lf-tag-symbolic-sort = or over lf-tag-sort = or
  over lf-tag-lit = or swap lf-tag-bvar = or ;
: lf-meta-class-none? ( type -- flag ) fi-strip lf-meta-head fi-not-class? ;
: fi-ho? ( i -- flag outcome )
  dup lf-meta-param drop lf-binder-default = if drop false outcome-ok exit then
  dup fi-x lf-fvar-type fi-strip dup lf-meta-head fi-not-class?
  if 2drop false outcome-ok exit then swap fi-ho-args? ;

\ ---- getFunInfoNArgs.
: fi-prop! ( i -- outcome )
  dup fi-x lf-fvar-type lf-meta-is-prop ok-then? 0= if nip exit then
  swap fi-params slab-at cell+ ! outcome-ok ;
\ Each parameter's prop flag; a higher-order out-parameter is unsupported.
: fi-ho-free ( i -- outcome )
  fi-ho? ok-then? if if outcome-unsupported else outcome-ok then then ;
: fi-prop-at ( i -- outcome ) dup fi-prop! ['] fi-ho-free ok-with nip ;
: fi-props ( -- outcome ) fi-params slab-count ['] fi-prop-at ok-each ;
\ The kinds' source: a constant's declared (input) type, else the type.
: fi-declared ( f type -- )
  swap dup lf-term-const?
  if nip lf-meta-const-decl if lf-menv-type else -1 then else drop then fi-src ! ;
: fi-run ( f n -- m outcome )
  fi-params slab-clear over lf-infer ok-then? 0= if nip nip no-result exit then
  rot over fi-declared swap fi-telescope dup ok? if drop fi-props then
  fi-params slab-count swap ;
\ The telescope's free variables (and inferType's) go again at the end.
: fi-mark ( -- mark ) lf-term-base lf-term-count @ + ;
: lf-meta-fun-info ( f n -- m outcome ) fi-mark >r fi-run r> lf-lctx-drop ;
