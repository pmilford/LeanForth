\ Goal operations of the tactic library (docs/design/TACTIC_PLUGINS.md
\ 2.4; slices a2-ii and a2-iii): Lean 4.35.0's Meta/Tactic layer, the
\ MVarId functions a tactic calls on its goal. Each word throws on
\ failure (meta-must.fs), as Lean's do.
\ Public words (stack effect; the Lean function, file:line under
\ src/lean/Lean/Meta/Tactic/):
\   lf-goal-not-assigned ( goal -- goal )  MVarId.checkNotAssigned
\       (Util.lean:65); an assigned goal is thrown invalid: no tactic of
\       LeanForth's is handed one (lf-main-goal skips them), so it is a
\       fault, not Lean's message
\   lf-goal-replace-target-eq ( goal new h -- goal' )  MVarId.replaceTargetEq
\       (Replace.lean:21-32): a new synthetic opaque goal of type new with
\       goal's tag in goal's context; goal assigned
\       Eq.mpr.{u} target new (id (target = new) h) goal', target goal's
\       type as stored and u its level
\   lf-goal-head-beta-type ( goal -- goal' )  MVarId.headBetaType
\       (Util.lean:94): goal's type head-beta reduced; Lean sets the
\       declaration's type, LeanForth's metavariables keep theirs, so a
\       type that changes gives a new goal of the same kind, tag and
\       context, goal assigned it (the instantiated proof term is the same
\       node for node); an unchanged type gives goal itself
\   lf-goal-tag-append ( goal parent -- )  appendTag's use in
\       appendParentTag (Util.lean:29): goal's tag made parent ++ the tag
\       with its macro scopes erased (print-names.fs's lf-pp-unhygienic,
\       Lean's eraseMacroScopes), inside a hygienic parent's macro scopes
\       (Name.modifyBase): zero and a._@.M._hyg.3 give zero.a, x._@.M._hyg.1
\       and left give x.left._@.M._hyg.1; an anonymous tag gives parent
\   lf-name-suffix-of? ( s n -- flag )  Name.isSuffixOf (Init/Meta/
\       Defs.lean): s's components the last ones of n (zero of succ.zero;
\       the anonymous name of any name)
\   lf-name-prefix-of? ( p n -- flag )  Name.isPrefixOf: p is n or one of
\       its prefixes (succ of succ.zero; su of su.x, not of succ: a
\       component compares whole)
\       (findTag?'s name tests, tactic-case.fs; general Name functions,
\       whose home is core/name-equal.fs once the [kernel] gate's next
\       batch takes them, plan 9.4.8l B)
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../core/names.fs
require ../../core/name-equal.fs
require ../../present/print-names.fs
require ../../author/declarations.fs
require ../mvars.fs
require ../goals.fs
require ../instantiate.fs
require ../meta-must.fs
require ../app-builder.fs

\ ---- checkNotAssigned.
: lf-goal-not-assigned ( goal -- goal )
  dup lf-goal-assigned? if outcome-invalid lf-must then ;

\ ---- replaceTargetEq: goal' new in goal's context with goal's tag, goal
\ assigned Eq.mpr.{u} target new (mkExpectedPropHint h (mkEq target new)) goal'.
: mtg-goal-new ( type goal -- goal' )
  dup lf-goal-tag swap lf-goal-view lf-goal-new lf-must ;
: mtg-fresh ( goal new -- goal goal' ) over lf-goal-not-assigned mtg-goal-new ;
: mtg-eq ( goal goal' -- eq ) lf-goal-type swap lf-goal-type swap lf-mk-eq ;
: mtg-hint ( goal goal' h -- goal goal' h' )
  >r 2dup mtg-eq r> swap lf-mk-expected-prop-hint ;
: mtg-mpr ( target -- f )   \ Eq.mpr.{u} target, u target's level
  s" Eq.mpr" lfa-intern over lf-level! 1 lf-mk-const-id swap lf-mk-app ;
: mtg-value ( goal goal' h' -- goal goal' value )
  >r 2dup lf-goal-type swap lf-goal-type mtg-mpr swap lf-mk-app r> lf-mk-app
  over lf-mk-app ;
: mtg-assign ( goal goal' value -- goal' ) rot swap lf-mvar-assign lf-must ;
: lf-goal-replace-target-eq ( goal new h -- goal' )
  >r mtg-fresh r> mtg-hint mtg-value mtg-assign ;

\ ---- headBetaType.
: mtg-tag-from ( goal' goal -- goal' ) lf-goal-tag over swap lf-mvar-tag! lf-must ;
: mtg-like ( type goal -- goal' )   \ a new metavariable as goal, of type
  tuck dup lf-goal-kind swap lf-goal-view lf-mvar-new-at lf-must swap mtg-tag-from ;
: lf-goal-head-beta-type ( goal -- goal' )
  dup lf-goal-type dup lf-meta-head-beta lf-must tuck = if drop exit then
  over mtg-like tuck lf-mvar-assign lf-must ;

\ ---- appendTag (Util.lean:29): parent.modifyBase (· ++ tag's macro
\ scopes erased); modifyBase (Init/Meta/Defs.lean:308) appends to the
\ part before a hygienic parent's macro scopes and puts them back after.
: mtg-graft ( name t base -- name' ) lf-name-graft 0= if outcome-full lf-must then ;
: mtg-plus ( tag base -- base' ) swap lf-pp-unhygienic dup lf-name-depth rot mtg-graft ;
: mtg-scopes ( parent -- parent n )   \ the macro scopes' parts
  dup lf-name-depth over lf-pp-unhygienic lf-name-depth - ;
: mtg-appended ( parent tag -- tag' )
  over lf-pp-unhygienic mtg-plus >r mtg-scopes r> mtg-graft ;
: lf-goal-tag-append ( goal parent -- )
  over lf-goal-tag mtg-appended lf-mvar-tag! lf-must ;

\ ---- Name.isSuffixOf and Name.isPrefixOf, component by component
\ (core/name-equal.fs's lf-name-part= and lf-name-same?).
: lf-name-suffix-of? ( s n -- flag )
  begin over while 2dup lf-name-part= 0= if 2drop false exit then lf-name-prefixes
  repeat 2drop true ;
: lf-name-prefix-of? ( p n -- flag )
  begin 2dup lf-name-same? 0= while dup 0= if 2drop false exit then lf-name-prefix@
  repeat 2drop true ;
base !   \ the BASE this file was loaded with
