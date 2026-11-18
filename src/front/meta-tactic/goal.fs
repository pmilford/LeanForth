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
\   lf-goal-tag-append ( goal tag -- )  appendTag's use in appendParentTag
\       (Util.lean:29): goal's tag made tag.suffix, suffix its own last
\       part (a name of one string part; another is thrown unsupported)
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../core/names.fs
require ../../author/declarations.fs
require ../mvars.fs
require ../goals.fs
require ../instantiate.fs
require ../meta-must.fs
require ../app-builder.fs

\ ---- checkNotAssigned.
: lf-goal-not-assigned ( goal -- goal )
  dup lf-goal-assigned? if outcome-invalid lf-must then ;

\ ---- replaceTargetEq: Eq.mpr.{u} target new (mkExpectedPropHint h
\ (mkEq target new)) goal'.
: mtg-type ( goal -- type ) lf-mvar-type 0= if outcome-invalid lf-must then ;
: mtg-tag ( goal -- tag ) lf-mvar-tag 0= if outcome-invalid lf-must then ;
: mtg-view ( goal -- view ) lf-mvar-view 0= if outcome-invalid lf-must then ;
: mtg-goal-new ( type goal -- goal' )
  dup mtg-tag swap mtg-view lf-goal-new lf-must ;
: mtg-hint ( target new h -- h' ) -rot lf-mk-eq lf-mk-expected-prop-hint ;
: mtg-mpr-const ( target -- c ) lf-level! >r s" Eq.mpr" r> lf-mk-const1 ;
: mtg-mpr ( target new h goal' -- value )
  >r >r over mtg-mpr-const -rot 2dup r> mtg-hint r> 4 lf-mk-app-n ;
: mtg-value ( new h goal goal' -- value ) >r mtg-type -rot r> mtg-mpr ;
: lf-goal-replace-target-eq ( goal new h -- goal' )
  rot lf-goal-not-assigned 2 pick over mtg-goal-new
  dup >r over >r mtg-value r> swap lf-mvar-assign lf-must r> ;

\ ---- headBetaType.
: mtg-kind ( goal -- kind ) lf-mvar-kind 0= if outcome-invalid lf-must then ;
: mtg-tag! ( goal tag -- ) ?dup if lf-mvar-tag! lf-must else drop then ;
: mtg-like ( type goal -- goal' )   \ a new metavariable as goal, of type
  >r r@ mtg-kind r@ mtg-view lf-mvar-new-at lf-must dup r> mtg-tag mtg-tag! ;
: lf-goal-head-beta-type ( goal -- goal' )
  dup mtg-type dup lf-meta-head-beta lf-must tuck = if drop exit then
  over mtg-like tuck lf-mvar-assign lf-must ;

\ ---- appendTag: parent ++ the goal's own tag (anonymous: parent), its
\ one string part as the suffix (Lean's eraseMacroScopes of a name with
\ no macro scope); a tag of more parts is not ported (unsupported).
: mtg-suffix ( name -- c-addr u )
  dup lf-name-prefix@ 0<> over lf-name-str? 0= or if outcome-unsupported lf-must then
  lf-name-text ;
: mtg-appended ( parent tag -- tag' ) ?dup if mtg-suffix lfa-intern-part then ;
: lf-goal-tag-append ( goal parent -- )
  over mtg-tag mtg-appended mtg-tag! ;
base !   \ the BASE this file was loaded with
