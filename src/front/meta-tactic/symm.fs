\ MVarId.applySymm, the goal operation of the symm tactic (plan row TB2,
\ tactic batch 2b), a port of Lean 4.35.0's src/lean/Lean/Meta/Tactic/
\ Symm.lean:83-102. Each word throws on failure (meta-must.fs).
\   lf-goal-symm ( goal -- goal' )  in goal's context: the target
\       instantiated must be a relation of two arguments, r x y (else
\       error 451 with Lean's text and the target); its @[symm] lemmas
\       (getSymmLems over the symm attribute's discrimination tree):
\       Init's, by the relation's head, Eq.symm, Iff.symm, Ne.symm,
\       HEq.symm, And.symm, Or.symm (Init/Prelude.lean:372, Init/
\       Core.lean:894, 957, 1059, 1063, 1067), another head not supported
\       yet (99: the attribute's lemmas are not in the elaboration data,
\       so a relation Mathlib or a user tags is not known); the lemma at
\       new level metavariables (mkConstWithFreshMVarLevels), a natural
\       metavariable per binder (forallMetaTelescopeReducing at reducible
\       transparency, telescope.fs), isDefEq of goal's type with the
\       lemma's conclusion (the transparency in force); goal assigned the
\       lemma applied to them; goal' the last of them, given goal's tag.
\       Lean's error when no lemma fits, 452's "No applicable symmetry
\       lemma found for", cannot come from Init's lemmas (each one's
\       conclusion fits any target of its relation): a conclusion that
\       does not fit is not supported (99), never an answer.
\ Lean call list: instantiateMVars -> lf-instantiate!; getSymmLems ->
\ msy-lemma (lib/find.fs's find-index over msy-pairs);
\ mkConstWithFreshMVarLevels -> lf-meta-const-fresh;
\ withReducible -> lf-with-reducible; forallMetaTelescopeReducing ->
\ lf-forall-meta-telescope-reducing; isDefEq -> lf-tac-defeq; assign ->
\ lf-mvar-assign; setTag -> lf-mvar-tag!.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none (the table msy-pairs is set while the file loads and
\ read-only afterwards). Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/find.fs
require ../../core/terms.fs
require ../../author/errors.fs
require ../../author/declarations.fs
require ../mvars.fs
require ../meta-config.fs
require ../term-eqv.fs
require ../tactic-run.fs
require ../tactic-msg.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs
require ./goal.fs

451 outcome-invalid s" Symmetry lemmas only apply to binary relations, not"
  lfa-code: lfa-e-symm-binary

\ ---- getSymmLems: a table of the relations, each word giving the
\ relation's name and its lemma's.
: msy-eq ( -- c-addr u c-addr' u' ) s" Eq" s" Eq.symm" ;
: msy-iff ( -- c-addr u c-addr' u' ) s" Iff" s" Iff.symm" ;
: msy-ne ( -- c-addr u c-addr' u' ) s" Ne" s" Ne.symm" ;
: msy-heq ( -- c-addr u c-addr' u' ) s" HEq" s" HEq.symm" ;
: msy-and ( -- c-addr u c-addr' u' ) s" And" s" And.symm" ;
: msy-or ( -- c-addr u c-addr' u' ) s" Or" s" Or.symm" ;
create msy-pairs ' msy-eq , ' msy-iff , ' msy-ne , ' msy-heq , ' msy-and , ' msy-or ,
6 constant msy-pairs#
: msy-pair ( k -- c-addr u c-addr' u' ) cells msy-pairs + @ execute ;
: msy-rel? ( head k -- head flag ) over swap msy-pair 2drop lf-meta-const-named? ;
: msy-lemma ( head -- c-addr u true | false )
  msy-pairs# ['] msy-rel? find-index if msy-pair 2swap 2drop true else false then ;

\ ---- The target: r x y, and its lemma.
: msy-binary? ( t -- flag )
  dup lf-term-app? if lf-term-first@ lf-term-app? else drop false then ;
: msy-target ( goal -- t )
  lf-goal-type lf-instantiate! dup msy-binary? if exit then
  dup ['] lf-tac-indented. lf-tac-detail lfa-e-symm-binary lf-tac-stop ;
: msy-fit ( flag -- ) 0= if lfa-e-tac-form lf-tac-fail then ;
: msy-decl ( t -- d )
  lf-meta-head msy-lemma dup msy-fit drop lfa-intern lf-menv-find lf-must ;

\ ---- The lemma applied to a metavariable per binder; its conclusion fits.
: msy-arg ( app mvar kind -- app' ) drop lf-mk-app ;
: msy-telescope ( d -- app body )
  dup lf-meta-const-fresh lf-must dup lf-infer! rot ['] msy-arg
  lf-forall-meta-telescope-reducing ;
: msy-applied ( d -- app body ) ['] msy-telescope lf-with-reducible ;
: msy-assigned ( goal app -- goal' )
  2dup lf-mvar-assign lf-must lf-term-second@ swap lf-goal-tag over swap lf-mvar-tag!
  lf-must ;
: msy-fits ( goal app body -- goal app )
  >r over lf-goal-type r> lf-tac-defeq lf-must msy-fit ;
: msy-run ( goal -- goal' ) dup msy-target msy-decl msy-applied msy-fits msy-assigned ;
: lf-goal-symm ( goal -- goal' ) dup ['] msy-run lf-with-goal ;
base !   \ the BASE this file was loaded with
