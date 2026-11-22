\ by-and-intros, Lean's and_intros (plan row TB2, tactic batch 2b), a port
\ of Lean 4.35.0's macro repeat' refine And.intro ?_ ?_ (src/lean/Init/
\ Tactics.lean:1405-1407) over evalRepeat' (Elab/Tactic/Repeat.lean:28-
\ 32: Meta.repeat' over every goal, getGoals, not only the main one):
\ meta-tactic/repeat.fs's lf-goals-repeat with f refine And.intro ?_ ?_
\ on one goal, in its context: its target instantiated, through whnf at
\ the transparency in force (what isDefEq of ?a ∧ ?b with it unfolds),
\ And a b (else f fails, Lean's elaboration error, and the goal is kept);
\ two new anonymous synthetic opaque goals ?l : a and ?r : b in its
\ context, the goal assigned @And.intro a b ?l ?r, and the two tagged by
\ refine's tagUntaggedGoals with the suffix refine (two anonymous holes:
\ tag.refine_1 and tag.refine_2). No goal is no error, as Lean's.
\ Lean call list: getGoals, setGoals -> lf-goals, lf-goals! (goals.fs);
\ Meta.repeat' -> lf-goals-repeat; refine's elaboration ->
\ lf-goal-target, lf-whnf!, lf-goal-new, lf-mk-app-n; tagUntaggedGoals
\ -> lf-tag-untagged (new-goals.fs); assign -> lf-mvar-assign.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/assert.fs
require ../meta-tactic/repeat.fs

tac-shape-plain lf-tactic: by-and-intros constant tac-k-and-intros
s" and_intros" tac-k-and-intros lf-tactic-lean!

\ ---- refine And.intro ?_ ?_ on one goal.
: tai-and? ( t -- flag ) 2 s" And" lf-meta-app-of? ;
: tai-and ( goal -- a b true | false )
  lf-goal-target drop lf-whnf! dup tai-and? if lf-meta-args2 true else drop false then ;
\ An anonymous hole of type t in goal's context; the two, ?l made first.
: tai-hole ( goal t -- goal g ) over lf-goal-view 0 swap lf-goal-new lf-must ;
: tai-split ( goal a b -- goal l r ) >r tai-hole r> swap >r tai-hole r> swap ;
\ @And.intro a b l r, a and b the holes' types.
: tai-intro ( a b -- f ) s" And.intro" lf-mk-const0 rot lf-mk-app swap lf-mk-app ;
: tai-types ( l r -- a b ) lf-goal-type swap lf-goal-type swap ;
: tai-term ( l r -- e ) 2dup tai-types tai-intro rot lf-mk-app swap lf-mk-app ;
: tai-holes ( goals -- l r ) dup 0 run@ swap 1 run@ ;
: tai-assign ( goals goal -- goals goal )
  over tai-holes tai-term over swap lf-mvar-assign lf-must ;
\ The holes tagged from goal's tag, tagUntaggedGoals with the suffix refine.
: tai-tag ( goals goal -- goals )
  over swap lf-goal-tag c" refine" swap lf-tag-untagged ;
: tai-f ( goal -- goals true | false )
  dup tai-and if tai-split lf-goals2 swap tai-assign tai-tag true else drop false then ;
: tai-in ( goal -- goals true | false ) dup ['] tai-f lf-with-goal ;
: tai-run ( i -- ) drop lf-goals ['] tai-in lf-goals-repeat lf-goals! lf-tac-must ;
' tai-run tac-k-and-intros lf-tactic-action!
