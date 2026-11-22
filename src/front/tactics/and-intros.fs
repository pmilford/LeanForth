\ by-and-intros, Lean's and_intros (plan row TB2, tactic batch 2b), a port
\ of Lean 4.35.0's macro repeat' refine And.intro ?_ ?_ (src/lean/Init/
\ Tactics.lean:1405-1407) over evalRepeat' (Elab/Tactic/Repeat.lean:28-
\ 32: Meta.repeat' over every goal, getGoals, not only the main one):
\ meta-tactic/repeat.fs's lf-goals-repeat with f refine And.intro ?_ ?_
\ on one goal, in its context: its target instantiated, through whnf at
\ the transparency in force (what isDefEq of ?a ∧ ?b with it unfolds),
\ And a b (else f fails, Lean's elaboration error, and the goal is kept);
\ two new synthetic opaque goals ?l : a and ?r : b in its context, tagged
\ tag.refine_1 and tag.refine_2 (refine's tagUntaggedGoals with the
\ suffix refine: two anonymous holes; an anonymous tag gives refine_1 and
\ refine_2), the goal assigned @And.intro a b ?l ?r. No goal is no error,
\ as Lean's.
\ Lean call list: getGoals, setGoals -> lf-goals, lf-goals! (goals.fs);
\ Meta.repeat' -> lf-goals-repeat; refine's elaboration ->
\ lf-goal-target, lf-whnf!, lf-goal-new, lf-mk-app-n; tagUntaggedGoals
\ -> lf-name-append-tag (meta-tactic/goal.fs); assign -> lf-mvar-assign.
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
\ A hole of type in goal's context, tagged goal's tag ++ the suffix.
: tai-tag ( goal c-addr u -- tag ) lfa-intern swap lf-goal-tag swap lf-name-append-tag ;
: tai-hole ( type tag goal -- g ) lf-goal-view lf-goal-new lf-must ;
: tai-left ( goal a -- goal l ) over dup s" refine_1" tai-tag swap tai-hole ;
: tai-right ( goal b -- goal r ) over dup s" refine_2" tai-tag swap tai-hole ;
: tai-split ( goal a b -- goal l r ) >r tai-left r> swap >r tai-right r> swap ;
\ @And.intro a b l r, a and b the holes' types.
: tai-intro ( a b -- f ) s" And.intro" lf-mk-const0 rot lf-mk-app swap lf-mk-app ;
: tai-types ( l r -- a b ) lf-goal-type swap lf-goal-type swap ;
: tai-term ( l r -- e ) 2dup tai-types tai-intro rot lf-mk-app swap lf-mk-app ;
: tai-assign ( goal l r -- l r ) 2dup 2>r tai-term lf-mvar-assign lf-must 2r> ;
: tai-f ( goal -- goals true | false )
  dup tai-and if tai-split tai-assign lf-goals2 true else drop false then ;
: tai-in ( goal -- goals true | false ) dup ['] tai-f lf-with-goal ;
: tai-run ( i -- ) drop lf-goals ['] tai-in lf-goals-repeat lf-goals! lf-tac-must ;
' tai-run tac-k-and-intros lf-tactic-action!
