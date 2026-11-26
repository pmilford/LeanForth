\ by-funext and by-funext[ x y ]: Lean's funext and funext x y (plan row
\ TB2, small tactics 1), ports of the macro of Lean 4.35.0's src/lean/
\ Init/NotationExtra.lean:279-284:
\   funext          repeat (apply funext; intro)
\   funext x xs*    apply funext; intro x; funext xs*
\ apply funext is evalApply of the identifier funext (meta-tactic/
\ apply.fs's lf-goal-apply-const under withSynthesize), the goal f = g
\ assigned @funext.{u,v} α β f g ?h and ?h : ∀ x, f x = g x in its place;
\ intro with no name (an inaccessible one, the binder's) or with the
\ list's next name (_ inaccessible). by-funext repeats the pair until a
\ pass fails, that pass undone (Elab/Tactic/Repeat.lean:17-26: repeat is
\ withoutRecover, each pass from a saved state: tactic-core.fs's
\ lf-tac-try-lean; only a Lean error ends it, anything else is thrown
\ on), so on a goal that is no function equation it changes nothing, as
\ Lean's. by-funext[ x .. ] (one name at least, 460: funext alone is
\ by-funext) does each pass once per name: a goal that is no function
\ equation is apply's error 380. Term patterns after funext (funext
\ (a, b)) are not read: the list holds names only.
\ Lean call list: apply funext -> lf-goal-apply-const in
\ lf-lift-meta-tactic, lf-tac-with-synth (tactic-core.fs); intro ->
\ lf-tac-intro1; repeat -> lf-tac-try-lean; the names -> lf-tac-arg.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-plain lf-tactic: by-funext constant tac-k-funext
s" funext" tac-k-funext lf-tactic-lean!
tac-shape-binders+ lf-tactic: by-funext[ constant tac-k-funext-names
s" funext" tac-k-funext-names lf-tactic-lean!

\ ---- apply funext; intro NAME on step i's main goal (name 0: none).
: tfx-apply ( goal -- goals ) s" funext" lf-goal-apply-const ;
: tfx-tac ( goal -- goals ) ['] tfx-apply lf-tac-with-synth ;
: tfx-pass ( name i -- ) dup ['] tfx-tac lf-lift-meta-tactic -1 swap lf-tac-intro1 ;

\ ---- funext: the pass until it fails; funext x xs*: once per name.
: tfx-once ( -- ) 0 lf-tac-step tfx-pass ;
: tfx-repeat ( i -- ) drop begin ['] tfx-once lf-tac-try-lean 0= until ;
' tfx-repeat tac-k-funext lf-tactic-action!
: tfx-named ( i k -- ) over swap lf-tac-arg swap tfx-pass ;
: tfx-names ( i -- ) dup lf-tac-args# 0 ?do dup i tfx-named loop drop ;
' tfx-names tac-k-funext-names lf-tactic-action!
