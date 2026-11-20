\ Goals with implicit and strict-implicit binders, which LeanForth text
\ cannot state yet (natural `forall` is plan FE2), introduced as by-intro
\ and by-intros introduce them and closed as by-rfl closes them (plan row
\ TB1; the goal words of src/front/meta-tactic/goal.fs called with the
\ tactics' arguments: lf-goal-intro-n with a name and kinds 0 for by-intro,
\ lf-goal-intros for by-intros, lf-goal-refl), over the S2 slice. Prints,
\ for each, "NAME type SX", "NAME value SX" (tests/front/elab-dump.fs's
\ printer) and "NAME binders K ..." (the value's lambdas' kinds: d
\ explicit, i implicit, s strict implicit, c instance), which
\ tests/front/tactics/intros/check.py compares with pinned Lean's lines of
\ tests/front/tactics/goal-layer.golden (in_implicit, in_strict,
\ is_implicit of goal-layer.lean).
\ Usage: gforth tests/front/tactics/intros/implicit.fs
require ../../elab-dump.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
s" tests/front/s2-slice.ndjson" true lfc-library-open dump-must
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" implicit.fs: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
lf-mctx-view constant view0
create xs 3 cells allot  create name1 1 cells allot
\ A new local of type Nat named c-addr u, of kind, current; its variable.
: local ( kind c-addr u -- fvar ) lfa-intern nat -rot swap lf-local-decl-new lf-mctx-view! ;
: x! ( fvar k -- fvar ) cells xs + over swap ! ;
\ ∀ {x : Nat}, x = x, and the same with a strict-implicit binder.
: one ( kind -- t ) s" x" local 0 x! dup lf-mk-eq xs 1 lf-mk-forall-fvars view0 lf-mctx-view! ;
\ ∀ {x : Nat} ⦃y : Nat⦄ (z : Nat), y = y.
: three ( -- t )
  lf-binder-implicit s" x" local 0 x! drop lf-binder-strict s" y" local 1 x!
  lf-binder-default s" z" local 2 x! drop dup lf-mk-eq xs 3 lf-mk-forall-fvars view0 lf-mctx-view! ;
: root-goal ( type -- goal ) 0 view0 lf-goal-new made ;
\ by-intro x (lf-tac-intro1's call: the name given, kinds 0) and by-intros.
: intro-x ( goal -- goal' ) s" x" lfa-intern name1 ! name1 0 1 xs lf-goal-intro-n ;
: rfl ( goal -- ) dup ['] lf-goal-refl lf-with-goal ;
: kind. ( kind -- ) s" disc" drop + c@ emit ;
: binders. ( e -- )
  begin dup lf-term-lam? while dup lf-binder-of 0= abort" implicit.fs: no binder"
    nip space kind. lf-term-second@ repeat drop ;
: shown ( goal type c-addr u -- )
  2dup type ."  type " rot .t cr 2dup type ."  value " 2 pick lf-instantiate! .t cr
  type ."  binders" lf-instantiate! binders. cr ;
: pinned ( type xt c-addr u -- )
  2>r over root-goal dup rot execute rfl swap 2r> shown ;
lf-binder-implicit one ' intro-x s" in_implicit" pinned
lf-binder-strict one ' intro-x s" in_strict" pinned
three ' lf-goal-intros s" is_implicit" pinned
bye
