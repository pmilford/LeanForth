\ LeanForth's side of tests/front/check_goals.py (plan FE1g-1): the goal
\ states of tests/front/goals-print.lean built by hand (free variables,
\ their locals and views, goals with their tags; src/front/goals.fs) and
\ printed by src/front/goal-print.fs, one block per `trace "=== NAME"` of
\ the Lean file, as its trace_state prints them. Test-only.

require ./goal-states.fs

: show ( c-addr u -- ) ." === " type cr lf-goals-print must-ok ;
: goals1 ( goal -- ) lf-pst-open must-ok ;
: goals2 ( g1 g2 -- ) >r 0 swap run-push made r> run-push made lf-goals! must-ok ;
: start ( -- ) g-fresh ['] type lf-print-unicode lf-print-setup ;
: zero. ( -- t ) 0 num ;
: one. ( -- t ) 1 num ;
: ones ( n -- t ) one. swap 1 ?do one. add loop ;
: ih-type ( k -- t ) zero. over add swap eq ;
\ The free variables and views of the states below.
0 value fn  0 value fn'  0 value fk  0 value fa  0 value fb  0 value fc
0 value fp  0 value fx  0 value fy  0 value vw  0 value vw0

\ t1: n : Nat ⊢ 0 + n = n, then the cases of induction n with | zero |
\ succ k ih (n cleared), then the goal rewrite [Nat.add_succ] leaves.
start 0 nat s" n" hyp to fn to vw
zero. fn add fn eq 0 vw goal goals1  s" t1.start" show
start zero. zero. add zero. eq s" zero" tag 0 goal goals1  s" t1.zero" show
start 0 nat s" k" hyp to fk  fk ih-type s" ih" hyp drop to vw
zero. fk one. add add fk one. add eq s" succ" tag vw goal goals1  s" t1.succ" show
zero. fk add succ fk one. add eq s" succ" tag vw goal goals1  s" t1.rewritten" show

\ t5: induction n without with: both cases, the second's hypotheses
\ inaccessible.
start zero. zero. add zero. eq s" zero" tag 0 goal
0 nat s" n" hyp-hidden to fn'  fn' ih-type s" a" hyp-hidden drop to vw
zero. fn' one. add add fn' one. add eq s" succ" tag vw goal goals2  s" t5.cases" show

\ t8: groups, a let shown, a have shown as a hypothesis.
start 0 nat s" a" hyp to fa  nat s" b" hyp to fb  t-prop s" p" hyp to fp
t-prop s" q" hyp drop fp s" h" hyp drop nat fa fb add s" x" let-hyp drop
nat fa s" y" have-hyp drop to vw
true. 0 vw goal goals1  s" t8" show

\ t9: the older n stays n; the case's own is n✝.
start 0 nat s" n" hyp to fn to vw0
vw0 zero. zero. eq s" h" hyp drop to vw
true. s" zero" tag vw goal
vw0 nat s" n" hyp-hidden to fn'  fn' fn' eq true. arrow s" a" hyp-hidden drop
fn' one. add fn' one. add eq s" h" hyp drop to vw
true. s" succ" tag vw goal goals2  s" t9.cases" show

\ c2: intro n shadows the hypothesis n; c4: intro without a name.
start 0 nat s" n" hyp to fn  nat s" n" hyp to fk to vw
fk fn add fk fn add eq 0 vw goal goals1  s" c2" show
start 0 nat s" x" hyp to fx  nat s" y" hyp-hidden drop to vw
fx fx eq 0 vw goal goals1  s" c4" show

\ s1, s2: tombstones with numbers.
start 0 nat s" x" hyp drop nat s" x" hyp drop nat s" x" hyp drop to vw
true. 0 vw goal goals1  s" s1" show
start 0 nat s" x" hyp-hidden drop nat s" x" hyp-hidden drop nat s" x" hyp-hidden drop
to vw  true. 0 vw goal goals1  s" s2" show

\ d2: equal types share a line (two terms built apart).
start 0 nat s" a" hyp to fa  nat s" b" hyp to fb  nat s" c" hyp to fc
fa fb eq s" h" hyp drop fa fb eq s" h'" hyp drop fb fc eq s" q" hyp drop to vw
true. 0 vw goal goals1  s" d2" show

\ d127: a let value of depth 256 (Lean's approxDepth: 2 * 127 + 2) is ⋯.
start 0 nat 127 ones s" y" let-hyp to fy to vw
fy fy eq 0 vw goal goals1  s" d127" show

\ e1: no goals; e2: two tagged goals; e3: intro x y over a let.
start 0 lf-goals! must-ok  s" e1" show
start 0 t-prop s" p" hyp to fp  fp s" hp" hyp drop to vw
fp s" left" tag vw goal  fp s" right" tag vw goal goals2  s" e2" show
start 0 nat s" x" hyp to fx  nat fx one. add s" y" let-hyp to fy to vw
fy fx one. add eq 0 vw goal goals1  s" e3" show

\ g1, g3: a Π that is a proposition (a gap of the term printer).
start 0 nat s" n" hyp to fn to vw
nat 0 t-var 0 t-var eq t-pi s" m" ex. 0 vw goal goals1  s" g1" show
start 0 nat s" n" hyp to fn  nat 0 t-var fn eq t-pi s" k" ex. s" h" hyp drop
to vw  true. 0 vw goal goals1  s" g3" show
bye
