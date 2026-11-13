\ Unit and end-to-end tests of the first tactics (plan FE1g-4;
\ src/front/tactic-basic.fs, design docs/design/FE1G_TACTICS.md 5.1-5.3),
\ by the classes of docs/development/TEST_COVERAGE_REVIEW.md. Until plan
\ FE1e elaborates statements and terms, stand-ins build them directly:
\ the statement (lf-front-by-statement) and by-exact's term (lf-tac-elab:
\ a hypothesis by its name in the goal's context, anything else the term
\ a test chooses). isDefEq, type inference and whnfCore are FE1c's own
\ (defeq.fs, infer.fs, whnf.fs), over terms with no library constant in
\ their way (the Meta layer reads the fed input, which a text's run does
\ not have yet: plan FE1e). Covered:
\ 1. every outcome: theorem t (p : Prop) : p -> p := by intro h; exact h
\    made as Lean's fun (p : Prop) (h : p) => h, node for node, also
\    through the command line and the kernel (exit 0); intro _ makes an
\    inaccessible hypothesis; rfl on p = p made as @Eq.refl.{1} Prop p
\    and checked by the kernel; errors 94 (with Lean's text), 95, 96
\    (with Lean's text), 97 (with Lean's text), 98, 99, 93, 71;
\ 2. malformed: a binder with no known kind, an implicit binder, a let;
\ 3. stack effects (every T{ }T checks the depth) and lf-tac-holds?;
\ 4. through cli-check: tests/front/07-intro-exact.lf, 08-rfl.lf;
\ 5. resources: the heap refusing each allocation of an intro-exact run;
\ 6. state: an intro undone at a choice point leaves no assignment, the
\    same verdicts run twice;
\ 7. regression pins: the terms and texts.
include ../support/heap-watch.fs
require ../support/tester.fs
require ../../src/main.fs
decimal

: library ( -- c-addr u ) s" tests/front/run-slice.ndjson" ;
T{ library true lfc-library-open -> outcome-ok }T

\ ---- Texts and errors.
create text 4096 allot  variable text#
: text0 ( -- ) 0 text# ! ;
: text+ ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
: text$ ( -- c-addr u ) text text# @ ;
\ A theorem t whose statement words are read only (the stand-in gives
\ the statement); by at 1:40, the proof's first word at 1:43.
: proof ( c-addr u -- c-addr' u' )
  text0 s" theorem t Nat explicit: n 0 n + n = := by " text+ text+ text$ ;
: nrun ( c-addr u -- outcome ) lf-author-begin lf-author-text ;
: err ( -- code line col ) lf-author-code lfa-error lfa-err-at @ lfa-pos> ;
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: detail ( -- c-addr u ) 0 lfa-detail slab-at lfa-detail slab-count ;

\ ---- Terms by name, binders named.
create us 4 2* cells allot
: u! ( level i -- ) >r dup lf-level-identity drop swap r> 2* cells us + 2! ;
: cst ( c-addr u n -- t )
  >r lfa-intern lf-name-generation @ us r> lf-cref-new 0= abort" ref"
  lf-cterm-new 0= abort" const" drop ;
: app ( f a -- t ) lf-term-app 0= abort" app" ;
: made ( x outcome -- x ) ok? 0= abort" not made" ;
: sort ( level -- t ) lf-term-symbolic-sort 0= abort" sort" ;
: prop ( -- t ) 0 sort ;
: level1 ( -- level ) 0 lf-level-succ 0= abort" level" ;
: named ( t c-addr u kind -- t ) >r lfa-intern >r dup r> r> lf-pres-binder! made ;
: pi-of ( dom body c-addr u kind -- t ) 2>r >r lf-term-pi 0= abort" pi" r> 2r> named ;
: arrow ( dom body -- t ) s" a" lf-binder-default pi-of ;
: local-of ( fvar c-addr u flags -- local ) >r lfa-intern r> lf-local-new made ;
: pushed ( local -- ) lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: binder ( type c-addr u -- fvar ) rot lf-lctx-local made dup 2swap 0 local-of pushed ;
: eq-of ( a b -- t ) >r >r level1 0 u! s" Eq" 1 cst prop app r> app r> app ;

\ ---- Stand-in statements (plan FE1e).
variable p  variable q
: p-prop ( -- ) prop s" p" binder p ! ;
: imp-p ( -- type ) p-prop p @ p @ arrow ;                  \ (p : Prop) : p -> p
: eq-pp ( -- type ) p-prop p @ p @ eq-of ;                 \ (p : Prop) : p = p
: eq-pq ( -- type ) p-prop prop s" q" binder q ! p @ q @ eq-of ;
: just-p ( -- type ) p-prop p @ ;                          \ (p : Prop) : p
: bare-pi ( -- type ) p-prop p @ p @ lf-term-pi 0= abort" pi" ;   \ no kind known
: implicit-pi ( -- type ) p-prop p @ p @ s" a" lf-binder-implicit pi-of ;
: let-p ( -- type ) p-prop prop p @ p @ lf-term-lam 0= abort" lam" 0 lf-let-make 0= abort" let" ;
: stating ( xt -- ) is lf-front-by-statement ;
\ Stand-in elaboration (plan FE1e): a hypothesis by its name in the
\ current context, any other term the one chosen.
variable chosen
: hyp-node? ( node -- flag ) syn-kind@ syn-k-hyp = ;
: hyp-fvar ( node -- fvar ) syn-a@ lf-mctx-view swap lf-view-named 0= abort" hyp"
  lf-mctx-view swap lf-view-local lf-local-fvar ;
: stand-in ( node expected -- term outcome )
  drop dup hyp-node? if hyp-fvar else drop chosen @ execute then outcome-ok ;
' stand-in is lf-tac-elab
: decl0 ( -- decl ) lf-author-count begin 1- dup lfa-library? 0= until lf-author-decl ;
: ty ( -- t ) decl0 lf-fdecl-type @ ;
: va ( -- t ) decl0 lf-fdecl-value @ ;
: name= ( id c-addr u -- flag ) lfa-intern = ;
: bname ( t -- id ) lf-pres-binder@ 2drop ;
: tag ( t -- tag ) lf-term-tag@ ;

\ ---- 1. intro h; exact h: fun (p : Prop) (h : p) => h, as pinned Lean's
\ #print (tests/front/tactic-run.lean's t4).
' imp-p stating
T{ s" by-intro: h h by-exact end t" proof nrun -> outcome-ok }T
T{ va tag va lf-term-second@ tag va lf-term-second@ lf-term-second@ dup tag swap lf-term-first@
   -> lf-tag-lam lf-tag-lam lf-tag-bvar 0 }T
T{ va bname s" p" name= va lf-term-second@ bname s" h" name= -> true true }T
T{ va lf-term-second@ lf-term-first@ dup tag swap lf-term-first@ -> lf-tag-bvar 0 }T
T{ ty tag ty lf-term-second@ dup tag swap lf-term-first@ tag -> lf-tag-pi lf-tag-pi lf-tag-bvar }T
\ The hypothesis's local: the given name, accessible, explicit.
: new-local ( -- local ) tb tb-new @ lf-mvar-view drop dup lf-view-count 1- lf-view-local ;
T{ new-local dup lf-local-name s" h" name= swap lf-local-flags -> true 0 }T
\ The goal's value before instantiation: fun h => ?n h, ?n delayed [h].
T{ lf-pst-root lf-mvar-value drop dup tag swap lf-term-second@ lf-term-first@ lf-mvar-delayed
   drop nip nip -> lf-tag-lam 1 }T
\ intro _: inaccessible, named as the binder (a); the goal as pinned Lean's
\ trace_state prints it (tactic-run.lean t3: p : Prop / a✝ : p / ⊢ p).
: part-goal ( k -- c-addr u ) trun-parts slab-at dup top-goal @ swap top-goal# @ lfr-chars ;
T{ s" by-intro: _ by-sorry end t" proof nrun new-local lf-local-name s" a" name= -> outcome-ok true }T
T{ new-local lf-local-inaccessible? 0 part-goal s\" p : Prop\na✝ : p\n⊢ p" compare -> true 0 }T

\ ---- 1. intro with nothing to introduce: 94 at the word, Lean's goal
\ after a blank line (t3's second intro); where whnf's delta might find a
\ binder (a constant the Meta layer does not hold): 93.
T{ s" by-intro: _ by-intro: _ end t" proof nrun err -> outcome-invalid 94 1 55 }T
T{ token s" by-intro:" compare detail s\" \np : Prop\na✝ : p\n⊢ p" compare -> 0 0 }T
' just-p stating
T{ s" by-intro: h end t" proof nrun err -> outcome-invalid 94 1 43 }T
: true-p ( -- type ) p-prop s" True" 0 cst ;
' true-p stating
T{ s" by-intro: h end t" proof nrun err -> outcome-unsupported 93 1 43 }T
\ ---- 2. Not supported yet (99): the name rfl, a binder of no known kind,
\ an implicit binder, a let.
' imp-p stating
T{ s" by-intro: rfl end t" proof nrun err -> outcome-unsupported 99 1 43 }T
' bare-pi stating
T{ s" by-intro: h end t" proof nrun err -> outcome-unsupported 99 1 43 }T
' implicit-pi stating
T{ s" by-intro: h end t" proof nrun err -> outcome-unsupported 99 1 43 }T
' let-p stating
T{ s" by-intro: h end t" proof nrun err -> outcome-unsupported 99 1 43 }T

\ ---- 1. exact: a term of another type, Lean's Type mismatch text (the
\ term, its type, the type expected; tactic-run.lean's x1 shape).
: p-term ( -- t ) p @ ;
' p-term chosen !
' imp-p stating
T{ s" by-intro: h n by-exact end t" proof nrun err -> outcome-invalid 96 1 57 }T
: sort-lines ( -- c-addr u )
  s\"   p\nhas type\n  Prop\nof sort `Type` but is expected to have type\n  p\nof sort `Prop`" ;
T{ detail sort-lines compare -> 0 }T
\ Types of one sort: no sort lines (tactic-run.lean's exact_wrong).
variable h
: pqh-p ( -- type ) p-prop prop s" q" binder q ! q @ s" h" binder h ! p @ ;
: h-term ( -- t ) h @ ;
' pqh-p stating  ' h-term chosen !
T{ s" n by-exact end t" proof nrun err -> outcome-invalid 96 1 45 }T
T{ detail s\"   h\nhas type\n  q\nbut is expected to have type\n  p" compare -> 0 }T
' p-term chosen !  ' imp-p stating
\ A metavariable the term made, left unassigned: 95; one made before the
\ step (by the statement), still open: 93; a free variable outside the
\ goal's context: 98, with the term and the goal.
: new-hole ( -- t ) p @ mv-natural lf-mvar-new made ;
' new-hole chosen !
T{ s" by-intro: h n by-exact end t" proof nrun err -> outcome-invalid 95 1 57 }T
variable old
: holed-p ( -- type ) imp-p p @ mv-natural lf-mvar-new made old ! ;
: old-hole ( -- t ) old @ ;
' holed-p stating  ' old-hole chosen !
T{ s" by-intro: h n by-exact end t" proof nrun err -> outcome-unsupported 93 1 57 }T
: stray ( -- t ) p @ lf-lctx-local made ;
' imp-p stating  ' stray chosen !
T{ s" by-intro: h n by-exact end t" proof nrun err -> outcome-invalid 98 1 57 }T
T{ detail drop 8 s"   _fvar." compare -> 0 }T
T{ detail s\" occurs-check failure\n\np : Prop\nh : p\n⊢ p" search nip nip -> true }T
\ A goal type holding an open synthetic opaque metavariable (Lean compares
\ with it assignable): 93 before isDefEq.
: so-p ( -- type ) p-prop prop mv-opaque lf-mvar-new made ;
' so-p stating  ' p-term chosen !
T{ s" n by-exact end t" proof nrun err -> outcome-unsupported 93 1 45 }T
\ No term elaborator (plan FE1e): 71 at the word.
' imp-p stating
' lfb-unelaborated is lf-tac-elab
T{ s" by-intro: h n by-exact end t" proof nrun err -> outcome-unsupported 71 1 57 }T
' stand-in is lf-tac-elab

\ ---- 1. rfl: p = p made as fun (p : Prop) => @Eq.refl.{1} Prop p.
: cname ( c -- id ) lf-term-first@ lf-cref-slot lf-cref-name@ drop ;
: one? ( level -- flag )
  dup lf-level-slot node-tag @ lf-level-tag-succ = swap lf-level-slot node-first @ 0= and ;
: refl-head ( -- c ) va lf-term-second@ lf-term-first@ lf-term-first@ ;
' eq-pp stating
T{ s" by-rfl end t" proof nrun -> outcome-ok }T
T{ refl-head cname s" Eq.refl" name= va lf-term-second@ lf-term-second@ tag -> true lf-tag-bvar }T
T{ refl-head lf-term-first@ lf-cref-slot lf-cref-pairs drop 0 lf-cref-pair@ drop one? -> true }T
\ Not equal: 97 with Lean's text (the two sides, the goal after a blank
\ line, tactic-run.lean's w1 shape).
' eq-pq stating
T{ s" by-rfl end t" proof nrun err -> outcome-invalid 97 1 43 }T
T{ detail s\"   p\nis not definitionally equal to the right-hand side\n  q\n\np q : Prop\n⊢ p = q"
   compare -> 0 }T
\ Not an equation: 93; not equal with a metavariable in a side: 93.
' just-p stating
T{ s" by-rfl end t" proof nrun err -> outcome-unsupported 93 1 43 }T
: eq-hole ( -- type )
  p-prop prop s" q" binder q ! p @ q @ prop mv-natural lf-mvar-new made arrow eq-of ;
' eq-hole stating
T{ s" by-rfl end t" proof nrun err -> outcome-unsupported 93 1 43 }T

\ ---- 3. lf-tac-holds?: a leaf found, none, and the outcome of the walk.
: fvar? ( leaf -- flag ) lf-term-tag@ lf-tag-fvar = ;
T{ prop ' fvar? lf-tac-holds? p @ ' fvar? lf-tac-holds? -> false outcome-ok true outcome-ok }T
T{ 1 heap-refusals ! p @ prop app ' fvar? lf-tac-holds? nip -> outcome-full }T

\ ---- 5. The heap refusing each allocation of an intro-exact run in turn:
\ never accepted, ok or full each time; past the last one, made.
' imp-p stating
: ie-text ( -- c-addr u ) s" by-intro: h h by-exact end t" proof ;
: refused-at ( k -- outcome ) ie-text 2>r heap-refusals ! 2r> nrun 0 heap-refusals ! ;
variable worst
: refusal-ok? ( outcome -- flag ) dup ok? swap outcome-full = or ;
: each-refused ( -- k )
  0 begin 1+ dup refused-at dup refusal-ok? 0= if dup worst ! then ok? until ;
T{ outcome-ok worst ! each-refused 1 > worst @ -> true outcome-ok }T

\ ---- 4. Through the command line and the kernel.
: tally ( k -- n ) cli-count-of @ ;
: check ( c-addr u -- code ) cli-options library cli-state opt-env 2! cli-check ;
' imp-p stating
T{ s" tests/front/07-intro-exact.lf" check outcome-ok tally cli-not-proved @ -> 0 49 1 }T
' eq-pp stating
T{ s" tests/front/08-rfl.lf" check outcome-ok tally cli-not-proved @ -> 0 49 1 }T
\ 6. The same again: the same verdicts.
T{ s" tests/front/08-rfl.lf" check outcome-ok tally -> 0 49 }T
' lfr-unelaborated stating
T{ s" tests/front/07-intro-exact.lf" check lf-author-code -> 2 71 }T
T{ lfc-library-close -> }T
T{ depth -> 0 }T
cr .( tactic-basic.fs: all tests passed) cr
bye
