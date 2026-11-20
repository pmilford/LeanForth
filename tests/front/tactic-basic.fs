\ Unit and end-to-end tests of the first tactics (plan FE1g-4;
\ src/front/tactics/intro.fs, exact.fs and rfl.fs on the tactic
\ library's goal words, design docs/design/FE1G_TACTICS.md 5.1-5.3),
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
\    through the command line and the kernel (exit 0); two binders closed
\    in order, (p q : Prop) : p -> p by intro and exact and (a : Type)
\    (x : a) : x = x by rfl, node for node and through the kernel; intro _
\    makes an inaccessible hypothesis; intro head-beta reduces the domain
\    and the body; rfl on p = p made as @Eq.refl.{1} Prop p and checked
\    by the kernel, on h1 = h2 (proofs of p) with the left side; errors 94
\    (with Lean's text), 95, 96 (with Lean's text), 97 (with Lean's text),
\    98, 99, 93, 71, and 91 when isDefEq or whnfCore runs out of fuel;
\ 2. malformed: a binder with no known kind, an implicit binder, a let;
\ 3. stack effects (every T{ }T checks the depth) and lf-term-holds?;
\ 4. through cli-check: tests/front/07-intro-exact.lf, 08-rfl.lf;
\ 5. resources: the heap refusing each allocation of an intro-exact run;
\ 6. state: an intro undone at a choice point leaves no assignment, the
\    goal list and the context as they were; the current context, the
\    printer's notation flag and defeq's configuration put back however a
\    step ends; the same verdicts run twice;
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
: eq-at ( α a b -- t ) >r >r >r level1 0 u! s" Eq" 1 cst r> app r> app r> app ;
: eq-of ( a b -- t ) prop -rot eq-at ;
: id-fun ( -- t ) prop 0 lf-term-bvar 0= abort" bvar" lf-term-lam 0= abort" lam" ;
: id-of ( t -- t' ) id-fun s" x" lf-binder-default named swap app ;   \ (fun x => x) t
: in2 ( t -- body ) lf-term-second@ lf-term-second@ ;

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
: stand-in ( node expected postpone? -- term outcome )
  2drop dup hyp-node? if hyp-fvar else drop chosen @ execute then outcome-ok ;
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
\ The hypothesis's local: the given name, accessible, explicit (the
\ newest of the new goal's context, the goal ?n of the root's value fun
\ h => ?n h is delayed-assigned).
: new-goal ( -- goal )
  lf-pst-root lf-mvar-value drop lf-term-second@ lf-term-first@ lf-mvar-delayed drop 2drop ;
: new-local ( -- local ) new-goal lf-mvar-view drop dup lf-view-count 1- lf-view-local ;
T{ new-local dup lf-local-name s" h" name= swap lf-local-flags -> true 0 }T
\ The goal's value before instantiation: fun h => ?n h, ?n delayed [h].
T{ lf-pst-root lf-mvar-value drop dup tag swap lf-term-second@ lf-term-first@ lf-mvar-delayed
   drop nip nip -> lf-tag-lam 1 }T
\ intro _: inaccessible, named as the binder (a); the goal as pinned Lean's
\ trace_state prints it (tactic-run.lean t3: p : Prop / a✝ : p / ⊢ p).
: part-goal ( k -- c-addr u ) trun-parts slab-at top-goal 2@ lfr-chars ;
T{ s" by-intro: _ by-sorry end t" proof nrun new-local lf-local-name s" a" name= -> outcome-ok true }T
T{ new-local lf-local-inaccessible? 0 part-goal s\" p : Prop\na✝ : p\n⊢ p" compare -> true 0 }T

\ intro head-beta reduces the binder's domain and the body (Lean's
\ introNCore, Meta/Tactic/Intro.lean): (fun x => x) p -> (fun x => x) p
\ gives the goal pinned Lean's trace_state prints (tactic-run.lean's
\ intro_beta); the same through whnfCore for (fun x => x) (p -> p).
: beta-imp ( -- type ) p-prop p @ id-of p @ id-of arrow ;
: beta-pi ( -- type ) p-prop p @ p @ arrow id-of ;
: h-goal ( -- c-addr u ) s\" p : Prop\nh : p\n⊢ p" ;
' beta-imp stating
T{ s" by-intro: h by-sorry end t" proof nrun 0 part-goal h-goal compare -> outcome-ok 0 }T
' beta-pi stating
T{ s" by-intro: h by-sorry end t" proof nrun 0 part-goal h-goal compare -> outcome-ok 0 }T

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
\ An alternative's field (lf-tac-intro1 given a kind, as induction's
\ eliminator gives it; review tactic-move M3): the kind given, here
\ implicit, is the local's; the node's own kind is not read (the binder
\ refused above, 99, is introduced). intro's row stands in for the call.
tac-k-intro lfr-row trow-run @ constant intro-action
: intro-implicit ( i -- ) dup 0 lf-tac-arg lf-binder-implicit rot lf-tac-intro1 ;
' intro-implicit tac-k-intro lf-tactic-action!
' implicit-pi stating
T{ s" by-intro: h by-sorry end t" proof nrun new-local dup lf-local-name s" h" name=
   swap lf-local-flags -> outcome-ok true lf-binder-implicit }T
intro-action tac-k-intro lf-tactic-action!

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
\ rw's own refusals at the rule (plan 9.4.8l-I C3, tactics/rewrite.fs),
\ the rule's place second: a rule holding the goal itself (220, Lean's
\ occurs check; no LeanForth text names the goal's metavariable, so the
\ stand-in gives it) and a rule left with an open metavariable (Lean's
\ new goals, 99). A place set already is kept.
: the-goal ( -- t ) lf-main-goal made ;
: open-eq ( -- t ) p @ p @ eq-of mv-natural lf-mvar-new made ;
: see@ ( -- line col ) lfa-error lfa-err-see @ lfa-pos> ;
' eq-pp stating  ' the-goal chosen !
T{ s" by-rw[ 0 ] end t" proof nrun err see@ -> outcome-invalid 220 1 43 1 50 }T
T{ 7 lfa-see! 0 trw-see lfa-error lfa-err-see @ -> 7 }T
' open-eq chosen !
T{ s" by-rw[ 0 ] end t" proof nrun err see@ -> outcome-unsupported 99 1 43 1 50 }T
\ An error of MVarId.rewrite's own (lf-goal-rewrite's 218: p is no
\ equation) gets the rule's place too.
' p-term chosen !
T{ s" by-rw[ 0 ] end t" proof nrun err see@ -> outcome-invalid 218 1 43 1 50 }T
\ lf-tac-goal. (tactic-core.fs): the last step's goal after a blank line
\ (induction's messages print it; no S2 text reaches them).
: goal-x ( x -- outcome ) drop lf-tac-goal. ;
lf-tac-forget
T{ 0 ' goal-x lf-tac-detail detail s\" \n\np : Prop\n⊢ p = p" compare -> 0 }T
lf-tac-forget
\ A goal type holding an open synthetic opaque metavariable ?o : Prop:
\ elabTermEnsuringType compares with it assignable (plan 9.4.8l J), so
\ fun (x : p) => x assigns it p -> p and closes the goal; p, whose type
\ Prop is no proposition, is Lean's Type mismatch with the sorts.
variable so
: so-p ( -- type ) p-prop prop mv-opaque lf-mvar-new made dup so ! ;
: id-p ( -- t ) p @ 0 lf-term-bvar 0= abort" bvar" lf-term-lam 0= abort" lam" ;
: so-value ( -- t ) so @ lf-instantiate-mvars made ;
' so-p stating  ' id-p chosen !
T{ s" n by-exact end t" proof nrun so-value lf-term-pi? -> outcome-ok true }T
T{ so-value lf-term-first@ p @ = so-value lf-term-second@ p @ = -> true true }T
' p-term chosen !
T{ s" n by-exact end t" proof nrun err -> outcome-invalid 96 1 45 }T
T{ detail s\"   p\nhas type\n  Prop\nof sort `Type` but is expected to have type\n  ?m.1\nof sort `Prop`"
   compare -> 0 }T
\ No term elaborator (plan FE1e): 71 at the word.
' imp-p stating
' tcr-unelaborated is lf-tac-elab
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
\ Not an equation: 93 (p; Ne p q, a relation of three arguments too, which
\ Lean's apply_rfl would try with @[refl] lemmas, plan FE5); not equal
\ with a metavariable in a side: 93.
' just-p stating
T{ s" by-rfl end t" proof nrun err -> outcome-unsupported 93 1 43 }T
: ne-pq ( -- type )
  p-prop prop s" q" binder q ! level1 0 u! s" Ne" 1 cst prop app p @ app q @ app ;
' ne-pq stating
T{ s" by-rfl end t" proof nrun err -> outcome-unsupported 93 1 43 }T
: eq-hole ( -- type )
  p-prop prop s" q" binder q ! p @ q @ prop mv-natural lf-mvar-new made arrow eq-of ;
' eq-hole stating
T{ s" by-rfl end t" proof nrun err -> outcome-unsupported 93 1 43 }T

\ Sides that differ but are definitionally equal (two proofs of p, by
\ proof irrelevance): Lean's Eq.refl takes the left side (MVarId.refl,
\ Meta/Tactic/Refl.lean:39; tactic-run.lean's refl_irrel):
\ fun (p : Prop) (h1 h2 : p) => @Eq.refl.{0} p h1, the level Eq's own.
: eq0 ( a b -- t ) >r >r 0 0 u! s" Eq" 1 cst p @ app r> app r> app ;
: irrel ( -- type ) p-prop p @ s" h1" binder p @ s" h2" binder eq0 ;
: in3 ( t -- body ) lf-term-second@ lf-term-second@ lf-term-second@ ;
' irrel stating
T{ s" by-rfl end t" proof nrun -> outcome-ok }T
T{ va in3 dup lf-term-second@ dup tag swap lf-term-first@ rot lf-term-first@ lf-term-second@ tag
   -> lf-tag-bvar 1 lf-tag-bvar }T
T{ va in3 lf-term-first@ lf-term-first@ lf-term-first@ lf-cref-slot lf-cref-pairs drop 0 lf-cref-pair@
   drop -> 0 }T

\ ---- 1. Two binders (review fe1g3 M1), closed oldest first as pinned
\ Lean's #print (tactic-run.lean's refl_x and imp_pq), node for node:
\ fun (a : Type) (x : a) => @Eq.refl.{1} a x, of type
\ forall (a : Type) (x : a), @Eq.{1} a x x.
variable ta  variable tx
: refl-x ( -- type )
  level1 sort s" a" binder ta ! ta @ s" x" binder tx ! ta @ tx @ tx @ eq-at ;
: bv ( t -- tag i ) dup tag swap lf-term-first@ ;
' refl-x stating
T{ s" by-rfl end t" proof nrun -> outcome-ok }T
T{ va bname s" a" name= va lf-term-second@ bname s" x" name= -> true true }T
T{ va lf-term-first@ bv one? va lf-term-second@ lf-term-first@ bv
   -> lf-tag-symbolic-sort true lf-tag-bvar 0 }T
T{ va in2 lf-term-first@ dup lf-term-first@ cname s" Eq.refl" name= swap lf-term-second@ bv
   -> true lf-tag-bvar 1 }T
T{ va in2 lf-term-second@ bv -> lf-tag-bvar 0 }T
T{ ty tag ty lf-term-first@ bv one? ty lf-term-second@ lf-term-first@ bv
   -> lf-tag-pi lf-tag-symbolic-sort true lf-tag-bvar 0 }T
T{ ty in2 lf-term-first@ lf-term-first@ lf-term-second@ bv ty in2 lf-term-second@ bv
   -> lf-tag-bvar 1 lf-tag-bvar 0 }T
\ fun (p q : Prop) (h : p) => h, of type forall (p q : Prop), p -> p.
: imp-pq ( -- type ) p-prop prop s" q" binder q ! p @ p @ arrow ;
' imp-pq stating
T{ s" by-intro: h h by-exact end t" proof nrun -> outcome-ok }T
T{ va bname s" p" name= va lf-term-second@ bname s" q" name= va in2 bname s" h" name=
   -> true true true }T
T{ va lf-term-second@ lf-term-first@ bv va in2 lf-term-first@ bv va in2 lf-term-second@ bv
   -> lf-tag-symbolic-sort 0 lf-tag-bvar 1 lf-tag-bvar 0 }T
T{ ty bname s" p" name= ty in2 lf-term-first@ bv ty in2 lf-term-second@ bv
   -> true lf-tag-bvar 1 lf-tag-bvar 2 }T

\ ---- 5. A Meta step out of fuel: 91, exhausted, at the step (review
\ fe1g3 L5): isDefEq of rfl's sides, whnfCore of intro's binder, each
\ given one unit.
' irrel stating
T{ 1 lf-defeq-fuel! s" by-rfl end t" proof nrun err 0 lf-defeq-fuel!
   -> outcome-exhausted 91 1 43 }T
' beta-pi stating
T{ 1 lf-whnf-fuel! s" by-intro: h end t" proof nrun err 0 lf-whnf-fuel!
   -> outcome-exhausted 91 1 43 }T

\ ---- 3. lf-term-holds?: a leaf found, none, and the outcome of the walk.
: fvar? ( leaf -- flag ) lf-term-tag@ lf-tag-fvar = ;
T{ prop ' fvar? lf-term-holds? p @ ' fvar? lf-term-holds? -> false outcome-ok true outcome-ok }T
T{ 1 heap-refusals ! p @ prop app ' fvar? lf-term-holds? nip -> outcome-full }T

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

\ ---- 6. An intro undone at a choice point (Lean's saveState and restore
\ around a failed alternative; review fe1g3 L9): a test row tries intro
\ h then fails; no assignment, the goal list and the context as before,
\ and by-sorry closes the goal as it was.
variable tried  variable goal0  variable seen
variable main-after  variable open-after  variable goals-after
: intro-fails ( -- ) tried @ tin-run lfa-e-tac-unsolved lfa-fail ;
: noted ( -- )
  lf-tac-main main-after ! goal0 @ lf-goal-assigned? open-after ! lf-goals run-count goals-after ! ;
: try-intro ( i -- )
  tried ! lf-tac-main goal0 ! ['] intro-fails lf-tac-try drop lf-author-code seen ! lf-tac-forget noted ;
' try-intro tac-k-intro lf-tactic-action!
' imp-p stating
T{ s" by-intro: h by-sorry end t" proof nrun seen @ -> outcome-ok 89 }T
T{ main-after @ goal0 @ = open-after @ goals-after @ -> true false 1 }T
T{ 0 part-goal s\" p : Prop\n⊢ p → p" compare -> 0 }T
' tin-run tac-k-intro lf-tactic-action!

\ ---- 6. Settings put back however a step ends (review fe1g3 L10): the
\ current context after a failed step on a goal of another context, the
\ printer's notation flag after a printing that throws, defeq's
\ configuration and mode after lf-tac-defeq.
T{ s" by-intro: h by-intro: k end t" proof nrun err lf-mctx-view lf-view-count
   -> outcome-invalid 94 1 55 1 }T
2variable settings
: sink-throws ( c-addr u -- ) 2drop -79 throw ;
: throwing-sink ( -- ) lf-print-settings settings 2! ['] sink-throws lf-print-unicode lf-print-setup ;
T{ false lf-print-notation! throwing-sink prop ' tmg-noted catch nip lf-print-notation? -> -79 false }T
settings 2@ lf-print-setup
T{ 0 lf-defeq-flags! lf-tr-all lf-defeq-mode! prop prop lf-tac-defeq lf-defeq-flags lf-defeq-mode
   -> true outcome-ok 0 lf-tr-all }T
lf-tr-default lf-defeq-mode!

\ ---- 1, 3. The shared step and message words of the tactics (review
\ 2026-11-19-s2-rest, finding 2): lf-tac-arg reads step i's argument k (a
\ name, 0 for _), as by-case: and the alternatives read their names;
\ lf-tac-.name writes a name between backquotes to the message's sink.
\ lf-tac-arg-at gives an argument's place: the second after the first.
variable seen#  variable seen0  variable seen1  variable at0  variable at1
: note-places ( i -- ) dup 0 lf-tac-arg-at at0 ! 1 lf-tac-arg-at at1 ! ;
: record-args ( i -- )
  dup note-places dup lf-tac-args# seen# ! dup 0 lf-tac-arg seen0 ! 1 lf-tac-arg seen1 !
  lfa-e-tac-unsolved lfa-fail ;
' record-args tac-k-case lf-tactic-action!
' imp-p stating
T{ s" by-case: succ k _ => by-sorry by-end end t" proof nrun drop seen# @ -> 2 }T
T{ seen0 @ s" k" lfa-intern = seen1 @ -> true 0 }T
T{ at0 @ 0> at1 @ at0 @ > -> true true }T
' tcs-w-case tac-k-case lf-tactic-action!
: grab ( c-addr u -- ) text+ ;
: named. ( c-addr u -- c-addr' u' )
  lf-print-settings settings 2! text0 ['] grab lf-print-unicode lf-print-setup
  lfa-intern lf-tac-.name settings 2@ lf-print-setup text$ ;
T{ s" succ.zero" named. s" `succ.zero`" compare -> 0 }T
T{ s" x" named. s" `x`" compare -> 0 }T

\ ---- 4. Through the command line and the kernel.
: tally ( k -- n ) cli-count-of @ ;
: check ( c-addr u -- code ) cli-options library cli-state opt-env 2! cli-check ;
' imp-p stating
T{ s" tests/front/07-intro-exact.lf" check outcome-ok tally cli-not-proved @ -> 0 49 1 }T
' eq-pp stating
T{ s" tests/front/08-rfl.lf" check outcome-ok tally cli-not-proved @ -> 0 49 1 }T
\ Two binders (review fe1g3 M1): the kernel accepts both closed terms.
' imp-pq stating
T{ s" tests/front/07-intro-exact.lf" check outcome-ok tally cli-not-proved @ -> 0 49 1 }T
' refl-x stating
T{ s" tests/front/08-rfl.lf" check outcome-ok tally cli-not-proved @ -> 0 49 1 }T
' eq-pp stating
\ 6. The same again: the same verdicts.
T{ s" tests/front/08-rfl.lf" check outcome-ok tally -> 0 49 }T
' lfr-unelaborated stating
T{ s" tests/front/07-intro-exact.lf" check lf-author-code -> 2 71 }T
T{ lfc-library-close -> }T
T{ depth -> 0 }T
cr .( tactic-basic.fs: all tests passed) cr
bye
