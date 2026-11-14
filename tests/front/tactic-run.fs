\ Unit and end-to-end tests of the tactic runner (plan FE1g-3a;
\ src/front/tactic-run.fs, design docs/design/FE1G_TACTICS.md 4.3-4.6),
\ by the classes of docs/development/TEST_COVERAGE_REVIEW.md. Until plan
\ FE1e elaborates statements, stand-in elaborators (lf-front-by-statement)
\ build each statement directly: a binder's free variable with its local
\ on the current view, and the statement's type. Covered:
\ 1. every outcome: a proof with by-sorry made and handed over (the term
\    sorryAx.{u} T Bool.false at levels 0 and 1, the open part kept and
\    reported); error 71 without an elaborator; 89 (unsolved goals, at by
\    or a block's =>, with Lean's text of the goals); 80 for each tactic
\    not ported yet, with its plan step and the goals; 90 (no goals); 91
\    (fuel); 92 (each kind of malformed record); 93 (a level type
\    inference cannot find, a let binder); the hand-over's 74;
\ 2. malformed records and proof states; 3. stack effects (every T{ }T
\    checks the depth) and the public words directly: focus, done,
\    blocks, saved states; 4. through the command line (cli-check, the
\    path of every text): tests/front/05-unsolved.lf exits 4 with error
\    89, tests/front/06-sorry.lf exits 0 with its own statement (the
\    library's constants in view, S1 merge B) and with the stand-in
\    p : Prop, the kernel accepting it NOT PROVED; 5. resources: fuel at every step, the heap refusing each
\    allocation of a run, 1,000 nested blocks (heap frames); 6. state:
\    rollback at choice points field by field, the same verdict after a
\    failed run, the open parts reset with each run, none kept by a
\    by-sorry that failed, the printer's settings put back after a THROW;
\    an open part or an error's detail cut where its slab is full;
\    7. regression pins: the terms, positions and texts.
\ Nothing here accepts a theorem except through the kernel's check.
include ../support/heap-watch.fs
require ../support/tester.fs
require ../../src/main.fs
decimal

: library ( -- c-addr u ) s" tests/front/run-slice.ndjson" ;
T{ library true lfc-library-open -> outcome-ok }T

\ ---- Texts and their errors.
create text 32768 allot  variable text#
: text0 ( -- ) 0 text# ! ;
: text+ ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
: text$ ( -- c-addr u ) text text# @ ;
\ A theorem t with n : Nat whose statement is 0 + n = n; by at 1:40, the
\ proof's first word at 1:43.
: proof ( c-addr u -- c-addr' u' )
  text0 s" theorem t Nat explicit: n 0 n + n = := by " text+ text+ text$ ;
: nrun ( c-addr u -- outcome ) lf-author-begin lf-author-text ;
: err ( -- code line col ) lf-author-code lfa-error lfa-err-at @ lfa-pos> ;
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: detail ( -- c-addr u ) 0 lfa-detail slab-at lfa-detail slab-count ;
: plan# ( -- n ) lfa-error lfa-err-number @ ;
: cut? ( -- flag ) lfa-error lfa-err-cut @ ;

\ ---- Terms by name (the author's names), as FE1e will build them.
create us 4 2* cells allot
: u! ( level i -- ) >r dup lf-level-identity drop swap r> 2* cells us + 2! ;
: u-zeros ( n -- ) 0 ?do 0 i u! loop ;
: cst ( c-addr u n -- t )
  >r lfa-intern lf-name-generation @ us r> lf-cref-new 0= abort" ref"
  lf-cterm-new 0= abort" const" drop ;
: app ( f a -- t ) lf-term-app 0= abort" app" ;
: raw-lit ( u -- t ) lf-hterm-cell 0= abort" lit" drop ;
: made ( x outcome -- x ) ok? 0= abort" not made" ;
: sort ( level -- t ) lf-term-symbolic-sort 0= abort" sort" ;
: level1 ( -- level ) 0 lf-level-succ 0= abort" level" ;
: nat ( -- t ) s" Nat" 0 cst ;
: hadd ( -- t ) 3 u-zeros s" HAdd.hAdd" 3 cst nat app nat app nat app ;
: inst ( -- t ) 1 u-zeros s" instHAdd" 1 cst nat app s" instAddNat" 0 cst app ;
: zero ( -- t )
  1 u-zeros s" OfNat.ofNat" 1 cst nat app 0 raw-lit app s" instOfNatNat" 0 cst 0 raw-lit app app ;
: eq ( a b -- t ) >r >r 1 lfa-level-number 0 u! s" Eq" 1 cst nat app r> app r> app ;
\ A binder: a free variable of the type, its local named and pushed on
\ the current view.
: local-of ( fvar c-addr u flags -- local ) >r lfa-intern r> lf-local-new made ;
: pushed ( local -- ) lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: binder ( type c-addr u -- fvar ) rot lf-lctx-local made dup 2swap 0 local-of pushed ;

\ ---- Stand-in statements (plan FE1e): 0 + n = n with n : Nat; p with
\ p : Prop; a with a : Type; the same with a let or an auxiliary local.
: zero-add ( -- type ) nat s" n" binder >r hadd inst app zero app r@ app r> eq ;
: prop-p ( -- type ) 0 sort s" p" binder ;
variable a-level   \ the level the stand-in made for Type
: type-a ( -- type ) level1 dup a-level ! sort s" a" binder ;
: let-x ( -- type )
  0 sort dup s" q" binder lf-lctx-let made s" x" 0 local-of pushed prop-p ;
: aux-p ( -- type )
  0 sort lf-lctx-local made s" t" lf-local-aux-decl local-of pushed prop-p ;
: stating ( xt -- ) is lf-front-by-statement ;
\ The text's own declaration: the last that is no library constant's
\ entry (those the text names follow the declaration that names them).
: decl0 ( -- decl ) lf-author-count begin 1- dup lfa-library? 0= until lf-author-decl ;
: ty ( -- t ) decl0 lf-fdecl-type @ ;
: va ( -- t ) decl0 lf-fdecl-value @ ;
: name= ( id c-addr u -- flag ) lfa-intern = ;
: bname ( t -- id ) lf-pres-binder@ 2drop ;
: cname ( t -- id ) lf-term-first@ lf-cref-slot lf-cref-name@ drop ;
: const-level ( t -- level ) lf-term-first@ lf-cref-slot lf-cref-pairs drop 0 lf-cref-pair@ drop ;
: sorry-app ( -- t ) va lf-term-second@ ;   \ sorryAx.{u} #0 Bool.false

\ ---- 1. The runner's own default with no statement elaborator set
\ (front/elab-decl.fs sets one): error 71 at end, as for a term proof; a
\ tactic proof with no step, the same.
' lfr-unelaborated stating
T{ s" by-sorry end t" proof nrun err -> outcome-unsupported 71 1 52 }T
T{ s" end t" proof nrun err -> outcome-unsupported 71 1 43 }T

\ ---- 1. by-sorry: theorem t (p : Prop) : p := by sorry, made as
\ fun (p : Prop) => sorryAx.{0} p Bool.false (Lean labels its sorry, plan
\ PD1), the statement closed as forall (p : Prop), p.
' prop-p stating
T{ s" by-sorry end t" proof nrun -> outcome-ok }T
T{ ty lf-term-tag@ va lf-term-tag@ -> lf-tag-pi lf-tag-lam }T
T{ ty bname s" p" name= va bname s" p" name= -> true true }T
T{ ty lf-term-first@ dup lf-term-tag@ swap lf-term-first@ -> lf-tag-symbolic-sort 0 }T
T{ ty lf-term-second@ dup lf-term-tag@ swap lf-term-first@ -> lf-tag-bvar 0 }T
T{ va lf-term-first@ ty lf-term-first@ = -> true }T
T{ sorry-app lf-term-second@ cname s" Bool.false" name= -> true }T
T{ sorry-app lf-term-first@ lf-term-second@ dup lf-term-tag@ swap lf-term-first@
   -> lf-tag-bvar 0 }T
T{ sorry-app lf-term-first@ lf-term-first@ dup cname s" sorryAx" name= swap const-level
   -> true 0 }T
T{ lfa-front-made? -> true }T
\ Its open part: the declaration, the position of by-sorry, the goal.
: part ( k -- addr ) trun-parts slab-at ;
: part-name ( k -- c-addr u ) part dup top-name @ swap top-name# @ lfr-chars ;
: part-goal ( k -- c-addr u ) part dup top-goal @ swap top-goal# @ lfr-chars ;
T{ lf-open-parts 0 part top-at @ lfa-pos> -> 1 1 43 }T
T{ 0 part-name s" t" compare 0 part-goal s\" p : Prop\n⊢ p" compare -> 0 0 }T
[defined] >string-execute [if]
: report ( -- c-addr u ) ['] lf-open-parts. >string-execute ;
: report-text ( -- c-addr u )
  s\" open part 1 of t (by-sorry at line:col 1:43):\np : Prop\n⊢ p\n" ;
T{ report drop report-text tuck compare -> 0 }T
T{ report report-text nip /string drop s" note: everything else" tuck compare -> 0 }T
[then]
\ A new run forgets the last run's open parts (lfa-run-fresh).
T{ lf-author-begin lf-open-parts -> 0 }T
\ Two declarations, a sorry each: two open parts, in order.
T{ s" by-sorry end t theorem u Nat explicit: n 0 n + n = := by by-sorry end u" proof nrun
   lf-open-parts -> outcome-ok 2 }T
T{ 1 part-name s" u" compare 1 part top-at @ lfa-pos> -> 0 1 100 }T

\ A definition at level 1: def d (a : Type) : a := by sorry gives
\ sorryAx.{1} a Bool.false.
' type-a stating
T{ s" def d Nat := by by-sorry end d" nrun -> outcome-ok }T
T{ sorry-app lf-term-first@ lf-term-first@ const-level -> a-level @ }T
T{ ty lf-term-first@ lf-term-first@ -> a-level @ }T

\ An auxiliary local (Lean's auxDecl for the declaration's own name) is
\ in the goal's context but no binder of the value.
' aux-p stating
T{ s" by-sorry end t" proof nrun -> outcome-ok }T
T{ va lf-term-second@ lf-term-tag@ va lf-term-tag@ -> lf-tag-app lf-tag-lam }T
T{ va bname s" p" name= -> true }T

\ ---- 1. Unsolved goals: error 89 at by, Lean's text of the goals
\ (tests/front/tactic-run.lean: theorem zero_add_open (n : Nat) : 0 + n =
\ n := by gives "unsolved goals" and the lines below).
' zero-add stating
: lean-goals ( -- c-addr u ) s\" n : Nat\n⊢ 0 + n = n" ;
T{ s" end t" proof nrun err -> outcome-invalid 89 1 40 }T
T{ token s" by" compare detail lean-goals compare cut? -> 0 0 false }T
T{ lfa-error lfa-err-see @ -> -1 }T
[defined] >string-execute [if]
\ As the command line prints it: the message, then Lean's goal lines.
: printed ( -- c-addr u ) ['] lf-author-error. >string-execute ;
: unsolved-line ( -- c-addr u )
  s\" error 89 at line:col 1:40 (token `by`): unsolved goals\nn : Nat\n⊢ 0 + n = n" ;
T{ printed unsolved-line compare -> 0 }T
[then]

\ ---- 1. Tactics not ported yet: 80 at the word, its plan step, the goals
\ (by-rfl, by-exact and by-intro: run since FE1g-4: tests/front/tactic-basic.fs).
: later ( c-addr u -- code line col plan ) proof nrun drop err plan# ;
T{ s" n by-induction end t" later -> 80 1 45 5 }T
T{ token s" by-induction" compare detail lean-goals compare -> 0 0 }T
T{ s" n by-induction-with | zero => by-rfl by-end end t" later -> 80 1 45 5 }T
T{ s" by-case: zero => by-rfl by-end end t" later -> 80 1 43 5 }T
T{ s" by-rw[ ] end t" later -> 80 1 43 6 }T
T{ s" by-rewrite[ ] end t" later -> 80 1 43 6 }T
T{ token s" by-rewrite[" compare outcome-unsupported lfa-e-tac-run lf-author-outcome = -> 0 true }T
[defined] >string-execute [if]
: error-text ( -- c-addr u ) ['] lf-author-error. >string-execute ;
T{ error-text s" (plan FE1g-6)" search nip nip -> true }T
[then]

\ ---- 1. No goals: a second by-sorry (Lean: "No goals to be solved" at
\ the second sorry); invalid, no goals shown.
' prop-p stating
T{ s" by-sorry by-sorry end t" proof nrun err -> outcome-invalid 90 1 52 }T
T{ token s" by-sorry" compare detail nip -> 0 0 }T

\ ---- 1. The constants of 0 + n = n in the Meta layer's view while the
\ text runs (S1 merge B, the library's route): the goal's level is
\ inferred and by-sorry closes it, the goal kept as Lean shows it.
' zero-add stating
T{ s" by-sorry end t" proof nrun lf-author-code lf-open-parts -> outcome-ok 0 1 }T
T{ 0 part-goal lean-goals compare -> 0 }T
\ A let among the binders: not supported yet when the value is closed.
' let-x stating
T{ s" by-sorry end t" proof nrun err -> outcome-unsupported 93 1 52 }T

\ ---- 5. Fuel: none left at a step is 91, exhausted, at that step with
\ the goals; exactly enough runs.
' prop-p stating
T{ 0 lf-tactic-fuel! s" by-sorry end t" proof nrun err -> outcome-exhausted 91 1 43 }T
T{ detail s\" p : Prop\n⊢ p" compare -> 0 }T
T{ 1 lf-tactic-fuel! s" by-sorry end t" proof nrun lf-tactic-fuel-left -> outcome-ok 0 }T
T{ 1 lf-tactic-fuel! s" by-sorry by-sorry end t" proof nrun err -> outcome-exhausted 91 1 52 }T
\ A no-op tactic in by-rfl's row (its own action kept and put back): with fuel
\ k, n steps stop at step k + 1 for every k < n, and run with k = n.
: skip-step ( i -- ) drop ;
tac-k-rfl lfr-row trow-run @ constant rfl-action
' skip-step tac-k-rfl lf-tactic-action!
: rfls ( n -- ) 0 ?do s" by-rfl " text+ loop ;
: steps ( n -- c-addr u ) s" " proof 2drop rfls s" by-sorry end t" text+ text$ ;
: stops-at ( k n -- flag ) swap lf-tactic-fuel! steps nrun drop err 2drop 91 = ;
: col-of ( k -- col ) 7 * 43 + ;
: at-step? ( k n -- flag ) over swap stops-at swap col-of lfa-error lfa-err-at @ lfa-pos> nip = and ;
: every ( n -- flag ) true over 0 ?do over i swap at-step? and loop nip ;
T{ 10 every -> true }T
T{ 11 lf-tactic-fuel! 10 steps nrun -> outcome-ok }T
T{ lf-tactic-fuel-default 10 steps nrun lf-tactic-fuel-left -> outcome-ok lfr-default-fuel 11 - }T
rfl-action tac-k-rfl lf-tactic-action!

\ ---- 2. Malformed records (checked before any step runs: 92 at end):
\ a stand-in that breaks the record the reader made, then states p.
variable breaker
: broken ( -- type ) breaker @ execute prop-p ;
' broken stating
: kind! ( kind i -- ) lf-tactic-step tac-kind ! ;
: parent! ( p i -- ) lf-tactic-step tac-parent ! ;
: breaks ( xt c-addr u -- code ) rot breaker ! proof nrun drop lf-author-code ;
T{ :noname 0 1 kind! ; s" by-sorry end t" breaks -> 92 }T
T{ :noname 12 1 kind! ; s" by-sorry end t" breaks -> 92 }T
T{ :noname tac-k-by 1 kind! ; s" by-sorry end t" breaks -> 92 }T
T{ :noname 1 1 parent! ; s" by-sorry end t" breaks -> 92 }T
T{ :noname -1 1 parent! ; s" by-sorry end t" breaks -> 92 }T
T{ :noname tac-k-rfl 0 kind! ; s" by-sorry end t" breaks -> 92 }T
T{ :noname 0 0 parent! ; s" by-sorry end t" breaks -> 92 }T
\ An alternative right inside the proof, a step right inside a with, a
\ step inside a rewrite's brackets.
T{ :noname tac-k-alt 1 kind! ; s" by-sorry end t" breaks -> 92 }T
T{ :noname tac-k-sorry 2 kind! ; s" n by-induction-with | zero => by-rfl by-end end t" breaks
   -> 92 }T
T{ :noname 1 2 parent! ; s" by-rw[ ] by-sorry end t" breaks -> 92 }T
T{ :noname 1 2 parent! ; s" by-sorry by-sorry end t" breaks -> 92 }T
\ A parent before its step and a block, but one already closed (review
\ fe1g3 L1): step 4 would be skipped; unbroken, the case step runs (80).
: closed-case ( -- c-addr u ) s" by-case: zero => by-sorry by-end by-sorry by-sorry end t" ;
T{ :noname 1 4 parent! ; closed-case breaks -> 92 }T
T{ :noname 0 2 parent! ; closed-case breaks -> 80 }T
T{ :noname ; closed-case breaks -> 80 }T
\ The record unbroken: the stand-in alone runs.
T{ :noname ; s" by-sorry end t" breaks -> 0 }T
\ A second by in the record where a step is: the check refuses it, and so
\ would its row (run here directly, the step running the last record's).
T{ tac-k-by lfr-row trow-run @ -> ' lfr-misplaced }T
\ A kind with no row (review fe1g3 L2): refused, nothing written.
T{ ' lfr-misplaced 0 ' lf-tactic-action! catch nip nip -> -2 }T
T{ ' lfr-misplaced lfr-kinds 1+ ' lf-tactic-action! catch nip nip -> -2 }T
T{ 1 ' lfr-misplaced catch nip lf-author-code -> lf-author-throw 92 }T

\ ---- 1. The hand-over's refusal: a test tactic that leaves a hole in
\ the value (a natural metavariable of type p): error 74 at end.
: holed ( i -- )
  drop lf-tac-main dup lf-mvar-type drop mv-natural lf-mvar-new made lf-mvar-assign made
  0 lf-replace-main made ;
' holed tac-k-rfl lf-tactic-action!
' prop-p stating
T{ s" by-rfl end t" proof nrun err -> outcome-invalid 74 1 50 }T
rfl-action tac-k-rfl lf-tactic-action!

\ ---- 3. Blocks, focus and done, through a stand-in case action (as
\ FE1g-5 will run by-case:): the main goal focused, a block whose end
\ is closeUsingOrAdmit at its =>.
: case-step ( i -- ) lf-tac-focus lf-tac-block ;
' case-step tac-k-case lf-tactic-action!
T{ s" by-case: zero => by-sorry by-end end t" proof nrun -> outcome-ok }T
\ The block ends with its goal open: 89 at =>, with the goal.
' skip-step tac-k-rfl lf-tactic-action!
T{ s" by-case: zero => by-rfl by-end end t" proof nrun err -> outcome-invalid 89 1 57 }T
T{ token s" =>" compare detail s\" p : Prop\n⊢ p" compare -> 0 0 }T
\ After the block, no goal for the next step: 90.
T{ s" by-case: zero => by-sorry by-end by-sorry end t" proof nrun err
   -> outcome-invalid 90 1 76 }T
\ 1,000 nested blocks, one a line: frames on the heap, no host recursion.
text0 s\" theorem t Nat explicit: n 0 n + n =\n:= by\n" text+
: cases ( n -- ) 0 ?do s\" by-case: a =>\n" text+ loop ;
: ends ( n -- ) 0 ?do s\" by-end\n" text+ loop ;
1000 cases s\" by-sorry\n" text+ 1000 ends s" end t" text+
T{ text$ nrun lf-tactic-count -> outcome-ok 1002 }T
' lf-tac-later 5 tac-k-case lfr-set
rfl-action tac-k-rfl lf-tactic-action!

\ ---- 3. The words directly, on a proof state made by hand: goals g1 g2
\ of type p in a view with p : Prop.
: fresh-state ( -- ) lf-author-begin lf-mctx-reset lf-lctx-reset lf-pst-reset lfr-fresh ;
variable g1  variable g2  variable pp
: two-goals ( -- )
  fresh-state 0 sort s" p" binder pp !
  pp @ 0 lf-mctx-view lf-goal-new made g1 !  pp @ 0 lf-mctx-view lf-goal-new made g2 !
  g1 @ lf-pst-open made  0 g2 @ run-push made lf-goals-append made ;
: goals@ ( -- g... n ) lf-goals dup run-count >r r@ 0 ?do dup i run@ swap loop drop r> ;
T{ two-goals goals@ -> g1 @ g2 @ 2 }T
\ focus: the first unsolved goal alone, the rest given back; unfocus puts
\ the unsolved ones before the rest.
variable rest
T{ lf-tac-focus rest ! goals@ rest @ run-count rest @ 0 run@ -> g1 @ 1 1 g2 @ }T
\ (An assignment checks no type, only the occurs check: g1 := p will do.)
T{ g1 @ pp @ lf-mvar-assign rest @ lf-tac-unfocus goals@ -> outcome-ok g2 @ 1 }T
T{ two-goals lf-tac-focus lf-tac-unfocus goals@ -> g1 @ g2 @ 2 }T
\ focus with no goal: 90 (at the current token: no step runs).
T{ fresh-state 0 lf-goals! ' lf-tac-focus catch lf-author-code
   -> outcome-ok lf-author-throw 90 }T

\ ---- 6. Saved states: a failed attempt leaves no assignment, tag, kind
\ or goal behind; a successful one keeps its changes; a Forth THROW that
\ is no authoring error passes on, the state given back.
: tagged ( -- ) s" zz" lfa-intern ;
: spoil ( -- )
  g1 @ g2 @ lf-mvar-assign made g2 @ tagged lf-mvar-tag! made
  g2 @ mv-natural lf-mvar-kind! made 0 lf-goals! made ;
: spoil-fail ( -- ) spoil lfa-e-tac-unsolved lfa-fail ;
: spoil-throw ( -- ) spoil -77 throw ;
: state? ( -- f1 f2 f3 n ) g1 @ lf-goal-assigned? g2 @ lf-mvar-tag drop
  g2 @ lf-mvar-kind drop lf-goals run-count ;
T{ two-goals state? -> false 0 mv-opaque 2 }T
T{ ' spoil-fail lf-tac-try lf-author-code -> lf-author-throw 89 }T
T{ state? lfr-saves -> false 0 mv-opaque 2 0 }T
T{ lf-tac-forget lf-author-code -> 0 }T
T{ two-goals ' spoil-throw ' lf-tac-try catch nip -> -77 }T
T{ state? lfr-saves -> false 0 mv-opaque 2 0 }T
T{ ' spoil lf-tac-try state? -> 0 true tagged mv-natural 0 }T
\ Nested: an inner failure undone, the outer success kept.
: inner ( -- ) ['] spoil-fail lf-tac-try drop lf-tac-forget ;
T{ two-goals ' inner lf-tac-try state? -> 0 false 0 mv-opaque 2 }T
\ Saves are last in, first out; another is refused, nothing changed.
variable s1  variable s2
T{ two-goals lf-tac-save swap s1 ! lf-tac-save swap s2 ! -> outcome-ok outcome-ok }T
T{ s1 @ lf-tac-restore s1 @ lf-tac-commit -1 lf-tac-restore -> outcome-invalid outcome-invalid
   outcome-invalid }T
T{ s2 @ lf-tac-commit s1 @ lf-tac-restore lfr-saves -> outcome-ok outcome-ok 0 }T
\ Open parts and blocks made in a failed attempt are dropped.
: part-fail ( -- ) 1 trun-parts slab-claim 2drop 5 trun-text slab-claim 2drop
  0 0 lf-tac-block lfa-e-tac-unsolved lfa-fail ;
T{ two-goals lf-open-parts lfr-depth ' part-fail lf-tac-try drop lf-open-parts lfr-depth
   -> 0 0 0 0 }T
\ No room for a second save (the slab limited to one): full, its mark
\ given back, the first save still open; a try then stops the run full.
: must-be-ok ( outcome -- ) ok? 0= abort" not ok" ;
: saves-most ( n -- ) trun-saves dup slab-free /tsv -rot slab-init must-be-ok ;
T{ two-goals 1 saves-most lf-tac-save nip lf-tac-save lfr-saves lf-mctx-marks
   -> outcome-ok -1 outcome-full 1 1 }T
T{ ' spoil ' lf-tac-try catch nip lf-author-code -> lf-author-throw 88 }T
T{ 0 lf-tac-commit lf-tac-forget max-n /tsv / saves-most lfr-saves -> outcome-ok 0 }T

\ ---- 6. The printer's sink and options put back when the printing
\ throws (review fe1g3 L10).
2variable settings
: throws ( x -- outcome ) drop -78 throw ;
T{ lf-print-settings settings 2! 0 ' throws ' 2drop ' lfr-printed catch nip nip nip -> -78 }T
T{ lf-print-settings settings 2@ d= -> true }T

\ ---- 5. Room for an open part's text or an error's detail used up (a
\ slab limited as saves-most limits trun-saves): the open part cut stops
\ the run full (88); the detail cut is noted and said.
: chars-most ( n slab -- ) dup slab-free 1 chars -rot slab-init must-be-ok ;
' prop-p stating
T{ 4 trun-text chars-most s" by-sorry end t" proof nrun err -> outcome-full 88 1 43 }T
T{ max-n trun-text chars-most -> }T
' zero-add stating
T{ 4 lfa-detail chars-most s" end t" proof nrun err cut? -> outcome-invalid 89 1 40 true }T
[defined] >string-execute [if]
T{ printed s" (the rest could not be shown)" search nip nip -> true }T
[then]
T{ max-n lfa-detail chars-most -> }T

\ ---- 5. The heap refusing each allocation of a by-sorry run in turn:
\ never accepted, a stated outcome each time, no block kept by the
\ failure; past the last one, made.
' prop-p stating
: sorry-text ( -- c-addr u ) s" by-sorry end t" proof ;
: refused-at ( k -- outcome ) sorry-text 2>r heap-refusals ! 2r> nrun 0 heap-refusals ! ;
variable worst
: refusal-ok? ( outcome -- flag ) dup ok? swap outcome-full = or ;
: each-refused ( -- k )
  0 begin 1+ dup refused-at dup refusal-ok? 0= if dup worst ! then ok? until ;
T{ outcome-ok worst ! each-refused 1 > worst @ -> true outcome-ok }T

\ ---- 4. Through the command line: the path of every text.
: tally ( k -- n ) cli-count-of @ ;
: check ( c-addr u -- code ) cli-options library cli-state opt-env 2! cli-check ;
' lfr-unelaborated stating
T{ s" tests/front/05-unsolved.lf" check lf-author-code -> 2 71 }T
T{ s" tests/front/06-sorry.lf" check lf-author-code -> 2 71 }T
' zero-add stating
T{ s" tests/front/05-unsolved.lf" check err -> 4 89 14 4 }T
T{ detail lean-goals compare -> 0 }T
T{ s" tests/front/06-sorry.lf" check outcome-ok tally cli-not-proved @ lf-open-parts -> 0 49 2 1 }T
\ The stand-in p : Prop: the kernel accepts the term, NOT PROVED, sorryAx
\ named; the open part outlives the stores the run emptied.
\ The slice's 48 declarations and the text's are accepted; NOT PROVED are
\ the axiom sorryAx itself and zero_add_sorry, which depends on it.
' prop-p stating
T{ s" tests/front/06-sorry.lf" check outcome-ok tally cli-not-proved @ -> 0 49 2 }T
T{ lf-open-parts 0 part-name s" zero_add_sorry" compare 0 part top-at @ lfa-pos> -> 1 0 17 3 }T
\ The same again in the same process: the same verdicts.
T{ s" tests/front/06-sorry.lf" check outcome-ok tally cli-not-proved @ lf-open-parts
   -> 0 49 2 1 }T
\ A front-end fault that closes the goal with a wrong term (Bool.false,
\ not a proof of p) reaches the kernel, which rejects it (exit 1).
: wrong-close ( i -- )
  drop lf-tac-main s" Bool.false" 0 cst lf-mvar-assign made 0 lf-replace-main made ;
' wrong-close tac-k-sorry lf-tactic-action!
T{ s" tests/front/06-sorry.lf" check outcome-rejected tally outcome-ok tally -> 1 1 48 }T
' lfr-sorry tac-k-sorry lf-tactic-action!
' lfr-unelaborated stating
T{ lfc-library-close -> }T
T{ depth -> 0 }T
cr .( tactic-run.fs: all tests passed) cr
bye
