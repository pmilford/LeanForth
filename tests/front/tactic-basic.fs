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
  drop dup hyp-node? if hyp-fvar else drop chosen @ then outcome-ok ;
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
T{ va lf-term-second@ lf-term-first@ tag -> lf-tag-fvar }T   \ the domain: p? no: abstracted
