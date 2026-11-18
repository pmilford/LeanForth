\ Unit tests of the goal layer's assumption (slice a2-iii;
\ src/front/meta-tactic/assumption.fs) over the S2 slice in an authoring
\ run, for what the .lf files of check.py cannot write (an implementation
\ detail in the context), by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md: 1. outcomes: the newest local
\ that fits, an implementation detail passed over though it fits, none
\ fits (error 381, thrown with no step running), an empty context;
\ 2. malformed input: an assigned goal (a fault, invalid); 3. stack
\ effects (each T{ }T checks the depth); 7. regression pins: the free
\ variable chosen (Lean's findDeclRevM? order).
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
require ../../../../src/main.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/s2-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" assumption test: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
\ A local of the type, named and of the flags given, pushed on the view.
: local ( type c-addr u flags -- fvar )
  >r lfa-intern swap lf-lctx-local made tuck swap r> lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: closes ( goal -- e ) dup lf-goal-assumption lf-instantiate! ;
: code1 ( x xt -- code ) catch dup if nip then ;
: le ( a b -- t ) >r >r s" LE.le" 0 lf-mk-const1 nat lf-mk-app s" instLENat" lf-mk-const0
  lf-mk-app r> lf-mk-app r> lf-mk-app ;

\ No local at all: error 381.
T{ nat goal ' lf-goal-assumption code1 lf-author-code -> lf-author-throw 381 }T
lf-tac-forget
nat s" a" 0 local constant fa
nat s" b" 0 local constant fb
fa fb le s" h1" 0 local constant h1
fa fb le s" h2" 0 local constant h2
\ The newest that fits: h2; for a goal Nat, b (isDefEq Nat (a ≤ b) is
\ false for h2 and h1, as Lean's).
T{ fa fb le goal closes h2 = -> true }T
T{ nat goal closes fb = -> true }T
\ An implementation detail (Lean's auxDecl) newer than h2 is passed over.
fa fb le s" aux" lf-local-aux-decl local constant aux
T{ fa fb le goal closes h2 = -> true }T
\ None fits: fb ≤ fa (error 381), nothing assigned.
T{ fb fa le goal dup ' lf-goal-assumption code1 lf-author-code rot lf-goal-assigned?
   -> lf-author-throw 381 false }T
lf-tac-forget
\ An assigned goal is a fault (checkNotAssigned): invalid.
: solved ( -- goal ) nat goal dup fa lf-mvar-assign made ;
T{ solved ' lf-goal-assumption code1 -> -4201 }T
.( assumption test.fs: all tests passed) cr
bye
