\ Unit tests of case patterns, slice E2a (plan row TB2, piece E; design
\ docs/design/TACTIC_PATTERNS.md) over decide's slice of Init in an
\ authoring run.
require ../../../support/tester.fs
include ../../../support/heap-watch.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/decide-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/decide-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" batch-h test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
lf-meta-throw-base outcome-rejected - constant thrown-rejected
: authored ( code -- n ) dup lf-author-throw = if drop lf-author-code lf-tac-forget then ;
: code2 ( x y xt -- code ) catch dup if nip nip then authored ;
: code3 ( x y z xt -- code ) catch dup if >r 2drop drop r> then authored ;
: code4 ( w x y z xt -- code ) catch dup if >r 2drop 2drop r> then authored ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: local+ ( type c-addr u flags -- fvar )
  >r lfa-intern swap lf-lctx-local made tuck swap r> lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: binder ( type c-addr u -- fvar ) 0 local+ ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: nm ( c-addr u -- name ) lfa-intern ;
: run1 ( x -- run ) 0 swap lf-run+ ;
: view# ( goal -- n ) lf-goal-view lf-view-count ;
: local-at ( goal i -- local ) swap lf-goal-view swap lf-view-local ;
: named? ( goal i c-addr u -- flag ) 2>r local-at lf-local-name 2r> nm lf-name-same? ;
: hidden? ( goal i -- flag ) local-at lf-local-inaccessible? ;
: open? ( goal -- flag ) lf-goal-assigned? 0= ;
: eqv? ( a b -- flag ) lf-meta-eqv made ;

fresh
nat s" a" binder constant fa
nat s" b" binder constant fb
fa fb lf-mk-eq s" h" binder constant fh
fb fa lf-mk-eq s" k" binder constant fk
fa fb lf-mk-eq goal constant g1
T{ g1 fh 0 lf-subst-symm lf-subst-skip or lf-goal-subst-core open? swap run-count -> true 3 }T
.( batch-h test.fs: all tests passed) cr
