\ Mixed syntax scope checks do not resolve or validate declarations.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/constant-term-scope.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../support/store-faults.fs

variable const-id
variable sort-id
variable var-id
variable app-id
variable lambda-id
variable saved-child
variable saved-sort-stamp
lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-name-generation @ 0 0 lf-cref-new -> 0 lf-cref-serial @ true }T
T{ 0 lf-cref-serial @ lf-cterm-new -> 0 term-serial true }T
term-serial const-id !
T{ 0 0 level-identity@ lf-hterm-sort -> 1 term-serial true }T
term-serial sort-id !
T{ 0 lf-hterm-bvar -> 2 term-serial true }T
term-serial var-id !
T{ 0 const-id @ 2 var-id @ lf-hterm-app -> 3 term-serial true }T
term-serial app-id !
T{ 1 sort-id @ 3 app-id @ lf-hterm-lam -> 4 term-serial true }T
term-serial lambda-id !
T{ 0 const-id @ 0 100 lf-constant-term-scope -> outcome-ok }T
T{ 2 var-id @ 0 100 lf-constant-term-scope -> outcome-invalid }T
T{ 2 var-id @ 1 100 lf-constant-term-scope -> outcome-ok }T
T{ 4 lambda-id @ 0 100 lf-constant-term-scope -> outcome-ok }T
\ Fuel left, which kernel passes continue with: what remains after the
\ structural audit when the root's data word shows the scope (no walk:
\ compact-store plan step S6 (c), before 89, 0 and exhausted), zero on
\ exhaustion of either pass (the scope walk runs only for a root that
\ fails), the given fuel when validation or the depth fails, two visits
\ used when only the scope pass fails, and unchanged for negative fuel.
T{ 4 lambda-id @ 0 100 lf-constant-term-scope lf-cts-fuel @ -> outcome-ok 94 }T
T{ 2 var-id @ 1 2 lf-constant-term-scope lf-cts-fuel @ -> outcome-ok 1 }T
T{ 2 var-id @ 1 1 lf-constant-term-scope lf-cts-fuel @ -> outcome-ok 0 }T
T{ 2 var-id @ 1 0 lf-constant-term-scope lf-cts-fuel @ -> outcome-exhausted 0 }T
T{ 2 var-id @ 0 1 lf-constant-term-scope lf-cts-fuel @ -> outcome-exhausted 0 }T
T{ 2 var-id @ -1 30 lf-constant-term-scope lf-cts-fuel @ -> outcome-invalid 30 }T
T{ 2 var-id @ 0 30 lf-constant-term-scope lf-cts-fuel @ -> outcome-invalid 28 }T
T{ 4 lambda-id @ 1+ 0 40 lf-constant-term-scope lf-cts-fuel @ -> outcome-invalid 40 }T
T{ 2 var-id @ 1 -1 lf-constant-term-scope lf-cts-fuel @ -> outcome-invalid 40 }T
\ Sharing a bound variable outside the lambda must fail regardless of order.
T{ 4 lambda-id @ 2 var-id @ lf-hterm-app -> 5 term-serial true }T
T{ 5 term-serial 0 100 lf-constant-term-scope -> outcome-invalid }T
T{ 2 var-id @ 4 lambda-id @ lf-hterm-app -> 6 term-serial true }T
T{ 6 term-serial 0 100 lf-constant-term-scope -> outcome-invalid }T
\ A variable in a binder's domain is not bound by that same binder.
T{ 2 var-id @ 0 const-id @ lf-hterm-lam -> 7 term-serial true }T
variable domain-lambda-id
term-serial domain-lambda-id !
T{ 7 domain-lambda-id @ 0 100 lf-constant-term-scope -> outcome-invalid }T
T{ 7 domain-lambda-id @ 1 100 lf-constant-term-scope -> outcome-ok }T
T{ 2 var-id @ 0 const-id @ lf-hterm-pi -> 8 term-serial true }T
T{ 8 term-serial 0 100 lf-constant-term-scope -> outcome-invalid }T
T{ 8 term-serial 1 100 lf-constant-term-scope -> outcome-ok }T
\ The Pi body does bind #0 when its domain is closed.
T{ 1 sort-id @ 2 var-id @ lf-hterm-pi -> 9 term-serial true }T
T{ 9 term-serial 0 100 lf-constant-term-scope -> outcome-ok }T
\ A shared constant is visited twice by the structural pass (the second
\ visit costs its unit only); the data word shows the scope, so no scope
\ pass runs (before plan step S6 (c) it visited both, 6 in all).
T{ 0 const-id @ 0 const-id @ lf-hterm-app -> 10 term-serial true }T
T{ 10 term-serial 0 2 lf-constant-term-scope -> outcome-exhausted }T
T{ 10 term-serial 0 3 lf-constant-term-scope -> outcome-ok }T
\ A single variable costs one structural visit (and one scope visit only
\ out of scope, above).
T{ 2 var-id @ 1 0 lf-constant-term-scope -> outcome-exhausted }T
T{ 2 var-id @ 1 1 lf-constant-term-scope -> outcome-ok }T
T{ 2 var-id @ lf-walk-room 2 lf-constant-term-scope -> outcome-ok }T
T{ 2 var-id @ 1 -1 lf-constant-term-scope -> outcome-invalid }T
\ Malformed edges and stale Sort stamps fail before scope is accepted.
5 lf-term-first@ saved-child !
5 5 term-first!
T{ 5 5 lf-term-identity drop 0 100 lf-constant-term-scope -> outcome-invalid }T
saved-child @ 5 term-first!
1 lf-hsort-level-stamp @ saved-sort-stamp !
0 1 lf-hsort-level-stamp !
T{ 4 lambda-id @ 0 100 lf-constant-term-scope -> outcome-invalid }T
saved-sort-stamp @ 1 lf-hsort-level-stamp !
T{ lf-term-count @ lf-level-count @ -> 11 1 }T
T{ 4 lambda-id @ -1 100 lf-constant-term-scope -> outcome-invalid }T
\ Any nonnegative outer depth is taken (plan task 6.2.0), max-n too: the
\ lambda's data word shows its scope, so no binder is entered (before plan
\ step S6 (c) the walk could not enter it there: full; the walk's full
\ binder depth is pinned below, on lf-cts-binary).
T{ 4 lambda-id @ lf-walk-room 1+ 100 lf-constant-term-scope -> outcome-ok }T
T{ 4 lambda-id @ max-n 100 lf-constant-term-scope -> outcome-ok }T
T{ 4 lambda-id @ 0 0 lf-constant-term-scope -> outcome-exhausted }T
T{ 4 lambda-id @ 0 100 ' lf-constant-term-scope rs-checked -> outcome-ok }T
T{ 4 lambda-id @ 1+ 0 100 lf-constant-term-scope -> outcome-invalid }T
\ Reuse the referenced slot: the original constant must remain stale.
lf-cref-reset
T{ 0 lf-name-generation @ 0 0 lf-cref-new -> 0 lf-cref-serial @ true }T
T{ 0 const-id @ 0 100 lf-constant-term-scope -> outcome-invalid }T
\ A binder at depth max-n cannot put its body one level deeper, which is
\ full and pushes nothing; an application does not deepen and is pushed.
\ Unreachable through lf-constant-term-scope (the outer depth is at most
\ lf-term-capacity), so the visit is driven white-box.
0 lf-cts-walker walk-pending !  max-n lf-cts-walker walk-context !
: pending ( -- n ) lf-cts-walker walk-pending @ ;
T{ 0 0 lf-cts-walker lf-tag-lam lf-cts-binary pending -> outcome-full 0 }T
T{ 0 0 lf-cts-walker lf-tag-app lf-cts-binary pending -> outcome-ok 4 }T
\ The depth check is independent of fuel (ADR 0008): a visit that took the
\ last unit still finds the binder full.
0 lf-cts-walker walk-pending !  0 lf-cts-walker walk-fuel !
T{ 0 0 lf-cts-walker lf-tag-pi lf-cts-binary pending lf-cts-fuel @ -> outcome-full 0 0 }T
bye
