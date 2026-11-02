\ Mixed syntax scope checks do not resolve or validate declarations.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/core/constant-term-scope.fs

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
T{ 0 lf-cref-serial @ lf-cterm-new -> 0 lf-term-serial @ true }T
lf-term-serial @ const-id !
T{ 0 lf-level-identities @ lf-hterm-sort -> 1 lf-term-serial @ true }T
lf-term-serial @ sort-id !
T{ 0 lf-hterm-bvar -> 2 lf-term-serial @ true }T
lf-term-serial @ var-id !
T{ 0 const-id @ 2 var-id @ lf-hterm-app -> 3 lf-term-serial @ true }T
lf-term-serial @ app-id !
T{ 1 sort-id @ 3 app-id @ lf-hterm-lam -> 4 lf-term-serial @ true }T
lf-term-serial @ lambda-id !
T{ 0 const-id @ 0 100 lf-constant-term-scope -> lf-repr-ok }T
T{ 2 var-id @ 0 100 lf-constant-term-scope -> lf-repr-invalid }T
T{ 2 var-id @ 1 100 lf-constant-term-scope -> lf-repr-ok }T
T{ 4 lambda-id @ 0 100 lf-constant-term-scope -> lf-repr-ok }T
\ Sharing a bound variable outside the lambda must fail regardless of order.
T{ 4 lambda-id @ 2 var-id @ lf-hterm-app -> 5 lf-term-serial @ true }T
T{ 5 lf-term-serial @ 0 100 lf-constant-term-scope -> lf-repr-invalid }T
T{ 2 var-id @ 4 lambda-id @ lf-hterm-app -> 6 lf-term-serial @ true }T
T{ 6 lf-term-serial @ 0 100 lf-constant-term-scope -> lf-repr-invalid }T
\ A variable in a binder's domain is not bound by that same binder.
T{ 2 var-id @ 0 const-id @ lf-hterm-lam -> 7 lf-term-serial @ true }T
variable domain-lambda-id
lf-term-serial @ domain-lambda-id !
T{ 7 domain-lambda-id @ 0 100 lf-constant-term-scope -> lf-repr-invalid }T
T{ 7 domain-lambda-id @ 1 100 lf-constant-term-scope -> lf-repr-ok }T
T{ 2 var-id @ 0 const-id @ lf-hterm-pi -> 8 lf-term-serial @ true }T
T{ 8 lf-term-serial @ 0 100 lf-constant-term-scope -> lf-repr-invalid }T
T{ 8 lf-term-serial @ 1 100 lf-constant-term-scope -> lf-repr-ok }T
\ The Pi body does bind #0 when its domain is closed.
T{ 1 sort-id @ 2 var-id @ lf-hterm-pi -> 9 lf-term-serial @ true }T
T{ 9 lf-term-serial @ 0 100 lf-constant-term-scope -> lf-repr-ok }T
\ A shared constant is visited twice by both structural and scope passes.
T{ 0 const-id @ 0 const-id @ lf-hterm-app -> 10 lf-term-serial @ true }T
T{ 10 lf-term-serial @ 0 5 lf-constant-term-scope -> lf-repr-exhausted }T
T{ 10 lf-term-serial @ 0 6 lf-constant-term-scope -> lf-repr-ok }T
\ A single variable costs one structural and one scope visit.
T{ 2 var-id @ 1 1 lf-constant-term-scope -> lf-repr-exhausted }T
T{ 2 var-id @ 1 2 lf-constant-term-scope -> lf-repr-ok }T
T{ 2 var-id @ lf-term-capacity 2 lf-constant-term-scope -> lf-repr-ok }T
T{ 2 var-id @ 1 -1 lf-constant-term-scope -> lf-repr-invalid }T
\ Malformed edges and stale Sort stamps fail before scope is accepted.
5 lf-term-slot cell+ @ saved-child !
5 5 lf-term-slot cell+ !
T{ 5 5 lf-term-identity drop 0 100 lf-constant-term-scope -> lf-repr-invalid }T
saved-child @ 5 lf-term-slot cell+ !
1 cells lf-hsort-level-identities + @ saved-sort-stamp !
0 1 cells lf-hsort-level-identities + !
T{ 4 lambda-id @ 0 100 lf-constant-term-scope -> lf-repr-invalid }T
saved-sort-stamp @ 1 cells lf-hsort-level-identities + !
T{ lf-term-count @ lf-level-count @ -> 11 1 }T
T{ 4 lambda-id @ -1 100 lf-constant-term-scope -> lf-repr-invalid }T
T{ 4 lambda-id @ lf-term-capacity 1+ 100 lf-constant-term-scope -> lf-repr-invalid }T
T{ 4 lambda-id @ 0 0 lf-constant-term-scope -> lf-repr-exhausted }T
T{ 4 lambda-id @ 1+ 0 100 lf-constant-term-scope -> lf-repr-invalid }T
\ Reuse the referenced slot: the original constant must remain stale.
lf-cref-reset
T{ 0 lf-name-generation @ 0 0 lf-cref-new -> 0 lf-cref-serial @ true }T
T{ 0 const-id @ 0 100 lf-constant-term-scope -> lf-repr-invalid }T
bye
