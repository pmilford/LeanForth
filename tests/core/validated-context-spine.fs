\ Test-only reconstruction of tests/reference/constant-application-oracle.lean.
\ All metadata, the universe context, and every result below are unchecked
\ assumptions or untrusted diagnostics. No declaration or proof is accepted.
\ Exercises the isolated application adapter and its failure boundaries.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs
include ../../src/experimental/raw-declaration-index.fs
include ../../src/experimental/level-substitute.fs
include ../../src/experimental/term-level-substitute.fs
include ../../src/experimental/raw-signature-specialize.fs
include ../../src/experimental/constant-signature-probe.fs
include ../../src/experimental/constant-term-boundary.fs
include ../../src/experimental/constant-term-type-probe.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs
include ../../src/experimental/tagged-compare.fs
include ../../src/experimental/tagged-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/tagged-convert.fs
include ../../src/experimental/tagged-infer.fs
include ../../src/experimental/constant-application-probe.fs
include ../../src/experimental/constant-spine-probe.fs
include ../../src/experimental/tagged-context-infer.fs
include ../../src/experimental/context-constant-spine.fs
include ../../src/experimental/context-validation-probe.fs
include ../../src/experimental/validated-context-spine.fs

decimal
10000 constant budget
create formals 1 cells allot
create actuals 2 cells allot

: require-ok ( flag -- ) 0= abort" fixture or diagnostic failed" ;
: node ( index true | false -- index ) 0= abort" allocation" ;
: handle ( index -- index identity )
  dup lf-term-identity 0= abort" term identity" ;
: sort-node ( level -- index )
  dup lf-level-identity 0= abort" level identity"
  lf-hterm-sort 0= abort" sort allocation" drop ;

lf-name-reset lf-term-reset lf-level-reset lf-lscope-context-reset lf-cref-reset
0 s" Identity" lf-name-str node constant identity-name
11 lf-lscope-context-add require-ok
11 formals !
11 lf-level-param node constant u
0 lf-level-succ node constant one
one lf-level-succ node constant two
u actuals ! u lf-level-identity require-ok actuals cell+ !
lf-ssession-begin require-ok
lf-rawdecl-begin require-ok

\ Candidate signature: forall (A : Sort u), forall (x : A), A.
\ No value or declaration is checked by these metadata operations.
u sort-node constant sort-u
0 lf-term-bvar node constant b0
1 lf-term-bvar node constant b1
b0 b1 lf-term-pi node constant inner-pi
sort-u inner-pi lf-term-pi node constant candidate-type
T{ identity-name candidate-type handle budget lf-rawdecl-put -> lf-rawdecl-ok }T
T{ lf-rspec-begin -> true }T
lf-rawdecl-token require-ok constant token
T{ token identity-name candidate-type handle formals 1 budget lf-rspec-put
   -> lf-rspec-ok }T
identity-name lf-name-generation @ actuals 1 lf-cref-new
require-ok lf-cterm-new require-ok
constant constant-root-id constant constant-root

\ Context A : Sort u, x : A. Arguments A (#1), x (#0) mirror the
\ body of fixturePoly, conditional on the separately staged signature.
create binder-context 4 cells allot
create arguments 4 cells allot
sort-u binder-context ! sort-u lf-term-identity require-ok binder-context cell+ !
b0 binder-context 2 cells + ! b0 lf-term-identity require-ok binder-context 3 cells + !
b1 arguments ! b1 lf-term-identity require-ok arguments cell+ !
b0 arguments 2 cells + ! b0 lf-term-identity require-ok arguments 3 cells + !
 token constant-root constant-root-id arguments 2 binder-context 2 lf-validated-context-spine
lf-caprobe-ok = require-ok
b1 handle budget lf-tagged-compare lf-tcompare-equal = require-ok
\ After only A is applied, A shifts under the remaining Pi binder: its
\ domain is #1 and body is #2 in the external A,x context.
2 lf-term-bvar node constant b2
b1 b2 lf-term-pi node constant expected-pi
token constant-root constant-root-id arguments 1 binder-context 2 lf-validated-context-spine
lf-caprobe-ok = require-ok
expected-pi handle budget lf-tagged-compare lf-tcompare-equal = require-ok
\ A later mismatch must roll back work performed for the first argument.
: framed-spine ( token root rid args count ctx depth -- result id status marker )
  444 >r lf-validated-context-spine r> ;
b1 arguments 2 cells + ! b1 lf-term-identity require-ok arguments 3 cells + !
lf-term-count @ constant mismatch-terms
lf-level-count @ constant mismatch-levels
lf-term-serial @ constant mismatch-serial
T{ 987 token constant-root constant-root-id arguments 2 binder-context 2 framed-spine
   -> 987 -1 0 lf-caprobe-unknown 444 }T
T{ lf-term-count @ lf-level-count @ -> mismatch-terms mismatch-levels }T
T{ lf-term-serial @ mismatch-serial > -> true }T
mismatch-terms cells lf-term-identities + @ constant discarded-id
0 lf-term-bvar node constant reused-term
T{ reused-term -> mismatch-terms }T
T{ reused-term discarded-id lf-hterm-valid? -> false }T
b0 arguments 2 cells + ! b0 lf-term-identity require-ok arguments 3 cells + !
\ Read-only overlap between caller context and argument arrays is permitted.
\ Here x is not a suitable first type argument, so conversion is unknown.
T{ token constant-root constant-root-id binder-context 2 cells + 1 binder-context 2
   lf-validated-context-spine -> -1 0 lf-caprobe-unknown }T
T{ binder-context @ binder-context 2 cells + @ -> sort-u b0 }T
\ A closed lambda is scoped but its inferred type is a Pi, not a Sort.
\ Context validation cannot accept it as a binder type.
sort-u b0 lf-term-lam node constant not-a-domain
not-a-domain binder-context !
not-a-domain lf-term-identity require-ok binder-context cell+ !
T{ token constant-root constant-root-id arguments 0 binder-context 1
   lf-validated-context-spine -> -1 0 lf-caprobe-unknown }T
sort-u binder-context ! sort-u lf-term-identity require-ok binder-context cell+ !
\ A bad later identity must fail before allocating any new slot.
lf-term-count @ constant terms-before
lf-level-count @ constant levels-before
lf-term-serial @ constant term-serial-before
lf-level-serial @ constant level-serial-before
0 arguments 3 cells + !
T{ 987 token constant-root constant-root-id arguments 2 binder-context 2 lf-validated-context-spine
   -> 987 -1 0 lf-caprobe-invalid }T
T{ lf-term-count @ lf-level-count @ -> terms-before levels-before }T
T{ lf-term-serial @ lf-level-serial @ -> term-serial-before level-serial-before }T
\ A predicted identity for the next unallocated slot must not be revived by
\ context validation allocating before the later argument or root is checked.
terms-before arguments 2 cells + !
term-serial-before 1+ arguments 3 cells + !
T{ token constant-root constant-root-id arguments 2 binder-context 2 lf-validated-context-spine
   -> -1 0 lf-caprobe-invalid }T
T{ token terms-before term-serial-before 1+ arguments 0 binder-context 2 lf-validated-context-spine
   -> -1 0 lf-caprobe-invalid }T
T{ lf-term-serial @ lf-level-serial @ -> term-serial-before level-serial-before }T
b0 arguments 2 cells + !
b0 lf-term-identity require-ok arguments 3 cells + !
\ A variable outside the two-entry binder-context is rejected before allocation.
2 lf-term-bvar node constant free-var
free-var arguments ! free-var lf-term-identity require-ok arguments cell+ !
T{ token constant-root constant-root-id arguments 2 binder-context 2 lf-validated-context-spine
   -> -1 0 lf-caprobe-invalid }T
\ A domain may not depend on a future binder.
b1 binder-context ! b1 lf-term-identity require-ok binder-context cell+ !
T{ token constant-root constant-root-id arguments 0 binder-context 2 lf-validated-context-spine
   -> -1 0 lf-caprobe-invalid }T
T{ token constant-root constant-root-id arguments 0 binder-context -1 lf-validated-context-spine
   -> -1 0 lf-caprobe-invalid }T
T{ token constant-root constant-root-id arguments 9 binder-context 2 lf-validated-context-spine
   -> -1 0 lf-caprobe-invalid }T
\ Inference statuses keep their meaning; other codes are invalid, never ok.
T{ lf-tinfer-ok lf-vcsp-status -> lf-caprobe-ok }T
T{ lf-tinfer-invalid lf-vcsp-status -> lf-caprobe-invalid }T
T{ lf-tinfer-exhausted lf-vcsp-status -> lf-caprobe-exhausted }T
T{ lf-tinfer-unknown lf-vcsp-status -> lf-caprobe-unknown }T
T{ 99 lf-vcsp-status -> lf-caprobe-invalid }T
bye
