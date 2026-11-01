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
one actuals ! one lf-level-identity require-ok actuals cell+ !
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

\ Two closed arguments: Prop and the proposition forall P : Prop, P -> P.
create spine-args 4 cells allot
0 sort-node constant prop
b0 b1 lf-term-pi node constant proof-body
prop proof-body lf-term-pi node constant proposition
prop spine-args ! prop lf-term-identity require-ok spine-args cell+ !
proposition spine-args 2 cells + !
proposition lf-term-identity require-ok spine-args 3 cells + !
prop prop lf-term-pi node constant expected
token constant-root constant-root-id spine-args 0 lf-constant-spine-probe
lf-caprobe-ok = require-ok 2drop
 token constant-root constant-root-id spine-args 1 lf-constant-spine-probe
lf-caprobe-ok = require-ok
expected handle budget lf-tagged-convert lf-tconvert-equal = require-ok
 token constant-root constant-root-id spine-args 2 lf-constant-spine-probe
lf-caprobe-ok = require-ok
prop handle budget lf-tagged-convert lf-tconvert-equal = require-ok
\ A separate unchecked signature has a result depending on its second
\ argument: forall (_ : Sort 1), forall (P : Prop), P. This checks that the
\ exact argument term, not its inferred type, is substituted into the result.
0 s" DependsOnSecond" lf-name-str node constant dependent-name
one sort-node constant sort-one
prop b0 lf-term-pi node constant dependent-inner
sort-one dependent-inner lf-term-pi node constant dependent-type
T{ dependent-name dependent-type handle budget lf-rawdecl-put -> lf-rawdecl-ok }T
T{ token dependent-name dependent-type handle formals 0 budget lf-rspec-put
   -> lf-rspec-ok }T
dependent-name lf-name-generation @ actuals 0 lf-cref-new require-ok
lf-cterm-new require-ok constant dependent-id constant dependent-root
token dependent-root dependent-id spine-args 2 lf-constant-spine-probe
lf-caprobe-ok = require-ok
proposition handle budget lf-tagged-compare lf-tcompare-equal = require-ok
\ A later type mismatch is unknown and rolls back the first application's
\ allocations. It must not issue a result or disturb the caller's prefix.
two sort-node constant wrong
wrong spine-args 2 cells + !
wrong lf-term-identity require-ok spine-args 3 cells + !
lf-term-count @ constant mismatch-terms
lf-level-count @ constant mismatch-levels
lf-term-serial @ constant mismatch-serial
T{ 888 token constant-root constant-root-id spine-args 2 lf-constant-spine-probe
   -> 888 -1 0 lf-caprobe-unknown }T
T{ lf-term-count @ lf-level-count @ -> mismatch-terms mismatch-levels }T
T{ lf-term-serial @ mismatch-serial > -> true }T
\ The rolled-back slot cannot revive its former allocation identity.
mismatch-terms cells lf-term-identities + @ constant discarded-id
0 lf-term-bvar node constant replacement
T{ replacement -> mismatch-terms }T
T{ replacement discarded-id lf-hterm-valid? -> false }T
proposition spine-args 2 cells + !
proposition lf-term-identity require-ok spine-args 3 cells + !
\ Invalid later handle must fail before allocating any intermediate nodes.
lf-term-count @ constant before-terms
lf-level-count @ constant before-levels
lf-term-serial @ constant before-term-serial
lf-level-serial @ constant before-level-serial
0 spine-args 3 cells + !
T{ 777 token constant-root constant-root-id spine-args 2 lf-constant-spine-probe
   -> 777 -1 0 lf-caprobe-invalid }T
T{ lf-term-count @ lf-level-count @ -> before-terms before-levels }T
T{ lf-term-serial @ lf-level-serial @ -> before-term-serial before-level-serial }T
proposition lf-term-identity require-ok spine-args 3 cells + !
T{ token constant-root constant-root-id spine-args -1 lf-constant-spine-probe
   -> -1 0 lf-caprobe-invalid }T
T{ token constant-root constant-root-id spine-args 9 lf-constant-spine-probe
   -> -1 0 lf-caprobe-invalid }T
T{ token constant-root 0 spine-args 0 lf-constant-spine-probe
   -> -1 0 lf-caprobe-invalid }T
T{ token prop prop lf-term-identity drop spine-args 0 lf-constant-spine-probe
   -> -1 0 lf-caprobe-invalid }T
\ A valid constant used as an argument is unsupported by this diagnostic.
constant-root spine-args ! constant-root-id spine-args cell+ !
T{ token constant-root constant-root-id spine-args 1 lf-constant-spine-probe
   -> -1 0 lf-caprobe-invalid }T
prop constant-root lf-term-app node constant nested-constant
nested-constant spine-args !
nested-constant lf-term-identity require-ok spine-args cell+ !
T{ token constant-root constant-root-id spine-args 1 lf-constant-spine-probe
   -> -1 0 lf-caprobe-invalid }T
\ Eight is accepted as a count; this two-binder candidate then becomes
\ unknown when a third argument is requested, rather than failing the bound.
create eight-args 16 cells allot
: fill-eight ( -- )
  8 0 do i 1 = if proposition else prop then
    dup eight-args i 2 * cells + !
    lf-term-identity require-ok eight-args i 2 * 1+ cells + !
  loop ;
fill-eight
T{ token constant-root constant-root-id eight-args 8 lf-constant-spine-probe
   -> -1 0 lf-caprobe-unknown }T
bye
