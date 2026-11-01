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

\ These cases reconstruct the positive and negative Lean oracle inputs. The
\ result is conditional on the unchecked candidate, never a theorem receipt.
0 sort-node constant prop
two sort-node constant wrong
prop prop lf-term-pi node constant expected
variable before-terms
variable before-levels
: snapshot ( -- ) lf-term-count @ before-terms ! lf-level-count @ before-levels ! ;
: unchanged ( -- )
  lf-term-count @ before-terms @ = require-ok
  lf-level-count @ before-levels @ = require-ok ;
: probe ( arg id -- result id status )
  >r >r token constant-root constant-root-id r> r> lf-constant-application-probe ;
prop handle probe lf-caprobe-ok = require-ok
constant result-id constant result
T{ result result-id expected handle budget lf-tagged-convert -> lf-tconvert-equal }T
T{ result lf-term-read -> lf-tag-pi prop prop true }T
snapshot
T{ wrong handle probe -> -1 0 lf-caprobe-unknown }T unchanged
snapshot
T{ prop 0 probe -> -1 0 lf-caprobe-invalid }T unchanged
snapshot
T{ token constant-root 0 prop handle lf-constant-application-probe
   -> -1 0 lf-caprobe-invalid }T unchanged
snapshot
T{ constant-root constant-root-id probe -> -1 0 lf-caprobe-invalid }T unchanged
constant-root prop lf-term-app node constant nested-constant
T{ nested-constant handle budget lf-cterm-check -> lf-repr-ok }T
snapshot
T{ nested-constant handle probe -> -1 0 lf-caprobe-invalid }T unchanged
snapshot
T{ b0 handle probe -> -1 0 lf-caprobe-invalid }T unchanged
snapshot
T{ 0 constant-root constant-root-id prop handle lf-constant-application-probe
   -> -1 0 lf-caprobe-invalid }T unchanged
0 s" Missing" lf-name-str node constant missing-name
missing-name lf-name-generation @ actuals 1 lf-cref-new require-ok
lf-cterm-new require-ok constant missing-id constant missing-root
snapshot
T{ token missing-root missing-id prop handle lf-constant-application-probe
   -> -1 0 lf-caprobe-unknown }T unchanged
identity-name lf-name-generation @ actuals 0 lf-cref-new require-ok
lf-cterm-new require-ok constant arity-id constant arity-root
snapshot
T{ token arity-root arity-id prop handle lf-constant-application-probe
   -> -1 0 lf-caprobe-invalid }T unchanged
\ Reproduction: an unchecked Pi with an escaping body variable must not
\ produce a conditional application result, even if its domain matches.
0 s" OpenCandidate" lf-name-str node constant open-name
one sort-node constant sort-one
sort-one b1 lf-term-pi node constant open-candidate
T{ open-name open-candidate handle budget lf-rawdecl-put -> lf-rawdecl-ok }T
T{ token open-name open-candidate handle formals 0 budget lf-rspec-put
   -> lf-rspec-ok }T
open-name lf-name-generation @ actuals 0 lf-cref-new require-ok
lf-cterm-new require-ok constant open-id constant open-root
snapshot
T{ 12345 token open-root open-id prop handle lf-constant-application-probe
   -> 12345 -1 0 lf-caprobe-invalid }T unchanged
\ The closed-scope walk has an independent budget and visits a shared node
\ separately in each binding context.
T{ candidate-type 0 lf-caprobe-closed -> lf-caprobe-exhausted }T
T{ candidate-type 1 lf-caprobe-closed -> lf-caprobe-exhausted }T
T{ open-candidate budget lf-caprobe-closed -> lf-caprobe-invalid }T
T{ candidate-type budget lf-caprobe-closed -> lf-caprobe-ok }T
\ The same variable is bound in the lambda body but free as the argument.
sort-one b0 lf-term-lam node constant bound-use
bound-use b0 lf-term-app node constant mixed-use
T{ mixed-use budget lf-caprobe-closed -> lf-caprobe-invalid }T
b0 bound-use lf-term-app node constant mixed-reversed
T{ mixed-reversed budget lf-caprobe-closed -> lf-caprobe-invalid }T
T{ 12345 constant-root constant-root-id probe
   -> 12345 -1 0 lf-caprobe-invalid }T
T{ 12345 wrong handle probe -> 12345 -1 0 lf-caprobe-unknown }T
T{ 12345 prop handle probe nip nip -> 12345 lf-caprobe-ok }T
\ Force failure after candidate specialization has allocated, with space for
\ some but not all further terms. Identities of rolled-back terms must not be
\ reused. Restore only the test's own filler suffix afterwards.
lf-term-count @ constant filler-start
: fill-arena ( -- )
  begin lf-term-count @ lf-term-capacity 2 - < while
    0 lf-term-bvar node drop
  repeat ;
fill-arena
snapshot
lf-term-serial @ constant serial-before
T{ 12345 prop handle probe -> 12345 -1 0 lf-caprobe-exhausted }T unchanged
T{ lf-term-serial @ serial-before > -> true }T
lf-term-count @ constant reused-index
reused-index cells lf-term-identities + @ constant rolled-back-id
0 lf-term-bvar node constant replacement
T{ replacement -> reused-index }T
T{ replacement lf-term-identity -> lf-term-serial @ true }T
T{ replacement rolled-back-id lf-hterm-valid? -> false }T
T{ lf-term-serial @ serial-before 1+ > -> true }T
filler-start lf-term-count !
bye
