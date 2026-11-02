\ Test-only reconstruction of tests/reference/constant-application-oracle.lean.
\ All metadata, the universe context, and every result below are unchecked
\ assumptions or untrusted diagnostics. No declaration or proof is accepted.
\ This deliberately calls the existing operations separately, not an adapter.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/legacy/raw-declaration-index.fs
include ../../src/core/level-substitute.fs
include ../../src/legacy/term-level-substitute.fs
include ../../src/legacy/raw-signature-specialize.fs
include ../../src/legacy/constant-signature-probe.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/legacy/constant-term-type-probe.fs
include ../../src/legacy/tagged-shift.fs
include ../../src/legacy/tagged-instantiate.fs
include ../../src/legacy/tagged-compare.fs
include ../../src/legacy/tagged-beta.fs
include ../../src/core/level-value.fs
include ../../src/core/level-compare.fs
include ../../src/legacy/tagged-convert.fs
include ../../src/legacy/tagged-infer.fs

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

\ The constant-root probe specializes only the unchecked candidate signature.
token constant-root constant-root-id budget budget lf-cttype-probe
lf-rspec-ok = require-ok
constant specialized-id constant specialized
T{ specialized specialized-id lf-hterm-valid? -> true }T
specialized lf-term-read require-ok
constant body constant domain
lf-tag-pi = require-ok
T{ domain lf-term-read -> lf-tag-symbolic-sort one 0 true }T

\ Lean's valid argument is Prop = Sort 0. Infer its type and compare it with
\ the specialized Pi domain before substituting into the Pi body.
0 sort-node constant prop
prop handle budget lf-tinfer lf-tinfer-ok = require-ok
constant prop-type-id constant prop-type
prop-type lf-term-read require-ok constant prop-type-unused constant prop-type-level
lf-tag-symbolic-sort = require-ok
T{ prop-type-unused -> 0 }T
T{ prop-type-level lf-level-read -> lf-level-tag-succ 0 0 true }T
T{ prop-type prop-type-id domain handle budget lf-tagged-convert
   -> lf-tconvert-equal }T
body handle prop handle budget lf-tagged-instantiate
lf-tinst-ok = require-ok
constant result-id constant result
prop prop lf-term-pi node constant expected
T{ result result-id expected handle budget lf-tagged-convert
   -> lf-tconvert-equal }T
\ Independently inspect the returned syntax: Pi (x : Prop), Prop.
T{ result lf-term-read -> lf-tag-pi prop prop true }T

\ Lean's wrong argument is Sort 2, whose inferred type is Sort 3. The
\ conservative converter reports unknown for the different sorts; this is not
\ a proof of inequality. In particular, do not instantiate after this result.
two sort-node constant wrong
wrong handle budget lf-tinfer lf-tinfer-ok = require-ok
constant wrong-type-id constant wrong-type
wrong-type lf-term-read require-ok constant wrong-type-unused constant wrong-type-level
lf-tag-symbolic-sort = require-ok
T{ wrong-type-unused -> 0 }T
T{ wrong-type-level lf-level-read -> lf-level-tag-succ two 0 true }T
T{ wrong-type wrong-type-id domain handle budget lf-tagged-convert
   -> lf-tconvert-unknown }T
bye
