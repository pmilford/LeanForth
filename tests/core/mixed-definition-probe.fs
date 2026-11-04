\ Experimental inference contract tests. Candidate signatures are assumptions;
\ a successful inference is not a checked theorem or declaration.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-definition-probe.fs
require ../../src/kernel/mixed-infer.fs
require ../../src/kernel/mixed-signature-probe.fs

\ Helpers adapted from mixed-convert.fs and mixed-signature-audit.fs.
create ids 64 cells allot
create actuals 2 cells allot
create formals 1 cells allot
variable token variable id-name variable missing-name variable later-name
create nested-args 2 cells allot
variable outer-name variable nested-root variable nested-id
variable outer-root variable outer-id variable generated-ref variable generated-ref-id
variable terms-before variable levels-before variable crefs-before
variable term-serial-before variable level-serial-before variable cref-serial-before
: save ( index identity true | false -- ) 0= abort" fixture allocation" swap cells ids + ! ;
: h ( index -- index identity ) dup cells ids + @ ;
: new-name ( addr len -- id ) 0 -rot lf-name-str 0= abort" name" ;
: snapshot ( -- )
  lf-term-count @ terms-before ! lf-level-count @ levels-before !
  lf-cref-count @ crefs-before ! lf-term-serial @ term-serial-before !
  lf-level-serial @ level-serial-before ! lf-cref-serial @ cref-serial-before ! ;
: counts-unchanged? ( -- flag )
  lf-term-count @ terms-before @ = lf-level-count @ levels-before @ = and
  lf-cref-count @ crefs-before @ = and ;
: serials-unchanged? ( -- flag )
  lf-term-serial @ term-serial-before @ = lf-level-serial @ level-serial-before @ = and
  lf-cref-serial @ cref-serial-before @ = and ;
: infer ( root fuel -- type identity status )
  >r h token @ -rot r> ['] lf-mixed-infer rs-checked ;
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  42 lf-lscope-context-add 0= abort" level context"
  42 lf-level-param 0= abort" level" drop
  lf-ssession-begin 0= abort" session"
  s" fixtureId" new-name id-name ! s" missing" new-name missing-name !
  s" later" new-name later-name !
  1 actuals ! 1 lf-level-identity 0= abort" level identity" actuals cell+ !
  42 formals !
  1 dup lf-level-identity 0= abort" level identity" lf-hterm-sort save \ 0 Sort u
  0 lf-hterm-bvar save                                             \ 1 bvar 0
  1 lf-hterm-bvar save                                             \ 2 bvar 1
  1 h 2 h lf-hterm-pi save                                        \ 3 (x : A) -> A
  0 h 3 h lf-hterm-pi save                                        \ 4 (A : Sort u) -> (x : A) -> A
  id-name @ lf-name-generation @ actuals 1 lf-cref-new 0= abort" cref"
  lf-cterm-new save                                                \ 5 id.{u}
  5 h 2 h lf-hterm-app save                                       \ 6 id A
  6 h 1 h lf-hterm-app save                                       \ 7 id A x
  1 h 7 h lf-hterm-lam save                                       \ 8 fun x : A => id A x
  0 h 8 h lf-hterm-lam save                                       \ 9 fun A : Sort u => ...
  5 h 0 h lf-hterm-app save                                       \ 10 id Sort u (wrong universe)
  missing-name @ lf-name-generation @ actuals 1 lf-cref-new 0= abort" missing cref"
  lf-cterm-new save                                                \ 11 missing constant
  1 h 1 h lf-hterm-lam save                                       \ 12 open domain
  0 h 1 h lf-hterm-lam save                                       \ 13 fun A : Sort u => A
  lf-msp-begin 0= abort" index" lf-msp-token 0= abort" token" token !
  token @ id-name @ 4 h formals 1 50000 lf-msp-put outcome-ok <> abort" id signature"
  token @ later-name @ 0 h formals 1 50000 lf-msp-put outcome-ok <> abort" later signature" ;

: expect-status ( actual expected -- )
  2dup <> if ." expected status " . ." actual " . cr -2 throw then 2drop ;

: probe ( claim value fuel -- status )
  >r >r h token @ -rot r> h r> ['] lf-mixed-definition-probe rs-checked ;
: assert-rollback ( -- ) counts-unchanged? 0= abort" arena counts changed" ;

\ The statuses are the shared outcomes, with the inference statuses' values.
: statuses ( -- ok invalid exhausted unknown )
  outcome-ok outcome-invalid outcome-exhausted outcome-unknown ;
T{ statuses -> outcome-ok outcome-invalid outcome-exhausted outcome-unknown }T
T{ statuses -> outcome-ok outcome-invalid outcome-exhausted outcome-unknown }T
\ The success fuel is pinned: preflight and the pair's inference spend 189
\ units here (observed before the refactor, at 398b76b), 183 since ADR 0011
\ Amendment 1 (structural level equality costs nothing), 169 since free
\ variables (plan task 4.2.2a: a bound variable's type is its entry's, with
\ no shift, and an application's type is instantiated without an audit).
\ The rejections are ADR 0011's, each as Lean's kernel decides: the value
\ id.{u} (Sort u) applies id to an argument of the wrong universe (D1 in
\ the value: appTypeMismatch); a function claimed to be a Sort u (D2:
\ declTypeMismatch); a lambda as the claimed type (S1: typeExpected).
: rejected-code? ( code -- flag ) lf-diag-code@ = ;
: basic-case ( -- )
  setup snapshot 4 9 50000 probe outcome-ok expect-status assert-rollback
  lf-mdefinition-fuel @ 49831 <> abort" success fuel"
  lf-term-serial @ term-serial-before @ <= abort" expected allocations"
  snapshot 0 10 50000 probe outcome-rejected expect-status assert-rollback
  lf-mdefinition-fuel @ 0<> abort" rejected fuel"
  lf-diag-argument-apart rejected-code? 0= abort" D1 in the value"
  snapshot 0 9 50000 probe outcome-rejected expect-status assert-rollback
  lf-diag-value-apart rejected-code? 0= abort" D2 for the value"
  snapshot 0 12 50000 probe outcome-invalid expect-status assert-rollback
  lf-mdefinition-fuel @ 0<> abort" invalid fuel"
  snapshot 9 9 50000 probe outcome-rejected expect-status assert-rollback
  lf-diag-type-expected rejected-code? 0= abort" S1" ;
: stale-case ( -- )
  setup snapshot token @ 4 h 9 h 1+ 50000 lf-mixed-definition-probe
  outcome-invalid expect-status assert-rollback
  serials-unchanged? 0= abort" stale value allocated"
  1 cells lf-msp-ids + dup @ 1+ swap ! snapshot
  4 9 50000 probe outcome-invalid expect-status assert-rollback
  serials-unchanged? 0= abort" stale index allocated" ;
variable other-name variable value-name
: generated-rollback-case ( -- )
  \ Candidate signature is an unchecked nested constant; its specialization
  \ allocates a level, reference and term before comparison returns unknown.
  setup s" outer" new-name outer-name !
  1 dup lf-level-identity 0= abort" parameter" lf-hlevel-succ 0= abort" successor"
  nested-args cell+ ! nested-args !
  id-name @ lf-name-generation @ nested-args 1 lf-cref-new 0= abort" nested ref"
  lf-cterm-new 0= abort" nested term" nested-id ! nested-root !
  token @ outer-name @ nested-root @ nested-id @ formals 1 50000 lf-msp-put
  outcome-ok expect-status
  0 nested-args ! 0 lf-level-identity 0= abort" zero" nested-args cell+ !
  outer-name @ lf-name-generation @ nested-args 1 lf-cref-new 0= abort" outer ref"
  lf-cterm-new save
  lf-term-count @ 1- snapshot 0 swap 50000 probe outcome-unknown expect-status
  assert-rollback lf-mdefinition-fuel @ 0<> abort" unknown fuel"
  lf-term-serial @ term-serial-before @ <= abort" no term allocation"
  lf-level-serial @ level-serial-before @ <= abort" no level allocation"
  lf-cref-serial @ cref-serial-before @ <= abort" no reference allocation" ;
: distinct-case ( -- )
  setup s" other" new-name other-name ! s" value" new-name value-name !
  \ A and B are different constants, each assumed to have type Sort u.
  token @ other-name @ 0 h formals 1 50000 lf-msp-put outcome-ok expect-status
  later-name @ lf-name-generation @ actuals 1 lf-cref-new 0= abort" A cref"
  lf-cterm-new save \ 14 A
  other-name @ lf-name-generation @ actuals 1 lf-cref-new 0= abort" B cref"
  lf-cterm-new save \ 15 B
  \ The value has assumed type B. Comparing B with A is inconclusive.
  token @ value-name @ 15 h formals 1 50000 lf-msp-put outcome-ok expect-status
  value-name @ lf-name-generation @ actuals 1 lf-cref-new 0= abort" value cref"
  lf-cterm-new save \ 16 value
  snapshot 14 16 50000 probe outcome-unknown expect-status assert-rollback ;

\ Assume, unchecked, that a constant has the type at a fixture index.
: assume ( name index -- )
  h 2>r token @ swap 2r> formals 1 50000 lf-msp-put outcome-ok expect-status ;
\ Save a constant term with the given universe arguments as the next fixture.
: reference ( name args count -- )
  2>r lf-name-generation @ 2r> lf-cref-new 0= abort" reference" lf-cterm-new save ;
create two-u-args 4 cells allot
\ Two copies of the universe argument u.
: two-u ( -- args count )
  actuals 2@ two-u-args 2! actuals 2@ two-u-args 2 cells + 2! two-u-args 2 ;
: ill-arity-case ( -- )
  \ B : Sort u and an ill-formed v : B.{u,u} are assumed. The claim B.{u}
  \ differs from v's type only in universe arity, so it is never accepted.
  setup s" B" new-name dup 0 assume dup actuals 1 reference \ 14 B.{u}
  two-u reference                                              \ 15 B.{u,u}
  s" v" new-name dup 15 assume actuals 1 reference           \ 16 v
  snapshot 14 16 50000 probe outcome-unknown expect-status assert-rollback
  lf-mdefinition-fuel @ 0<> abort" unknown fuel" ;
: non-type-case ( -- )
  \ fun (x : fun A => A) => x has a binder domain whose type is not a Sort
  \ (S2: typeExpected); (A : Sort u) -> fun (x : A) => x has such a Pi
  \ body as the claim (S4, ADR 0011 Amendment 2: typeExpected).
  setup 13 h 1 h lf-hterm-lam save 0 h 12 h lf-hterm-pi save \ 14, 15
  snapshot 4 14 50000 probe outcome-rejected expect-status assert-rollback
  lf-diag-domain-type rejected-code? 0= abort" S2"
  snapshot 15 9 50000 probe outcome-rejected expect-status assert-rollback
  lf-diag-body-type rejected-code? 0= abort" S4" ;
: future-handle-case ( -- )
  \ A forged future identity would become live after the first allocation if
  \ the second source or later index record were checked too late.
  setup snapshot token @ 4 h lf-term-count @ lf-term-serial @ 1+ 50000
  lf-mixed-definition-probe outcome-invalid expect-status
  assert-rollback serials-unchanged? 0= abort" future value allocated"
  setup lf-term-count @ 1 cells lf-msp-roots + !
  lf-term-serial @ 1+ 1 cells lf-msp-ids + ! snapshot
  4 9 50000 probe outcome-invalid expect-status
  assert-rollback serials-unchanged? 0= abort" future index allocated" ;
variable saw-exhaustion variable saw-success variable saw-partial
: fuel-case ( -- )
  false saw-exhaustion ! false saw-success ! false saw-partial !
  1200 0 do
    setup snapshot 4 9 i probe
    dup outcome-exhausted = if
      drop true saw-exhaustion !
      serials-unchanged? 0= if true saw-partial ! then
      lf-mdefinition-fuel @ 0<> abort" failure fuel"
    else outcome-ok expect-status true saw-success ! then
    assert-rollback lf-minfer-context-depth @ 0<> abort" context leak"
  loop
  saw-exhaustion @ 0= abort" no exhaustion"
  saw-partial @ 0= abort" no partial exhaustion"
  saw-success @ 0= abort" no success"
  setup snapshot 4 9 -1 probe outcome-invalid expect-status assert-rollback ;
\ Cases that only the retired legacy probes covered (gap T2 of the legacy
\ coverage map).
: open-claim-case ( -- )
  \ (x : A) -> A has a loose A: the claim fails its preflight.
  setup snapshot 3 9 50000 probe outcome-invalid expect-status assert-rollback ;
variable saw-invalid
: open-value-fuel-case ( -- )
  \ A closed claim and an open value: with too little fuel the preflight is
  \ exhausted, with enough it reaches the value and finds it invalid.
  false saw-exhaustion ! false saw-invalid !
  200 0 do
    setup snapshot 4 12 i probe dup outcome-exhausted = if
      drop true saw-exhaustion !
    else outcome-invalid expect-status true saw-invalid ! then
    assert-rollback
  loop
  saw-exhaustion @ 0= abort" no exhaustion" saw-invalid @ 0= abort" no invalid" ;
: corrupt-node-case ( -- )
  \ A raw corrupted tag, or a node that is its own child, in the claim (node
  \ 3) or the value (node 7) is invalid; restored, the pair checks again.
  setup 3 lf-term-slot @ 99 3 lf-term-slot !
  snapshot 4 9 50000 probe outcome-invalid expect-status assert-rollback
  3 lf-term-slot ! 7 lf-term-slot cell+ @ 7 7 lf-term-slot cell+ !
  snapshot 4 9 50000 probe outcome-invalid expect-status assert-rollback
  7 lf-term-slot cell+ ! 3 lf-term-slot cell+ @ 3 3 lf-term-slot cell+ !
  snapshot 4 9 50000 probe outcome-invalid expect-status assert-rollback
  3 lf-term-slot cell+ !
  snapshot 4 9 50000 probe outcome-ok expect-status assert-rollback ;
: stale-value-non-type-case ( -- )
  \ A lambda claim with a stale value: invalid before any allocation.
  setup snapshot token @ 9 h 9 h 1+ 50000 lf-mixed-definition-probe
  outcome-invalid expect-status assert-rollback
  serials-unchanged? 0= abort" stale value allocated" ;
: prop-claim-case ( -- )
  \ forall P : Prop, P -> P with fun P h => h: a claim in Sort 0. Prop
  \ itself as the value has type Sort 1, apart from the claim (D2).
  setup 0 dup lf-level-identity 0= abort" zero" lf-hterm-sort save \ 14 Prop
  14 h 3 h lf-hterm-pi save 14 h 12 h lf-hterm-lam save           \ 15, 16
  snapshot 15 16 50000 probe outcome-ok expect-status assert-rollback
  snapshot 15 14 50000 probe outcome-rejected expect-status assert-rollback
  lf-diag-value-apart rejected-code? 0= abort" D2" ;
' open-claim-case s" open claim" run-case
' open-value-fuel-case s" open value behind the claim's preflight" run-case
' corrupt-node-case s" corrupted claim and value nodes" run-case
' stale-value-non-type-case s" stale value with a non-type claim" run-case
' prop-claim-case s" claim in Prop" run-case
' basic-case s" mixed definition" run-case
' stale-case s" preflight stale handles" run-case
' distinct-case s" distinct constants" run-case
' ill-arity-case s" universe arity mismatch" run-case
' non-type-case s" non-type binder domain and Pi body" run-case
' generated-rollback-case s" generated allocations and rollback" run-case
' future-handle-case s" future handles" run-case
' fuel-case s" shared fuel and rollback" run-case
cases-done bye
