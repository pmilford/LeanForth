\ Experimental inference contract tests. Candidate signatures are assumptions;
\ a successful inference is not a checked theorem or declaration.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs
include ../../src/experimental/constant-term-boundary.fs
include ../../src/experimental/level-substitute.fs
include ../../src/experimental/mixed-level-substitute.fs
include ../../src/experimental/mixed-signature-probe.fs
include ../../src/experimental/constant-term-scope.fs
include ../../src/experimental/mixed-signature-audit.fs
include ../../src/experimental/mixed-compare.fs
include ../../src/experimental/mixed-shift.fs
include ../../src/experimental/mixed-instantiate.fs
include ../../src/experimental/mixed-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/mixed-convert.fs
include ../../src/experimental/mixed-infer.fs
include ../../src/experimental/mixed-definition-probe.fs

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
: infer ( root fuel -- type identity status ) >r h token @ -rot r> lf-mixed-infer ;
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
  token @ id-name @ 4 h formals 1 50000 lf-msp-put lf-msp-ok <> abort" id signature"
  token @ later-name @ 0 h formals 1 50000 lf-msp-put lf-msp-ok <> abort" later signature" ;

: expect-status ( actual expected -- )
  2dup <> if ." expected status " . ." actual " . cr -2 throw then 2drop ;

: probe ( claim value fuel -- status )
  >r h lf-mdefinition-value-id ! lf-mdefinition-value !
  h lf-mdefinition-type-id ! lf-mdefinition-type !
  token @ lf-mdefinition-type @ lf-mdefinition-type-id @
  lf-mdefinition-value @ lf-mdefinition-value-id @ r> lf-mixed-definition-probe ;
: assert-rollback ( -- ) counts-unchanged? 0= abort" arena counts changed" ;
: basic-case ( -- )
  setup snapshot 4 9 50000 probe lf-mdefinition-ok expect-status assert-rollback
  lf-mdefinition-fuel @ 0<= abort" success fuel"
  lf-term-serial @ term-serial-before @ <= abort" expected allocations"
  snapshot 0 10 50000 probe lf-mdefinition-unknown expect-status assert-rollback
  lf-mdefinition-fuel @ 0<> abort" unknown fuel"
  snapshot 0 9 50000 probe lf-mdefinition-unknown expect-status assert-rollback
  snapshot 0 12 50000 probe lf-mdefinition-invalid expect-status assert-rollback
  lf-mdefinition-fuel @ 0<> abort" invalid fuel"
  snapshot 9 9 50000 probe lf-mdefinition-unknown expect-status assert-rollback
  99 lf-mdefinition-infer-status lf-mdefinition-invalid expect-status ;
: stale-case ( -- )
  setup snapshot token @ 4 h 9 h 1+ 50000 lf-mixed-definition-probe
  lf-mdefinition-invalid expect-status assert-rollback
  serials-unchanged? 0= abort" stale value allocated"
  1 cells lf-msp-ids + dup @ 1+ swap ! snapshot
  4 9 50000 probe lf-mdefinition-invalid expect-status assert-rollback
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
  lf-msp-ok expect-status
  0 nested-args ! 0 lf-level-identity 0= abort" zero" nested-args cell+ !
  outer-name @ lf-name-generation @ nested-args 1 lf-cref-new 0= abort" outer ref"
  lf-cterm-new save
  lf-term-count @ 1- snapshot 0 swap 50000 probe lf-mdefinition-unknown expect-status
  assert-rollback lf-mdefinition-fuel @ 0<> abort" unknown fuel"
  lf-term-serial @ term-serial-before @ <= abort" no term allocation"
  lf-level-serial @ level-serial-before @ <= abort" no level allocation"
  lf-cref-serial @ cref-serial-before @ <= abort" no reference allocation" ;
: distinct-case ( -- )
  setup s" other" new-name other-name ! s" value" new-name value-name !
  \ A and B are different constants, each assumed to have type Sort u.
  token @ other-name @ 0 h formals 1 50000 lf-msp-put lf-msp-ok expect-status
  later-name @ lf-name-generation @ actuals 1 lf-cref-new 0= abort" A cref"
  lf-cterm-new save \ 14 A
  other-name @ lf-name-generation @ actuals 1 lf-cref-new 0= abort" B cref"
  lf-cterm-new save \ 15 B
  \ The value has assumed type B. Comparing B with A is inconclusive.
  token @ value-name @ 15 h formals 1 50000 lf-msp-put lf-msp-ok expect-status
  value-name @ lf-name-generation @ actuals 1 lf-cref-new 0= abort" value cref"
  lf-cterm-new save \ 16 value
  snapshot 14 16 50000 probe lf-mdefinition-unknown expect-status assert-rollback ;
: future-handle-case ( -- )
  \ A forged future identity would become live after the first allocation if
  \ the second source or later index record were checked too late.
  setup snapshot token @ 4 h lf-term-count @ lf-term-serial @ 1+ 50000
  lf-mixed-definition-probe lf-mdefinition-invalid expect-status
  assert-rollback serials-unchanged? 0= abort" future value allocated"
  setup lf-term-count @ 1 cells lf-msp-roots + !
  lf-term-serial @ 1+ 1 cells lf-msp-ids + ! snapshot
  4 9 50000 probe lf-mdefinition-invalid expect-status
  assert-rollback serials-unchanged? 0= abort" future index allocated" ;
variable saw-exhaustion variable saw-success variable saw-partial
: fuel-case ( -- )
  false saw-exhaustion ! false saw-success ! false saw-partial !
  1200 0 do
    setup snapshot 4 9 i probe
    dup lf-mdefinition-exhausted = if
      drop true saw-exhaustion !
      serials-unchanged? 0= if true saw-partial ! then
      lf-mdefinition-fuel @ 0<> abort" failure fuel"
    else lf-mdefinition-ok expect-status true saw-success ! then
    assert-rollback lf-minfer-context-depth @ 0<> abort" context leak"
  loop
  saw-exhaustion @ 0= abort" no exhaustion"
  saw-partial @ 0= abort" no partial exhaustion"
  saw-success @ 0= abort" no success"
  setup snapshot 4 9 -1 probe lf-mdefinition-invalid expect-status assert-rollback ;
variable failures variable initial-depth
: run-case ( xt addr len -- ) type cr depth 1- initial-depth ! catch ?dup if
  .error-string cr 1 failures +! then
  depth initial-depth @ <> if abort" test stack imbalance" then ;
' basic-case s" mixed definition" run-case
' stale-case s" preflight stale handles" run-case
' distinct-case s" distinct constants" run-case
' generated-rollback-case s" generated allocations and rollback" run-case
' future-handle-case s" future handles" run-case
' fuel-case s" shared fuel and rollback" run-case
failures @ . ." case(s) failed" cr
: finish ( -- ) failures @ if -1 throw then ;
finish bye
