\ Experimental inference contract tests. Candidate signatures are assumptions;
\ a successful inference is not a checked theorem or declaration.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/lib/lib.fs
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
require ../../src/kernel/mixed-convert.fs
require ../../src/kernel/mixed-infer.fs
require ../../src/kernel/mixed-signature-audit.fs
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
\ A failed inference returns no root and no identity.
: expect-no-result ( type identity -- )
  0<> abort" failure identity" -1 <> abort" failure root" ;

: fixture-case ( -- )
  setup
  token @ 50000 lf-mixed-signature-audit outcome-ok expect-status
  9 h 0 50000 lf-constant-term-scope outcome-ok expect-status
  token @ id-name @ actuals 1 50000 lf-msp-specialize
  outcome-ok expect-status lf-hterm-valid? 0= abort" signature result" ;

\ Check the result semantically, rather than relying on generated node indices.
\ The fuel left is pinned: preflight, inference and the specialization of
\ id spend 109 units here (observed before the refactor, at 398b76b), 106
\ since ADR 0011 Amendment 1 (structural level equality costs nothing), 94
\ since free variables (plan task 4.2.2a: no shift for a variable's type,
\ no audit when an application's type is instantiated, a chain of lambdas
\ closed once).
\ fun (A : Sort u) => id (A -> A) (fun (x : A) => x): the inner lambda,
\ an argument, begins a chain of lambdas under A's binder, so its type is
\ closed there (A's bound variable becomes A's free variable; plan task
\ 4.2.2a) before it is compared with id's domain. The whole has type
\ (A : Sort u) -> A -> A.
: newest ( -- index identity ) lf-term-count @ 1- h ;
: chain-argument-case ( -- )
  setup 5 h 3 h lf-hterm-app save newest 12 h lf-hterm-app save
  0 h newest lf-hterm-lam save lf-term-count @ 1- 50000 infer outcome-ok expect-status
  4 h 50000 lf-mixed-convert outcome-ok <> abort" chain argument type" ;
: poly-case ( -- )
  setup 9 50000 infer outcome-ok expect-status
  lf-minfer-fuel @ 49906 <> abort" poly fuel"
  4 h 50000 lf-mixed-convert outcome-ok <> abort" poly type" ;
: invalid-argument-case ( -- )
  \ id.{u} (Sort u): the argument has type Sort (u+1) where id.{u} wants a
  \ Sort u; with u = 0 the levels are 1 and 0, so rule D1 (ADR 0011)
  \ rejects, as Lean's kernel does (appTypeMismatch).
  setup snapshot lf-diag-clear 10 50000 infer
  outcome-rejected expect-status
  0<> abort" failure identity" -1 <> abort" failure root"
  counts-unchanged? 0= abort" invalid argument rollback"
  lf-diag@ lf-diag-argument-apart <> abort" argument rule code" drop
  0<> abort" second number" 1 <> abort" rule D1" ;
: missing-case ( -- )
  setup snapshot 11 50000 infer
  outcome-unknown expect-status
  0<> abort" failure identity" -1 <> abort" failure root"
  counts-unchanged? 0= abort" missing rollback" ;
: stale-case ( -- )
  setup 1 cells lf-msp-ids + dup @ 1+ swap ! snapshot
  9 50000 infer outcome-invalid <> abort" stale later signature"
  0<> abort" failure identity" -1 <> abort" failure root"
  counts-unchanged? 0= abort" preflight counts"
  serials-unchanged? 0= abort" preflight allocated" ;
: context-case ( -- )
  setup 13 50000 infer outcome-ok <> abort" binder inference"
  lf-hterm-valid? 0= abort" binder result handle"
  lf-minfer-context-depth @ 0<> abort" binder context leak"
  snapshot 12 50000 infer outcome-invalid <> abort" open binder domain"
  0<> abort" failure identity" -1 <> abort" failure root"
  counts-unchanged? 0= abort" scope rollback" ;
: unknown-rolled-back ( root -- )
  snapshot 50000 infer outcome-unknown expect-status expect-no-result
  counts-unchanged? 0= abort" unknown rollback" ;
: rejected-rolled-back ( root -- )
  snapshot 50000 infer outcome-rejected expect-status expect-no-result
  counts-unchanged? 0= abort" rejected rollback" ;
: non-type-case ( -- )
  \ fun (x : fun A => A) => x has a binder domain whose type, a Pi, is not a
  \ Sort: rule S2 rejects it (Lean: typeExpected). (A : Sort u) -> fun (x :
  \ A) => x has such a Pi body: rule S4 rejects it (ADR 0011 Amendment 2;
  \ Lean's infer_pi: typeExpected), recorded with code 61.
  setup 13 h 1 h lf-hterm-lam save 0 h 12 h lf-hterm-pi save \ 14, 15
  14 rejected-rolled-back 15 rejected-rolled-back
  lf-diag-code@ lf-diag-body-type <> abort" S4 code" ;
: preflight-fuel-case ( -- )
  setup
  9 -1 infer outcome-invalid expect-status 2drop
  lf-minfer-fuel @ 0<> abort" negative fuel remainder"
  12 50000 infer outcome-invalid expect-status 2drop
  lf-minfer-fuel @ 0<> abort" scope failure remainder"
  9 1 infer outcome-exhausted expect-status 2drop
  lf-minfer-fuel @ 0<> abort" exhausted preflight remainder"
  token @ 1+ 9 h 50000 lf-mixed-infer outcome-invalid expect-status 2drop
  lf-minfer-fuel @ 0<> abort" invalid token remainder" ;
\ This deliberately assumes a candidate signature without claiming it is a
\ type. Substitution changes a universe inside a nested constant reference.
: generated-reference-case ( -- )
  setup s" outer" new-name outer-name !
  1 dup lf-level-identity 0= abort" parameter" lf-hlevel-succ 0= abort" succ"
  nested-args cell+ ! nested-args !
  id-name @ lf-name-generation @ nested-args 1 lf-cref-new 0= abort" nested cref"
  lf-cterm-new 0= abort" nested constant" nested-id ! nested-root !
  token @ outer-name @ nested-root @ nested-id @ formals 1 50000 lf-msp-put
  outcome-ok expect-status
  0 nested-args ! 0 lf-level-identity 0= abort" zero" nested-args cell+ !
  outer-name @ lf-name-generation @ nested-args 1 lf-cref-new 0= abort" outer cref"
  lf-cterm-new 0= abort" outer constant" outer-id ! outer-root !
  token @ outer-root @ outer-id @ 50000 lf-mixed-infer outcome-ok expect-status
  2dup 50000 lf-cterm-check outcome-ok expect-status
  drop lf-term-read 0= abort" generated term"
  rot lf-tag-constant <> abort" generated constant"
  generated-ref-id ! generated-ref !
  generated-ref @ generated-ref-id @ lf-cref-read 0= abort" generated cref"
  1 <> abort" generated arity" lf-name-generation @ <> abort" generated generation"
  id-name @ <> abort" generated name"
  generated-ref @ generated-ref-id @ 0 lf-cref-level 0= abort" generated level"
  drop lf-level-read 0= abort" generated level node"
  0<> abort" succ payload" 0<> abort" succ predecessor"
  lf-level-tag-succ <> abort" expected succ zero"
  \ Applying this assumed non-Pi candidate causes a later unknown after
  \ generating a level, reference and term. All three counts must roll back.
  outer-root @ outer-id @ 0 h lf-hterm-app save
  lf-term-count @ 1- snapshot 50000 infer outcome-unknown expect-status 2drop
  counts-unchanged? 0= abort" generated rollback"
  lf-term-serial @ term-serial-before @ <= abort" no term allocation"
  lf-level-serial @ level-serial-before @ <= abort" no level allocation"
  lf-cref-serial @ cref-serial-before @ <= abort" no cref allocation"
  \ Reuse each first rolled-back slot and reject its discarded identity.
  0 dup lf-level-identity 0= abort" zero" lf-hlevel-succ 0= abort" reuse level"
  over levels-before @ <> abort" level slot"
  2dup lf-hlevel-valid? 0= abort" new level identity"
  over level-serial-before @ 1+ lf-hlevel-valid? abort" stale level revived" 2drop
  id-name @ lf-name-generation @ nested-args 1 lf-cref-new 0= abort" reuse cref"
  over crefs-before @ <> abort" cref slot"
  2dup lf-cref-valid? 0= abort" new cref identity"
  over cref-serial-before @ 1+ lf-cref-valid? abort" stale cref revived" 2drop
  0 lf-hterm-bvar 0= abort" reuse term"
  over terms-before @ <> abort" term slot"
  2dup lf-hterm-valid? 0= abort" new term identity"
  over term-serial-before @ 1+ lf-hterm-valid? abort" stale term revived" 2drop ;
\ A job started directly, as the definition probe does after its own
\ preflight: the given fuel, no frames or binders, an empty local context,
\ and only nodes below the term count at the start are source; nodes
\ inference made are not. Since plan task 4.2.2a the lambda's binder got
\ a free variable of the local context.
: start-case ( -- )
  setup token @ 500 lf-minfer-start
  lf-minfer-fuel @ 500 <> abort" start fuel"
  lf-minfer-depth @ lf-minfer-context-depth @ or abort" start depths"
  lf-lctx-count @ abort" start locals"
  13 lf-minfer-walk outcome-ok expect-status lf-term-count @ 1- <> abort" new type"
  lf-minfer-fuel @ 500 < 0= abort" walk fuel"
  lf-lctx-count @ 1 <> abort" one free variable"
  lf-term-count @ 1- lf-minfer-walk outcome-invalid expect-status
  -1 <> abort" no type" ;
variable saw-exhaustion variable saw-success variable saw-partial
: fuel-case ( -- )
  false saw-exhaustion ! false saw-success ! false saw-partial !
  500 0 do
    setup snapshot 13 i infer
    dup outcome-exhausted = if
      drop 0<> abort" fuel identity" -1 <> abort" fuel root"
      counts-unchanged? 0= abort" fuel rollback"
      serials-unchanged? 0= if true saw-partial ! then
      true saw-exhaustion !
    else
      outcome-ok expect-status
      lf-hterm-valid? 0= abort" fuel result handle" true saw-success !
    then
    lf-minfer-context-depth @ 0<> abort" fuel context leak"
  loop
  saw-exhaustion @ 0= abort" no exhaustion"
  saw-partial @ 0= abort" no post-allocation exhaustion"
  saw-success @ 0= abort" no sufficient fuel" ;

' fixture-case s" fixture preflight and specialization" run-case
' poly-case s" fixturePoly" run-case
' chain-argument-case s" lambda argument under a binder" run-case
' invalid-argument-case s" invalid argument" run-case
' missing-case s" missing constant" run-case
' stale-case s" stale later candidate" run-case
' context-case s" binder context" run-case
' non-type-case s" non-type binder domain and Pi body" run-case
' preflight-fuel-case s" preflight fuel" run-case
' generated-reference-case s" generated reference and rollback" run-case
' start-case s" job started directly" run-case
' fuel-case s" fuel and rollback" run-case
cases-done
\ The frames grow with the depth (plan task 6.2.0): a stack the heap
\ cannot grow makes a visit full, spending no fuel. With no fuel as well,
\ the fuel decides: exhausted.
lf-minfer-frames frame-free  1 heap-refusals !  100 lf-minfer-fuel !
T{ 0 lf-minfer-walk lf-minfer-fuel @ lf-minfer-depth @ -> -1 outcome-full 100 0 }T
0 lf-minfer-fuel !  1 heap-refusals !
T{ 0 lf-minfer-walk lf-minfer-depth @ heap-refusals @ -> -1 outcome-exhausted 0 1 }T
0 heap-refusals !
\ The scope grows too: a scope the heap cannot grow opens no binder,
\ which is full, and neither the scope nor the local context changes.
\ That is checked before anything else, so with no fuel left it is still
\ full.
lf-minfer-fvars slab-capacity dup lf-minfer-context-depth !  100 lf-minfer-fuel !
constant scope-room
lf-lctx-count @ constant locals-before
1 heap-refusals !
T{ 0 0 lf-minfer-bind lf-minfer-context-depth @ -> outcome-full scope-room }T
0 lf-minfer-fuel !  1 heap-refusals !
T{ 0 0 lf-minfer-bind lf-minfer-fuel @ lf-lctx-count @ -> outcome-full 0 locals-before }T
0 heap-refusals !  0 lf-minfer-context-depth !
bye
