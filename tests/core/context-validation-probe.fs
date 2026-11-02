\ Conditional open-term inference; not a theorem checker.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs
include ../../src/experimental/tagged-compare.fs
include ../../src/experimental/tagged-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/tagged-convert.fs
include ../../src/experimental/tagged-infer.fs
include ../../src/experimental/tagged-context-infer.fs
include ../../src/experimental/context-validation-probe.fs

create ctx lf-term-capacity 2 * cells allot
variable sid
variable vid
variable saved-id
variable saved-level-id
variable sort1-id
variable lambda-id
variable terms-before
variable levels-before
: setup ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  lf-ssession-begin 0= abort" session"
  0 lf-level-identities @ lf-hterm-sort 0= abort" sort" sid ! drop
  0 lf-hterm-bvar 0= abort" bvar" vid ! drop
  0 ctx ! sid @ ctx cell+ !
  1 ctx 2 cells + ! vid @ ctx 3 cells + ! ;
: counts ( -- ) lf-term-count @ terms-before ! lf-level-count @ levels-before ! ;
: unchanged ( -- flag )
  lf-term-count @ terms-before @ = lf-level-count @ levels-before @ = and ;

setup counts
T{ 0 0 0 lf-context-validation-probe -> lf-tinfer-ok }T
T{ ctx 2 10000 lf-context-validation-probe -> lf-tinfer-ok }T
T{ unchanged -> true }T
\ Result allocations were discarded and their stamps are never revived.
lf-term-serial @ saved-id !
T{ 0 lf-hterm-bvar -> 2 lf-term-serial @ true }T
T{ 2 saved-id @ lf-hterm-valid? -> false }T
T{ lf-term-serial @ saved-id @ > -> true }T

\ Scope is against preceding entries, not the whole context.
setup 1 ctx ! vid @ ctx cell+ ! counts
T{ ctx 2 10000 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ unchanged -> true }T
setup
T{ 1 lf-hterm-bvar -> 2 lf-term-serial @ true }T
2 ctx 2 cells + ! lf-term-serial @ ctx 3 cells + ! counts
T{ ctx 2 10000 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ unchanged -> true }T
\ Audit a later fake handle before allocating for the earlier valid Sort.
setup 999 ctx 3 cells + ! counts
lf-term-serial @ saved-id !
T{ ctx 2 10000 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ unchanged lf-term-serial @ saved-id @ = and -> true }T
\ Stale term stamp after slot reuse.
setup 1 lf-term-count !
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
counts T{ ctx 2 10000 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ unchanged -> true }T
\ Level stamp and session epoch are checked too.
setup 0 lf-hsort-level-identities ! counts
T{ ctx 1 10000 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ unchanged -> true }T
setup lf-lscope-context-reset counts
T{ 0 0 100 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ ctx 2 10000 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ unchanged -> true }T
\ A lambda has a Pi type: conservatively unknown, not invalid.
setup
T{ 0 sid @ 1 vid @ lf-hterm-lam -> 2 lf-term-serial @ true }T
2 ctx ! lf-term-serial @ ctx cell+ ! counts
T{ ctx 1 10000 lf-context-validation-probe -> lf-tinfer-unknown }T
T{ unchanged -> true }T
\ Unsupported application also propagates unknown after allocations.
setup
T{ 0 sid @ 0 sid @ lf-hterm-app -> 2 lf-term-serial @ true }T
2 ctx ! lf-term-serial @ ctx cell+ ! counts
T{ ctx 1 10000 lf-context-validation-probe -> lf-tinfer-unknown }T
T{ unchanged -> true }T
T{ 0 -1 100 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ 0 lf-term-capacity 1+ 100 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ 0 0 -1 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ lf-tinfer-ok lf-cv-status -> lf-tinfer-ok }T
T{ lf-tinfer-invalid lf-cv-status -> lf-tinfer-invalid }T
T{ lf-tinfer-exhausted lf-cv-status -> lf-tinfer-exhausted }T
T{ lf-tinfer-unknown lf-cv-status -> lf-tinfer-unknown }T
T{ 99 lf-cv-status -> lf-tinfer-invalid }T
\ Full capacity, including its last entry; no intermediate results persist.
setup
: full ( -- ) lf-term-capacity 0 do
  0 ctx i 2 * cells + ! sid @ ctx i 2 * 1+ cells + !
loop ;
full counts
T{ ctx lf-term-capacity 1000000 lf-context-validation-probe -> lf-tinfer-ok }T
T{ unchanged -> true }T
\ A guessed future slot/stamp cannot become valid through an earlier inference.
setup 2 ctx 2 cells + ! lf-term-serial @ 1+ ctx 3 cells + ! counts
lf-term-serial @ saved-id ! lf-level-serial @ saved-level-id !
T{ ctx 2 10000 lf-context-validation-probe -> lf-tinfer-invalid }T
T{ unchanged lf-term-serial @ saved-id @ = and
   lf-level-serial @ saved-level-id @ = and -> true }T
\ A : Sort 0, x : A, and a proposed domain x. Its inferred type is
\ the variable A, not syntactically a Sort, so the result is unknown.
setup
1 ctx 4 cells + ! vid @ ctx 5 cells + ! counts
T{ ctx 3 10000 lf-context-validation-probe -> lf-tinfer-unknown }T
T{ unchanged -> true }T
\ D := (lambda X : Sort 1 => X) (Sort 0) reduces to Sort 0.
\ D is a type, but inferring the next domain x : D returns the
\ unreduced application D; this probe conservatively says unknown.
setup
T{ 0 lf-level-identities @ lf-hlevel-succ -> 1 lf-level-serial @ true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 2 lf-term-serial @ true }T
lf-term-serial @ sort1-id !
T{ 2 sort1-id @ 1 vid @ lf-hterm-lam -> 3 lf-term-serial @ true }T
lf-term-serial @ lambda-id !
T{ 3 lambda-id @ 0 sid @ lf-hterm-app -> 4 lf-term-serial @ true }T
4 ctx ! lf-term-serial @ ctx cell+ ! counts
T{ ctx 1 100000 lf-context-validation-probe -> lf-tinfer-ok }T
T{ ctx 2 100000 lf-context-validation-probe -> lf-tinfer-unknown }T
T{ unchanged -> true }T
\ Full arenas exhaust inference and leave both counts unchanged.
: fill-terms ( -- ) begin lf-term-count @ lf-term-capacity < while
  0 lf-hterm-bvar 0= abort" fill terms" 2drop repeat ;
: fill-levels ( -- ) begin lf-level-count @ lf-level-capacity < while
  0 lf-level-identities @ lf-hlevel-succ 0= abort" fill levels" 2drop repeat ;
setup fill-terms counts
T{ ctx 1 10000 lf-context-validation-probe -> lf-tinfer-exhausted }T
T{ unchanged -> true }T
setup fill-levels counts
T{ ctx 1 10000 lf-context-validation-probe -> lf-tinfer-exhausted }T
T{ unchanged -> true }T
\ Fuel sweeps cover failures in audit and inference, plus success.
variable exhausted
variable successes
: sweep ( -- )
  0 exhausted ! 0 successes !
  300 0 do
    setup counts ctx 2 i lf-context-validation-probe
    case
      lf-tinfer-exhausted of 1 exhausted +! endof
      lf-tinfer-ok of 1 successes +! endof
      abort" unexpected status"
    endcase
    unchanged 0= abort" rollback"
    lf-tinfer-context-depth @ 0<> abort" context leak"
  loop
  exhausted @ 0= successes @ 0= or abort" sweep coverage" ;
sweep
bye
