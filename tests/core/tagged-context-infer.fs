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

create ctx 8 cells allot
variable sort-id
variable var-id
variable root-id
: setup ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  lf-ssession-begin 0= abort" session"
  0 lf-level-identities @ lf-hterm-sort 0= abort" sort" sort-id ! drop
  0 lf-hterm-bvar 0= abort" bvar" var-id ! drop
  0 ctx ! sort-id @ ctx cell+ !
  1 ctx 2 cells + ! var-id @ ctx 3 cells + ! ;

\ A : Sort 0, x : A; x has type A, shifted under x.
setup
T{ 1 var-id @ ctx 2 1000 lf-tcontext-infer -> 2 lf-term-serial @ lf-tinfer-ok }T
T{ 2 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ lf-tinfer-context-depth @ -> 0 }T
\ Under an additional lambda binder, x becomes bvar 1 and its type bvar 2.
setup
T{ 1 lf-hterm-bvar -> 2 lf-term-serial @ true }T
T{ 0 sort-id @ 2 lf-term-serial @ lf-hterm-lam -> 3 lf-term-serial @ true }T
lf-term-serial @ root-id !
T{ 3 root-id @ ctx 2 1000 lf-tcontext-infer -> 6 lf-term-serial @ lf-tinfer-ok }T
T{ 5 lf-term-read -> lf-tag-bvar 2 0 true }T
T{ 6 lf-term-read -> lf-tag-pi 0 5 true }T
\ The Lean oracle's A : Sort 1, a : A, B : Sort 1, b : B context.
\ Its a (bvar 2) has type bvar 3; b (bvar 0) has type bvar 1.
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-level-identities @ lf-hlevel-succ -> 1 lf-level-serial @ true }T
T{ 1 lf-level-serial @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ sort-id !
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
lf-term-serial @ var-id !
0 ctx ! sort-id @ ctx cell+ !
1 ctx 2 cells + ! var-id @ ctx 3 cells + !
0 ctx 4 cells + ! sort-id @ ctx 5 cells + !
1 ctx 6 cells + ! var-id @ ctx 7 cells + !
T{ 2 lf-hterm-bvar -> 2 lf-term-serial @ true }T
T{ 2 lf-term-serial @ ctx 4 2000 lf-tcontext-infer -> 3 lf-term-serial @ lf-tinfer-ok }T
T{ 3 lf-term-read -> lf-tag-bvar 3 0 true }T
T{ 1 var-id @ ctx 4 2000 lf-tcontext-infer -> 4 lf-term-serial @ lf-tinfer-ok }T
T{ 4 lf-term-read -> lf-tag-bvar 1 0 true }T

\ Root and dependent domains must be scoped in the correct preceding context.
setup
T{ 1 var-id @ ctx 0 1000 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
1 ctx ! var-id @ ctx cell+ !
T{ 1 var-id @ ctx 1 1000 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ lf-level-count @ -> 2 1 }T
\ The second domain cannot refer to a binder that has not yet been added.
setup
T{ 1 lf-hterm-bvar -> 2 lf-term-serial @ true }T
2 ctx 2 cells + ! lf-term-serial @ ctx 3 cells + !
T{ 1 var-id @ ctx 2 1000 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ lf-level-count @ -> 3 1 }T
\ Stale domain identity after suffix rollback and slot reuse.
setup
1 lf-term-count !
T{ 0 lf-hterm-bvar -> 1 lf-term-serial @ true }T
T{ 1 lf-term-serial @ ctx 2 1000 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ lf-level-count @ -> 2 1 }T
\ A stale session invalidates even otherwise live-looking context pairs.
setup
lf-lscope-context-reset
T{ 1 var-id @ ctx 2 1000 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ lf-level-count @ -> 2 1 }T
\ Deliberate test-only corruption of a reachable graph: cycles fail closed.
setup
lf-tag-app 0 lf-term-slot ! 0 0 lf-term-slot cell+ ! 0 0 lf-term-slot 2 cells + !
T{ 1 var-id @ ctx 1 1000 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ lf-level-count @ -> 2 1 }T
\ Syntactically scoped domains may be ill typed. Success is conditional.
setup
T{ 0 sort-id @ 0 sort-id @ lf-hterm-app -> 2 lf-term-serial @ true }T
2 ctx ! lf-term-serial @ ctx cell+ !
T{ 1 var-id @ ctx 1 1000 lf-tcontext-infer -> 3 lf-term-serial @ lf-tinfer-ok }T
T{ 3 lf-term-read -> lf-tag-app 0 0 true }T
\ A successful result stamp is not revived by later suffix reuse.
setup
T{ 1 var-id @ ctx 2 1000 lf-tcontext-infer -> 2 lf-term-serial @ lf-tinfer-ok }T
lf-term-serial @ root-id !
2 lf-term-count !
T{ 0 lf-hterm-bvar -> 2 lf-term-serial @ true }T
T{ 2 root-id @ lf-hterm-valid? -> false }T
T{ 1 var-id @ ctx 2 1000 lf-tcontext-infer -> 3 lf-term-serial @ lf-tinfer-ok }T
T{ lf-tinfer-context-depth @ -> 0 }T
\ Bad counts never access the array; negative fuel is invalid.
T{ 0 sort-id @ 0 -1 100 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
T{ 0 sort-id @ 0 lf-term-capacity 1+ 100 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
T{ 0 sort-id @ 0 0 -1 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
\ Unknown application after domain inference must restore both arenas.
setup
T{ 0 sort-id @ 0 sort-id @ lf-hterm-app -> 2 lf-term-serial @ true }T
T{ 0 sort-id @ 2 lf-term-serial @ lf-hterm-pi -> 3 lf-term-serial @ true }T
lf-term-serial @ root-id !
T{ 3 root-id @ ctx 1 1000 lf-tcontext-infer -> -1 0 lf-tinfer-unknown }T
T{ lf-term-count @ lf-level-count @ -> 4 1 }T
\ A binder inside a domain adds scope only to its body, not its annotation.
setup
T{ 0 sort-id @ 1 var-id @ lf-hterm-lam -> 2 lf-term-serial @ true }T
2 ctx ! lf-term-serial @ ctx cell+ !
T{ 1 var-id @ ctx 1 1000 lf-tcontext-infer -> 3 lf-term-serial @ lf-tinfer-ok }T
setup
T{ 1 var-id @ 1 var-id @ lf-hterm-lam -> 2 lf-term-serial @ true }T
2 ctx ! lf-term-serial @ ctx cell+ !
T{ 1 var-id @ ctx 1 1000 lf-tcontext-infer -> -1 0 lf-tinfer-invalid }T
T{ lf-term-count @ lf-level-count @ -> 3 1 }T

\ Full context capacity is usable; one further nested binder exhausts the
\ context stack after work has allocated, and must roll both arenas back.
create guarded-context lf-term-capacity 2 * 2 + cells allot
: full-context ( -- )
  12345 guarded-context !
  54321 guarded-context lf-term-capacity 2 * 1+ cells + !
  lf-term-capacity 0 do
    0 guarded-context i 2 * 1+ cells + !
    sort-id @ guarded-context i 2 * 2 + cells + !
  loop ;
setup full-context
T{ 9876 1 var-id @ guarded-context cell+ lf-term-capacity 100000 lf-tcontext-infer
   -> 9876 0 sort-id @ lf-tinfer-ok }T
T{ guarded-context @ guarded-context lf-term-capacity 2 * 1+ cells + @
   -> 12345 54321 }T
T{ lf-tinfer-context-depth @ -> 0 }T
T{ 0 sort-id @ 1 var-id @ lf-hterm-lam -> 2 lf-term-serial @ true }T
lf-term-serial @ root-id !
T{ 9876 2 root-id @ guarded-context cell+ lf-term-capacity 100000 lf-tcontext-infer
   -> 9876 -1 0 lf-tinfer-exhausted }T
T{ lf-term-count @ lf-level-count @ lf-tinfer-context-depth @ -> 3 1 0 }T
T{ guarded-context @ guarded-context lf-term-capacity 2 * 1+ cells + @
   -> 12345 54321 }T

\ Test a return-stack sentinel through both successful and failing paths.
: return-sentinels ( -- )
  2468 >r
  1 var-id @ guarded-context cell+ lf-term-capacity 100000 lf-tcontext-infer
  lf-tinfer-ok <> abort" success status" 2drop
  r> 2468 <> abort" return stack success"
  1357 >r
  2 root-id @ guarded-context cell+ lf-term-capacity 100000 lf-tcontext-infer
  lf-tinfer-exhausted <> abort" exhaustion status" 2drop
  r> 1357 <> abort" return stack failure" ;
return-sentinels

\ All audit status values, including unrecognized values, are mapped.
T{ lf-repr-ok lf-tci-audit-status -> lf-tinfer-ok }T
T{ lf-repr-invalid lf-tci-audit-status -> lf-tinfer-invalid }T
T{ lf-repr-exhausted lf-tci-audit-status -> lf-tinfer-exhausted }T
T{ 99 lf-tci-audit-status -> lf-tinfer-invalid }T
\ Sweep fuel over validation, shifting and inference; every failure rolls back.
variable successes
variable exhausted
: sweep ( -- )
  0 successes ! 0 exhausted !
  200 0 do
    setup
    1 var-id @ ctx 2 i lf-tcontext-infer
    dup lf-tinfer-exhausted = if
      drop 0<> abort" identity" -1 <> abort" index"
      lf-term-count @ 2 <> abort" terms"
      lf-level-count @ 1 <> abort" levels"
      1 exhausted +!
    else
      lf-tinfer-ok <> abort" status"
      lf-hterm-valid? 0= abort" result" 1 successes +!
    then
    lf-tinfer-context-depth @ 0<> abort" context leak"
  loop
  successes @ 0= exhausted @ 0= or abort" sweep coverage" ;
sweep
bye
