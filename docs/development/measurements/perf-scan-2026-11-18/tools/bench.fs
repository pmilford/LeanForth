\ perf-scan micro-benchmarks (not part of the repository's tests; report only).
\ Usage, from the worktree root:  gforth-fast src/main.fs build/perf/bench.fs -e bye
\ Prints, per case, the size and the nanoseconds per operation (utime).
decimal
2variable t0
: start ( -- ) utime t0 2! ;
: ns/op ( ops -- ) utime t0 2@ d- drop 1000 * swap / . ." ns/op" cr ;
: case. ( n c-addr u -- ) type ."  n=" dup . ;

\ ---- memo (htab + slab): put n keys, then find each (both counted)
create mb /memo allot
: memo-run ( n -- )
  2 1 mb memo-init drop
  start dup 0 ?do i 7 * i 0 mb memo! drop loop
  dup 0 ?do i 0 mb memo@ 0= abort" memo miss" drop loop
  2* ns/op mb memo-free ;
: memo-case ( n -- ) s" memo put+find" case. memo-run ;

\ ---- sort: timed by sortbench.fs (a first version here passed the repetition
\ count as the record count, overran its buffer and was discarded)

\ ---- sha256 of short texts (64 bytes) - per call
sha256: hb  create hd 32 allot  create htext 64 allot
: sha-case ( reps -- )
  s" sha256 64-byte message" case.
  start dup 0 ?do hb sha256-init htext 64 hb sha256-update hd hb sha256-final loop ns/op ;

\ ---- the name store in its stored mode (no view): intern n distinct
\ string components under the anonymous prefix; per intern
create nbuf 16 allot
: name-text ( i -- c-addr u ) 0 <# #s [char] n hold #> ;
: names-run ( n -- )
  start dup 0 ?do 0 i name-text lf-name-str 0= abort" name refused" drop loop ns/op ;
: names-case ( n -- ) s" lf-name-str (stored mode)" case. lf-name-reset 200000 lf-name-capacity! drop names-run ;

