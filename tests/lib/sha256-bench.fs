\ Speed of src/lib/sha256.fs (report only, not part of make test): hashes
\ 64 MiB of pseudo-random bytes held in memory, in one update, three times,
\ and prints the digest and the rate of each run. Run with gforth-fast for
\ the figures in docs/development/FORTH_LIBRARY.md; define sha256-portable
\ first (gforth-fast -e ': sha256-portable ;' tests/lib/sha256-bench.fs) for
\ the plain definitions. Uses Gforth's utime.
require ../../src/lib/sha256.fs

64 1024 * 1024 * constant bench-bytes
sha256: hasher
create digest 32 allot
create text 64 allot
variable fill-seed  12345 fill-seed !
: next-byte ( -- c )
  fill-seed @ 1103515245 * 12345 + $7fffffff and dup fill-seed ! 16 rshift 255 and ;
: filled ( -- addr ) bench-bytes allocate throw dup bench-bytes 0 do next-byte over i + c! loop ;
: rate. ( d-microseconds -- ) d>f 1e6 f/ fdup f. ." s, " bench-bytes s>f 1e6 f/ fswap f/ f. ." MB/s" ;
: run ( addr -- )
  utime 2>r hasher sha256-init bench-bytes hasher sha256-update digest hasher sha256-final
  utime 2r> d- digest text digest>hex text 64 type space rate. cr ;
filled dup run dup run dup run free throw
bye
