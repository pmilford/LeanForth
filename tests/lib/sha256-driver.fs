\ Driver for tests/lib/test_sha256.py: hash-file reads a file whole, gives
\ it to SHA-256 in updates of random sizes (0 to 139 bytes, from a seeded
\ generator, so empty updates and updates across block boundaries occur)
\ and prints the digest as 64 hexadecimal digits on a line of its own.
require ../../src/lib/sha256.fs

sha256: hasher
create digest 32 allot
create text 64 allot
variable split-seed
: next-split ( -- n )
  split-seed @ 1103515245 * 12345 + $7fffffff and dup split-seed ! 16 rshift 140 mod ;
\ The whole file, in heap memory the caller frees.
: file-bytes ( c-addr u -- addr n )
  r/o bin open-file throw >r
  r@ file-size throw drop dup allocate throw swap
  2dup r@ read-file throw over <> abort" sha256-driver: short read"
  r> close-file throw ;
\ Updates of random sizes until the message is used up.
: chunks ( addr n -- )
  begin dup while next-split over min >r over r@ hasher sha256-update r> /string repeat
  2drop ;
: hash-file ( c-addr u seed -- )
  split-seed ! file-bytes over >r hasher sha256-init chunks
  digest hasher sha256-final digest text digest>hex text 64 type cr r> free throw ;
