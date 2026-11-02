\ Test-only byte protocol for staged declarations. Every field is four-byte
\ little-endian, restricted to the nonnegative signed 32-bit range. The first
\ three fields are node count, claim index, and value index; each following
\ node has four fields (index, tag, first, second). This is not a public format.
\ Input is read as data; no input bytes are evaluated as Forth source.
include ../../src/legacy/declaration-probe.fs
include ../../src/import/load.fs
decimal
create stream-byte 1 allot
variable stream-count
variable stream-claim
variable stream-value

\ Read one required byte and abort on EOF or host I/O error.
: stream-read-byte ( -- byte )
  stream-byte 1 stdin read-file throw
  1 <> if lf-load-abort -1 throw then stream-byte c@ ;

\ Decode a nonnegative signed-32-bit value without overflowing a 32-bit cell.
\ A high byte with its sign bit set is outside this test protocol's range.
: stream-read-field ( -- number )
  stream-read-byte stream-read-byte 8 lshift or
  stream-read-byte 16 lshift or
  stream-read-byte dup 128 >= if 2drop lf-load-abort -1 throw then
  24 lshift or ;

\ Stage exactly the declared number of nodes, reject trailing data, and emit
\ the untrusted probe status followed by node fields. Zero never registers a
\ theorem; the emitted nodes let tests verify the decoded values exactly.
: stream-probe ( -- )
  lf-term-reset lf-load-begin 0= if -1 throw then
  stream-read-field stream-count !
  stream-read-field stream-claim ! stream-read-field stream-value !
  stream-count @ 0= stream-count @ lf-term-capacity > or if
    lf-load-abort -1 throw
  then
  stream-count @ 0 do
    stream-read-field stream-read-field stream-read-field stream-read-field
    lf-load-node 0= if -1 throw then
  loop
  stream-byte 1 stdin read-file throw 0<> if lf-load-abort -1 throw then
  lf-load-finish 0= if -1 throw then
  stream-claim @ stream-value @ 50000 lf-declaration-probe . cr
  stream-count @ 0 do
    i . i lf-term-read 0= if -1 throw then
    >r >r . r> . r> . cr
  loop ;
stream-probe
bye
