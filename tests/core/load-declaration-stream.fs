\ Test-only byte protocol for staged declarations. The first three bytes are
\ node count, claim index, and value index; each following node is four bytes
\ (index, tag, first, second). This is not a public format or theorem API.
\ Input is read as data; no input bytes are evaluated as Forth source.
include ../../src/experimental/declaration-probe.fs
include ../../src/experimental/load.fs
decimal
create stream-byte 1 allot
variable stream-count
variable stream-claim
variable stream-value

\ Read one required byte and abort on EOF or host I/O error.
: stream-read-byte ( -- byte )
  stream-byte 1 stdin read-file throw
  1 <> if lf-load-abort -1 throw then stream-byte c@ ;

\ Stage exactly the declared number of nodes, reject trailing data, and emit
\ only the untrusted probe status. A status of zero never registers a theorem.
: stream-probe ( -- )
  lf-term-reset lf-load-begin 0= if -1 throw then
  stream-read-byte stream-count !
  stream-read-byte stream-claim ! stream-read-byte stream-value !
  stream-count @ 0= stream-count @ lf-term-capacity > or if
    lf-load-abort -1 throw
  then
  stream-count @ 0 do
    stream-read-byte stream-read-byte stream-read-byte stream-read-byte
    lf-load-node 0= if -1 throw then
  loop
  stream-byte 1 stdin read-file throw 0<> if lf-load-abort -1 throw then
  lf-load-finish 0= if -1 throw then
  stream-claim @ stream-value @ 50000 lf-declaration-probe . cr ;
stream-probe
bye
