\ Test-only binary bridge for one small decoded Lean fixture. Each record is
\ four unsigned bytes: local index, tag, first field, second field. This is
\ not a public serialization format, parser, declaration checker or proof API.
\ Input is data read from stdin; it is never evaluated as Forth source.
include ../../src/experimental/infer.fs
include ../../src/experimental/load.fs
decimal
create fixture-byte 1 allot

\ Read one byte. EOF is represented by false; any I/O error throws.
: fixture-read-byte ( -- byte true | false )
  fixture-byte 1 stdin read-file throw
  0= if false exit then fixture-byte c@ true ;

\ A record that ends partway through is an error, not a shorter batch.
: fixture-required-byte ( -- byte )
  fixture-read-byte 0= if lf-load-abort -1 throw then ;

\ Stage all records and exercise experimental inference on the fixture's
\ value and claim. These fixed indices are specific to the test fixture, and
\ a matching result does not register or establish validity of a theorem.
: fixture-load-stream ( -- )
  lf-term-reset lf-load-begin 0= if -1 throw then
  begin fixture-read-byte while
    fixture-required-byte fixture-required-byte fixture-required-byte
    lf-load-node 0= if -1 throw then
  repeat
  lf-term-count @ 0= if lf-load-abort -1 throw then
  lf-load-finish 0= if -1 throw then
  lf-term-count @ 21 <> if -1 throw then
  20 50000 lf-infer dup if 2drop -1 throw then drop
  10 50000 lf-compare lf-compare-equal <> if -1 throw then
  \ Inference appends scratch nodes; print only the 21 decoded input nodes.
  21 0 do
    i . i lf-term-read 0= if -1 throw then
    >r >r . r> . r> . cr
  loop ;
fixture-load-stream
bye
