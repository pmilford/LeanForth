\ Test-only binary bridge for one small decoded Lean fixture. Each record is
\ four unsigned bytes: local index, tag, first field, second field. This is
\ not a public serialization format, parser, declaration checker or proof API.
\ Input is data read from stdin; it is never evaluated as Forth source.
include ../../src/experimental/declaration-probe.fs
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

\ Stage all records and probe the fixture's value and proposition claim.
\ These fixed indices are specific to the test fixture, and
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
  10 20 50000 lf-declaration-probe lf-infer-ok <> if -1 throw then
  \ Print only the 21 decoded input nodes; probe scratch nodes were discarded.
  21 0 do
    i . i lf-term-read 0= if -1 throw then
    >r >r . r> . r> . cr
  loop ;
fixture-load-stream
bye
