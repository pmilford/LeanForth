\ Test-only binary bridge for one small decoded Lean fixture. Each record is
\ four unsigned bytes: local index, tag, first field, second field. This is
\ not a public serialization format, parser, declaration checker or proof API.
\ Input is data read from stdin; it is never evaluated as Forth source.
\ It checks the staging round trip of src/import/load.fs only; the current
\ checker examines the same export in tests/core/test_export_definitions.py.
include ../../src/core/terms.fs
include ../../src/import/load.fs
decimal
create fixture-byte 1 allot

\ Read one byte. EOF is represented by false; any I/O error throws.
: fixture-read-byte ( -- byte true | false )
  fixture-byte 1 stdin read-file throw
  0= if false exit then fixture-byte c@ true ;

\ A record that ends partway through is an error, not a shorter batch.
: fixture-required-byte ( -- byte )
  fixture-read-byte 0= if lf-load-abort -1 throw then ;

\ Print one staged node: index, tag, first field, second field.
: fixture-row ( index -- )
  dup . lf-term-read 0= if -1 throw then >r >r . r> . r> . cr ;

\ Stage all records and print the 21 staged nodes of the composition
\ fixture. Staging checks record shape and child order only; nothing here
\ registers or establishes the validity of a theorem.
: fixture-load-stream ( -- )
  lf-term-reset lf-load-begin 0= if -1 throw then
  begin fixture-read-byte while
    fixture-required-byte fixture-required-byte fixture-required-byte
    lf-load-node 0= if -1 throw then
  repeat
  lf-term-count @ 0= if lf-load-abort -1 throw then
  lf-load-finish 0= if -1 throw then
  lf-term-count @ 21 <> if -1 throw then
  21 0 do i fixture-row loop ;
fixture-load-stream
bye
