\ Driver for tests/lib/test_json_write.py: reads lines of Forth from
\ standard input and evaluates each under HEX, so that the writer runs
\ whatever BASE is (the generated lines write numbers with a # prefix).
\ Each line writes one case between case-start and case-end, which prints
\ the bytes the writer gave its sink, a tab and the outcome's name on one
\ line; written JSON never holds a raw tab or line feed. Gforth only
\ (stdin), like the other test drivers.
require ../../src/lib/json-write.fs

64 4096 json-writer: dw
json: dv
64 dv json-init drop
: case-start ( -- ) ['] type dw jw-start ;
: case-end ( -- ) dw jw-end 9 emit outcome-text type cr ;
: sorted ( -- ) true dw jw-sorted ! ;
: unsorted ( -- ) false dw jw-sorted ! ;
\ Parse a JSON text with json.fs and copy its value with jw-copy.
: copy-text ( c-addr u -- )
  dv json-parse dup ok? if drop 0 dv dw jw-copy else ." parse " outcome-text type then ;

1048576 constant line-size
create case-line line-size allot
: dw-next-line ( -- c-addr u flag ) case-line dup line-size stdin read-line throw ;
: run-cases ( -- ) begin dw-next-line while hex evaluate decimal repeat 2drop ;
