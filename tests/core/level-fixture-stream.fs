\ Test-only byte stream for staging a small symbolic level DAG from preview.
\ Bytes are data, never executable Forth. This is not a public serialization,
\ importer, trusted scope checker, level equality algorithm or theorem interface.
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
decimal
create level-stream-byte 1 allot
variable level-stream-count
variable level-stream-index
variable level-stream-tag
variable level-stream-first
variable level-stream-second

\ Read a required byte or stop without emitting a partial table.
: level-stream-byte@ ( -- byte )
  level-stream-byte 1 stdin read-file throw
  1 <> if -1 throw then level-stream-byte c@ ;

\ Validate and allocate the current row. Zero is preallocated by reset.
: level-stream-add ( -- )
  level-stream-tag @ lf-level-tag-zero = if
    level-stream-index @ level-stream-first @ or level-stream-second @ or
    if -1 throw then exit
  then
  level-stream-tag @ case
    lf-level-tag-succ of
      level-stream-second @ if -1 throw then
      level-stream-first @ lf-level-succ
    endof
    lf-level-tag-param of
      level-stream-second @ if -1 throw then
      level-stream-first @ lf-level-param
    endof
    lf-level-tag-max of
      level-stream-first @ level-stream-second @ lf-level-max
    endof
    lf-level-tag-imax of
      level-stream-first @ level-stream-second @ lf-level-imax
    endof
    -1 throw
  endcase
  0= if -1 throw then
  level-stream-index @ <> if -1 throw then ;

\ Read a byte-sized context, stage the table, then structurally check its last
\ root. Context IDs are opaque, not verified Lean names. No partial table is
\ printed if the stream or check fails.
: level-stream-run ( -- )
  lf-level-reset lf-lscope-context-reset
  level-stream-byte@ dup 1 < over lf-level-capacity > or if drop -1 throw then
  level-stream-count !
  level-stream-byte@ dup lf-level-capacity > if drop -1 throw then
  0 ?do level-stream-byte@ lf-lscope-context-add 0= if -1 throw then loop
  level-stream-count @ 0 do
    level-stream-byte@ dup i <> if drop -1 throw then level-stream-index !
    level-stream-byte@ level-stream-tag !
    level-stream-byte@ level-stream-first !
    level-stream-byte@ level-stream-second !
    i 0= level-stream-tag @ lf-level-tag-zero <> and if -1 throw then
    level-stream-add
  loop
  level-stream-byte 1 stdin read-file throw 0<> if -1 throw then
  lf-level-count @ level-stream-count @ <> if -1 throw then
  level-stream-count @ 1- 10000 lf-lscope-check lf-lscope-ok <> if -1 throw then
  level-stream-count @ 0 do
    i . i lf-level-read 0= if -1 throw then
    >r >r . r> . r> . cr
  loop ;
level-stream-run
bye
