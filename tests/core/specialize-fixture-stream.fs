\ Test-only data stream for specializing exported universe levels. Fields are
\ little-endian nonnegative signed-32-bit integers, never Forth source. This
\ stages one concrete instance and runs an untrusted declaration diagnostic;
\ it does not import, register, or prove the polymorphic theorem.
include ../../src/experimental/declaration-probe.fs
include ../../src/experimental/load.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/level-value.fs
decimal
create sp-byte 1 allot
variable sp-level-count
variable sp-term-count
variable sp-claim
variable sp-value
variable sp-context-count
variable sp-assignment-count
variable sp-index
variable sp-tag
variable sp-first
variable sp-second

\ Read one required byte or abort the untrusted staging transaction.
: sp-byte@ ( -- byte )
  sp-byte 1 stdin read-file throw 1 <> if lf-load-abort -1 throw then sp-byte c@ ;

\ Read a portable, nonnegative signed-32-bit field without cell overflow.
: sp-field ( -- number )
  sp-byte@ sp-byte@ 8 lshift or sp-byte@ 16 lshift or
  sp-byte@ dup 128 >= if 2drop lf-load-abort -1 throw then 24 lshift or ;

\ Decode one bounded symbolic level row; zero is already allocated.
: sp-level ( -- )
  sp-field sp-index ! sp-field sp-tag ! sp-field sp-first ! sp-field sp-second !
  sp-tag @ lf-level-tag-zero = if
    sp-index @ sp-first @ or sp-second @ or if -1 throw then exit
  then
  sp-tag @ case
    lf-level-tag-succ of
      sp-second @ if -1 throw then sp-first @ lf-level-succ
    endof
    lf-level-tag-param of
      sp-second @ if -1 throw then sp-first @ lf-level-param
    endof
    lf-level-tag-max of sp-first @ sp-second @ lf-level-max endof
    lf-level-tag-imax of sp-first @ sp-second @ lf-level-imax endof
    -1 throw
  endcase
  0= if -1 throw then sp-index @ <> if -1 throw then ;

\ Decode an expression row. A sort's first field is a level-table index;
\ its explicit assignment must evaluate successfully before staging.
: sp-term ( -- )
  sp-field sp-index ! sp-field sp-tag ! sp-field sp-first ! sp-field sp-second !
  sp-tag @ lf-tag-sort = if
    sp-first @ 50000 lf-level-value-assigned
    if drop lf-load-abort -1 throw then sp-first !
  then
  sp-index @ sp-tag @ sp-first @ sp-second @ lf-load-node
  0= if -1 throw then ;

\ Header: level count, term count, claim, value, context count, assignment
\ count. Then context IDs, level rows, assignment pairs, and expression rows.
: sp-run ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  sp-field sp-level-count ! sp-field sp-term-count ! sp-field sp-claim ! sp-field sp-value !
  sp-field sp-context-count ! sp-field sp-assignment-count !
  sp-level-count @ 1 < sp-level-count @ lf-level-capacity > or
  sp-term-count @ 1 < or sp-term-count @ lf-term-capacity > or
  sp-context-count @ lf-level-capacity > or sp-assignment-count @ lf-level-capacity > or
  sp-context-count @ sp-assignment-count @ <> or
  if -1 throw then
  sp-context-count @ 0 ?do sp-field lf-lscope-context-add 0= if -1 throw then loop
  sp-level-count @ 0 do
    sp-level lf-level-count @ i 0= if 1 else i 1+ then <> if -1 throw then
  loop
  lf-lassign-reset
  sp-assignment-count @ 0 ?do sp-field sp-field lf-lassign-add 0= if -1 throw then loop
  lf-load-begin 0= if -1 throw then
  sp-term-count @ 0 do sp-term loop
  sp-byte 1 stdin read-file throw 0<> if lf-load-abort -1 throw then
  lf-load-finish 0= if -1 throw then
  sp-claim @ sp-value @ 50000 lf-declaration-probe . cr
  \ Emit the specialized syntax so tests can check the actual level mapping.
  sp-term-count @ 0 do
    i . i lf-term-read 0= if -1 throw then
    >r >r . r> . r> . cr
  loop ;
sp-run
bye
