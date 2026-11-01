\ Test-only little-endian signed-31-bit fields: count, claim, value, parameter
\ ID, then (index, tag, first, second) per node. Sort payloads are 0 (zero)
\ or 1 (the parameter). Input is data, never evaluated as Forth. A successful
\ structural check, inference or diagnostic is not theorem acceptance. Exit
\ zero means the stream was processed; consumers must inspect status fields.
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs
include ../../src/experimental/tagged-compare.fs
include ../../src/experimental/tagged-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/tagged-convert.fs
include ../../src/experimental/tagged-infer.fs
include ../../src/experimental/tagged-declaration-probe.fs
decimal
create input-byte 1 allot
create identities lf-term-capacity cells allot
variable count-n
variable claim-n
variable value-n
variable param-id
variable level-index
variable level-id
variable node-index
variable node-tag
variable first-n
variable second-n
variable level-start

: byte-in ( -- u )
  input-byte 1 stdin read-file throw 1 <> if -1 throw then input-byte c@ ;
: field-in ( -- u )
  byte-in byte-in 8 lshift or byte-in 16 lshift or
  byte-in dup 128 >= if 2drop -1 throw then 24 lshift or ;
: handle-at ( index -- index identity )
  dup node-index @ >= if -1 throw then dup cells identities + @ ;
: stage-node ( -- )
  field-in node-index ! field-in node-tag !
  field-in first-n ! field-in second-n !
  node-index @ lf-term-count @ <> if -1 throw then
  node-tag @ 1 = if
    second-n @ 0<> if -1 throw then
    first-n @ 0 = if lf-hlevel-zero else
      first-n @ 1 <> if -1 throw then level-index @ level-id @ true
    then
    0= if -1 throw then lf-hterm-sort
  else node-tag @ 2 = if
    second-n @ 0<> if -1 throw then first-n @ lf-hterm-bvar
  else
    first-n @ handle-at second-n @ handle-at
    node-tag @ case
      3 of lf-hterm-app endof
      4 of lf-hterm-lam endof
      5 of lf-hterm-pi endof
      -1 throw
    endcase
  then then
  0= if -1 throw then
  node-index @ cells identities + ! node-index @ <> if -1 throw then ;
: root-handle ( index -- index identity )
  dup count-n @ >= if -1 throw then dup cells identities + @ ;
: run-stream ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  field-in count-n ! field-in claim-n ! field-in value-n ! field-in param-id !
  count-n @ 0= count-n @ lf-term-capacity > or if -1 throw then
  param-id @ lf-lscope-context-add 0= if -1 throw then
  param-id @ lf-hlevel-param 0= if -1 throw then level-id ! level-index !
  lf-ssession-begin 0= if -1 throw then
  count-n @ 0 do stage-node loop
  lf-level-count @ level-start !
  input-byte 1 stdin read-file throw 0<> if -1 throw then
  claim-n @ count-n @ >= value-n @ count-n @ >= or if -1 throw then
  claim-n @ root-handle 50000 lf-hterm-check .
  value-n @ root-handle 50000 lf-hterm-check . cr
  count-n @ 0 do
    i . i lf-term-read 0= if -1 throw then >r >r . r> . r> . cr
  loop
  claim-n @ root-handle 50000 lf-tinfer . 2drop
  count-n @ lf-term-count ! level-start @ lf-level-count !
  value-n @ root-handle 50000 lf-tinfer . 2drop
  count-n @ lf-term-count ! level-start @ lf-level-count !
  claim-n @ root-handle value-n @ root-handle 100000 lf-tagged-declaration-probe . cr ;
run-stream
bye
