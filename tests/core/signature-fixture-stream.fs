\ Untrusted test transport and raw signature specialization; no declaration checking.
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/legacy/raw-declaration-index.fs
include ../../src/kernel/level-substitute.fs
include ../../src/legacy/term-level-substitute.fs
include ../../src/legacy/raw-signature-specialize.fs
include ../../src/kernel/level-value.fs
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

create formals 1 cells allot
create actuals 2 cells allot
variable token-n
variable result-n
: must ( flag -- ) 0= if -1 throw then ;
: status-invalid ( status -- ) lf-rspec-invalid = must ;
: output-node ( index -- )
  dup . lf-term-read must
  rot dup lf-tag-symbolic-sort = if
    . drop 10000 lf-level-value if drop -1 then . 0 .
  else . swap . . then cr ;
: run-stream ( -- )
  lf-name-reset lf-term-reset lf-level-reset lf-lscope-context-reset
  0 s" poly_identity" lf-name-str must 1 = must
  field-in count-n ! field-in claim-n ! field-in value-n ! field-in param-id !
  count-n @ 0= count-n @ lf-term-capacity > or if -1 throw then
  param-id @ lf-lscope-context-add must
  param-id @ lf-hlevel-param must level-id ! level-index !
  lf-ssession-begin must
  count-n @ 0 do stage-node loop
  input-byte 1 stdin read-file throw 0<> if -1 throw then
  claim-n @ count-n @ >= value-n @ count-n @ >= or if -1 throw then
  lf-rawdecl-begin must
  1 claim-n @ root-handle 10000 lf-rawdecl-put lf-rawdecl-ok = must
  lf-rspec-begin must lf-rawdecl-token must token-n !
  param-id @ formals !
  token-n @ 1 claim-n @ root-handle formals 1 10000 lf-rspec-put lf-rspec-ok = must
  lf-hlevel-zero must actuals cell+ ! actuals !
  token-n @ 1+ 1 actuals 1 10000 lf-rspec-specialize status-invalid
  token-n @ 1 actuals 0 10000 lf-rspec-specialize status-invalid
  token-n @ 1 actuals 2 10000 lf-rspec-specialize status-invalid
  actuals cell+ @ 1+ actuals cell+ !
  token-n @ 1 actuals 1 10000 lf-rspec-specialize status-invalid
  lf-hlevel-zero must actuals cell+ ! actuals !
  2 0 do
    token-n @ 1 actuals 1 10000 lf-rspec-specialize lf-rspec-ok = must
    drop result-n !
    i . result-n @ . lf-term-count @ . cr
    lf-term-count @ 0 do i output-node loop
    actuals @ actuals cell+ @ lf-hlevel-succ must actuals cell+ ! actuals !
  loop
  lf-rawdecl-begin must
  token-n @ 1 actuals 1 10000 lf-rspec-specialize status-invalid ;
run-stream
bye
