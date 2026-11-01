\ Execute actual host PUSH literals, DUP and + on the data stack. This finite
\ test is untrusted and is not a verifier or a proof of host semantics.
\ Values start within [-3,7]; at most five additions/doublings keep their
\ magnitude below 224, within the Forth-2012 minimum signed cell range.
\ Only this isolated test owns the data stack; it starts with depth zero.
decimal
variable pv-length
variable pv-index
variable pv-seed
variable pv-number
variable pv-count
variable pv-failed

\ ( -- ) Place the selected modeled initial stack on the actual data stack.
: pv-initial ( -- )
  pv-seed @ case
    0 of endof
    1 of -3 endof
    2 of -1 2 endof
    3 of 7 3 -2 endof
    -1 throw
  endcase ;

\ ( opcode -- ) The opcode is removed before DEPTH is inspected. Underflow
\ sets failure and never executes the offending host word.
: pv-step ( opcode -- )
  case
    0 of -2 endof
    1 of 0 endof
    2 of 3 endof
    3 of depth 1 < if true pv-failed ! else dup then endof
    4 of depth 2 < if true pv-failed ! else + then endof
    -1 throw
  endcase ;

\ ( -- ) Output modeled stack top first or fail; discard any partial stack.
: pv-run ( -- )
  false pv-failed ! pv-index @ pv-number ! pv-initial
  pv-length @ 0 ?do
    pv-number @ 5 /mod pv-number ! pv-step
    pv-failed @ if leave then
  loop
  pv-failed @ if
    s" fail" type cr
  else
    s" ok " type depth dup . 0 ?do i pick . loop cr
  then
  depth 0 ?do drop loop ;

: pv-table ( -- )
  depth 0<> abort" expected empty data stack"
  1 pv-count !
  6 0 do
    i pv-length !
    pv-count @ 0 ?do
      i pv-index !
      4 0 do
        i pv-seed !
        pv-length @ . pv-index @ . pv-seed @ . pv-run
      loop
    loop
    pv-count @ 5 * pv-count !
  loop ;
pv-table
bye
