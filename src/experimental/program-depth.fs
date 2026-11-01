\ Development-only stack-depth diagnostic for the Lean reference Op list.
\ This is untrusted: it neither proves nor executes a program. PUSH's value
\ is irrelevant to depth and is deliberately absent from this representation.
\ An opcode array is a contiguous, aligned array of cells with these tags.
\ The caller must supply genuinely readable allocated storage and its capacity;
\ Forth cannot validate allocation, ownership, or concurrent mutation.
\ ALIGNED is a Forth-2012 CORE word, but applying it to arbitrary fabricated
\ addresses and detecting address wrap assume a flat, cell-sized address
\ representation. Portability to other address models has not been tested.
\ Scratch variables make the analyzer single-threaded and non-reentrant.

decimal
0 constant lf-depth-push
1 constant lf-depth-dup
2 constant lf-depth-add

\ Largest nonnegative signed cell, without overflowing signed arithmetic.
-1 1 rshift constant lf-depth-max

\ ( depth opcode -- depth' true | 0 false )
\ One reverse transfer. Reject negative depth, unknown tags and overflow.
: lf-depth-step ( depth opcode -- result ok )
  over 0< if 2drop 0 false exit then
  dup lf-depth-push = if drop 1- 0 max true exit then
  dup lf-depth-dup = if drop 1- 1 max true exit then
  lf-depth-add = if
    dup lf-depth-max = if drop 0 false exit then
    1+ 2 max true exit
  then
  drop 0 false ;

\ Private scratch storage; callers must not modify it during analysis.
variable lf-depth-addr
variable lf-depth-capacity
variable lf-depth-count
variable lf-depth-fuel
variable lf-depth-result

\ ( addr capacity count fuel -- depth true | 0 false )
\ Analyze the first count tags in reverse; fuel bounds the number of reads.
\ Reject negative sizes, count beyond capacity or fuel, misalignment, null
\ nonempty storage, and address/offset overflow before any array read. Empty
\ arrays need no storage. capacity is in cells, not bytes. A caller-supplied
\ capacity is only a claim, not a memory-safety guarantee.
: lf-program-required-depth ( addr capacity count fuel -- result ok )
  lf-depth-fuel ! lf-depth-count ! lf-depth-capacity ! lf-depth-addr !
  lf-depth-capacity @ 0< lf-depth-count @ 0< or lf-depth-fuel @ 0< or
  if 0 false exit then
  lf-depth-count @ lf-depth-capacity @ >
  lf-depth-count @ lf-depth-fuel @ > or if 0 false exit then
  lf-depth-count @ 0= if 0 true exit then
  lf-depth-addr @ 0= if 0 false exit then
  lf-depth-addr @ aligned lf-depth-addr @ <> if 0 false exit then
  lf-depth-count @ lf-depth-max 1 cells / > if 0 false exit then
  \ Check the exclusive end address does not wrap an unsigned cell.
  lf-depth-addr @ lf-depth-count @ cells + lf-depth-addr @ u<
  if 0 false exit then
  0 lf-depth-result !
  lf-depth-count @ 0 do
    lf-depth-result @
    lf-depth-addr @ lf-depth-count @ 1- i - cells + @ lf-depth-step
    0= if drop 0 false unloop exit then
    lf-depth-result !
  loop
  lf-depth-result @ true ;
