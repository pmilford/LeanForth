\ Development-only stack-depth diagnostic for the Lean reference Op list.
\ This is untrusted: it neither proves nor executes a program. PUSH's value
\ is irrelevant to depth and is deliberately absent from this representation.
\ An opcode array is a contiguous, aligned array of cells with these tags.
\ The caller must supply genuinely readable allocated storage and its capacity;
\ Forth cannot validate allocation, ownership, or concurrent mutation.
\ ALIGNED is a Forth-2012 CORE word, but applying it to arbitrary fabricated
\ addresses and detecting address wrap assume a flat, cell-sized address
\ representation. Portability to other address models has not been tested.
\ Requires ../lib/lib.fs (loaded here). State: none; every value is on the
\ stack, so the analyzer is re-entrant.

decimal
require ../lib/lib.fs

0 constant lf-depth-push
1 constant lf-depth-dup
2 constant lf-depth-add

\ Largest nonnegative signed cell, without overflowing signed arithmetic.
max-n constant lf-depth-max

\ One reverse transfer: the depth a program needs before an opcode, given
\ the depth it needs after it. Reject negative depth, unknown tags and
\ overflow.
: lf-depth-before-add ( depth -- depth' true | 0 false )
  dup lf-depth-max = if drop 0 false else 1+ 2 max true then ;
: lf-depth-transfer ( depth opcode -- depth' true | 0 false )
  case lf-depth-push of 1- 0 max true endof
    lf-depth-dup of 1- 1 max true endof
    lf-depth-add of lf-depth-before-add endof
    >r drop 0 false r> endcase ;
: lf-depth-step ( depth opcode -- depth' true | 0 false )
  over 0< if 2drop 0 false else lf-depth-transfer then ;

\ Validation before any array read. The count must fit both the capacity
\ and the fuel, so no size can be negative. Nonempty storage must be a
\ nonnull aligned address whose byte size fits a signed cell and whose
\ exclusive end address does not wrap an unsigned cell. capacity is in
\ cells, not bytes, and only a claim, not a memory-safety guarantee.
: lf-depth-count? ( capacity count fuel -- count flag ) rot min over swap upto? ;
: lf-depth-address? ( addr -- flag ) dup 0<> swap dup aligned = and ;
: lf-depth-fits? ( addr count -- flag )
  dup lf-depth-max 1 cells / > if 2drop false else cells over + swap u< 0= then ;
: lf-depth-storage? ( addr count -- flag )
  over lf-depth-address? if lf-depth-fits? else 2drop false then ;

\ Step back from depth 0 through the tags from last to first.
: lf-depth-op ( addr i -- opcode ) cells + @ ;
: lf-depth-fold ( addr count -- depth true | 0 false )
  0 0 rot 1- do over i lf-depth-op lf-depth-step 0= if nip false unloop exit then
  -1 +loop nip true ;
: lf-depth-run ( addr count -- depth true | 0 false )
  dup 0= if 2drop 0 true exit then
  2dup lf-depth-storage? if lf-depth-fold else 2drop 0 false then ;

\ Analyze the first count tags in reverse; fuel bounds the number of reads.
\ Reject negative sizes, count beyond capacity or fuel, misalignment, null
\ nonempty storage, and address/offset overflow before any array read. Empty
\ arrays need no storage.
: lf-program-required-depth ( addr capacity count fuel -- depth true | 0 false )
  lf-depth-count? if lf-depth-run else 2drop 0 false then ;
