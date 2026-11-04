\ Test-only heap accounting: ALLOCATE and FREE that count the heap blocks
\ held, for showing that a module frees what it allocated. Include before
\ requiring the module under test, so that its words call these. They are
\ defined in their own word list, first in the search order, so the host's
\ words keep their names and no redefinition warning is printed.
\ RESIZE keeps a block's count; it is not counted.
\ heap-refusals fails one allocation: set to k, the k-th ALLOCATE or
\ RESIZE from then on fails with a nonzero ior (-59, ALLOCATE's own;
\ RESIZE keeps the block), as a full heap would; 0 (the start, and after
\ that failure) fails none.

variable live-blocks               \ blocks allocated and not yet freed
variable last-freed                \ the address most recently freed
variable heap-refusals             \ the allocation that fails: 1, 2, ...; 0 none
: heap-refused? ( -- flag )
  heap-refusals @ dup 0= if exit then 1- dup heap-refusals ! 0= ;
wordlist constant heap-watch
get-current heap-watch set-current
: allocate ( u -- addr ior )
  heap-refused? if drop 0 -59 exit then allocate dup 0= if 1 live-blocks +! then ;
: free ( addr -- ior ) dup last-freed ! free dup 0= if -1 live-blocks +! then ;
: resize ( addr u -- addr' ior ) heap-refused? if drop -59 exit then resize ;
set-current
get-order heap-watch swap 1+ set-order
