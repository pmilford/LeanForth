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
\ Watched blocks, for showing that a module never frees a block it only
\ reads (another context's): heap-watch-block adds one (0, no block, is
\ not added; at most heap-watch-most), heap-watched-frees counts the FREEs
\ given a watched block since, and heap-unwatch forgets the blocks and
\ the count.

variable live-blocks               \ blocks allocated and not yet freed
variable last-freed                \ the address most recently freed
variable heap-refusals             \ the allocation that fails: 1, 2, ...; 0 none
: heap-refused? ( -- flag )
  heap-refusals @ dup 0= if exit then 1- dup heap-refusals ! 0= ;
16 constant heap-watch-most
create heap-watched heap-watch-most cells allot
variable heap-watched#             \ blocks watched
variable heap-watched-frees        \ FREEs given a watched block
: heap-unwatch ( -- ) 0 heap-watched# ! 0 heap-watched-frees ! ;
heap-unwatch
: heap-watch-block ( addr -- )
  ?dup 0= if exit then
  heap-watched# @ heap-watch-most = abort" heap-watch: too many blocks"
  heap-watched heap-watched# @ cells + ! 1 heap-watched# +! ;
: heap-watched? ( addr -- flag )
  false heap-watched# @ 0 ?do over heap-watched i cells + @ = or loop nip ;
: heap-watch-free ( addr -- addr ) dup heap-watched? if 1 heap-watched-frees +! then ;
wordlist constant heap-watch
get-current heap-watch set-current
: allocate ( u -- addr ior )
  heap-refused? if drop 0 -59 exit then allocate dup 0= if 1 live-blocks +! then ;
: free ( addr -- ior )
  heap-watch-free dup last-freed ! free dup 0= if -1 live-blocks +! then ;
: resize ( addr u -- addr' ior ) heap-refused? if drop -59 exit then resize ;
set-current
get-order heap-watch swap 1+ set-order
