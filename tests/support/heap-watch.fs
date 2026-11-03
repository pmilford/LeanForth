\ Test-only heap accounting: ALLOCATE and FREE that count the heap blocks
\ held, for showing that a module frees what it allocated. Include before
\ requiring the module under test, so that its words call these. They are
\ defined in their own word list, first in the search order, so the host's
\ words keep their names and no redefinition warning is printed.
\ RESIZE keeps a block's count; it is not counted.

variable live-blocks               \ blocks allocated and not yet freed
variable last-freed                \ the address most recently freed
wordlist constant heap-watch
get-current heap-watch set-current
: allocate ( u -- addr ior ) allocate dup 0= if 1 live-blocks +! then ;
: free ( addr -- ior ) dup last-freed ! free dup 0= if -1 live-blocks +! then ;
set-current
get-order heap-watch swap 1+ set-order
