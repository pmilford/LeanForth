\ Tagged nodes: records of a tag and two fields, the record shape of the
\ term and level stores. No state of its own.
\ Example: two nodes in a store of four, the second read back.
\   4 /node 0 store: nodes
\   1 10 20 nodes node-new drop .  2 0 1 nodes node-new drop .
\   1 nodes node-read . . . .   9 nodes node-read .   \ prints: 0 1 -1 1 0 2 0

require ./portability.fs
require ./store.fs

begin-structure /node
  field: node-tag
  field: node-first
  field: node-second
end-structure

\ Store or fetch a whole node at addr, in stack-picture order.
: node! ( tag first second addr -- ) tuck node-second ! tuck node-first ! node-tag ! ;
: node@ ( addr -- tag first second ) dup node-tag @ over node-first @ rot node-second @ ;

\ Append a node to a store of /node records. The caller has validated the
\ tag and fields; a failed allocation (see store-new) changes nothing.
: node-new ( tag first second store -- index true | false )
  store-new-slot if >r node! r> true else 2drop drop false then ;
\ Read an allocated node; an index the store does not hold returns only
\ false, unread. Only the index is checked (store-at?: index < count <=
\ capacity), not the rest of the header: a pass checks that once, at its
\ root (store-count-valid?), so every visit of a walk costs one range
\ check (compact-store plan step S2).
: node-read ( index store -- tag first second true | false )
  2dup store-at? if store-slot node@ true else 2drop false then ;
