\ Tagged nodes: records of a tag and two fields, the record shape of the
\ term and level stores. Requires: store.fs. No state of its own.

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
\ Read an allocated node; an invalid index returns only false, unread.
: node-read ( index store -- tag first second true | false )
  2dup store-valid? if store-slot node@ true else 2drop false then ;
