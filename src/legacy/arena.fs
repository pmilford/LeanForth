\ Bounded, mutable storage experiment for atom and pair nodes.
\ This is not a Lean expression representation or a proof checker.
\ Each node occupies three cells: a tag followed by payload or child indices.
\ Indices are valid only until reset; this global arena is not thread-safe.

64 constant lf-arena-capacity
3 constant lf-node-cells
create lf-arena lf-arena-capacity lf-node-cells * cells allot
variable lf-arena-count

\ Forget all allocated nodes; previously returned indices become invalid.
: lf-arena-reset ( -- ) 0 lf-arena-count ! ;

\ Return a node's address. Caller must first ensure index is valid.
: lf-node-address ( index -- addr ) lf-node-cells * cells lf-arena + ;

\ Validate the mutable count before using it to calculate an address.
: lf-arena-count-valid? ( -- flag )
  lf-arena-count @ dup 0< 0= swap lf-arena-capacity <= and ;

\ Test whether an index names a node in a valid current allocation range.
\ This cannot detect an index retained across reset and subsequently reused.
: lf-node-valid? ( index -- flag )
  lf-arena-count-valid? 0= if drop false exit then
  dup 0< 0= swap lf-arena-count @ < and ;

\ Allocate an atom with an opaque single-cell payload.
\ Returns index and true, or false when full; failure leaves count unchanged.
: lf-node-atom ( payload -- index true | false )
  lf-arena-count-valid? 0= if drop false exit then
  lf-arena-count @ lf-arena-capacity >= if drop false exit then
  lf-arena-count @ lf-node-address
  1 over ! cell+ !
  lf-arena-count @ 1 lf-arena-count +! true ;

\ Allocate a pair of existing node indices, preserving left-to-right order.
\ Reject invalid indices or a full arena without changing the allocation count.
: lf-node-pair ( left right -- index true | false )
  over lf-node-valid? over lf-node-valid? and 0= if 2drop false exit then
  lf-arena-count @ lf-arena-capacity >= if 2drop false exit then
  lf-arena-count @ lf-node-address
  2 over ! cell+ dup >r cell+ ! r> !
  lf-arena-count @ 1 lf-arena-count +! true ;
