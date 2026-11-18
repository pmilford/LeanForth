\ Heap blocks held in a cell: claimed, zeroed, resized, released. A
\ general tool with no Lean knowledge; untrusted. Written for the
\ modules that each wrote "allocate at least one unit, erase it, store
\ its address, else full" or "resize the block, or allocate it when the
\ cell is empty" by hand (library audit 2026-11-13, action 6; plan
\ 9.4.8b); heap-claim and heap-release moved here from bytes.fs, which
\ requires this file, so their callers keep them.
\
\ The method. A block is named by the cell that holds its address (0:
\ none), so a record's fields hold its blocks and one word frees each.
\ block-zeroed allocates u address units (at least one, so a count of 0
\ still gives a block to free), erases them and stores the address;
\ block-resize resizes the cell's block to u units, or allocates one
\ when the cell holds none, and stores the new address. Both leave the
\ cell as it was when the heap refuses (full), so a caller's earlier
\ block is neither lost nor freed. heap-release frees the cell's block,
\ if any, and zeroes the cell, so releasing twice is harmless.
\
\ Genericity: any size; the caller's cell may be a record field, a
\ variable or a context member. Cost: one ALLOCATE or RESIZE, plus the
\ erase's u units for block-zeroed; no state of its own.
\
\ Example:
\   variable buf  0 buf !
\   100 buf block-zeroed .  buf @ 99 + c@ .     \ 0 0: ok, zeroed
\   200 buf block-resize .                      \ 0: ok, the first 100 kept
\   buf heap-release  buf @ .  buf heap-release  \ 0: freed, then nothing
\   64 heap-claim . free .                      \ -1 0: a block as a flag
\   \ prints: 0 0 0 0 -1 0
\
\ Interface: heap-claim heap-release allocate0 block-zeroed block-resize
\ block-reused block-free. State:
\ none. Requires outcome.fs; no helpers.

require ./outcome.fs

\ Heap memory as a flag: true with the address, or false alone.
: heap-claim ( u -- addr true | false ) allocate if drop false else true then ;
\ Free the heap block whose address is in the cell at a-addr, if there is
\ one, and zero the cell.
: heap-release ( a-addr -- ) dup @ ?dup if free drop then 0 swap ! ;
\ A new block of u address units (at least one), zeroed, its address
\ stored at a-addr: ok, or full with the cell unchanged. The cell's
\ earlier block, if any, is not freed (heap-release it first).
\ ALLOCATE u zeroed address units: the address and 0, or an undefined
\ address and the ior (moved here from store.fs; store.fs, htab.fs,
\ context.fs, task.fs and the modules use it).
: allocate0 ( u -- addr ior ) dup allocate ?dup if rot drop exit then tuck swap erase 0 ;
: block-zeroed ( u a-addr -- outcome )
  swap 1 max allocate0 if 2drop outcome-full exit then swap ! outcome-ok ;
\ The cell's block resized to u address units (at least one), or a new
\ block when the cell holds 0; the units kept as RESIZE keeps them, any
\ new ones not erased. ok, or full with the cell and its block unchanged.
: block-resize ( u a-addr -- outcome )
  >r 1 max r@ @ ?dup if swap resize else allocate then
  if drop r> drop outcome-full else r> ! outcome-ok then ;
\ A module's block of u units kept for reuse: the cell's block erased
\ when it holds one (made earlier with the same u), else a new zeroed
\ one: true, or false when the heap refuses (the cell then unchanged).
: block-reused ( u a-addr -- flag )
  dup @ ?dup if nip swap erase true exit then block-zeroed ok? ;
\ Free the cell's block, if any, and zero the cell: 0, or FREE's ior
\ with the cell unchanged, so that a later call tries again.
: block-free ( a-addr -- ior )
  dup @ ?dup 0= if drop 0 exit then free dup 0= if over 0 swap ! then nip ;
