\ Open-addressing hash tables of 32-bit slots (ADR 0016 C4). A general tool
\ with no Lean knowledge; untrusted. A table indexes records that live
\ elsewhere and are named by numbers 0 .. 2^32-2: a slot holds a record's
\ number plus one, 0 when empty. The table does not store keys or hashes;
\ the owner gives two hooks, in a /htab-hooks record:
\
\   rehash ( n htab -- h )        the hash of entry n, recomputed from its record
\   same ( n key htab -- flag )   whether entry n is equal to the key
\
\ Each hook is given the table's address, so an owner that puts the table
\ first in its own record reaches its records from it (cons.fs does).
\
\ Linear probing in a power-of-two number of slots; a hash is only a hint,
\ and an entry is found only when same says so. htab-ready doubles the
\ table, re-inserting every entry by its recomputed hash, before an
\ insertion would make it more than 3/4 full, so a probe always ends at an
\ empty slot. htab-remove deletes an entry with Knuth's Algorithm R (TAOCP
\ 6.4), moving later entries of its run back into the hole, so every other
\ entry stays findable, whatever the order of insertions and growth.
\ htab-spread rebuilds the table at the smallest power of two at most half
\ full (ADR 0016 C4 seals the input's tables that way: a miss reads every
\ occupied slot of its run). Statistics count finds, occupied slots
\ compared and doublings.
\
\ Outcomes (ADR 0008): full when the slots would pass the table's limit
\ (htab-limit, at most 2^32 slots, fewer where a cell cannot address them)
\ or the heap has no room, the table then unchanged; invalid for an entry
\ that is not present, and for any change to a frozen table. A table is
\ single-threaded while it changes. A find counts itself in the table's
\ statistics, a write; once htab-freeze has frozen the table, finds write
\ nothing, so any number of tasks may find in it at once.
\
\ Example (with hash32.fs): distinct numbers below 2^32 kept in an array,
\ found by value.
\   require lib/hash32.fs
\   create values 100 cells allot   create seen /htab allot
\   create hooks /htab-hooks allot
\   : value@ ( n -- x ) cells values + @ ;
\   : rehash ( n htab -- h ) drop value@ hash-fmix ;
\   : same ( n key htab -- flag ) drop swap value@ = ;
\   ' rehash ' same hooks htab-hooks!
\   4 hooks seen htab-init drop
\   : add ( x n -- )   \ make x value n, unless x is already present
\     seen htab-ready drop  over dup hash-fmix seen htab-find
\     if 2drop drop else >r tuck cells values + ! r> seen htab-put then ;
\   7 0 add  9 1 add  7 2 add                \ 7 is there already
\   seen htab-count .  9 dup hash-fmix seen htab-find . .  seen htab-free
\   \ prints: 2 -1 1
\
\ Interface: /htab /htab-hooks hook-rehash hook-same htab-hooks! htab-init
\ htab-free htab-limit htab-find htab-ready htab-put htab-remove htab-holds? htab-clear
\ htab-small-slots htab-small? htab-renew htab-presize
\ htab-spread htab-freeze htab-frozen? htab-live?
\ htab-count htab-slots htab-base htab-stats. State: none of its own; every word
\ takes a table record, which owns its slot block until htab-free. Its
\ memory is host-specific and never written to a file. Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./bounds.fs
require ./outcome.fs
require ./u32.fs
require ./bits.fs
require ./blocks.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
begin-structure /htab-hooks
  field: hook-rehash        \ xt ( n htab -- h )
  field: hook-same          \ xt ( n key htab -- flag )
end-structure
\ Fill a hooks record.
: htab-hooks! ( rehash same hooks -- ) tuck hook-same ! hook-rehash ! ;

begin-structure /htab
lf-lib-private set-current
  field: htab-block         \ heap block of the slots, or 0
  field: htab-log2          \ log2 of the number of slots
  field: htab-mask          \ slots - 1
  field: htab-entries       \ entries
  field: htab-most          \ most slots allowed, as a power of two
  field: htab-hooks         \ the owner's hooks
  field: htab-finds         \ statistics: finds
  field: htab-compared      \ statistics: occupied slots compared by finds
  field: htab-grows         \ statistics: doublings by htab-ready
  field: htab-frozen        \ true once frozen: read-only, not even counted
end-structure

\ The largest log2 of slots: 32, or fewer when a cell cannot address the
\ slots' bytes (a 32-bit host).
cell-bits 3 - 32 min constant htab-log2-max

lf-lib set-current
: htab-count ( htab -- n ) htab-entries @ ;
: htab-slots ( htab -- n ) htab-mask @ 1+ ;
\ The slots' block, or 0: a new one after any growth, htab-spread or
\ htab-renew (a reader of the slots in place, such as another task, watches it).
: htab-base ( htab -- addr ) htab-block @ ;
\ Finds, occupied slots compared by them, and doublings so far (a frozen
\ table counts nothing).
: htab-stats ( htab -- finds compared grows )
  dup htab-finds @ over htab-compared @ rot htab-grows @ ;
: htab-frozen? ( htab -- flag ) htab-frozen @ ;
lf-lib-private set-current
\ Whether the size fields agree: 2^log2 slots, log2 within the host's.
: htab-shape? ( htab -- flag )
  dup htab-log2 @ dup 0 htab-log2-max between?
  if 1 swap lshift swap htab-slots = else 2drop false then ;
\ Add n to a statistic, unless the table is frozen.
: htab-tally ( n addr htab -- ) htab-frozen? if 2drop else +! then ;
lf-lib set-current
\ Whether the table may be used: a block, sizes that agree, and at least
\ one empty slot (so every probe ends).
: htab-live? ( htab -- flag )
  dup htab-block @ 0<> over htab-shape? and swap dup htab-count swap htab-slots u< and ;
lf-lib-private set-current

\ Slots. Unchecked: i is 0 .. slots-1.
: htab-slot ( i htab -- addr ) htab-block @ swap u32s + ;
: htab@ ( i htab -- v ) htab-slot u32@ ;
: htab-start ( h htab -- i ) htab-mask @ and ;
: htab-next ( i htab -- i' ) swap 1+ swap htab-mask @ and ;
: htab-rehash ( n htab -- h ) dup htab-hooks @ hook-rehash @ execute ;
: htab-same ( n key htab -- flag ) dup htab-hooks @ hook-same @ execute ;
\ The first empty slot from h's start.
: htab-empty ( h htab -- i )
  >r r@ htab-start begin dup r@ htab@ while r@ htab-next repeat r> drop ;

lf-lib set-current
\ Find the entry equal to key, starting at hash h: its number and true, or
\ the empty slot where it belongs and false. Counts the find and the
\ occupied slots compared, unless the table is frozen: a find in a frozen
\ table writes nothing, so any number of tasks may find in it at once.
: htab-find ( key h htab -- n true | i false )
  dup >r 1 over htab-finds r> htab-tally rot >r >r r@ htab-start
  begin dup r@ htab@ ?dup while
    1 r@ htab-compared r@ htab-tally 1- dup 2r@ htab-same if nip 2r> 2drop true exit then
    drop r@ htab-next
  repeat 2r> 2drop false ;
\ Unchecked: put entry n into the empty slot i that htab-find gave, with
\ no htab-ready, htab-remove or other insertion since.
: htab-put ( n i htab -- ) 1 over htab-entries +! htab-slot swap 1+ swap u32! ;
lf-lib-private set-current

\ Rebuilding. A new block of 2^log2 zeroed slots replaces the old one,
\ whose entries are then placed by their recomputed hashes.
: htab-zeroed ( slots -- addr ior ) u32s allocate0 ;
: htab-install ( addr log2 htab -- old slots )
  >r r@ htab-block @ r@ htab-slots 2swap
  dup r@ htab-log2 ! 1 swap lshift 1- r@ htab-mask ! r> htab-block ! ;
: htab-place ( v htab -- ) >r dup 1- r@ htab-rehash r@ htab-empty r> htab-slot u32! ;
: htab-move ( old slots htab -- )
  swap 0 ?do over i u32s + u32@ ?dup if over htab-place then loop 2drop ;
\ Whether 2^log2 slots are allowed and hold the entries at most 3/4 full.
: htab-fits? ( log2 htab -- flag )
  2dup htab-most @ upto? if htab-count 4 * 1 rot lshift 3 * <= else 2drop false then ;
: htab-resize ( log2 htab -- outcome )
  dup htab-frozen? if 2drop outcome-invalid exit then
  2dup htab-fits? 0= if 2drop outcome-full exit then
  over 1 swap lshift htab-zeroed if drop 2drop outcome-full exit then
  -rot dup >r htab-install over swap r> htab-move ?dup if free drop then outcome-ok ;

lf-lib set-current
\ Make an empty table of 2^log2 slots with the hooks, allowed to grow to
\ the largest size the host allows: ok, or full (no heap, or log2 beyond
\ that size) with no block. It must not be given a table that holds a
\ block: htab-free first.
: htab-init ( log2 hooks htab -- outcome )
  dup /htab erase tuck htab-hooks ! -1 over htab-mask ! htab-log2-max over htab-most !
  htab-resize ;
\ Allow at most 2^log2 slots (log2 >= 0), for example in tests.
: htab-limit ( log2 htab -- ) swap htab-log2-max min 0 max swap htab-most ! ;
: htab-free ( htab -- ) dup htab-block @ ?dup if free drop then /htab erase ;
\ Empty the table, keeping its size; a frozen table is left as it is.
: htab-clear ( htab -- )
  dup htab-frozen? if drop exit then
  0 over htab-entries ! dup htab-block @ swap htab-slots u32s erase ;
\ Empty a table that a run may have grown: clear it while it is live with
\ at most htab-small-slots slots, else free it and make it again with
\ xt ( -- ), so that a table one large run doubled does not keep its
\ block, and its clearing cost, for every later run. The cut-over is the
\ one constant of every table reset (memo.fs's memo-small is the same).
1024 constant htab-small-slots
: htab-small? ( htab -- flag )
  dup htab-live? if htab-slots htab-small-slots <= else drop false then ;
: htab-renew ( htab xt -- )
  over htab-small? if drop htab-clear else swap htab-free execute then ;
\ Freeze the table: from now on it only finds (htab-find, htab-holds?),
\ writing nothing, and every word that would change it refuses (invalid)
\ or, for htab-clear, does nothing. A sealed input's tables are frozen.
: htab-freeze ( htab -- ) true swap htab-frozen ! ;
\ Before an insertion: double the table if one more entry would make it
\ more than 3/4 full. ok, full with the table unchanged, or invalid for a
\ frozen table.
: htab-ready ( htab -- outcome )
  dup htab-frozen? if drop outcome-invalid exit then
  dup htab-count 1+ 4 * over htab-slots 3 * <= if drop outcome-ok exit then
  1 over htab-grows +! dup htab-log2 @ 1+ swap htab-resize ;
\ Grow to 2^log2 slots now, when that is more than the table has, so that
\ a known number of insertions does not rehash: ok, or full unchanged.
: htab-presize ( log2 htab -- outcome )
  2dup htab-log2 @ > if htab-resize else 2drop outcome-ok then ;
\ Rebuild at the smallest power of two at most half full (at least 16
\ slots); ok, or full with the table unchanged.
: htab-spread ( htab -- outcome )
  dup htab-count 2* 16 max log2-ceiling 2dup swap htab-log2 @ =
  if 2drop outcome-ok else swap htab-resize then ;
lf-lib-private set-current

\ Algorithm R. The entry at slot j may stay when its home slot is
\ cyclically in (hole, j]; otherwise it moves into the hole, which moves
\ to j. The run's last hole is emptied.
: htab-home ( j htab -- k ) tuck htab@ 1- over htab-rehash swap htab-start ;
: htab-stays? ( hole j htab -- flag )
  >r tuck r@ htab-home over - 1- r@ htab-mask @ and -rot - r> htab-mask @ and u< ;
: htab-shift ( hole j htab -- ) tuck htab@ -rot htab-slot u32! ;
: htab-close ( i htab -- )
  >r dup begin r@ htab-next dup r@ htab@ while
    2dup r@ htab-stays? 0= if tuck r@ htab-shift dup then
  repeat drop 0 swap r> htab-slot u32! ;
\ The slot of entry n, searched from hash h: the slot and true, or false
\ when an empty slot ends the run first.
: htab-stop? ( v i htab -- flag ) htab@ tuck = swap 0= or ;
: htab-seek ( n h htab -- i true | false )
  >r r@ htab-start swap 1+ swap
  begin 2dup r@ htab-stop? 0= while r@ htab-next repeat
  tuck r> htab@ = dup 0= if nip then ;

lf-lib set-current
\ Remove entry n, whose hash is h: ok, or invalid when it is not present
\ or the table is frozen.
: htab-remove ( n h htab -- outcome )
  dup htab-frozen? if drop 2drop outcome-invalid exit then
  dup >r htab-seek 0= if r> drop outcome-invalid exit then
  r@ htab-close -1 r> htab-entries +! outcome-ok ;
\ Whether entry n, whose hash is h, is present.
: htab-holds? ( n h htab -- flag ) htab-seek dup if nip then ;

module-close
base !   \ the BASE this file was loaded with
