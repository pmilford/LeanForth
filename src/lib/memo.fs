\ Keyed memo tables: a map from keys of a fixed number of cells to values
\ of a fixed number of cells, for remembering results (a pass's result per
\ node and offset, a cache of types, an index's ordinal). A general tool
\ with no Lean knowledge; untrusted. Written for the checker's three
\ hand-written memos (src/kernel/caches.fs, replace-memo.fs and
\ src/import/ndjson.fs's index maps; library audit 2026-11-13, action 2).
\
\ The method. A memo's entries, each its key's cells then its value's,
\ live in a slab (slab.fs) and are found through an open-addressing hash
\ table (htab.fs) whose hooks hash and compare the key cells: every key
\ cell is mixed in by its low 32 bits, and its high bits too when any are
\ set (hash32.fs), so 32- and 64-bit hosts find the same entries and two
\ keys that differ only in their high bits do not collide. The table
\ doubles before it is 3/4 full and the slab doubles as it fills, so a
\ find or a put costs a few probes whatever the size, and the memory is
\ about (key + value cells + 1) cells and 4 bytes of slots per entry
\ (between 1.3 and 2.7 slots per entry). A key is compared cell by cell,
\ never as bytes; a hash is only a hint.
\
\ Genericity. The caller chooses the key's cells (at least one) and the
\ value's (none, for a set of keys); keys are given by address
\ (memo-find, memo-put) or, for keys of one or two cells, on the stack
\ (memo-at, memo-claim, memo@, memo!; a memo of one key cell reads only
\ k1). Two optional hooks fit callers that keep results which may go
\ stale or whose memory is metered: check ( a-addr -- flag ), given a
\ found entry's value cells, says whether the value still holds (else the
\ find is a miss; memo-put still finds the entry, to write over it); admit
\ ( memo -- flag ), asked before an entry is added, may refuse it (full).
\ Hooks must not use the memo they serve.
\
\ Outcomes (lib/outcome.fs): memo-init ok, invalid for a key of no cells
\ or a negative or too large shape (nothing made), full when the heap
\ refuses the table (the memo is then not live). memo-put ok; full when
\ the table or the entries cannot grow or admit refuses, nothing changed;
\ invalid for a memo that is not live. A memo that is not live (never
\ made, refused by the heap, freed) finds nothing and holds nothing.
\ Addresses of value cells are valid until the next memo-put, memo-claim
\ or memo! on the memo (the entries' block may move), or memo-cut,
\ memo-clear or memo-empty.
\
\ Emptying. memo-clear takes every entry out and keeps the memory;
\ memo-empty does the same for a small table and makes one of more than
\ memo-small slots small again (its blocks given back), so that emptying
\ often costs little whatever an earlier use needed. memo-cut ( n memo )
\ takes out the entries from the n-th on, newest first (Knuth's
\ Algorithm R in the table), for a caller that forgets what one call
\ kept.
\
\ Example: squares by a key of two cells; a key of three cells by address.
\   create sq /memo allot   2 1 sq memo-init drop
\   49 7 0 sq memo! drop   7 0 sq memo@ . .     \ -1 49
\   8 0 sq memo@ .                              \ 0: no entry
\   create m3 /memo allot   3 2 m3 memo-init drop
\   create key 1 , 2 , 3 ,
\   key m3 memo-put drop  10 over !  20 swap cell+ !
\   key m3 memo-find @ .                        \ 10
\   sq memo-free  m3 memo-free
\
\ Interface: /memo memo-init memo-free memo-live? memo-count memo-bytes
\ memo-find memo-put memo-at memo-claim memo@ memo! memo-clear memo-empty
\ memo-cut memo-check! memo-admit! memo-small. State: none of its own but
\ the table hooks (read-only); every word takes a memo record made by the
\ caller (in the dictionary or inside a larger record), which owns its
\ heap blocks until memo-free. One memo is single-threaded; separate memos
\ are independent. Requires portability.fs, bounds.fs, outcome.fs,
\ u32.fs, hash32.fs, slab.fs, htab.fs and module.fs; helpers are private
\ in lf-lib-private (ADR 0010). Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./bounds.fs
require ./outcome.fs
require ./u32.fs
require ./hash32.fs
require ./slab.fs
require ./htab.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
begin-structure /memo
lf-lib-private set-current
  /htab +field memo-table       \ first: the table's hooks reach the memo from it
  /slab +field memo-entries     \ the entries: key cells, then value cells
  field: memo-kcells            \ a key's cells; 0 in a memo never initialized
  field: memo-vcells            \ a value's cells
  field: memo-check             \ xt ( a-addr -- flag ): a found value holds; or 0
  field: memo-admit             \ xt ( memo -- flag ): an entry may be added; or 0
  2 cells +field memo-probe     \ the key of memo-at and memo-claim while they run
end-structure
4 constant memo-first-log2      \ a new table's slots: 16
lf-lib set-current
1024 constant memo-small        \ memo-empty makes a table of more slots small again
lf-lib-private set-current

\ ---- Entries, keys and their hashes.
: memo-unit ( memo -- au ) dup memo-kcells @ swap memo-vcells @ + cells ;
: memo-entry ( n memo -- a-addr ) memo-entries slab-at ;
: memo-value-at ( n memo -- a-addr ) tuck memo-entry swap memo-kcells @ cells + ;
\ A cell into a hash: its low 32 bits, then its high bits when any is set
\ (two shifts: one by the cell's width would be ambiguous on a 32-bit host).
: memo-mix ( h x -- h' ) tuck hash-step swap 16 rshift 16 rshift ?dup if hash-step then ;
: memo-hash ( key memo -- h )
  0 swap memo-kcells @ 0 ?do over i cells + @ memo-mix loop nip ;
: memo-cells= ( a-addr1 a-addr2 n -- flag )
  0 ?do over i cells + @ over i cells + @ <> if 2drop false unloop exit then loop
  2drop true ;
\ The table's hooks: entry n's hash, and whether its key is the one at key
\ (the table is the memo's first field, so htab is the memo).
: memo-rehash ( n htab -- h ) tuck memo-entry swap memo-hash ;
: memo-same ( n key htab -- flag ) >r swap r@ memo-entry r> memo-kcells @ memo-cells= ;
create memo-hooks /htab-hooks allot   ' memo-rehash ' memo-same memo-hooks htab-hooks!

\ ---- Making and freeing. A shape: a key of at least one cell, a value of
\ none or more, an entry's cells within a cell's count of address units.
: memo-shape? ( kcells vcells -- flag )
  over 1 max-n cell / between? if swap max-n cell / swap - upto? else 2drop false then ;
: memo-shape! ( kcells vcells memo -- ) tuck memo-vcells ! memo-kcells ! ;
\ The slab (no heap yet; its shape is sound, so slab-init gives ok), then
\ the table of 16 slots: ok, or full with no block.
: memo-slab ( memo -- ) dup memo-unit dup slab-limit-max rot memo-entries slab-init drop ;
: memo-make ( memo -- outcome )
  dup memo-slab memo-first-log2 memo-hooks rot memo-table htab-init ;
: memo-release ( memo -- ) dup memo-table htab-free memo-entries slab-free ;
lf-lib set-current
\ Format a record as an empty memo of keys of kcells cells and values of
\ vcells cells, with its table made: ok; full when the heap refuses (the
\ memo not live, holding nothing); invalid for a bad shape. It must not be
\ given a memo that holds memory: memo-free first.
: memo-init ( kcells vcells memo -- outcome )
  dup /memo erase >r 2dup memo-shape? 0= if 2drop r> drop outcome-invalid exit then
  r@ memo-shape! r> memo-make ;
\ Free the blocks; the record is zero, not live.
: memo-free ( memo -- ) dup memo-release /memo erase ;
: memo-live? ( memo -- flag ) dup memo-table htab-live? swap memo-entries slab-live? and ;
\ Entries held (0 when not live), and address units held.
: memo-count ( memo -- n ) dup memo-live? if memo-entries slab-count else drop 0 then ;
: memo-bytes ( memo -- u )
  dup memo-live? 0= if drop 0 exit then
  dup memo-table htab-slots u32s swap memo-entries slab-bytes + ;
\ The hooks (see the header); 0 for none.
: memo-check! ( xt memo -- ) memo-check ! ;
: memo-admit! ( xt memo -- ) memo-admit ! ;
lf-lib-private set-current

\ ---- Finding: entry n, or the empty slot i where key belongs.
: memo-look ( key memo -- n true | i false ) 2dup memo-hash swap memo-table htab-find ;
: memo-valid? ( a-addr memo -- flag ) memo-check @ ?dup if execute else drop true then ;
: memo-found ( n memo -- a-addr | 0 )
  tuck memo-value-at tuck swap memo-valid? 0= if drop 0 then ;
lf-lib set-current
\ The value cells of the entry of the key at key (kcells cells), or 0 for
\ none, a value the check hook refuses, or a memo that is not live.
: memo-find ( key memo -- a-addr | 0 )
  dup memo-live? 0= if 2drop 0 exit then
  tuck memo-look if swap memo-found else 2drop 0 then ;
lf-lib-private set-current

\ ---- Putting. A new entry n at the table's empty slot i: the key copied,
\ the value cells zero.
: memo-admitted? ( memo -- flag ) dup memo-admit @ ?dup if execute else drop true then ;
: memo-key! ( key n memo -- ) tuck memo-entry swap memo-kcells @ cells move ;
: memo-blank ( n memo -- ) tuck memo-value-at swap memo-vcells @ cells erase ;
: memo-enter ( key i n memo -- a-addr )
  >r tuck swap r@ memo-table htab-put dup r@ memo-blank tuck r@ memo-key!
  r> memo-value-at ;
: memo-add ( key i memo -- a-addr outcome )
  dup memo-admitted? 0= if drop 2drop 0 outcome-full exit then
  1 over memo-entries slab-claim ok-then? 0= if >r drop 2drop 0 r> exit then
  swap memo-enter outcome-ok ;
: memo-place ( key memo -- a-addr outcome )
  2dup memo-look if rot drop swap memo-value-at outcome-ok else swap memo-add then ;
lf-lib set-current
\ The value cells of key's entry, found (whatever the check hook says) or
\ added, for the caller to write: a-addr and ok; or 0 and full (no room,
\ or admit refused) or invalid (not live), nothing changed.
: memo-put ( key memo -- a-addr outcome )
  dup memo-live? 0= if 2drop 0 outcome-invalid exit then
  dup memo-table htab-ready ok-then? 0= if nip 0 swap exit then
  memo-place ;
lf-lib-private set-current

\ ---- Keys of one or two cells on the stack.
: memo-probe! ( k1 k2 memo -- key memo ) dup >r memo-probe tuck cell+ ! tuck ! r> ;
lf-lib set-current
: memo-at ( k1 k2 memo -- a-addr | 0 ) memo-probe! memo-find ;
: memo-claim ( k1 k2 memo -- a-addr outcome ) memo-probe! memo-put ;
\ A memo with at least one value cell: the first value cell of (k1 k2).
: memo@ ( k1 k2 memo -- x true | false ) memo-at dup if @ true then ;
: memo! ( x k1 k2 memo -- outcome ) memo-claim ok-then? if ! outcome-ok else nip then ;
lf-lib-private set-current

\ ---- Emptying. The newest entry out of the table and the slab.
: memo-small? ( memo -- flag ) memo-table htab-slots memo-small > 0= ;
: memo-remake ( memo -- ) dup memo-release memo-make drop ;
: memo-last ( memo -- n ) memo-entries slab-count 1- ;
: memo-drop-last ( memo -- )
  dup memo-last swap 2dup memo-rehash swap >r r@ memo-table htab-remove drop
  -1 r> memo-entries slab-commit ;
lf-lib set-current
\ Every entry out, the memory kept (nothing for a memo that is not live).
: memo-clear ( memo -- )
  dup memo-live? 0= if drop exit then dup memo-table htab-clear memo-entries slab-clear ;
\ Every entry out; a table of more than memo-small slots is made again at
\ its first size and its blocks given back (a heap that refuses the new
\ table leaves the memo not live). The shape and hooks stay.
: memo-empty ( memo -- )
  dup memo-live? 0= if drop exit then
  dup memo-small? if memo-clear else memo-remake then ;
\ Take out the entries from the n-th on, newest first.
: memo-cut ( n memo -- )
  swap 0 max swap begin 2dup memo-count < while dup memo-drop-last repeat 2drop ;

module-close
base !   \ the BASE this file was loaded with
