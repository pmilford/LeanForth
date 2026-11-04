\ Growable heap stores (plan task 1.1.5; ADR 0016 C3, C5). A slab is an
\ array of units of a fixed size (records, 32-bit fields or bytes) in one
\ heap block that grows by doubling with RESIZE up to a limit, with a
\ count of units in use, a reset generation and marks. A general tool with
\ no Lean knowledge; untrusted. The growable counterpart of store.fs's
\ store:, with the same kind of checks and outcomes (ADR 0008):
\
\ - ok;
\ - full when the limit would be passed or the heap has no room: a failed
\   ALLOCATE or RESIZE leaves the slab unchanged (Forth-2012 RESIZE keeps
\   the old region), never a crash;
\ - invalid for a corrupted or poisoned slab, a negative size or a stale
\   mark: the checked words test, before they form an address, a check
\   value sealing the shape (unit and limit, fixed by slab-init) and the
\   block and its capacity (resealed whenever the block grows), 0 <= count
\   <= capacity, and a generation >= 0. So corrupting any one of those
\   fields fails closed.
\
\ Units are numbered from 0. Addresses: slab-at gives a unit's address,
\ valid only until the next word that may grow the slab (slab-room,
\ slab-claim, slab-reserve): keep numbers, never addresses, across them
\ (plan 6.3). Units past the count are free space: a caller may build a
\ candidate record there (slab-top) after slab-room and then either keep
\ it with slab-commit or leave it. RESIZE keeps their contents.
\
\ Marks work as store.fs's store-mark and store-rollback: slab-rollback to
\ a mark gives back every unit claimed since, and refuses, with invalid
\ and nothing changed, a mark of another slab, of another generation (a
\ slab-clear since), of a poisoned slab, or one that is stale because an
\ earlier rollback went below it. A slab has no per-unit identities;
\ instead it keeps a stack of marked counts (ADR 0016 C3), strictly
\ increasing, each with a serial that never repeats: a mark is valid
\ exactly while its entry is on the stack. A rollback pops the entries
\ above its own; marks taken at the same count share one entry, so the
\ stack never holds more entries than distinct counts. The generation
\ grows by one per slab-clear and saturates to -1, poisoned, as store.fs's
\ does; a spent mark serial makes slab-mark full.
\
\ Example: a byte pool of at most 1 MB, a text kept in it, and a rollback.
\   create pool /slab allot    create here-mark /slab-mark allot
\   1 chars 1048576 pool slab-init drop
\   here-mark pool slab-mark drop
\   s" Nat" dup pool slab-claim drop pool slab-at swap move    \ units 0 .. 2
\   here-mark pool slab-rollback drop    \ the count is 0 again
\   pool slab-free
\
\ Interface: /slab slab-init slab-free slab-live? slab-valid? slab-count
\ slab-capacity slab-limit slab-unit slab-at slab-top slab-room
\ slab-reserve slab-claim slab-commit slab-trim slab-clear slab-bytes
\ slab-used-bytes slab-limit-max slab-offset
\ slab-generation /slab-mark slab-mark slab-mark-valid? slab-rollback
\ slab-mark-count. State: none of its own; every word takes a slab record
\ made by the caller (in the dictionary or inside a larger record) and a
\ slab owns its heap blocks until slab-free. One slab is single-threaded;
\ separate slabs are independent. Its memory is host-specific and never
\ written to a file. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./bounds.fs
require ./outcome.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
begin-structure /slab
lf-lib-private set-current
  field: slab-block          \ the heap block, or 0 before any capacity
  field: slab-room-units     \ units the block holds: the capacity
  field: slab-used           \ units in use, 0 .. used-1
  field: slab-unit-size      \ address units per unit (shape)
  field: slab-most           \ most units ever (shape): the limit
  field: slab-seal           \ check value of the shape
  field: slab-epoch          \ clears so far; -1 once poisoned
  field: slab-marks          \ heap block of the mark stack, or 0
  field: slab-marks-room     \ entries it holds
  field: slab-depth          \ entries in use
  field: slab-serial         \ last mark serial issued
end-structure

\ A mark-stack entry: a marked count and its serial (in this order, so 2@
\ and 2! copy both to and from a mark's slab-mark-count).
begin-structure /mark-entry
  field: mark-entry-count
  field: mark-entry-serial
end-structure

lf-lib set-current
begin-structure /slab-mark
  field: slab-mark-slab      \ the slab marked; 0 when marking failed
  field: slab-mark-epoch     \ its generation then
  field: slab-mark-entry     \ its entry's position on the mark stack
  field: slab-mark-count     \ the count marked; then its entry's serial
  field: slab-mark-serial
end-structure
lf-lib-private set-current

16 constant slab-min-units   \ the first capacity, unless more is asked for
8 constant slab-min-marks

lf-lib set-current
: slab-count ( slab -- n ) slab-used @ ;
: slab-capacity ( slab -- n ) slab-room-units @ ;
: slab-limit ( slab -- n ) slab-most @ ;
: slab-unit ( slab -- au ) slab-unit-size @ ;
: slab-generation ( slab -- n ) slab-epoch @ ;
lf-lib-private set-current

\ The seal: a check value of the shape, the block and its capacity. Every
\ word that changes one of them reseals.
: slab-check ( slab -- x )
  dup slab-unit over slab-limit xor over slab-block @ xor swap slab-capacity xor invert ;
: slab-reseal ( slab -- ) dup slab-check swap slab-seal ! ;
: slab-sealed? ( slab -- flag ) dup slab-check swap slab-seal @ = ;
: slab-block! ( addr units slab -- ) tuck slab-room-units ! tuck slab-block !
  slab-reseal ;
\ A sound shape: a positive unit and 0 <= limit, small enough that limit
\ units fit in a cell of address units.
: slab-plan? ( unit limit -- flag )
  over 0> if swap max-n swap / upto? else 2drop false then ;

lf-lib set-current
\ Whether the slab may be used: not poisoned, sealed, 0 <= count <=
\ capacity.
: slab-live? ( slab -- flag )
  dup slab-generation 0< 0= over slab-sealed? and swap dup slab-count swap slab-capacity
  upto? and ;
\ Whether unit i is in use, 0 <= i < count, in a live slab.
: slab-valid? ( i slab -- flag )
  dup slab-live? if slab-count 0 swap within else 2drop false then ;
\ Unchecked: the address of unit i, and of the first free unit.
: slab-at ( i slab -- addr ) tuck slab-unit * swap slab-block @ + ;
\ Unit 0's address, for callers that step through units themselves.
: slab-base ( slab -- addr ) slab-block @ ;
: slab-top ( slab -- addr ) dup slab-count swap slab-at ;
\ Address units held, and in use.
: slab-bytes ( slab -- u ) dup slab-capacity swap slab-unit * ;
: slab-used-bytes ( slab -- u ) dup slab-count swap slab-unit * ;
\ The largest limit a slab of units of unit address units may have.
: slab-limit-max ( unit -- n ) 1 max max-n swap / ;
\ Where addr lies in the slab's block, in address units from its start; or
\ -1 when it lies outside. An address inside moves when the block grows:
\ keep the offset across slab-room and find the address again with it.
: slab-offset ( addr slab -- offset | -1 )
  swap over slab-block @ - tuck swap slab-bytes u< 0= if drop -1 then ;

\ Making and freeing. slab-init formats an unused record as an empty slab
\ of units of unit address units and at most limit units: ok, or invalid
\ for an unsound shape (the record is then zero, which no check accepts).
\ It allocates nothing; the first slab-room does. It must not be given a
\ slab that holds memory: slab-free first. slab-free frees the blocks and
\ zeroes the record.
: slab-init ( unit limit slab -- outcome )
  dup /slab erase >r 2dup slab-plan? 0= if r> drop 2drop outcome-invalid exit then
  r@ slab-most ! r@ slab-unit-size ! r> slab-reseal outcome-ok ;
lf-lib-private set-current
: slab-release ( addr -- ) ?dup if free drop then ;
lf-lib set-current
: slab-free ( slab -- ) dup slab-block @ slab-release dup slab-marks @ slab-release
  /slab erase ;
lf-lib-private set-current

\ Growth. ALLOCATE the first block, RESIZE the others; on failure the old
\ block stays as it was and the result is full.
: slab-heap ( u addr -- addr' ior ) ?dup if swap resize else allocate then ;
: slab-resize ( units slab -- outcome )
  2dup slab-unit * over slab-block @ slab-heap
  if drop 2drop outcome-full else -rot slab-block! outcome-ok then ;
\ The capacity to grow to for n more units: at least what they need,
\ double the old capacity, slab-min-units, and never past the limit.
\ Doubling adds the smaller of the capacity and the room left, so it
\ cannot overflow.
: slab-doubled ( slab -- units ) dup slab-capacity dup rot slab-limit over - min + ;
: slab-target ( n slab -- units )
  tuck slab-count + over slab-doubled max slab-min-units max swap slab-limit min ;
\ Whether n more units fit the capacity, and the limit; n >= 0.
: slab-has? ( n slab -- flag ) dup slab-capacity swap slab-count - 0 swap between? ;
: slab-allowed? ( n slab -- flag ) dup slab-limit swap slab-count - 0 swap between? ;
: slab-bad? ( n slab -- flag ) slab-live? 0= swap 0< or ;
: slab-grow ( n slab -- outcome )
  2dup slab-allowed? if tuck slab-target swap slab-resize else 2drop outcome-full then ;

lf-lib set-current
\ Make room for n more units: ok (the count is unchanged), full, or invalid
\ for a negative n or a slab that is not live.
: slab-room ( n slab -- outcome )
  2dup slab-bad? if 2drop outcome-invalid exit then
  2dup slab-has? if 2drop outcome-ok else slab-grow then ;
\ Grow the capacity to at least n units, for example to pre-size a slab.
: slab-reserve ( n slab -- outcome ) tuck slab-count - 0 max swap slab-room ;
\ Room for n units in all, from unit 0, for a slab used as an array whose
\ count stays 0: ok at once when it holds them, else as slab-reserve.
: slab-hold ( n slab -- outcome )
  2dup slab-capacity > if slab-reserve else 2drop outcome-ok then ;
\ Unchecked: count n more units in use; slab-room n gave ok since.
: slab-commit ( n slab -- ) slab-used +! ;
\ Claim n units: the number of the first and ok, or -1 and the outcome of
\ slab-room.
: slab-claim ( n slab -- i outcome )
  2dup slab-room dup ok? if drop dup slab-count -rot slab-commit outcome-ok
  else nip nip no-result then ;
\ Shrink the block to the units in use (at least one), for a slab that is
\ complete: ok, full when RESIZE fails (nothing changed), or invalid.
: slab-trim ( slab -- outcome )
  dup slab-live? 0= if drop outcome-invalid exit then
  dup slab-count 1 max over slab-capacity = if drop outcome-ok exit then
  dup slab-count 1 max swap slab-resize ;
lf-lib-private set-current

\ Clearing: the count and the mark stack go to 0 and the generation grows
\ by one, saturating to -1 (poisoned), which stays.
: slab-epoch+ ( generation -- generation' )
  dup 0< if exit then dup max-n = if drop -1 else 1+ then ;
lf-lib set-current
: slab-clear ( slab -- )
  0 over slab-used ! 0 over slab-depth ! slab-epoch dup @ slab-epoch+ swap ! ;
lf-lib-private set-current

\ The mark stack. Entry k (from 0, the oldest) is at slab-entry.
: slab-entry ( k slab -- entry ) slab-marks @ swap /mark-entry * + ;
: slab-newest ( slab -- entry ) dup slab-depth @ 1- swap slab-entry ;
: mark-entry! ( count serial entry -- ) tuck mark-entry-serial ! mark-entry-count ! ;
\ Whether the newest entry marks the current count.
: slab-marked? ( slab -- flag )
  dup slab-depth @ if dup slab-newest mark-entry-count @ swap slab-count =
  else drop false then ;
: slab-marks-grow ( slab -- outcome )
  >r r@ slab-marks-room @ 2* slab-min-marks max dup /mark-entry * r@ slab-marks @
  slab-heap
  if 2drop r> drop outcome-full else r@ slab-marks ! r> slab-marks-room ! outcome-ok
  then ;
: slab-marks-ready ( slab -- outcome )
  dup slab-depth @ over slab-marks-room @ < if drop outcome-ok else slab-marks-grow then ;
: slab-serial+ ( slab -- serial ) slab-serial 1 over +! @ ;
\ Unchecked: push an entry for the current count; there is room.
: slab-push ( slab -- )
  >r r@ slab-count r@ slab-serial+ r@ dup slab-depth @ swap slab-entry mark-entry!
  1 r> slab-depth +! ;
: slab-new-entry ( slab -- outcome )
  dup slab-serial @ max-n = if drop outcome-full exit then
  dup slab-marks-ready dup ok? if drop slab-push outcome-ok else nip then ;
\ An entry for the current count on top of the stack.
: slab-entry-ready ( slab -- outcome )
  dup slab-marked? if drop outcome-ok else slab-new-entry then ;
\ Fill the mark from the newest entry.
: slab-mark-set ( mark slab -- )
  swap >r dup r@ slab-mark-slab ! dup slab-generation r@ slab-mark-epoch !
  dup slab-depth @ 1- r@ slab-mark-entry ! slab-newest 2@ r> slab-mark-count 2! ;

lf-lib set-current
\ Record where a live slab's count stands: ok; or, with a mark every
\ rollback refuses, invalid for a slab that is not live and full when the
\ mark stack cannot grow or the serial is spent.
: slab-mark ( mark slab -- outcome )
  dup slab-live? 0= if drop /slab-mark erase outcome-invalid exit then
  dup slab-entry-ready dup ok? if drop slab-mark-set outcome-ok
  else nip swap /slab-mark erase then ;
lf-lib-private set-current

\ Checks of a mark against a slab.
: slab-mark-this? ( mark slab -- flag )
  2dup swap slab-mark-slab @ = >r dup slab-live? >r
  slab-generation swap slab-mark-epoch @ = r> r> and and ;
\ Its entry is on the stack and the count marked is not above the count.
: slab-mark-held? ( mark slab -- flag )
  2dup swap slab-mark-entry @ swap slab-depth @ 0 swap within >r
  slab-count swap slab-mark-count @ swap upto? r> and ;
: slab-mark-same? ( mark slab -- flag )
  over >r swap slab-mark-entry @ swap slab-entry 2@ r> slab-mark-count 2@ d= ;

lf-lib set-current
\ Whether slab-rollback would accept the mark now.
: slab-mark-valid? ( mark slab -- flag )
  2dup slab-mark-this? 0= if 2drop false exit then
  2dup slab-mark-held? if slab-mark-same? else 2drop false then ;
\ Roll the slab back to the mark: ok, or invalid with nothing changed.
: slab-rollback ( mark slab -- outcome )
  2dup slab-mark-valid? 0= if 2drop outcome-invalid exit then
  over slab-mark-count @ over slab-used ! swap slab-mark-entry @ 1+ swap slab-depth !
  outcome-ok ;

module-close
base !   \ the BASE this file was loaded with
