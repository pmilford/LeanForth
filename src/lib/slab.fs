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
\ Marks work as store.fs's store-mark and store-rollback: slab-rollback
\ to a mark gives back every unit claimed since, and refuses, with
\ invalid and nothing changed, a mark of another slab, of another
\ generation (a slab-clear since), of a poisoned slab, or one that is
\ stale because an earlier rollback went below it. slab-cut
\ ( n slab -- ) is a rollback to a count n the caller kept (a scope's
\ start), with no mark: 0 <= n <= count, else it throws slab-bad-cut (-4133), a fault
\ in the caller, as slab-underflow is; slab-remove ( i slab -- ) takes
\ unit i out of the middle, the later units moved down one and the marks
\ above i refused from then on, with the same refusal. A slab has no
\ per-unit identities; instead it keeps a stack of marked counts (ADR
\ 0016 C3), strictly increasing, each with a
\ serial that never repeats: a mark is valid exactly while its entry is
\ on the stack. A rollback pops the entries above its own; marks taken
\ at the same count share one entry, so the stack never holds more
\ entries than distinct counts. The generation grows by one per
\ slab-clear and saturates to -1, poisoned, as store.fs's does; a spent
\ mark serial makes slab-mark full.
\
\ Stacks: a slab used as a stack keeps one value (units of a cell) or one
\ pair (two cells) per unit, the newest on top: slab-push and slab-pop,
\ slab-2push and slab-2pop, slab-last (the newest unit's address) and
\ slab-drop. A push has slab-claim's outcomes, and is invalid for units
\ too narrow for what it stores; a pop, drop or slab-last of an empty slab
\ throws slab-underflow (-4132), since callers test slab-count first.
\ A worklist: slab-all? and slab-2all? pop a value (pair) and test it,
\ the test pushing more, until the slab is empty or a test says false or
\ fails (flag and outcome).
\
\ Example: a byte pool of at most 1 MB, a text kept in it, and a rollback;
\ then a stack of cells, and a worklist: whether 40 and its halves are
\ all below 100.
\   create pool /slab allot    create here-mark /slab-mark allot
\   1 chars 1048576 pool slab-init drop
\   here-mark pool slab-mark drop
\   s" Nat" dup pool slab-claim drop pool slab-at swap move    \ units 0 .. 2
\   pool slab-data type                  \ Nat: unit 0's address and the count
\   here-mark pool slab-rollback drop    \ the count is 0 again
\   pool slab-free
\   create todo /slab allot   1 cells 1000 todo slab-init drop
\   7 todo slab-push drop  8 todo slab-push drop
\   todo slab-pop . todo slab-pop . todo slab-count .   \ 8 7 0
\   : small? ( n -- flag outcome )
\     dup 100 < swap 2/ ?dup if todo slab-push else outcome-ok then ;
\   40 todo slab-push drop  todo ' small? slab-all? . .   \ 0 (ok) -1 (true)
\   todo slab-free                              \ prints: Nat8 7 0 0 -1
\
\ Interface: /slab slab-init slab-free slab-live? slab-valid? slab-count
\ slab-capacity slab-limit slab-unit slab-at slab-base slab-data slab-top slab-room
\ slab-reserve slab-hold slab-claim slab-commit slab-cut slab-remove
\ slab-bad-cut slab-trim
\ slab-clear slab-bytes slab-used-bytes slab-limit-max slab-offset
\ slab-push slab-pop slab-2push slab-2pop slab-last slab-drop
\ slab-keep slab-restore slab-forget slab-kept
\ slab-underflow slab-all? slab-2all?
\ slab-generation /slab-mark slab-mark slab-mark-valid? slab-rollback, and
\ the mark's fields slab-mark-slab slab-mark-epoch slab-mark-entry
\ slab-mark-count slab-mark-serial. State: none of its own; every word takes a slab record
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
\ The units added since the slab held k (its count less k): a span's
\ length from a mark kept as a count.
: slab-since ( k slab -- n ) slab-count swap - ;
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
  dup slab-live? if slab-count index? else 2drop false then ;
\ Unchecked: the address of unit i, and of the first free unit.
: slab-at ( i slab -- addr ) tuck slab-unit * swap slab-block @ + ;
\ Unit 0's address, for callers that step through units themselves.
: slab-base ( slab -- addr ) slab-block @ ;
\ The units in use: unit 0's address and the count (a block that moves when
\ the slab grows: a reader of the units in place watches both).
: slab-data ( slab -- addr n ) dup slab-base swap slab-count ;
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
-4132 constant slab-underflow   \ THROW code: no newest unit to pop, drop or read
-4133 constant slab-bad-cut     \ THROW code: a cut outside 0 .. count, or of a dead slab
lf-lib-private set-current

\ A stack on a slab: the newest unit is the top, one value or pair to a
\ unit. A unit claimed for a push: its address and ok; or -1 and full (as
\ slab-claim), or invalid for a slab not live (slab-claim checks) or too
\ narrow.
: slab-claim-one ( slab -- addr outcome )
  1 over slab-claim ok-then? if swap slab-at outcome-ok else nip no-result then ;
: slab-claim-wide ( u slab -- addr outcome )
  tuck slab-unit u> if drop outcome-invalid no-result else slab-claim-one then ;
\ Whether the slab has a newest unit of at least u address units: units
\ that wide, and a count in 1 .. capacity. Not the seal and generation
\ again: the push that made the unit checked them, a pop is on the hot
\ path of every walk (review reuse-1a M1), and a bounded count keeps the
\ address inside the block.
: slab-has-top? ( u slab -- flag )
  tuck slab-unit u<= swap dup slab-count swap slab-capacity 1 swap between? and ;
\ The newest unit's address; else throw slab-underflow.
: slab-newest-unit ( u slab -- addr )
  tuck slab-has-top? 0= if slab-underflow throw then dup slab-count 1- swap slab-at ;
\ The newest unit given back, and its address: its contents stay until
\ the next claim.
: slab-shed ( slab -- ) -1 swap slab-used +! ;
: slab-take ( u slab -- addr ) tuck slab-newest-unit swap slab-shed ;

lf-lib set-current
\ Push a cell, or a pair (stored by 2!, so slab-2pop gives x1 x2 back):
\ ok; full when the slab cannot grow; invalid, nothing changed, for a
\ slab that is not live or whose units are narrower than a cell (two).
: slab-push ( x slab -- outcome )
  cell swap slab-claim-wide ok-store ;
: slab-2push ( x1 x2 slab -- outcome )
  2 cells swap slab-claim-wide ok-then? if 2! outcome-ok else nip nip then ;
\ Pop the newest cell or pair; slab-drop gives the newest unit back and
\ slab-last is its address. An empty slab, one whose count is past its
\ capacity or one too narrow throws slab-underflow, nothing changed:
\ callers test slab-count first, so this is a fault in the caller, never
\ an outcome. (A slab that is not live has nothing to pop: every push
\ refuses it, and slab-clear and slab-free empty it.)
: slab-pop ( slab -- x ) cell swap slab-take @ ;
: slab-2pop ( slab -- x1 x2 ) 2 cells swap slab-take 2@ ;
: slab-drop ( slab -- ) 1 swap slab-take drop ;
: slab-last ( slab -- addr ) 1 swap slab-newest-unit ;
lf-lib-private set-current

\ Drains (a worklist): one step run on the newest value or pair popped,
\ the slab and the xt kept below; the loop, on a live slab, until it is
\ empty or ok-true? stops it (outcome.fs); then false and the outcome
\ alone. step is slab-step or slab-2step.
: slab-step ( slab xt -- slab xt flag outcome ) over slab-pop over execute ;
: slab-2step ( slab xt -- slab xt flag outcome ) >r dup slab-2pop r@ execute r> -rot ;
: slab-more? ( slab xt -- slab xt flag ) over slab-count 0> ;
: slab-stop ( slab xt false outcome -- false outcome ) 2swap 2drop ;
: slab-drained ( slab xt step -- flag outcome )
  >r begin slab-more? while r@ execute ok-true? 0= if r> drop slab-stop exit then
  repeat r> drop 2drop true outcome-ok ;
\ A slab that is not live: no step run.
: slab-dead ( slab xt -- false outcome ) 2drop false outcome-invalid ;

lf-lib set-current
\ Whether every value of a worklist passes a test that may push more:
\ xt ( x -- flag outcome ), for slab-2all? ( x1 x2 -- flag outcome ), runs
\ on the newest value (pair) popped until the slab is empty. Below the
\ value lie the slab and, for slab-all?, the xt (slab-2all? keeps its xt
\ on the return stack): the test leaves them untouched (review reuse-1a
\ re-check L). The answer: true and ok; or false and ok at the first
\ false answer, false and the outcome at the first that is not ok, the
\ values not yet tested left on the slab (clear it before the next run).
\ A slab that is not live: false and invalid, no test run. A slab whose
\ units are narrower than a cell (slab-all?) or a pair (slab-2all?)
\ throws slab-underflow, as slab-pop and slab-2pop do. Example in the
\ header.
: slab-all? ( slab xt -- flag outcome )
  over slab-live? if ['] slab-step slab-drained else slab-dead then ;
: slab-2all? ( slab xt -- flag outcome )
  over slab-live? if ['] slab-2step slab-drained else slab-dead then ;
lf-lib-private set-current

\ Clearing: the count and the mark stack go to 0 and the generation grows
\ by one, saturating to -1 (poisoned), which stays.
lf-lib set-current
: slab-clear ( slab -- )
  0 over slab-used ! 0 over slab-depth ! slab-epoch dup @ epoch+ swap ! ;
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
: slab-entry-push ( slab -- )
  >r r@ slab-count r@ slab-serial+ r@ dup slab-depth @ swap slab-entry mark-entry!
  1 r> slab-depth +! ;
: slab-new-entry ( slab -- outcome )
  dup slab-serial @ max-n = if drop outcome-full exit then
  dup slab-marks-ready dup ok? if drop slab-entry-push outcome-ok else nip then ;
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
  2dup swap slab-mark-entry @ swap slab-depth @ index? >r
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
lf-lib-private set-current

\ Cutting back to a count n the caller kept (0 <= n <= count): a
\ rollback without a mark. The mark entries above n go, so their marks
\ are refused from then on, as after a rollback below them.
: slab-cut? ( n slab -- flag ) dup slab-live? if slab-count upto? else 2drop false then ;
: slab-marked-above? ( n slab -- flag )
  dup slab-depth @ if slab-newest mark-entry-count @ < else 2drop false then ;
: slab-unmark-above ( n slab -- )
  begin 2dup slab-marked-above? while -1 over slab-depth +! repeat 2drop ;

lf-lib set-current
\ The count back to n: the units from n on given back (their contents
\ stay until the next claim). A slab that is not live, or n outside 0 ..
\ count, throws slab-bad-cut (-4133), nothing changed: n is a count the
\ caller kept, so this is a fault in the caller, never an outcome.
: slab-cut ( n slab -- )
  2dup slab-cut? 0= if slab-bad-cut throw then 2dup slab-unmark-above slab-used ! ;
lf-lib-private set-current

\ Copies kept as a stack (a choice point's saved state): slab-keep
\ ( slab store -- outcome ) pushes onto store, a slab of the same unit at
\ least a cell wide, a copy of slab's units and then one unit whose first
\ cell is their count, in one claim: ok; full, or invalid for another
\ unit, store unchanged. slab-restore ( slab store -- outcome ) makes
\ slab's units the newest copy's and drops it (full when slab cannot hold
\ them again; the copy is dropped all the same); slab-forget ( store -- )
\ drops it; slab-kept ( undo? slab store -- outcome ) restores (true) or
\ forgets (false, ok). With no copy kept they throw slab-underflow,
\ nothing changed.
: slab-same-unit? ( slab store -- flag )
  slab-unit swap slab-unit over = swap cell < 0= and ;
: slab-count-after ( slab addr -- ) over slab-used-bytes + swap slab-count swap ! ;
: slab-in-use ( slab -- addr u ) dup slab-base swap slab-used-bytes ;
: slab-copy-in ( slab addr -- ) 2dup slab-count-after swap slab-in-use rot swap move ;
: slab-kept-first ( store -- i ) dup slab-count 1- swap slab-last @ - ;
lf-lib set-current
: slab-forget ( store -- ) dup slab-kept-first swap slab-cut ;
lf-lib-private set-current
: slab-kept-at ( store -- addr ) dup slab-kept-first swap slab-at ;
: slab-restored ( store slab -- ) over slab-kept-at swap slab-in-use move slab-forget ;
\ Slab emptied, then as many units claimed as the newest copy holds (its
\ count read first: with no copy, slab-underflow and nothing changed).
: slab-refill ( slab store -- slab store i outcome )
  2dup slab-last @ over 0 swap slab-cut swap slab-claim ;
lf-lib set-current
: slab-keep ( slab store -- outcome )
  2dup slab-same-unit? 0= if 2drop outcome-invalid exit then
  over slab-count 1+ over slab-claim ok-then? 0= if nip nip exit then
  swap slab-at slab-copy-in outcome-ok ;
: slab-restore ( slab store -- outcome )
  slab-refill ok-then? 0= if swap slab-forget nip exit then
  drop swap slab-restored outcome-ok ;
: slab-kept ( undo? slab store -- outcome )
  rot if slab-restore else nip slab-forget outcome-ok then ;
lf-lib-private set-current

\ Taking a unit out of the middle: the units after unit i move down one
\ (to unit i's address from the next unit's, the bytes of those after).
: slab-hole ( i slab -- from to ) tuck slab-at tuck swap slab-unit + swap ;
: slab-rest ( i slab -- u ) tuck slab-since 1- swap slab-unit * ;
: slab-close-up ( i slab -- ) 2dup slab-rest >r slab-hole r> move ;

lf-lib set-current
\ Unit i taken out, the units after it moved down one (their numbers
\ drop by one), the count one less. The mark entries above i go (a
\ rollback to one would keep units that moved, or cut below them); a mark
\ at i or below stays. A slab that is not live, or i outside 0 .. count -
\ 1, throws slab-bad-cut (-4133), nothing changed: i is a number the
\ caller holds, so this is a fault in the caller.
: slab-remove ( i slab -- )
  2dup slab-valid? 0= if slab-bad-cut throw then
  2dup slab-unmark-above tuck slab-close-up dup slab-count 1- swap slab-cut ;

module-close
base !   \ the BASE this file was loaded with
