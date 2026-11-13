\ Stable sorting of records in place: n records of a fixed size in address
\ units (cells, packed 32-bit fields, 24-byte records, any size), ordered
\ by the caller's comparison. A general tool with no Lean knowledge;
\ untrusted. Written for the checker's hand-written insertion sorts (the
\ kernel refactor review's batch C2, docs/development/forth-reviews/
\ 2026-11-12-backlog-kernel.md), whose results, such as a snapshot's bytes,
\ depend on the exact order of records with equal keys.
\
\ The comparison. A sorter record holds the record size, the order xt and
\ optionally a key xt. order ( a-addr1 a-addr2 -- n ) is given two records'
\ addresses, or with a key word fetch ( a-addr -- x ) (sorter-key!) their
\ keys, always the earlier record first, never a record and itself; n > 0
\ means the earlier goes after the later; zero or negative leave them in
\ their order. So the sort is stable, and since the stable order is unique,
\ any order that is a total preorder gives exactly an insertion sort's
\ result. Any other order still leaves a permutation of the records. Both
\ words must take their arguments and give one result, as the depth shows
\ after every call (otherwise sort-records gives invalid); they may read the
\ records and anything else, but must not change the records, the sorter
\ or the stack below their arguments.
\
\ The method. n <= sorter-short records (sort-short, 32, unless set) are
\ sorted by insertion: each record from the second on is compared with the
\ earlier ones from the nearest down while the order is positive, exactly
\ as by exchanging neighbours, and is then rotated into place; at most
\ n(n-1)/2 comparisons, no scratch. Larger n are merge sorted bottom up from
\ runs of one record: in pass k, from the start, runs of 2^k records are
\ merged in pairs (a last run without a partner stays), the right run's
\ record first only when the order is positive, through a scratch of n
\ records, at most n*ceil(log2 n) comparisons. These are, call for call,
\ the comparisons of src/kernel/level-normalize.fs's lf-lnorm-sort (whose
\ cut-over is also 32), so a comparison that spends fuel spends the same.
\ No recursion; the host's stacks hold a few cells whatever n is.
\ Why so: insertion is the fastest and needs no memory for the short lists
\ the checker sorts most; merging from runs of one record makes the fewest
\ comparisons, which cost an EXECUTE or two each, and is stable. Each merge
\ reads its two runs in the records' own memory and writes the scratch, and
\ only then copies the result back in one MOVE; so the order only ever sees
\ addresses of the records themselves, and at each call they are a
\ permutation of the input. Records move only by MOVE (no byte access), a
\ rotation through a temp of sort-chunk address units at a time; a record
\ larger than that is rotated in several passes.
\
\ Outcomes (lib/outcome.fs): ok; invalid with nothing done for a negative n,
\ n records that would not fit a cell's count of address units, or a sorter
\ that sorter-init did not accept or that is sorting already (a nested call
\ from its own order); invalid when the order or key word changed the stack
\ depth, the records then in some order; full, nothing changed, when n is
\ above the cut-over and the heap refuses the scratch (n * size address
\ units, unless the caller's buffer, sorter-buffer!, holds that many). A
\ THROW out of the order or key word is passed on after the scratch is
\ freed, the records then a permutation of the input, the sorter ready to
\ sort again (a THROW with sort-unbalanced's code, -4131, reads as invalid).
\
\ Example: cells by value; then 8-byte (key, payload) pairs by their first
\ packed 32-bit field (lib/u32.fs), pairs of equal keys kept in order.
\   create by-value /sorter allot   create numbers 5 , 3 , 9 , 3 ,
\   ' sort-signed by-value sorter-cells drop
\   numbers 4 by-value sort-records .     \ 0 (ok); numbers: 3 3 5 9
\   create by-key /sorter allot
\   8 ' sort-unsigned by-key sorter-init drop  ' u32@ by-key sorter-key!
\   pairs 1000 by-key sort-records .      \ ok, or 6 (full) without scratch
\
\ Interface: /sorter sorter-init sorter-cells sorter-u32s sorter-key!
\ sorter-buffer! sorter-short sort-short sort-records sort-signed
\ sort-unsigned. State: none of its own; a sorter record is the caller's
\ (in the dictionary, or a member of a larger record) and holds the working
\ state of one sort at a time; separate sorters are independent. Requires
\ portability.fs, bounds.fs, outcome.fs, u32.fs and module.fs; helpers are
\ private in lf-lib-private (ADR 0010). Loads in decimal whatever BASE is,
\ then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./bounds.fs
require ./outcome.fs
require ./u32.fs
require ./module.fs

lf-lib-private module-open

4 cells constant sort-chunk      \ the temp: a record is rotated this much at a time
-4131 constant sort-unbalanced   \ THROW code: an order or key word changed the depth

lf-lib set-current
32 constant sort-short           \ the default cut-over: up to 32 records by insertion
begin-structure /sorter
lf-lib-private set-current
  field: sorter-size       \ a record's address units; 0 in a sorter not accepted
  field: sorter-order      \ the order xt
  field: sorter-fetch      \ the key xt, or 0: the order gets addresses
lf-lib set-current
  field: sorter-short      \ setting: n <= this by insertion, else merged
lf-lib-private set-current
  field: sorter-buffer     \ the caller's scratch, or 0
  field: sorter-room       \ its address units
  field: sorter-busy       \ true while a sort runs
  field: sorter-base       \ the records of the sort in progress
  field: sorter-end        \ the address after them
  field: sorter-scratch    \ the scratch of a merge
  field: sorter-owned      \ the scratch when allocated here (freed after), or 0
  field: sorter-width      \ a merge pass's run length, in address units
  field: sorter-lo         \ a merge: the left run's start
  field: sorter-left       \ the left run's next record; insertion: the place
  field: sorter-mid        \ the right run's start; insertion: the record placed
  field: sorter-right      \ the right run's next record; insertion: mid's end
  field: sorter-stop       \ the right run's end
  field: sorter-out        \ the merge's next record in the scratch
  sort-chunk +field sorter-temp
end-structure

\ ---- Sorters.
: sort-plan? ( size order -- flag ) 0<> swap 0> and ;
: sort-set ( size order sorter -- )
  sort-short over sorter-short ! tuck sorter-order ! sorter-size ! ;
lf-lib set-current
\ A sorter for records of size address units, ordered by order ( a-addr1
\ a-addr2 -- n ): ok; or invalid, the sorter then refused by every sort,
\ for a size below 1 or no order (0). Clears every setting.
: sorter-init ( size order sorter -- outcome )
  dup /sorter erase >r 2dup sort-plan? r> swap
  if sort-set outcome-ok else drop 2drop outcome-invalid then ;
\ From now on the order is given each record's key, fetch ( a-addr -- x ).
: sorter-key! ( fetch sorter -- ) sorter-fetch ! ;
\ Sorters of cells and of packed 32-bit fields by value: order ( x1 x2 --
\ n ). The outcome is sorter-init's.
: sorter-cells ( order sorter -- outcome )
  >r 1 cells swap r@ sorter-init ['] @ r> sorter-key! ;
: sorter-u32s ( order sorter -- outcome )
  >r 1 u32s swap r@ sorter-init ['] u32@ r> sorter-key! ;
\ The caller's scratch: u address units at addr, used by a merge of at most
\ u address units of records instead of the heap.
: sorter-buffer! ( addr u sorter -- ) tuck sorter-room ! sorter-buffer ! ;
\ Orders of signed and unsigned values: -1, 0 or 1.
: sort-signed ( n1 n2 -- n ) 2dup = if 2drop 0 else < 2* 1+ then ;
: sort-unsigned ( u1 u2 -- n ) 2dup = if 2drop 0 else u< 2* 1+ then ;
lf-lib-private set-current

\ ---- The comparison: whether the earlier record goes after the later,
\ the depth checked after each key word and after the order, before their
\ results are used.
: sort-size ( sorter -- u ) sorter-size @ ;
: sort-fetched ( a-addr xt -- x )
  depth >r execute depth r> 1- <> if sort-unbalanced throw then ;
: sort-key ( a-addr sorter -- x ) sorter-fetch @ ?dup if sort-fetched then ;
: sort-keys ( a-addr1 a-addr2 sorter -- x1 x2 ) tuck sort-key >r sort-key r> ;
: sort-compare ( a-addr1 a-addr2 sorter -- n )
  dup >r sort-keys r> sorter-order @ execute ;
: sort-after? ( a-addr1 a-addr2 sorter -- flag )
  depth >r sort-compare depth r> 2 - <> if sort-unbalanced throw then 0> ;

\ ---- Insertion. The record at mid goes to the place p: below every
\ earlier record, from the nearest down, that goes after it. Then the
\ records from p to mid's end (right) rotate up by one record.
: sort-goes-below? ( p sorter -- flag )
  2dup sorter-base @ u> 0= if 2drop false exit then
  tuck sort-size - over sorter-mid @ rot sort-after? ;
: sort-scan ( sorter -- p )
  dup sorter-mid @ begin 2dup swap sort-goes-below? while over sort-size - repeat nip ;
\ Rotating left..right up by u <= sort-chunk address units: the last u to
\ the temp, the rest up, the temp to the start.
: sort-hold ( u sorter -- ) dup sorter-temp >r sorter-right @ over - r> rot move ;
: sort-shift ( u sorter -- )
  2dup sorter-right @ swap - over sorter-left @ - >r sorter-left @ tuck + r> move ;
: sort-put ( u sorter -- ) dup sorter-temp swap sorter-left @ rot move ;
: sort-roll ( u sorter -- ) 2dup sort-hold 2dup sort-shift sort-put ;
: sort-rotate ( sorter -- )
  dup sort-size begin dup 0> while
    2dup sort-chunk min tuck swap sort-roll - repeat 2drop ;
: sort-place ( p sorter -- )
  2dup sorter-mid @ u< 0= if 2drop exit then
  tuck sorter-left ! dup sorter-mid @ over sort-size + over sorter-right ! sort-rotate ;
: sort-insert ( a-addr sorter -- ) tuck sorter-mid ! dup sort-scan swap sort-place ;
: sort-second ( sorter -- a-addr ) dup sorter-base @ swap sort-size + ;
: sort-insertion ( sorter -- )
  dup sorter-end @ over sort-second ?do i over sort-insert dup sort-size +loop drop ;

\ ---- Merging. A run ends width address units after its start, or at the
\ end. The merge at lo: left lo..mid, right mid..stop, written to the
\ scratch from lo's place; when a run is used up, the left run's rest goes
\ after them, the right one's is in its place already, and the scratch
\ goes back over lo in one MOVE.
: sort-total ( sorter -- u ) dup sorter-end @ swap sorter-base @ - ;
: sort-cut ( a-addr sorter -- a-addr' )
  2dup sorter-end @ swap - over sorter-width @ min nip + ;
: sort-runs ( lo sorter -- )
  2dup sorter-lo ! 2dup sorter-left ! tuck sort-cut
  2dup swap sorter-mid ! 2dup swap sorter-right ! over sort-cut swap sorter-stop ! ;
: sort-paired? ( sorter -- flag ) dup sorter-mid @ swap sorter-stop @ u< ;
: sort-both? ( sorter -- flag )
  dup sorter-left @ over sorter-mid @ u<
  swap dup sorter-right @ swap sorter-stop @ u< and ;
: sort-right-first? ( sorter -- flag )
  dup sorter-left @ over sorter-right @ rot sort-after? ;
: sort-cursor ( sorter -- field )
  dup sort-right-first? if sorter-right else sorter-left then ;
\ The records from a-addr1 to a-addr2 to the scratch, which moves on.
: sort-rest ( a-addr1 a-addr2 sorter -- )
  >r over - r@ sorter-out @ swap dup r> sorter-out +! move ;
: sort-copy ( a-addr sorter -- ) 2dup sort-size + swap sort-rest ;
: sort-take ( field sorter -- ) over @ over sort-copy sort-size swap +! ;
: sort-left-rest ( sorter -- ) dup sorter-left @ over sorter-mid @ rot sort-rest ;
: sort-scratch-at ( a-addr sorter -- a-addr' )
  tuck sorter-base @ - swap sorter-scratch @ + ;
: sort-back ( sorter -- )
  dup sorter-lo @ over sort-scratch-at over sorter-out @ over -
  rot sorter-lo @ swap move ;
: sort-merging ( sorter -- )
  dup sorter-lo @ over sort-scratch-at over sorter-out !
  begin dup sort-both? while dup sort-cursor over sort-take repeat
  dup sort-left-rest sort-back ;
\ The merge at lo, when it has a right run; the next merge's start.
: sort-merge ( lo sorter -- lo' )
  tuck sort-runs dup sort-paired? if dup sort-merging then sorter-stop @ ;
: sort-pass ( sorter -- )
  dup sorter-base @ begin over sorter-end @ over u> while over sort-merge repeat 2drop ;
: sort-more? ( sorter -- flag ) dup sorter-width @ swap sort-total u< ;
: sort-widen ( sorter -- ) sorter-width dup @ 2* swap ! ;
: sort-merges ( sorter -- )
  dup sort-size over sorter-width !
  begin dup sort-more? while dup sort-pass dup sort-widen repeat drop ;

\ ---- A sort: insertion or merging, run under CATCH, so that the scratch is
\ freed and the sorter ready again after a THROW; sort-unbalanced, thrown
\ when the order or key word changed the depth, is invalid.
: sort-count ( sorter -- n ) dup sort-total swap sort-size / ;
: sort-by-merge? ( sorter -- flag ) dup sort-count swap sorter-short @ > ;
: sort-body ( sorter -- ) dup sort-by-merge? if sort-merges else sort-insertion then ;
: sort-done ( sorter -- )
  dup sorter-owned @ ?dup if free drop then
  0 over sorter-owned ! false swap sorter-busy ! ;
: sort-ior ( ior -- outcome )
  dup sort-unbalanced = if drop outcome-invalid else throw outcome-ok then ;
: sort-guarded ( sorter -- outcome )
  true over sorter-busy ! dup ['] sort-body catch dup if nip then
  swap sort-done sort-ior ;
\ A merge's scratch: the caller's buffer when it holds the records, else
\ the heap (full when it refuses).
: sort-buffered? ( sorter -- flag ) dup sorter-room @ swap sort-total < 0= ;
: sort-owned! ( a-addr sorter -- ) 2dup sorter-owned ! sorter-scratch ! ;
: sort-allocate ( sorter -- outcome )
  dup sort-total allocate if 2drop outcome-full else swap sort-owned! outcome-ok then ;
: sort-scratch ( sorter -- outcome )
  dup sort-buffered? if dup sorter-buffer @ swap sorter-scratch ! outcome-ok
  else sort-allocate then ;
: sort-prepared ( sorter -- outcome )
  dup sort-by-merge? if dup sort-scratch dup ok? 0= if nip exit then drop then
  sort-guarded ;
\ A sorter that may sort n records: accepted, not busy, 0 <= n and n
\ records' address units within a cell.
: sort-usable? ( sorter -- flag )
  dup sort-size 0> over sorter-order @ 0<> and swap sorter-busy @ 0= and ;
: sort-ready? ( n sorter -- flag )
  dup sort-usable? if max-n swap sort-size / upto? else 2drop false then ;
: sort-bounds! ( a-addr n sorter -- sorter )
  tuck sort-size * >r 2dup sorter-base ! r> rot + over sorter-end ! ;

lf-lib set-current
\ Sort the n records at a-addr in place: ok, invalid or full (above).
: sort-records ( a-addr n sorter -- outcome )
  2dup sort-ready? 0= if drop 2drop outcome-invalid exit then
  over 2 < if drop 2drop outcome-ok exit then
  sort-bounds! sort-prepared ;

module-close
base !   \ the BASE this file was loaded with
