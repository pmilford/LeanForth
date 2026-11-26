\ Unit tests of src/lib/slab.fs, growable heap stores (plan task 1.1.5):
\ shapes, room and claims, the limit at and one past its bound, growth
\ keeping the contents, trimming, clearing and poisoning, every sealed
\ field corrupted, marks and every refusal of a rollback, cutting back
\ (slab-cut) and its refusals, and a randomized model of claims, marks,
\ rollbacks, cuts and clears. Loaded under
\ HEX. T{ }T checks results and data-stack depth; rs-checked the return
\ stack.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/slab.fs decimal
lf-lib-private order+

create s1 /slab allot   create s2 /slab allot   create s3 /slab allot
create m0 /slab-mark allot   create m1 /slab-mark allot   create m2 /slab-mark allot

\ Shapes: a positive unit, 0 <= limit, limit units within a cell.
T{ 1 cells 10 s1 slab-init -> outcome-ok }T
T{ s1 slab-live? s1 slab-count s1 slab-capacity s1 slab-limit s1 slab-unit -> true 0 0 10 1 cells }T
T{ 0 10 s2 slab-init s2 slab-live? -> outcome-invalid false }T
T{ -1 10 s2 slab-init 1 cells -1 s2 slab-init -> outcome-invalid outcome-invalid }T
T{ 2 max-n s2 slab-init s2 slab-live? -> outcome-invalid false }T
T{ 1 max-n s2 slab-init s2 slab-live? -> outcome-ok true }T
T{ 1 0 s2 slab-init 0 s2 slab-room 1 s2 slab-room -> outcome-ok outcome-ok outcome-full }T
s2 slab-free

\ Claims. The first block holds slab-min-units, or the limit if smaller.
T{ 3 s1 ' slab-claim rs-checked s1 slab-count s1 slab-capacity -> 0 outcome-ok 3 10 }T
\ The limit: room for 7 more, not 8; a claim at the limit, then one past.
T{ 7 s1 slab-room 8 s1 slab-room -> outcome-ok outcome-full }T
T{ 7 s1 slab-claim s1 slab-count -> 3 outcome-ok 10 }T
\ slab-since (cleanup-families-2): the units added since a count, 0 at
\ the count itself, negative for a count above the slab's.
T{ 3 s1 slab-since 0 s1 slab-since 10 s1 slab-since 12 s1 ' slab-since rs-checked
   -> 7 10 0 -2 }T
T{ 1 s1 slab-claim s1 slab-count -> -1 outcome-full 10 }T
T{ 0 s1 slab-room -1 s1 slab-room -1 s1 slab-claim -> outcome-ok outcome-invalid -1 outcome-invalid }T
T{ 0 s1 slab-valid? 9 s1 slab-valid? 10 s1 slab-valid? -1 s1 slab-valid? -> true true false false }T
T{ 1 s1 slab-at 0 s1 slab-at - s1 slab-top 10 s1 slab-at = -> 1 cells true }T
\ slab-claim-one (review tb2-batch3b 3): the claimed unit's address, each
\ claim the next unit; at the limit -1 and full, nothing claimed; a slab
\ not live -1 and invalid.
1 cells 2 s2 slab-init drop
T{ s2 ' slab-claim-one rs-checked s2 slab-count rot 0 s2 slab-at = -> outcome-ok 1 true }T
T{ s2 slab-claim-one swap 1 s2 slab-at = s2 slab-count -> outcome-ok true 2 }T
T{ s2 slab-claim-one s2 slab-count -> -1 outcome-full 2 }T
s2 slab-free
T{ s2 slab-claim-one s2 slab-count -> -1 outcome-invalid 0 }T

\ Growth keeps the contents: 1,000 cells claimed one at a time.
1 cells 1000 s2 slab-init drop
: fill-cells ( n slab -- ) swap 0 ?do 1 over slab-claim drop i 7 * swap 2 pick slab-at ! loop drop ;
: filled? ( n slab -- flag ) true rot 0 ?do over i swap slab-at @ i 7 * = and loop nip ;
T{ 1000 s2 fill-cells s2 slab-count s2 slab-capacity -> 1000 1000 }T
T{ 1000 s2 filled? 1 s2 slab-room -> true outcome-full }T
\ Doubling: 16, 32, 64, ... capped at the limit.
1 cells 100 s3 slab-init drop
T{ 1 s3 slab-claim 2drop s3 slab-capacity 16 s3 slab-claim 2drop s3 slab-capacity -> 16 32 }T
T{ 40 s3 slab-claim 2drop s3 slab-capacity 50 s3 slab-room s3 slab-capacity -> 64 outcome-full 64 }T
\ slab-reserve pre-sizes; slab-trim shrinks to the count, keeping it.
T{ 100 s3 slab-reserve s3 slab-capacity s3 slab-trim s3 slab-capacity s3 slab-count -> outcome-ok 100 outcome-ok 57 57 }T
T{ 5 s3 slab-claim nip s3 slab-count -> outcome-ok 62 }T
s3 slab-free
T{ s3 slab-live? 0 s3 slab-room -> false outcome-invalid }T
\ slab-zeroed: an empty slab claims n units, all zero (their old bytes
\ overwritten); a slab with units is left as it is; beyond the limit
\ full, nothing claimed. slab-cell-put: cell i set, the cells added
\ before it -1; within the count no growth; beyond the limit full.
1 cells 8 s3 slab-init drop
T{ 3 s3 slab-claim 2drop 7 0 s3 slab-at ! 7 2 s3 slab-at ! s3 slab-clear -> }T
T{ 3 s3 slab-zeroed s3 slab-count 0 s3 slab-at @ 2 s3 slab-at @ -> outcome-ok 3 0 0 }T
T{ 5 s3 slab-zeroed s3 slab-count -> outcome-ok 3 }T
s3 slab-clear
T{ 9 s3 slab-zeroed s3 slab-count -> outcome-full 0 }T
T{ 42 2 s3 slab-cell-put s3 slab-count 0 s3 slab-at @ 1 s3 slab-at @ 2 s3 slab-at @
   -> outcome-ok 3 -1 -1 42 }T
T{ 5 1 s3 slab-cell-put s3 slab-count 1 s3 slab-at @ -> outcome-ok 3 5 }T
\ Beyond the limit: full, x not stored, the cells added up to the limit
\ kept (-1).
T{ 9 8 s3 slab-cell-put s3 slab-count 7 s3 slab-at @ -> outcome-full 8 -1 }T
s3 slab-free

\ Clearing: count 0, generation + 1; at max-n the slab is poisoned.
T{ s2 slab-generation s2 slab-clear s2 slab-count s2 slab-generation -> 0 0 1 }T
max-n 1- s2 slab-epoch !
T{ s2 slab-clear s2 slab-generation s2 slab-live? -> max-n true }T
T{ s2 slab-clear s2 slab-generation s2 slab-live? 1 s2 slab-room -> -1 false outcome-invalid }T
T{ s2 slab-clear s2 slab-generation -> -1 }T
s2 slab-free

\ Corrupting any sealed field, or the count, fails closed.
1 cells 10 s2 slab-init drop  4 s2 slab-claim 2drop
: field+! ( delta xt -- ) s2 swap execute +! ;
: tamper ( xt delta -- flag outcome )   \ change the field xt gives, test, restore
  2dup swap field+! s2 slab-live? 1 s2 slab-room 2swap negate swap field+! ;
T{ ' slab-block 8 tamper -> false outcome-invalid }T
T{ ' slab-room-units 1 tamper -> false outcome-invalid }T
T{ ' slab-unit-size 1 tamper -> false outcome-invalid }T
T{ ' slab-most 1 tamper -> false outcome-invalid }T
T{ ' slab-seal 1 tamper -> false outcome-invalid }T
T{ ' slab-used 100 tamper -> false outcome-invalid }T
T{ ' slab-used -5 tamper -> false outcome-invalid }T
T{ ' slab-epoch max-n negate tamper -> false outcome-invalid }T
T{ s2 slab-live? 1 s2 slab-room -> true outcome-ok }T
s2 slab-free

\ Marks. A mark records the slab, its generation, its entry and count.
1 cells 100 s1 slab-free s1 slab-init drop
T{ m0 s1 ' slab-mark rs-checked -> outcome-ok }T
T{ m0 slab-mark-slab @ s1 = m0 slab-mark-count @ m0 slab-mark-entry @ s1 slab-depth @ -> true 0 0 1 }T
T{ 3 s1 slab-claim nip s1 slab-count -> outcome-ok 3 }T
T{ m0 s1 ' slab-rollback rs-checked s1 slab-count -> outcome-ok 0 }T
\ Still valid: rolling back twice is harmless.
T{ m0 s1 slab-mark-valid? m0 s1 slab-rollback s1 slab-count -> true outcome-ok 0 }T
\ Marks at one count share an entry.
T{ m1 s1 slab-mark s1 slab-depth @ m1 slab-mark-serial @ m0 slab-mark-serial @ = -> outcome-ok 1 true }T
\ A mark above a rollback's target is stale, and stays stale when the
\ count passes it again; the older mark stays valid.
4 s1 slab-claim 2drop
T{ m2 s1 slab-mark m2 slab-mark-count @ s1 slab-depth @ -> outcome-ok 4 2 }T
T{ m1 s1 slab-rollback s1 slab-count s1 slab-depth @ -> outcome-ok 0 1 }T
T{ m2 s1 slab-mark-valid? m2 s1 slab-rollback s1 slab-count -> false outcome-invalid 0 }T
6 s1 slab-claim 2drop
T{ m2 s1 slab-rollback s1 slab-count m0 s1 slab-rollback s1 slab-count -> outcome-invalid 6 outcome-ok 0 }T
\ A mark of another slab, and one from before a clear.
1 cells 100 s2 slab-init drop
T{ m0 s2 slab-rollback m0 s2 slab-mark-valid? -> outcome-invalid false }T
T{ m0 s1 slab-mark s1 slab-clear m0 s1 slab-rollback m0 s1 slab-mark-valid? -> outcome-ok outcome-invalid false }T
\ A forged entry position, and a forged count, are refused.
T{ m0 s1 slab-mark 99 m0 slab-mark-entry ! m0 s1 slab-rollback -> outcome-ok outcome-invalid }T
T{ m0 s1 slab-mark 1 m0 slab-mark-count ! m0 s1 slab-rollback -> outcome-ok outcome-invalid }T
\ A slab that is not live cannot be marked; the mark is then refused.
T{ m1 s3 slab-mark m1 slab-mark-slab @ m1 s3 slab-rollback -> outcome-invalid 0 outcome-invalid }T
\ The mark stack grows: 100 marks at counts 0 .. 99, then a rollback to
\ the 50th leaves 51 entries.
create many 100 /slab-mark * allot
: mark# ( k -- mark ) /slab-mark * many + ;
: mark-all ( -- flag ) true 100 0 do i mark# s1 slab-mark ok? and 1 s1 slab-claim nip ok? and loop ;
T{ s1 slab-clear mark-all s1 slab-depth @ s1 slab-count -> true 100 100 }T
: valid-all ( -- n ) 0 100 0 do i mark# s1 slab-mark-valid? if 1+ then loop ;
T{ valid-all 50 mark# s1 slab-rollback s1 slab-depth @ valid-all s1 slab-count -> 100 outcome-ok 51 51 50 }T
s1 slab-free s2 slab-free

\ Cutting back to a count kept earlier (slab-cut): the units above it
\ given back, those below unchanged; marks above it refused from then on,
\ marks at or below it kept. A count outside 0 .. count, or a slab that
\ is not live, throws slab-bad-cut, the slab unchanged.
T{ slab-bad-cut -> -4133 }T
: cut-throws? ( n slab -- flag ) ['] slab-cut catch dup if nip nip then slab-bad-cut = ;
1 cells 100 s1 slab-init drop  6 s1 fill-cells
T{ 4 s1 ' slab-cut rs-checked s1 slab-count 4 s1 filled? -> 4 true }T
T{ 4 s1 slab-cut s1 slab-count 0 s1 slab-cut s1 slab-count -> 4 0 }T
3 s1 fill-cells
T{ 4 s1 cut-throws? -1 s1 cut-throws? s1 slab-count 3 s1 filled? -> true true 3 true }T
T{ 3 s1 cut-throws? 0 s2 cut-throws? -> false true }T
T{ m0 s1 slab-mark 2 s1 slab-claim nip m1 s1 slab-mark 2 s1 slab-claim nip
   -> outcome-ok outcome-ok outcome-ok outcome-ok }T
T{ 4 s1 slab-cut m1 s1 slab-mark-valid? m0 s1 slab-mark-valid? s1 slab-depth @ -> false true 1 }T
\ The mark at 5 stays refused when the count passes 5 again.
T{ 3 s1 slab-claim nip m1 s1 slab-rollback m0 s1 slab-rollback s1 slab-count
   -> outcome-ok outcome-invalid outcome-ok 3 }T
T{ 2 s1 slab-claim nip 3 s1 slab-cut m0 s1 slab-mark-valid? s1 slab-count -> outcome-ok true 3 }T
s1 slab-free

\ Taking a unit out (slab-remove): the units after it move down one, the
\ count is one less; the first, a middle and the last unit; the marks
\ above i refused, those at i or below kept; an i outside
\ 0 .. count - 1, or a slab that is not live, throws slab-bad-cut, the
\ slab unchanged. Units of two cells move whole.
: cell@ ( i slab -- x ) slab-at @ ;
: cells@ ( slab -- x0 .. xn-1 ) dup slab-count 0 ?do i over cell@ swap loop drop ;
: remove-throws? ( i slab -- flag )
  ['] slab-remove catch dup if nip nip then slab-bad-cut = ;
1 cells 100 s1 slab-init drop  5 s1 fill-cells
T{ 2 s1 ' slab-remove rs-checked s1 cells@ -> 0 7 21 28 }T
T{ 0 s1 slab-remove s1 cells@ -> 7 21 28 }T
T{ 2 s1 slab-remove s1 cells@ s1 slab-count -> 7 21 2 }T
T{ 2 s1 remove-throws? -1 s1 remove-throws? s1 cells@ -> true true 7 21 }T
T{ 0 s2 remove-throws? -> true }T
T{ m0 s1 slab-mark 1 s1 slab-claim nip m1 s1 slab-mark 0 s1 slab-remove
   -> outcome-ok outcome-ok outcome-ok }T
T{ m1 s1 slab-mark-valid? m0 s1 slab-mark-valid? s1 slab-count -> false false 2 }T
\ The mark at 3 stays refused when the count passes 3 again.
T{ 1 s1 slab-claim nip m1 s1 slab-mark-valid? 2 s1 slab-cut -> outcome-ok false }T
T{ 0 s1 slab-remove 0 s1 slab-remove s1 slab-count 0 s1 remove-throws? -> 0 true }T
s1 slab-free
\ Review s1-elab re-check M1: [7 21], a mark at 2, 99 claimed after it,
\ unit 0 taken out: the mark is refused (a rollback to 2 would keep 99);
\ a mark at 1 stays when unit 1 is taken out, and rolls back to [21].
1 cells 100 s1 slab-init drop
T{ 7 s1 slab-push 21 s1 slab-push m0 s1 slab-mark 99 s1 slab-push
   -> outcome-ok outcome-ok outcome-ok outcome-ok }T
T{ 0 s1 slab-remove m0 s1 slab-mark-valid? m0 s1 slab-rollback s1 cells@
   -> false outcome-invalid 21 99 }T
T{ 1 s1 slab-cut m1 s1 slab-mark 5 s1 slab-push 6 s1 slab-push 1 s1 slab-remove
   m1 s1 slab-mark-valid? s1 cells@ -> outcome-ok outcome-ok outcome-ok true 21 6 }T
T{ m1 s1 slab-rollback s1 cells@ -> outcome-ok 21 }T
s1 slab-free
\ Review s1-elab re-check 2 M: a mark at exactly i + 1, below the new
\ count: [7], a mark at 1, 21 and 99 pushed, unit 0 taken out: refused.
1 cells 100 s1 slab-init drop
T{ 7 s1 slab-push m0 s1 slab-mark 21 s1 slab-push 99 s1 slab-push 0 s1 slab-remove
   m0 s1 slab-mark-valid? -> outcome-ok outcome-ok outcome-ok outcome-ok false }T
s1 slab-free
2 cells 10 s1 slab-init drop
: pair+ ( x1 x2 -- ) s1 slab-2push drop ;
T{ 1 2 pair+ 3 4 pair+ 5 6 pair+ 0 s1 slab-remove s1 slab-2pop s1 slab-2pop s1 slab-count
   -> 5 6 3 4 0 }T
s1 slab-free

\ Stacks. Cells: pushed, read with slab-last, popped newest first.
T{ slab-underflow -> -4132 }T
1 cells 3 s1 slab-init drop
T{ 7 s1 ' slab-push rs-checked 8 s1 slab-push s1 slab-count -> outcome-ok outcome-ok 2 }T
T{ s1 slab-last @ s1 slab-last 1 s1 slab-at = -> 8 true }T
T{ s1 ' slab-pop rs-checked s1 slab-count s1 slab-pop s1 slab-count -> 8 1 7 0 }T
\ Full at the limit, nothing changed; the slab grows under pushes.
T{ 1 s1 slab-push 2 s1 slab-push 3 s1 slab-push 4 s1 slab-push s1 slab-count
   -> outcome-ok outcome-ok outcome-ok outcome-full 3 }T
T{ s1 slab-pop s1 slab-pop s1 slab-pop -> 3 2 1 }T
s1 slab-free
1 cells 1000 s1 slab-init drop
: push-all ( n -- outcome ) outcome-ok swap 0 ?do i 3 * s1 slab-push outcome-and loop ;
: pop-all? ( n -- flag ) true swap 0 ?do s1 slab-pop 999 i - 3 * = and loop ;
T{ 1000 push-all s1 slab-count s1 slab-capacity -> outcome-ok 1000 1000 }T
T{ 999 pop-all? s1 slab-count s1 slab-pop -> true 1 0 }T
\ slab-drop gives the newest unit back; its contents stay until a claim.
T{ 5 s1 slab-push 6 s1 slab-push s1 slab-drop s1 slab-count s1 slab-pop -> 0 0 1 5 }T
\ Pairs keep 2!'s order: slab-2pop gives back what slab-2push took.
2 cells 10 s2 slab-init drop
T{ 1 2 s2 ' slab-2push rs-checked 3 4 s2 slab-2push s2 slab-count -> outcome-ok outcome-ok 2 }T
T{ s2 slab-last 2@ s2 ' slab-2pop rs-checked s2 slab-2pop s2 slab-count -> 3 4 3 4 1 2 0 }T
\ Units of two cells hold a cell too, from the unit's start.
T{ 9 s2 slab-push s2 slab-pop s2 slab-count -> outcome-ok 9 0 }T
\ Units too narrow for what is pushed: invalid, nothing changed.
1 cells 1- 10 s3 slab-init drop
T{ 1 s3 slab-push 1 2 s1 slab-2push s1 slab-count s3 slab-count
   -> outcome-invalid outcome-invalid 0 0 }T
\ An empty slab, one too narrow for what is popped, and one not live
\ throw slab-underflow, the stack and the slab unchanged.
: underflow? ( slab xt -- flag ) catch dup if nip then slab-underflow = ;
T{ s1 ' slab-pop underflow? s1 ' slab-2pop underflow? s1 slab-count -> true true 0 }T
T{ s1 ' slab-drop underflow? s1 ' slab-last underflow? -> true true }T
7 s1 slab-push drop
T{ s1 ' slab-2pop underflow? s1 slab-count s1 slab-pop -> true 1 7 }T
T{ 0 s3 slab-claim 2drop s3 ' slab-pop underflow? -> true }T
1 s3 slab-claim 2drop
T{ s3 ' slab-pop underflow? s3 slab-count s3 slab-last s3 slab-base = -> true 1 true }T
\ slab-data: unit 0's address and the count, after a claim and after growth
\ (a new block).
T{ s3 slab-data swap s3 slab-base = -> 1 true }T
: grown ( -- base? n ) 5 s3 slab-claim 2drop s3 slab-data swap s3 slab-base = swap ;
T{ grown -> true 6 }T
1 s3 slab-cut
T{ s3 ' slab-drop rs-checked s3 slab-count -> 0 }T
s2 slab-free
T{ 1 s2 slab-push s2 ' slab-pop underflow? s2 ' slab-last underflow? -> outcome-invalid true true }T
\ A corrupted count is refused: nothing pushed or popped.
1 cells 10 s2 slab-init drop  4 s2 slab-push drop
50 s2 slab-used !
T{ 1 s2 slab-push s2 ' slab-pop underflow? -> outcome-invalid true }T
1 s2 slab-used !
T{ s2 slab-pop s2 slab-count -> 4 0 }T
\ Marks see a stack's pushes: a rollback takes them back.
T{ m0 s2 slab-mark 1 s2 slab-push 2 s2 slab-push m0 s2 slab-rollback s2 slab-count
   -> outcome-ok outcome-ok outcome-ok outcome-ok 0 }T
s1 slab-free s2 slab-free s3 slab-free

\ Copies kept as a stack (a choice point's saved state): slab-keep pushes
\ a copy of the units and their count onto a store of the same unit,
\ slab-restore makes them the slab's again and drops the copy,
\ slab-forget drops it; last in, first out.
1 cells 10 s1 slab-init drop  1 cells 100 s2 slab-init drop
: s1-cells ( -- x... n ) s1 slab-count 0 ?do i s1 slab-at @ loop s1 slab-count ;
T{ 7 s1 slab-push 8 s1 slab-push s1 s2 slab-keep s2 slab-count
   -> outcome-ok outcome-ok outcome-ok 3 }T
T{ s1 slab-pop 9 s1 slab-push 10 s1 slab-push s1 s2 slab-keep s2 slab-count
   -> 8 outcome-ok outcome-ok outcome-ok 7 }T
T{ 11 s1 slab-push s1 s2 slab-restore s1-cells s2 slab-count -> 0 0 7 9 10 3 3 }T
T{ 0 s1 slab-cut s1 s2 slab-restore s1-cells s2 slab-count -> 0 7 8 2 0 }T
\ An empty slab is kept as one; a copy forgotten leaves the slab as it is.
T{ 0 s1 slab-cut s1 s2 slab-keep 5 s1 slab-push s2 slab-forget s1-cells s2 slab-count
   -> outcome-ok outcome-ok 5 1 0 }T
T{ s1 s2 slab-keep 0 s1 slab-cut 6 s1 slab-push s1 s2 slab-restore s1-cells
   -> outcome-ok outcome-ok outcome-ok 5 1 }T
\ Another unit, or one narrower than a cell: invalid; a store with no
\ room for the copy and its count: full; nothing changed either way.
2 cells 10 s3 slab-init drop
T{ s1 s3 slab-keep s3 slab-count -> outcome-invalid 0 }T
s3 slab-free  1 cells 1- 10 s3 slab-init drop
T{ s3 s3 slab-keep s3 slab-count -> outcome-invalid 0 }T
s3 slab-free  1 cells 2 s3 slab-init drop
T{ 1 s1 slab-push s1 s3 slab-keep s3 slab-count s1-cells -> outcome-ok outcome-full 0 5 1 2 }T
\ slab-kept: put back (true) or forgotten (false, ok), the copy dropped.
s3 slab-free  1 cells 100 s3 slab-init drop
T{ s1 s3 slab-keep 9 s1 slab-push true s1 s3 slab-kept s1-cells s3 slab-count
   -> outcome-ok outcome-ok outcome-ok 5 1 2 0 }T
T{ s1 s3 slab-keep 9 s1 slab-push false s1 s3 slab-kept s1-cells s3 slab-count
   -> outcome-ok outcome-ok outcome-ok 5 1 9 3 0 }T
0 s1 slab-cut 5 s1 slab-push drop 1 s1 slab-push drop
s3 slab-free  1 cells 2 s3 slab-init drop
\ With no copy kept: slab-underflow, nothing changed.
T{ s3 ' slab-forget underflow? s1 s3 ' slab-restore catch nip nip s3 slab-count
   s1 slab-count -> true slab-underflow 0 2 }T
s1 slab-free s2 slab-free s3 slab-free

\ Worklists: slab-all? pops a value and tests it, the test pushing more,
\ until the slab is empty (true ok), a test says false (false ok) or one
\ fails (false and its outcome), the values not yet tested left; the
\ trail shows the order, newest first. down? n: n < 5, n - 2 pushed when
\ positive.
1 cells 100 s1 slab-init drop  2 cells 100 s2 slab-init drop
variable all-trail
: trail+ ( n -- ) all-trail @ 10 * + all-trail ! ;
: all-run ( slab xt -- flag outcome trail ) 0 all-trail ! slab-all? all-trail @ ;
: step-push ( n -- outcome ) dup 0> if s1 slab-push else drop outcome-ok then ;
: down? ( n -- flag outcome ) dup trail+ dup 5 < swap 2 - step-push ;
T{ 3 s1 slab-push 4 s1 slab-push s1 ' down? all-run s1 slab-count
   -> outcome-ok outcome-ok true outcome-ok 4231 0 }T
T{ 7 s1 slab-push s1 ' down? all-run s1 slab-count s1 slab-pop
   -> outcome-ok false outcome-ok 7 1 5 }T
\ Empty: true and ok, no test run; a step that uses the return stack.
T{ s1 ' down? all-run -> true outcome-ok 0 }T
: down-r? ( n -- flag outcome ) >r r@ trail+ r@ 5 < r> 2 - step-push ;
T{ 4 s1 slab-push s1 ' down-r? ' all-run rs-checked -> outcome-ok true outcome-ok 42 }T
\ A failing test stops the run with false and its outcome, true flag or
\ not; the values below stay.
: fail-at-2 ( n -- flag outcome ) dup trail+ 2 = if true outcome-full else true outcome-ok then ;
T{ 1 s1 slab-push 2 s1 slab-push 3 s1 slab-push 2drop drop s1 ' fail-at-2 all-run
   s1 slab-count s1 slab-pop -> false outcome-full 32 1 1 }T
: fail-odd ( n -- flag outcome ) trail+ false 99 ;
T{ 5 s1 slab-push s1 ' fail-odd all-run s1 slab-count -> outcome-ok false 99 5 0 }T
\ A push the test makes that the slab refuses: full, through the test.
s3 slab-free 1 cells 1 s3 slab-init drop
: two? ( n -- flag outcome ) trail+ true 1 s3 slab-push 2 s3 slab-push outcome-and ;
T{ 9 s3 slab-push s3 ' two? all-run s3 slab-count -> outcome-ok false outcome-full 9 1 }T
\ Pairs: slab-2all? pops x1 x2 in slab-2push's order. pair? a b: a + b
\ < 9, a - 1 b pushed while a > 0; the trail holds each a.
: pair? ( a b -- flag outcome )
  over trail+ over 0> if over 1- over s2 slab-2push else outcome-ok then >r + 9 < r> ;
: all2-run ( slab xt -- flag outcome trail ) 0 all-trail ! slab-2all? all-trail @ ;
T{ 3 2 s2 slab-2push s2 ' pair? all2-run s2 slab-count -> outcome-ok true outcome-ok 3210 0 }T
T{ 8 3 s2 slab-2push s2 ' pair? all2-run s2 slab-2pop -> outcome-ok false outcome-ok 8 7 3 }T
T{ 2 2 s2 slab-2push s2 ' pair? ' all2-run rs-checked -> outcome-ok true outcome-ok 210 }T
\ A slab that is not live: false and invalid, no test run, nothing
\ popped; units too narrow for a pair throw slab-underflow, nothing
\ popped.
2 1 s2 slab-2push drop  s2 slab-seal @ 1+ s2 slab-seal !
T{ s2 ' pair? all2-run s2 slab-count -> false outcome-invalid 0 1 }T
s2 slab-seal @ 1- s2 slab-seal !
T{ s2 slab-2pop s1 slab-free s1 ' down? all-run -> 2 1 false outcome-invalid 0 }T
1 cells 100 s1 slab-init drop
T{ 5 s1 slab-push s1 ' pair? ' slab-2all? catch nip nip s1 slab-count s1 slab-pop
   -> outcome-ok -4132 1 5 }T
s1 slab-free s2 slab-free s3 slab-free

\ A randomized stack: pushes, pair pushes and pops against a model array,
\ the slab's limit reached now and then (full, nothing changed).
create stack-model 64 cells allot
variable stack-n   variable stack-seed   variable stack-bad
: stack-rnd ( n -- u ) stack-seed @ 1103515245 * 12345 + $7FFFFFFF and dup stack-seed ! 7 rshift swap mod ;
: stack-fail ( -- ) 1 stack-bad +! ;
: model@ ( k -- x ) cells stack-model + @ ;
: model-push ( x -- ) stack-n @ cells stack-model + ! 1 stack-n +! ;
: stack-push ( -- )
  1000 stack-rnd dup s1 slab-push stack-n @ 40 < if ok? 0= if stack-fail then model-push
  else outcome-full <> if stack-fail then drop then ;
: stack-2push ( -- )   \ a cell slab: refused as too narrow
  1 2 s1 slab-2push outcome-invalid <> if stack-fail then ;
: stack-pop ( -- )
  stack-n @ 0= if s1 ['] slab-pop underflow? 0= if stack-fail then exit then
  s1 slab-pop -1 stack-n +! stack-n @ model@ <> if stack-fail then ;
: stack-check ( -- )
  s1 slab-count stack-n @ <> if stack-fail then
  stack-n @ if s1 slab-last @ stack-n @ 1- model@ <> if stack-fail then then ;
: stack-step ( -- )
  10 stack-rnd dup 5 < if drop stack-push else 6 < if stack-2push else stack-pop then then
  stack-check ;
: stack-run ( seed steps -- bad )
  swap stack-seed ! 0 stack-bad ! 0 stack-n ! 1 cells 40 s1 slab-init drop
  0 ?do stack-step loop s1 slab-free stack-bad @ ;
T{ 1 20000 stack-run 2 20000 stack-run -> 0 0 }T

\ A randomized model: claims, marks into eight records, rollbacks and
\ clears, compared at every step with a model that keeps the count and,
\ per mark, whether it lives (a mark dies when a rollback goes below its
\ count or the slab is cleared) and its count.
8 constant #model-marks
create model-alive #model-marks cells allot
create model-at #model-marks cells allot
variable model-n   variable model-seed   variable model-bad
: model-rnd ( n -- u ) model-seed @ 1103515245 * 12345 + $7FFFFFFF and dup model-seed ! 7 rshift swap mod ;
: alive ( k -- addr ) cells model-alive + ;
: at ( k -- addr ) cells model-at + ;
: bad ( -- ) 1 model-bad +! ;
: model-kill-above ( n -- ) #model-marks 0 do dup i at @ < if false i alive ! then loop drop ;
: model-claim ( -- )
  4 model-rnd dup s1 slab-claim 2 pick model-n @ + 60 >
  if nip outcome-full <> if bad then drop exit then
  ok? 0= if bad then model-n @ <> if bad then model-n +! ;
: model-mark ( -- )
  #model-marks model-rnd dup mark# s1 slab-mark ok? 0= if bad then
  true over alive ! model-n @ swap at ! ;
: model-rollback ( -- )
  #model-marks model-rnd dup mark# s1 slab-rollback ok? over alive @ <> if bad then
  dup alive @ if at @ dup model-n ! model-kill-above else drop then ;
: model-clear ( -- ) s1 slab-clear 0 model-n ! model-alive #model-marks cells erase ;
: model-cut ( -- ) model-n @ 1+ model-rnd dup s1 slab-cut dup model-n ! model-kill-above ;
: model-check ( -- )
  s1 slab-count model-n @ <> if bad then
  #model-marks 0 do i mark# s1 slab-mark-valid? i alive @ <> if bad then loop ;
: model-step ( -- )
  22 model-rnd dup 8 < if drop model-claim else dup 13 < if drop model-mark else
  dup 19 < if drop model-rollback else 21 < if model-cut else model-clear then then then
  then model-check ;
: model-run ( seed steps -- bad )
  swap model-seed ! 0 model-bad ! 0 model-n ! model-alive #model-marks cells erase
  1 cells 60 s1 slab-init drop 0 ?do model-step loop s1 slab-free model-bad @ ;
T{ 1 20000 model-run 2 20000 model-run 3 20000 model-run -> 0 0 0 }T
bye
