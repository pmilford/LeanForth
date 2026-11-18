\ Tests for untrusted structured-name interning; no theorem is checked.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/core/names.fs

\ Equal components under equal prefixes are interned; different prefixes and
\ numeric versus string components remain distinct.
lf-name-reset
T{ 0 s" u" lf-name-str -> 1 true }T
T{ 0 s" u" lf-name-str -> 1 true }T
T{ 0 s" v" lf-name-str -> 2 true }T
T{ 1 s" u" lf-name-str -> 3 true }T
T{ 0 1 lf-name-num -> 4 true }T
T{ 0 1 lf-name-num -> 4 true }T
T{ 0 s" 1" lf-name-str -> 5 true }T
T{ 1 1 lf-name-num -> 6 true }T
T{ 0 s" α" lf-name-str -> 7 true }T
T{ 0 s" α" lf-name-str -> 7 true }T
T{ 0 s" " lf-name-str -> 8 true }T
T{ 0 s" " lf-name-str -> 8 true }T
T{ lf-name-count @ -> 9 }T
T{ 3 1 lf-name-field -> 1 }T
T{ 4 0 lf-name-field -> lf-name-tag-num }T
T{ 5 0 lf-name-field -> lf-name-tag-str }T

\ Invalid prefixes, lengths and numeric components do not allocate.
T{ -1 0 lf-name-num -> false }T
T{ 9 0 lf-name-num -> false }T
T{ 0 -1 lf-name-num -> false }T
T{ -1 s" bad" lf-name-str -> false }T
T{ 9 s" bad" lf-name-str -> false }T
T{ 0 0 -1 lf-name-str -> false }T
T{ 123 0 0 -1 lf-name-str -> 123 false }T
T{ lf-name-count @ -> 9 }T

\ Internal offset corruption is detected before byte comparison or
\ allocation: the find that reaches the corrupted entry refuses its name.
\ The kept audit (ADR 0005 Amendment 1) does not read an entry it passed
\ again, so the storage still passes it; an audit from entry 1 does not.
lf-name-byte-capacity 1+ 1 lf-name-slot lf-entry-payload !
T{ 0 s" u" lf-name-str -> false }T
T{ lf-name-storage-valid? 1 lf-name-entries-from? 2 lf-name-entries-from? -> true false true }T
T{ lf-name-count @ -> 9 }T
0 1 lf-name-slot lf-entry-payload !
T{ 0 s" u" lf-name-str -> 1 true }T
99 1 lf-name-slot lf-entry-tag !
T{ 0 s" u" lf-name-str 1 lf-name-entries-from? -> false false }T
lf-name-tag-str 1 lf-name-slot lf-entry-tag !
1 1 lf-name-slot lf-entry-prefix !
T{ 0 s" u" lf-name-str -> false }T
0 1 lf-name-slot lf-entry-prefix !
-1 1 lf-name-slot lf-entry-length !
T{ 0 s" u" lf-name-str -> false }T
lf-name-used @ 1+ 1 lf-name-slot lf-entry-length !
T{ 0 s" u" lf-name-str -> false }T
1 1 lf-name-slot lf-entry-length !
1 0 lf-name-slot lf-entry-tag !
T{ 0 1 lf-name-num -> false }T
0 0 lf-name-slot lf-entry-tag !
T{ 0 s" u" lf-name-str -> 1 true }T

\ A query may alias this module's own buffers, because it is copied before
\ anything changes: the whole input copy, and the unused tail of the byte
\ store. The caller still guarantees that source memory is valid.
create name-test-scratch 2 allot
s" xy" name-test-scratch swap move
lf-name-reset
name-test-scratch lf-name-input-copy 2 move
T{ 0 lf-name-input-copy 2 lf-name-str -> 1 true }T
T{ 1 2 lf-name-field lf-name-bytes + 2 name-test-scratch 2 compare -> 0 }T
s" pq" lf-name-bytes lf-name-used @ + swap move
T{ 0 lf-name-bytes lf-name-used @ + 2 lf-name-str -> 2 true }T
T{ 0 s" pq" lf-name-str -> 2 true }T
T{ lf-name-count @ -> 3 }T
lf-name-reset
T{ 0 s" abc" lf-name-str -> 1 true }T
T{ 0 lf-name-bytes 1+ 2 lf-name-str -> 2 true }T
T{ 0 s" bc" lf-name-str -> 2 true }T
T{ 0 s" abc" lf-name-str -> 1 true }T
T{ 0 lf-name-input-copy 1+ 2 lf-name-str -> 2 true }T

\ A query may also alias the next free entry, or an existing entry's own
\ record; the stored names stay intact.
lf-name-reset
T{ 0 s" u" lf-name-str -> 1 true }T
s" ab" lf-name-count @ lf-name-slot swap move
T{ 0 lf-name-count @ lf-name-slot 2 lf-name-str -> 2 true }T
T{ 0 s" ab" lf-name-str -> 2 true }T
T{ 0 1 lf-name-slot 1 cells lf-name-str -> 3 true }T
T{ 0 s" u" lf-name-str -> 1 true }T
T{ lf-name-storage-valid? -> true }T

\ Exhaust node storage. A duplicate may still be found without allocating.
lf-name-reset
: fill-numeric-names ( -- )
  lf-name-capacity 1 ?do
    0 i lf-name-num 0= if -1 throw then drop
  loop ;
fill-numeric-names
T{ lf-name-count @ -> lf-name-capacity }T
T{ 0 1 lf-name-num -> 1 true }T
T{ 0 999 lf-name-num -> false }T
T{ 0 s" new" lf-name-str -> false }T

\ Byte storage has no fixed limit (plan task 6.2.0): a name longer than
\ the pool's first room, and more after it, grow it; a duplicate is still
\ found without storing its bytes again.
create name-test-bytes 3000 allot
name-test-bytes 3000 65 fill
lf-name-reset
T{ 0 name-test-bytes 3000 lf-name-str -> 1 true }T
T{ lf-name-used @ lf-name-byte-room 3000 < -> 3000 false }T
T{ 0 name-test-bytes 3000 lf-name-str -> 1 true }T
T{ 0 s" x" lf-name-str lf-name-used @ -> 2 true 3001 }T
T{ lf-name-count @ -> 3 }T
T{ 0 name-test-bytes 3000 lf-name-str 1 lf-name-text name-test-bytes 3000 compare
   -> 1 true 0 }T

\ Invalid counters and saturated generation fail closed until a fresh process.
-1 lf-name-used !
T{ 0 1 lf-name-num -> false }T
lf-name-reset
lf-name-byte-room 1+ lf-name-used !
T{ 0 1 lf-name-num -> false }T
lf-name-reset
0 lf-name-count !
T{ 0 1 lf-name-num -> false }T
lf-name-capacity 1+ lf-name-count !
T{ 0 1 lf-name-num -> false }T
lf-name-reset
-1 1 rshift lf-name-generation !
lf-name-reset
T{ lf-name-generation @ -> -1 }T
T{ 0 1 lf-name-num -> false }T

\ The component of a valid name: a string's bytes, a number.
0 lf-name-generation !
lf-name-reset
T{ 0 s" Nat" lf-name-str -> 1 true }T
T{ 1 41 lf-name-num -> 2 true }T
T{ 1 lf-name-text s" Nat" compare 2 lf-name-payload -> 0 41 }T
T{ 1 lf-name-tag@ 2 lf-name-tag@ -> lf-name-tag-str lf-name-tag-num }T

\ Kinds, depth, ancestors, root (reuse-out-2, ROUT3): Nat.41.zero is 3.
T{ 2 s" zero" lf-name-str -> 3 true }T
T{ 1 lf-name-str? 2 lf-name-str? 0 lf-name-str? 3 lf-name-str? -> true false false true }T
T{ 1 lf-name-num? 2 lf-name-num? 0 lf-name-num? 3 lf-name-num? -> false true false false }T
T{ 3 s" zero" lf-name-str-is? 3 s" zer" lf-name-str-is? 1 s" Nat" lf-name-str-is? -> true false true }T
T{ 2 s" 41" lf-name-str-is? 0 s" " lf-name-str-is? -> false false }T
T{ 0 lf-name-depth 1 lf-name-depth 3 lf-name-depth -> 0 1 3 }T
T{ 3 0 lf-name-ancestor 3 1 lf-name-ancestor 3 2 lf-name-ancestor 3 3 lf-name-ancestor -> 3 2 1 0 }T
T{ 3 lf-name-root 2 lf-name-root 1 lf-name-root 0 lf-name-root -> 1 1 1 0 }T
T{ 0 lf-name-anon? 1 lf-name-anon? 2 lf-name-anon? -> true false false }T
\ A name kept with its generation is current until the store is reset.
T{ 3 lf-name-generation @ lf-name-current? 3 lf-name-generation @ 1+ lf-name-current? -> true false }T
T{ lf-name-count @ lf-name-generation @ lf-name-current? -> false }T
\ A one-component name by its text: Nat is, Nat.41.zero and the anonymous
\ name are not, nor is a string that differs.
T{ 1 s" Nat" lf-name-top? 3 s" zero" lf-name-top? 1 s" Na" lf-name-top? -> true false false }T
T{ 0 s" " lf-name-top? 2 s" 41" lf-name-top? 1 s" Nat" ' lf-name-top? rs-checked -> false false true }T
T{ 3 ' lf-name-root rs-checked 3 2 ' lf-name-ancestor rs-checked -> 1 1 }T
\ Putting components on a base: Std, then Std.Nat.41.zero from Nat.41.zero
\ (all three components, numeric one included), and its last two alone.
T{ 0 s" Std" lf-name-str -> 4 true }T
T{ 4 3 lf-name-put 4 2 lf-name-put -> 5 true 6 true }T
T{ 5 lf-name-text s" zero" compare 5 lf-name-prefix@ 6 lf-name-payload -> 0 4 41 }T
T{ 3 3 4 lf-name-graft -> 9 true }T
T{ 9 lf-name-depth 9 lf-name-root 9 lf-name-prefix@ lf-name-payload -> 4 4 41 }T
T{ 9 lf-name-text s" zero" compare 3 2 4 lf-name-graft 3 0 4 lf-name-graft -> 0 10 true 4 true }T
T{ 3 3 4 ' lf-name-graft rs-checked -> 9 true }T
\ A refusal stops the graft: false alone, the count unchanged after it.
lf-name-count @ constant names-before-full
lf-name-capacity lf-name-count !
T{ 3 3 9 lf-name-graft 9 3 lf-name-put 3 3 0 lf-name-graft -> false false 3 true }T
names-before-full lf-name-count !

\ ---------------------------------------------------------------------------
\ The index (ADR 0005 Amendment 1), against the linear search it replaced:
\ every name interned gets the ID the first equal entry has, or the next
\ ID. The names mix both kinds, many prefixes and many repeats.
create ref-text 8 allot  variable ref-len
: ref-text! ( c-addr u -- ) dup ref-len ! ref-text swap move ;
: ref-str? ( prefix id -- flag )
  dup lf-name-str? 0= if 2drop false exit then
  tuck lf-name-prefix@ = swap lf-name-text ref-text ref-len @ compare 0= and ;
: ref-num? ( prefix n id -- flag )
  dup lf-name-num? 0= if drop 2drop false exit then
  tuck lf-name-payload = -rot lf-name-prefix@ = and ;
: ref-find-str ( prefix -- id|0 )
  lf-name-count @ 1 ?do dup i ref-str? if drop i unloop exit then loop drop 0 ;
: ref-find-num ( prefix n -- id|0 )
  lf-name-count @ 1 ?do 2dup i ref-num? if 2drop i unloop exit then loop 2drop 0 ;
: ref-or-new ( id|0 -- id ) ?dup 0= if lf-name-count @ then ;
: mixed-num ( prefix n -- flag )
  2dup ref-find-num ref-or-new >r lf-name-num if r> = else r> drop false then ;
: mixed-str ( prefix n -- flag )
  0 <# #s #> ref-text! dup ref-find-str ref-or-new >r
  ref-text ref-len @ lf-name-str if r> = else r> drop false then ;
: mixed-one ( i -- flag )
  dup 31 * lf-name-count @ mod swap dup 50 mod swap 3 mod if mixed-num else mixed-str then ;
: mixed-all ( n -- flag ) true swap 0 ?do i mixed-one and loop ;
: index-whole? ( -- flag ) lf-name-table htab-count lf-name-count @ 1- = ;
lf-name-reset
T{ 8192 lf-name-capacity! -> outcome-ok }T
T{ 3000 mixed-all index-whole? -> true true }T
T{ 3000 mixed-all index-whole? lf-name-storage-valid? -> true true true }T
T{ lf-name-count @ 1000 > lf-name-table htab-slots 1024 > -> true true }T
\ A reset empties the index and makes a large table small again.
lf-name-reset
T{ lf-name-table htab-count lf-name-table htab-slots -> 0 16 }T
T{ 300 mixed-all index-whole? -> true true }T

\ Rollback (core/input.fs rolls the store back to its mark after each
\ check): the names given back leave the index at the next find, and are
\ made again under the same numbers; a name before the mark keeps its ID.
create name-mark /store-mark allot
T{ 0 s" early" lf-name-str -> lf-name-count @ 1- true }T
lf-name-count @ constant before-mark
lf-name-used @ constant used-mark
T{ name-mark lf-names store-mark -> outcome-ok }T
T{ 0 s" late-a" lf-name-str 0 s" late-b" lf-name-str -> before-mark true before-mark 1+ true }T
T{ name-mark lf-names store-rollback -> outcome-ok }T
used-mark lf-name-used !
T{ 0 s" late-b" lf-name-str index-whole? -> before-mark true true }T
T{ 0 s" late-a" lf-name-str 0 s" early" lf-name-str -> before-mark 1+ true before-mark 1- true }T
T{ index-whole? 1 lf-name-entries-from? lf-name-storage-valid? -> true true true }T
\ A rollback, then a store's block shrunk below the name given back: its
\ slot can no longer be taken out by hash and stays, and is passed over.
lf-name-count @ constant shrink-at
T{ name-mark lf-names store-mark 0 s" gone" lf-name-str -> outcome-ok shrink-at true }T
T{ name-mark lf-names store-rollback shrink-at lf-name-capacity! -> outcome-ok outcome-ok }T
T{ shrink-at 16 + lf-name-capacity! 0 s" gone" lf-name-str -> outcome-ok shrink-at true }T
T{ 0 s" gone" lf-name-str 0 s" late-a" lf-name-str -> shrink-at true before-mark 1+ true }T

\ A stale ID: detaching (no view: a reset) advances the generation and
\ empties the index; the same name is then made again as ID 1.
lf-name-reset
T{ 0 s" kept" lf-name-str -> 1 true }T
lf-name-generation @ constant gen-before
lf-name-detach
T{ 1 gen-before lf-name-current? lf-name-table htab-count lf-name-count @ -> false 0 1 }T
T{ 0 s" kept" lf-name-str 1 lf-name-generation @ lf-name-current? -> 1 true true }T

\ The index out of room: a table held to 16 slots takes 12 names; the
\ 13th is refused as names full (the entries listed, then 0), nothing is
\ made, and a name already there is still found.
lf-name-reset
lf-name-table htab-free lf-name-table-make 4 lf-name-table htab-limit
: index-fill ( -- flag ) true 13 1 ?do 0 i lf-name-num nip and loop ;
T{ index-fill lf-name-table htab-count -> true 12 }T
lf-diag-clear
T{ 0 13 lf-name-num lf-diag@ nip -> false 12 0 lf-diag-names-full }T
T{ 0 s" new" lf-name-str 0 5 lf-name-num lf-name-count @ -> false 5 true 13 }T
32 lf-name-table htab-limit
T{ 0 13 lf-name-num 0 s" new" lf-name-str -> 13 true 14 true }T

\ The kept audit: an entry made since the last audit is read, the newest
\ too; one it passed is not read again, until byte use goes down (then,
\ and after a failed audit, every entry is read again).
lf-name-reset
T{ 0 s" a" lf-name-str 0 s" b" lf-name-str -> 1 true 2 true }T
99 2 lf-name-slot lf-entry-tag !
T{ lf-name-storage-valid? 0 s" c" lf-name-str -> false false }T
lf-name-tag-str 2 lf-name-slot lf-entry-tag !
T{ lf-name-storage-valid? -> true }T
99 1 lf-name-slot lf-entry-tag !
T{ lf-name-storage-valid? 0 s" c" lf-name-str -> true 3 true }T
T{ lf-name-storage-valid? -> true }T
lf-name-used @ 1- lf-name-used !
T{ lf-name-storage-valid? -> false }T
lf-name-used @ 1+ lf-name-used !
T{ lf-name-storage-valid? -> false }T
lf-name-tag-str 1 lf-name-slot lf-entry-tag !
T{ lf-name-storage-valid? -> true }T
\ After a reset every entry is read again, here two that a raw count and
\ byte use exposed, the second corrupted.
99 2 lf-name-slot lf-entry-tag !
lf-name-reset 3 lf-name-used ! 3 lf-name-count !
T{ lf-name-storage-valid? -> false }T

\ A walk's check (lf-name-chain-ok?): every component of the chain is a
\ name whose own entry is well formed. A prefix pointed forward after the
\ audit passed the entry (here a cycle: 2 -> 3 -> 2) and a text outside
\ the bytes in use are caught on the walk, so it ends.
lf-name-reset
T{ 0 s" A" lf-name-str 1 s" B" lf-name-str 2 7 lf-name-num -> 1 true 2 true 3 true }T
T{ 3 lf-name-chain-ok? 0 lf-name-chain-ok? 4 lf-name-chain-ok? -1 lf-name-chain-ok? -> true true false false }T
T{ lf-name-storage-valid? lf-name-audit-all? -> true true }T
3 2 lf-name-slot lf-entry-prefix !
T{ lf-name-storage-valid? 3 lf-name-chain-ok? 2 lf-name-chain-ok? 1 lf-name-chain-ok? -> true false false true }T
T{ lf-name-audit-all? -> false }T
1 2 lf-name-slot lf-entry-prefix !
lf-name-used @ 1+ 1 lf-name-slot lf-entry-length !
T{ 3 lf-name-chain-ok? lf-name-audit-all? -> false false }T
1 1 lf-name-slot lf-entry-length !
T{ 3 lf-name-chain-ok? lf-name-audit-all? -> true true }T
\ The kept hashes (the hand-over audit, lf-name-audit-all?): a hash cell
\ rewritten after the audit passed its entry is found.
2 lf-name-slot lf-entry-hash @ constant hash-2
5 2 lf-name-slot lf-entry-hash !
T{ lf-name-storage-valid? lf-name-hashes-ok? lf-name-audit-all? -> true false false }T
hash-2 2 lf-name-slot lf-entry-hash !
T{ lf-name-hashes-ok? -> true }T

\ The index with no table block (the heap refused it): every name is
\ refused as names full, a name already made too, and nothing is read; a
\ reset makes the table again.
lf-name-reset
T{ 0 s" kept" lf-name-str -> 1 true }T
lf-name-table htab-free lf-diag-clear
T{ 0 s" kept" lf-name-str 0 s" new" lf-name-str lf-diag-code@ -> false false lf-diag-names-full }T
T{ lf-name-count @ lf-name-table htab-live? -> 2 false }T
lf-name-reset
T{ lf-name-table htab-live? 0 s" kept" lf-name-str -> true 1 true }T
lf-name-reset
bye
