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

\ Internal offset corruption is detected before byte comparison or allocation.
lf-name-byte-capacity 1+ 1 lf-name-slot lf-entry-payload !
T{ 0 s" u" lf-name-str -> false }T
T{ 0 7 lf-name-num -> false }T
T{ lf-name-count @ -> 9 }T
0 1 lf-name-slot lf-entry-payload !
T{ 0 s" u" lf-name-str -> 1 true }T
99 1 lf-name-slot lf-entry-tag !
T{ 0 1 lf-name-num -> false }T
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
bye
