\ Tests for untrusted structured-name interning; no theorem is checked.
include ../support/tester.fs
include ../../src/core/names.fs

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

\ Exhaust byte storage while retaining free node slots and retry duplicates.
create name-test-bytes lf-name-byte-capacity allot
name-test-bytes lf-name-byte-capacity 65 fill
lf-name-reset
T{ 0 name-test-bytes lf-name-byte-capacity lf-name-str -> 1 true }T
T{ lf-name-used @ -> lf-name-byte-capacity }T
T{ 0 name-test-bytes lf-name-byte-capacity lf-name-str -> 1 true }T
T{ 0 s" x" lf-name-str -> false }T
T{ lf-name-count @ -> 2 }T

\ Invalid counters and saturated generation fail closed until a fresh process.
-1 lf-name-used !
T{ 0 1 lf-name-num -> false }T
lf-name-reset
lf-name-byte-capacity 1+ lf-name-used !
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
bye
