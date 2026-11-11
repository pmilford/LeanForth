\ Test-only access to the records and identities of the term and level
\ stores (compact-store plan step S2). A test that plants a fault in a
\ record (a tag, a child, a payload), reads an identity without a check,
\ or reads or spends a store's identity serial goes through these words,
\ never through the record layout (lf-term-slot and cell offsets) or the
\ serial cells, so that the layout can change (plan step S3: compact
\ records) by changing this file alone. Nothing here checks anything: a
\ fault word writes what a corrupted store would hold. Production code
\ never loads this file. Example: plant a forward child in node 3, then
\ expect every pass over it to refuse:
\   7 3 term-first!

require ../../src/core/terms.fs
require ../../src/core/levels.fs

\ Overwrite one field of a record (unchecked: the index is the test's).
\ Term records are four 32-bit fields (core/terms.fs, compact-store plan
\ step S3): a field keeps the low 32 bits of what is written, so -1
\ reads back as 2^32 - 1; the data word is never recomputed.
: term-tag! ( tag index -- ) lf-term-slot u32! ;
: term-first! ( first index -- ) lf-term-slot lf-term-first-at + u32! ;
: term-second! ( second index -- ) lf-term-slot lf-term-second-at + u32! ;
: term-data! ( data index -- ) lf-term-slot lf-term-data-at + u32! ;
: level-tag! ( tag index -- ) lf-level-slot node-tag ! ;
: level-first! ( first index -- ) lf-level-slot node-first ! ;
: level-second! ( second index -- ) lf-level-slot node-second ! ;

\ A record's identity read without any check: also of a record rolled
\ back, whose cell keeps the identity it had.
: term-identity@ ( index -- identity ) lf-terms store-identity @ ;
: level-identity@ ( index -- identity ) lf-levels store-identity @ ;

\ Break a store's seal, or mend it by flipping it again: the count stays
\ sound, so reads by index still read, and every checked root (a handle,
\ lf-term-root?, a count check) must refuse the store.
: seal-flip ( store -- ) store-seal dup @ invert swap ! ;
: term-seal-flip ( -- ) lf-terms seal-flip ;
: level-seal-flip ( -- ) lf-levels seal-flip ;

\ The identity a store issued last (that of its newest record, unless a
\ rollback removed it), and setting it, for instance to max-n to spend
\ the serial.
: term-serial ( -- identity ) lf-term-serial @ ;
: term-serial! ( identity -- ) lf-term-serial ! ;
: level-serial ( -- identity ) lf-level-serial @ ;
: level-serial! ( identity -- ) lf-level-serial ! ;
