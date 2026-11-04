\ Hash-consed sets of records in two tiers (ADR 0016 C3, C4). A general
\ tool with no Lean knowledge; untrusted. A set (a cons) keeps each
\ distinct record once and names it by a number: records live in a slab
\ (slab.fs), a hash table (htab.fs) finds them by content, and texts that
\ records refer to live in a second slab of bytes. A class says how the
\ records of one kind are hashed, compared and measured; pools.fs has the
\ classes of interned lists and texts, and the Lean store its own.
\
\ Two tiers. A set may extend a sealed set, its *under* set: a big input
\ set, filled once and then read-only, shared by every worker without
\ locks, and a small per-check set, emptied after each check. Numbers
\ continue: below the extension's first number they name the under set's
\ records, from it the extension's own. Finding a candidate looks in the
\ under set first, when the caller says the candidate may be there (a
\ candidate whose parts are all under records may be; one with an own part
\ cannot), so a record rebuilt by a check gets the input's number; then
\ in the own set. A set that extends another never changes it.
\
\ Building a record, the protocol every class follows:
\   1. cons-room: room for the candidate's units and bytes, and the table
\      ready for one more entry (full when there is none);
\   2. write the candidate at cons-top, the first free unit (a text it
\      refers to stays where it is, in cons-key, until it is kept);
\   3. cons-find with the candidate's hash: an equal record's number, or
\      the empty slot where the candidate belongs;
\   4. if new: cons-commit keeps the candidate and enters it into the
\      table (full at the class's limit), then cons-text, keeps the text
\      and the record is given its offset.
\ Equal numbers always mean equal records, because an entry is returned
\ only when the class's comparison says so (a hash match is only a
\ hint); soundness never depends on the table, which only makes finding
\ fast (ADR 0016 C8).
\
\ A class (cons-class:) gives the record unit's size, the most numbers of
\ the two tiers together (at most 2^32-1, since a table slot holds a
\ number plus one), and three hooks; each gets the set's address as the
\ table's, because the table comes first in a set:
\   rehash ( n cons -- h )       the hash of record n, recomputed from it
\   same ( n key cons -- flag )  record n of cons equals the candidate of key
\   span ( local cons -- units ) units of cons's own record at local
\
\ Marks (cons-mark, cons-rollback) work as slab.fs's for an open set, and
\ also take the records given back out of the table (Algorithm R); the
\ under set has no marks. cons-reset empties an open set. cons-seal makes
\ a set read-only: its table is rebuilt at most half full (ADR 0016 C4) and
\ its slabs trimmed. Outcomes (ADR 0008): ok; full for a limit or no heap;
\ invalid for a sealed or corrupted set, a bad argument or a stale mark.
\
\ Example (with pools.fs): an input set of texts, sealed, and a scratch set
\ over it that finds the input's texts and adds its own.
\   create input /cons allot   create scratch /cons allot
\   4 text-class input cons-init drop
\   s" Nat" input text-intern 2drop  input cons-seal drop
\   4 input scratch cons-extend drop
\   s" Nat" scratch text-intern drop .     \ 0, the input's
\   s" Int" scratch text-intern drop .     \ 1, the scratch set's first
\   scratch cons-reset drop  scratch cons-free  input cons-free
\
\ Interface: cons-class: cons-hooks! /cons cons-init cons-extend cons-free
\ cons-numbers cons-first cons-under cons-at cons-text-at cons-top
\ cons-key cons-room cons-find cons-text, cons-commit cons-entry? /cons-mark
\ cons-mark cons-mark-valid? cons-rollback cons-reset cons-seal
\ cons-sealed? cons-building cons-table cons-records cons-bytes
\ cons-numbers-max. State: none of its own; classes are made while
\ loading and read-only afterwards; a set owns its heap blocks until
\ cons-free. A set is single-threaded while it changes; any number of
\ tasks may read and find in a sealed set. Speed: the hooks are called
\ through EXECUTE, about one call per record compared; measured in
\ docs/development/FORTH_LIBRARY.md. Loads in decimal whatever BASE is,
\ then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./outcome.fs
require ./u32.fs
require ./slab.fs
require ./htab.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
\ The most numbers a class may allow: a table slot holds a number plus one
\ in 32 bits; on a 32-bit host, the largest positive cell.
u32-mask 0> [if] u32-mask [else] max-n [then] constant cons-numbers-max

begin-structure /cons-class
  /htab-hooks +field class-hooks    \ first: the table's rehash and same
  field: class-span        \ xt ( local cons -- units )
  field: class-unit        \ address units per record unit
  field: class-limit       \ most numbers in the two tiers together
end-structure
\ A class of records of unit address units, at most limit numbers.
: cons-class: ( unit limit "name" -- )
  create here /cons-class allot dup /cons-class erase
  swap cons-numbers-max min over class-limit ! class-unit ! ;
\ Set a class's hooks.
: cons-hooks! ( rehash same span class -- )
  tuck class-span ! class-hooks htab-hooks! ;

begin-structure /cons
  /htab +field cons-table     \ first, so the table's hooks get the set
  /slab +field cons-records   \ the own records
  /slab +field cons-bytes     \ the own records' texts
  field: cons-class
  field: cons-first           \ the first own number: the under set's count
  field: cons-under           \ the sealed set this one extends, or 0
  field: cons-sealed          \ true once sealed
  field: cons-building        \ for classes that build a candidate in steps
  aligned 2 cells +field cons-key   \ the candidate's text, address and length
end-structure

\ Numbers so far, and the set that holds number n: the under set below the
\ first own number.
: cons-numbers ( cons -- n ) dup cons-first @ swap cons-records slab-count + ;
: cons-sealed? ( cons -- flag ) cons-sealed @ ;
lf-lib-private set-current
: cons-home ( n cons -- n cons' ) 2dup cons-first @ u< if cons-under @ then ;
: cons-local ( n cons -- local slab ) tuck cons-first @ - swap cons-records ;
lf-lib set-current
\ Unchecked: the address of record n, of the bytes at offset of record
\ n's tier, and of the candidate.
: cons-at ( n cons -- addr ) cons-home cons-local slab-at ;
: cons-text-at ( offset n cons -- addr ) cons-home nip cons-bytes slab-at ;
: cons-top ( cons -- addr ) cons-records slab-top ;
lf-lib-private set-current

\ The class's hooks, for the set's own records.
: cons-rehash ( n cons -- h ) dup cons-class @ hook-rehash @ execute ;
: cons-span ( local cons -- units ) dup cons-class @ class-span @ execute 1 max ;

\ Making a set. The records' slab holds two units more than the numbers
\ the class allows, so that a candidate of up to two units can be built,
\ and found, when the set is at its limit; cons-commit checks the limit.
2 constant cons-spare
: cons-limit ( cons -- n ) cons-class @ class-limit @ ;
: cons-records-init ( limit cons -- outcome )
  swap cons-spare + over cons-class @ class-unit @ swap rot cons-records slab-init ;
: cons-bytes-init ( cons -- outcome ) 1 chars cons-numbers-max rot cons-bytes slab-init ;
: cons-slabs-init ( cons -- outcome )
  dup cons-limit over cons-records-init dup ok? if drop cons-bytes-init else nip then ;
lf-lib set-current
\ An empty set of the class with a table of 2^log2 slots: ok, invalid for
\ a bad class, or full. It allocates only the table; the slabs grow when
\ used. It must not be given a set that holds memory: cons-free first.
: cons-init ( log2 class cons -- outcome )
  dup /cons erase tuck cons-class ! dup cons-slabs-init dup ok?
  if drop dup cons-class @ swap cons-table htab-init else nip nip then ;
: cons-free ( cons -- )
  dup cons-table htab-free dup cons-records slab-free dup cons-bytes slab-free /cons erase ;
lf-lib-private set-current
: cons-attach ( under cons -- outcome )
  2dup cons-under ! swap cons-numbers over cons-first !
  dup cons-limit over cons-first @ - swap cons-records-init ;
: cons-sealed-live? ( cons -- flag )
  dup cons-sealed? swap cons-table htab-block @ 0<> and ;
lf-lib set-current
\ An empty set over the sealed set under, of its class, with a table of
\ 2^log2 slots: ok, invalid when under is not sealed, or full.
: cons-extend ( log2 under cons -- outcome )
  over cons-sealed-live? 0= if 2drop drop outcome-invalid exit then
  >r dup cons-class @ rot swap r@ cons-init dup ok?
  if drop r> cons-attach else nip r> drop then ;

\ An open set may change: not sealed, with a table.
: cons-open? ( cons -- flag ) dup cons-sealed? 0= swap cons-table htab-block @ 0<> and ;
lf-lib-private set-current
: cons-bytes-room ( bytes cons -- outcome )
  over if cons-bytes slab-room else 2drop outcome-ok then ;
lf-lib set-current
\ Room for a candidate of units record units and bytes of text, and the
\ table ready for one more entry: ok, full, or invalid for a sealed set.
: cons-room ( units bytes cons -- outcome )
  dup cons-open? 0= if drop 2drop outcome-invalid exit then
  tuck cons-bytes-room dup ok? 0= if nip nip exit then drop
  tuck cons-records slab-room dup ok? 0= if nip exit then drop
  cons-table htab-ready ;
lf-lib-private set-current
\ Look in the under set, read-only, giving the key as this set.
: cons-under-find ( h cons -- n true | false )
  dup cons-under @ ?dup 0= if 2drop false exit then
  rot swap htab-find dup 0= if nip then ;
lf-lib set-current
\ Find the candidate whose hash is h: under? says it may be in the under
\ set, which is searched first. A record's number and true, or the empty
\ slot of the own table where it belongs and false. cons-room first.
: cons-find ( h under? cons -- n true | i false )
  swap if 2dup cons-under-find if nip nip true exit then then tuck cons-table htab-find ;
\ Unchecked, after cons-room and a find that gave false: keep u bytes of
\ text at addr as the own set's, giving their offset.
: cons-text, ( addr u cons -- offset )
  cons-bytes >r r@ slab-count -rot tuck r@ slab-top swap move r> slab-commit ;
\ After cons-room and a find that gave slot i: keep the candidate of units
\ record units as a new record and enter it at slot i: its number and ok,
\ or -1 and full, with nothing kept, when the class's limit of numbers
\ would be passed. A text the record refers to is kept after it, with
\ cons-text, (whose room cons-room made).
lf-lib-private set-current
: cons-past? ( units cons -- flag ) dup cons-numbers rot + swap cons-limit > ;
lf-lib set-current
: cons-commit ( units i cons -- n outcome )
  >r over r@ cons-past? if 2drop r> drop outcome-full no-result exit then
  r@ cons-numbers tuck swap r@ cons-table htab-put swap r> cons-records slab-commit outcome-ok ;

\ Whether n names a record of the set or its under set: in range, the
\ record within the numbers, and found in its table (exact: a number in
\ the middle of a record, or of a part of a record that is not an entry,
\ is refused).
lf-lib-private set-current
: cons-fits? ( n cons -- flag ) cons-numbers 0 swap within ;
\ Unchecked: n is in range. Its record ends within its tier.
: cons-whole? ( n cons -- flag )
  cons-home tuck cons-local slab-count >r tuck swap cons-span + r> <= ;
: cons-listed? ( n cons -- flag ) cons-home 2dup cons-rehash swap cons-table htab-holds? ;
lf-lib set-current
: cons-entry? ( n cons -- flag )
  2dup cons-fits? 0= if 2drop false exit then
  2dup cons-whole? if cons-listed? else 2drop false then ;

\ Forgetting the own records from local on: their table entries go.
lf-lib-private set-current
: cons-unlist ( local cons -- )
  tuck cons-first @ + swap 2dup cons-rehash swap cons-table htab-remove drop ;
: cons-forget ( local cons -- )
  begin 2dup cons-records slab-count < while
    2dup cons-unlist 2dup cons-span rot + swap
  repeat 2drop ;
\ Emptying the table costs its size; forgetting costs the records: choose
\ the cheaper.
: cons-crowded? ( cons -- flag ) dup cons-records slab-count 4 * swap cons-table htab-slots > ;
: cons-empty ( cons -- )
  dup cons-crowded? if cons-table htab-clear else 0 swap cons-forget then ;
: cons-cleared ( cons -- ) dup cons-records slab-clear cons-bytes slab-clear ;

\ Marks: one for the records and one for the texts.
lf-lib set-current
begin-structure /cons-mark
  /slab-mark +field cons-mark-records
  /slab-mark +field cons-mark-bytes
end-structure
lf-lib-private set-current
: cons-mark-records? ( mark cons -- mark-part slab ) cons-records swap cons-mark-records swap ;
: cons-mark-bytes? ( mark cons -- mark-part slab ) cons-bytes swap cons-mark-bytes swap ;
lf-lib set-current
\ Mark an open set: ok; or, with a mark every rollback refuses, invalid or
\ full.
: cons-mark ( mark cons -- outcome )
  dup cons-open? 0= if drop /cons-mark erase outcome-invalid exit then
  2dup cons-mark-records? slab-mark dup ok? 0= if nip nip exit then drop
  cons-mark-bytes? slab-mark ;
: cons-mark-valid? ( mark cons -- flag )
  dup cons-open? 0= if 2drop false exit then
  2dup cons-mark-records? slab-mark-valid? >r cons-mark-bytes? slab-mark-valid? r> and ;
lf-lib-private set-current
: cons-slabs-back ( mark cons -- )
  2dup cons-mark-records? slab-rollback drop cons-mark-bytes? slab-rollback drop ;
lf-lib set-current
\ Give back every record made since the mark, with its table entry and
\ text: ok, or invalid with nothing changed. A candidate being built is
\ dropped.
: cons-rollback ( mark cons -- outcome )
  2dup cons-mark-valid? 0= if 2drop outcome-invalid exit then
  over cons-mark-records slab-mark-count @ over cons-forget
  false over cons-building ! cons-slabs-back outcome-ok ;
\ Empty an open set: ok, or invalid for a sealed one. Its generation
\ grows, so every mark of it is refused afterwards.
: cons-reset ( cons -- outcome )
  dup cons-open? 0= if drop outcome-invalid exit then
  dup cons-empty false over cons-building ! cons-cleared outcome-ok ;
\ Make an open set read-only: the table rebuilt at most half full and the
\ slabs trimmed (both kept as they were when the heap has no room for it,
\ which only costs speed). ok, or invalid when it is not open.
: cons-seal ( cons -- outcome )
  dup cons-open? 0= if drop outcome-invalid exit then
  dup cons-table htab-spread drop dup cons-records slab-trim drop
  dup cons-bytes slab-trim drop true swap cons-sealed ! outcome-ok ;

module-close
base !   \ the BASE this file was loaded with
