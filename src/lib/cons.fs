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
\ cons-key cons-key! cons-key-fix cons-room cons-room-key cons-find
\ cons-text, cons-commit cons-entry? cons-in? cons-under? cons-base?
\ cons-open? cons-allocated cons-used /cons-mark cons-mark
\ cons-mark-valid? cons-rollback cons-reset cons-seal cons-sealed?
\ cons-building cons-table cons-records cons-bytes cons-under-finds
\ cons-numbers-max cons-load-room cons-adopt (loading a set's records from
\ a file, each checked by the caller; see cons-load-room).
\ A sealed set's table is frozen (htab.fs): finds in it write nothing.
\ Only a base set (sealed, extending none) can be extended, so there are
\ at most two tiers. State: none of its own; classes are made while
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
lf-lib-private set-current
  /htab-hooks +field class-hooks    \ first: the table's rehash and same
  field: class-span        \ xt ( local cons -- units )
  field: class-unit        \ address units per record unit
  field: class-limit       \ most numbers in the two tiers together
end-structure
lf-lib set-current
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
  field: cons-key-base        \ where that text lies in cons-bytes, or -1
  field: cons-under-finds     \ statistics: finds this set made in its under set
end-structure

\ Numbers so far, and the set that holds number n: the under set below the
\ first own number.
: cons-numbers ( cons -- n ) dup cons-first @ swap cons-records slab-count + ;
: cons-sealed? ( cons -- flag ) cons-sealed @ ;
\ Whether n is a number of the set or its under set, and whether it is an
\ under number.
: cons-in? ( n cons -- flag ) cons-numbers u< ;
: cons-under? ( n cons -- flag ) cons-first @ u< ;
lf-lib-private set-current
: cons-home ( n cons -- n cons' ) 2dup cons-under? if cons-under @ then ;
: cons-local ( n cons -- local slab ) tuck cons-first @ - swap cons-records ;
lf-lib set-current
\ Unchecked: the address of record n, of the bytes at offset of record
\ n's tier, and of the candidate.
: cons-at ( n cons -- addr ) cons-home cons-local slab-at ;
: cons-text-at ( offset n cons -- addr ) cons-home nip cons-bytes slab-at ;
: cons-top ( cons -- addr ) cons-records slab-top ;
\ Address units allocated, and in use, by the set's slabs and table.
: cons-allocated ( cons -- u )
  dup cons-records slab-bytes over cons-bytes slab-bytes +
  swap cons-table htab-slots u32s + ;
: cons-used ( cons -- u )
  dup cons-records slab-used-bytes over cons-bytes slab-used-bytes +
  swap cons-table htab-slots u32s + ;
lf-lib-private set-current

\ The class's hooks, for the set's own records. A span of 0 counts as 1,
\ so that walking the records always moves on.
: cons-rehash ( n cons -- h ) dup cons-class @ hook-rehash @ execute ;
: cons-span ( local cons -- units )
  dup cons-class @ class-span @ execute ?dup 0= if 1 then ;

\ Making a set. The records' slab holds two units more than the numbers
\ the class allows, so that a candidate of up to two units can be built,
\ and found, when the set is at its limit (cons-commit checks the limit);
\ never more than a cell can address, which on a 32-bit host is less than
\ cons-numbers-max of 16-byte records.
2 constant cons-spare
: cons-limit ( cons -- n ) cons-class @ class-limit @ ;
: spare+ ( n -- n' ) dup max-n cons-spare - u< if cons-spare + else drop max-n then ;
: cons-records-limit ( limit cons -- units )
  cons-class @ class-unit @ slab-limit-max swap spare+ min ;
: cons-records-init ( limit cons -- outcome )
  tuck cons-records-limit over cons-class @ class-unit @ swap rot cons-records slab-init ;
: cons-bytes-init ( cons -- outcome ) 1 chars cons-numbers-max rot cons-bytes slab-init ;
: cons-slabs-init ( cons -- outcome )
  dup cons-limit over cons-records-init dup ok? if drop cons-bytes-init else nip then ;
lf-lib set-current
\ An empty set of the class with a table of 2^log2 slots: ok, invalid for
\ a bad class, or full. It allocates only the table; the slabs grow when
\ used. It must not be given a set that holds memory: cons-free first.
: cons-init ( log2 class cons -- outcome )
  dup /cons erase -1 over cons-key-base ! tuck cons-class ! dup cons-slabs-init dup ok?
  if drop dup cons-class @ swap cons-table htab-init else nip nip then ;
: cons-free ( cons -- )
  dup cons-table htab-free dup cons-records slab-free
  dup cons-bytes slab-free /cons erase ;
lf-lib-private set-current
: cons-attach ( under cons -- outcome )
  2dup cons-under ! swap cons-numbers over cons-first !
  dup cons-limit over cons-first @ - swap cons-records-init ;
lf-lib set-current
\ Whether a set may be extended: sealed, with a live table, and extending
\ no set itself. Numbers name records one tier down only, so a set over a
\ sealed scratch set (three tiers) is refused.
: cons-base? ( cons -- flag )
  dup cons-sealed? over cons-table htab-live? and swap cons-under @ 0= and ;
\ An empty set over the set under, of its class, with a table of 2^log2
\ slots: ok, invalid when under is not a base set (cons-base?), or full.
: cons-extend ( log2 under cons -- outcome )
  over cons-base? 0= if 2drop drop outcome-invalid exit then
  >r dup cons-class @ rot swap r@ cons-init dup ok?
  if drop r> cons-attach else nip r> drop then ;

\ An open set may change: not sealed, with a live table.
: cons-open? ( cons -- flag ) dup cons-sealed? 0= swap cons-table htab-live? and ;
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
\ The candidate's text, kept in cons-key: addr u, and where addr lies in
\ the set's own byte slab, which may move while room is made (or -1).
: cons-key! ( addr u cons -- )
  >r 2dup r@ cons-key 2! drop r@ cons-bytes slab-offset r> cons-key-base ! ;
\ After room is made: the text's address again, when it lies in the slab.
: cons-key-fix ( cons -- )
  dup cons-key-base @ dup 0< if 2drop exit then over cons-bytes slab-at
  swap cons-key cell+ ! ;
\ Room for a candidate of units record units and the key's text (as
\ cons-room), its address found again: a text may come from the set's own
\ byte slab, for example a name's component given back to name-str.
: cons-room-key ( units cons -- outcome )
  >r r@ cons-key @ r@ cons-room dup ok? if r@ cons-key-fix then r> drop ;
lf-lib-private set-current
\ Look in the under set, read-only, giving the key as this set; the find
\ is counted here, in this set (the under set's table is frozen).
: cons-under-find ( h cons -- n true | false )
  dup cons-under @ ?dup 0= if 2drop false exit then
  over cons-under-finds 1 swap +! rot swap htab-find dup 0= if nip then ;
lf-lib set-current
\ Find the candidate whose hash is h: under? says it may be in the under
\ set, which is searched first, read-only (a sealed set's table is frozen,
\ so the find writes nothing there). A record's number and true, or the
\ empty slot of the own table where it belongs and false. cons-room first.
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
\ Whether units more numbers pass the limit, or the numbers already do;
\ compares with the numbers left, so no sum can wrap.
: cons-past? ( units cons -- flag )
  dup cons-limit swap cons-numbers 2dup u< if 2drop drop true else - u> then ;
lf-lib set-current
: cons-commit ( units i cons -- n outcome )
  >r over r@ cons-past? if 2drop r> drop outcome-full no-result exit then
  r@ cons-numbers tuck swap r@ cons-table htab-put swap r> cons-records slab-commit
  outcome-ok ;

\ Loading a set from a file (a snapshot): its records, written by the
\ caller in order into the free space of the records slab after
\ cons-load-room, are each checked by the caller and then entered with
\ cons-adopt, so that the table is built once, at its final size, without
\ doubling. cons-load-room gives room for units more record units and
\ makes the table now the size cons-seal gives that many numbers (at most
\ half full): ok, full, or invalid for a set that is not open.
lf-lib-private set-current
: cons-load-log2 ( units cons -- log2 ) cons-numbers + 2* 16 max log2-ceiling ;
\ Room in the table for one more entry without passing 3/4 full.
: cons-table-room? ( cons -- flag )
  cons-table dup htab-count 1+ 4 * swap htab-slots 3 * <= ;
\ The candidate at cons-top found by its hash: an equal record's number
\ and true, or the empty slot and false (the hooks read record n =
\ cons-numbers, the candidate itself, when given the next number).
: cons-candidate-find ( cons -- n true | i false )
  dup cons-numbers over cons-rehash false rot cons-find ;
lf-lib set-current
: cons-load-room ( units cons -- outcome )
  dup cons-open? 0= if 2drop outcome-invalid exit then
  2dup cons-records slab-room ok-then2? 0= if exit then
  tuck cons-load-log2 swap cons-table htab-presize ;
\ Enter the candidate of units record units at cons-top, written and
\ checked by the caller, as the next number: its number and ok; -1 and
\ invalid when an equal record is already in the set (hash-consing keeps
\ each record once, so a file with two is refused); -1 and full when the
\ table has no room (it was not sized by cons-load-room) or the class's
\ limit would be passed. A class whose comparison reads cons-key (texts,
\ names) needs it set to the candidate's text first (cons-key!).
: cons-adopt ( units cons -- n outcome )
  dup cons-table-room? 0= if 2drop outcome-full no-result exit then
  dup cons-candidate-find if drop 2drop outcome-invalid no-result exit then
  swap cons-commit ;

\ Whether n names a record of the set or its under set: in range, the
\ record within the numbers, and found in its table (exact: a number in
\ the middle of a record, or of a part of a record that is not an entry,
\ is refused).
lf-lib-private set-current
\ Unchecked: n is in range. Its record ends within its tier; the span is
\ compared with the records left, so no sum can wrap.
: cons-whole? ( n cons -- flag )
  cons-home tuck cons-local slab-count over - >r swap cons-span r> u> 0= ;
: cons-listed? ( n cons -- flag ) cons-home 2dup cons-rehash swap cons-table htab-holds? ;
lf-lib set-current
: cons-entry? ( n cons -- flag )
  2dup cons-in? 0= if 2drop false exit then
  2dup cons-whole? if cons-listed? else 2drop false then ;

\ Forgetting the own records from local on: their table entries go. An
\ entry that is missing (a corrupted table) is invalid, after the others
\ have gone.
lf-lib-private set-current
: cons-unlist ( local cons -- outcome )
  tuck cons-first @ + swap 2dup cons-rehash swap cons-table htab-remove ;
\ The first failure of two outcomes.
: worse ( outcome1 outcome2 -- outcome ) over ok? if nip else drop then ;
: cons-forget ( local cons -- outcome )
  outcome-ok -rot begin 2dup cons-records slab-count < while
    2dup cons-unlist >r rot r> worse -rot 2dup cons-span rot + swap
  repeat 2drop ;
\ Emptying the table costs its size; forgetting costs the records: choose
\ the cheaper.
: cons-crowded? ( cons -- flag )
  dup cons-records slab-count 4 * swap cons-table htab-slots > ;
: cons-empty ( cons -- outcome )
  dup cons-crowded? if cons-table htab-clear outcome-ok else 0 swap cons-forget then ;
: cons-cleared ( cons -- ) dup cons-records slab-clear cons-bytes slab-clear ;

\ Marks: one for the records and one for the texts.
lf-lib set-current
begin-structure /cons-mark
  /slab-mark +field cons-mark-records
  /slab-mark +field cons-mark-bytes
end-structure
lf-lib-private set-current
: cons-mark-records? ( mark cons -- mark-part slab )
  cons-records swap cons-mark-records swap ;
: cons-mark-bytes? ( mark cons -- mark-part slab ) cons-bytes swap cons-mark-bytes swap ;
lf-lib set-current
\ Mark an open set: ok; or, with a mark every rollback refuses, invalid or
\ full.
: cons-mark ( mark cons -- outcome )
  dup cons-open? 0= if drop /cons-mark erase outcome-invalid exit then
  2dup cons-mark-records? slab-mark ok-then2? 0= if exit then
  cons-mark-bytes? slab-mark ;
: cons-mark-valid? ( mark cons -- flag )
  dup cons-open? 0= if 2drop false exit then
  2dup cons-mark-records? slab-mark-valid? >r cons-mark-bytes? slab-mark-valid? r> and ;
lf-lib-private set-current
: cons-slabs-back ( mark cons -- )
  2dup cons-mark-records? slab-rollback drop cons-mark-bytes? slab-rollback drop ;
lf-lib set-current
\ Give back every record made since the mark, with its table entry and
\ text: ok; invalid with nothing changed for a mark that is not valid; or
\ invalid after the rollback when the table missed an entry (corrupted). A
\ candidate being built is dropped.
: cons-rollback ( mark cons -- outcome )
  2dup cons-mark-valid? 0= if 2drop outcome-invalid exit then
  over cons-mark-records slab-mark-count @ over cons-forget >r
  false over cons-building ! cons-slabs-back r> ;
\ Empty an open set: ok, invalid for a sealed one (or, after emptying it,
\ when the table missed an entry). Its generation grows, so every mark of
\ it is refused afterwards.
: cons-reset ( cons -- outcome )
  dup cons-open? 0= if drop outcome-invalid exit then
  dup cons-empty >r false over cons-building ! cons-cleared r> ;
\ Make an open set read-only: the table rebuilt at most half full and the
\ slabs trimmed (both kept as they were when the heap has no room for it,
\ which only costs speed), then the table frozen, so that finds in it
\ write nothing. ok, or invalid when it is not open.
: cons-seal ( cons -- outcome )
  dup cons-open? 0= if drop outcome-invalid exit then
  dup cons-table htab-spread drop dup cons-records slab-trim drop
  dup cons-bytes slab-trim drop
  true over cons-sealed ! cons-table htab-freeze outcome-ok ;

module-close
base !   \ the BASE this file was loaded with
