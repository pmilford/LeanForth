\ Discrimination-tree keys of the elaboration data (plan row FE1e1;
\ docs/design/FE1E_APPLICATIONS.md §3.1): the keys of Lean's instance tree,
\ as src/front/elab-data.fs reads them from a format-2 file, kept for the
\ instance table (FE1e3). A key is one of Lean's DiscrTree.Key: star,
\ other, arrow, a natural-number literal, a string literal, a constant
\ applied to n arguments, a projection of field i of a structure applied
\ to n arguments -- or, in an instance the export lacks, a foreign key: a
\ constant, or a projection of a structure, that no declaration of the
\ library has, kept as text, which no query of the library can equal.
\ LeanForth-specific (Lean's keys over the importer stage's declaration
\ numbers). Untrusted.
\
\ Keys are numbered from 0 in the order kept. Reading them, for any key k
\ below elab-keys# (unchecked):
\   elab-key-tag ( k -- tag )     elab-key-star, -other, -lit, -str,
\                                 -const, -arrow, -proj or -foreign
\   elab-key-decl ( k -- d )      a constant's or projection's declaration
\   elab-key-idx ( k -- i )       a projection's field
\   elab-key-arity ( k -- n )     Lean's Key.arity: the terms that follow
\                                 k in a path (a constant's arguments; a
\                                 projection's plus one, its structure;
\                                 arrow 1, its domain; a foreign key's
\                                 arity field, which is Lean's; 0
\                                 otherwise)
\   elab-key-text ( k -- c-addr u ) a literal's decimal digits (canonical:
\                                 no sign, no leading zero), a string
\                                 literal's bytes, a foreign key's name
\                                 as elab-data.fs encodes it; valid
\                                 until texts are next added
\   elab-key= ( k1 k2 -- flag )   Lean's equality of keys (Key's BEq);
\                                 texts compared byte for byte
\   elab-key-hash ( k -- h )      a 32-bit hash, equal for equal keys
\   elab-one-term? ( k n -- flag ) whether keys k .. k+n-1 are one term
\                                 in Lean's path order: each key followed
\                                 by as many terms as its arity
\ Making them (elab-data.fs): elab-key-new ( tag -- k outcome ) a key of
\ that tag, every field 0 (-1 when not ok); elab-key-ref! ( d k -- ) its
\ declaration, elab-key-arity! ( n k -- ) its arity field (a projection's
\ without the structure), elab-key-idx! ( i k -- ); a texted key's text
\ is every byte added between elab-key-text-start ( k -- ) and
\ elab-key-text-end ( k -- ), each run of bytes by elab-text-room
\ ( n -- addr outcome ), whose addr is valid until the next room;
\ elab-keys-clear ( -- ) forgets every key and text. Outcomes (ADR 0008):
\ ok, or full when the heap has no room.
\
\ State: two context slabs: elab-keys (four cells a key: tag, arity
\ field, declaration or text offset, field index or text length) and
\ elab-texts (bytes). Requires lib/slab.fs and hash32.fs through lib.fs
\ and context.fs. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/hash32.fs

0 constant elab-key-star    1 constant elab-key-other   2 constant elab-key-lit
3 constant elab-key-str     4 constant elab-key-const   5 constant elab-key-arrow
6 constant elab-key-proj    7 constant elab-key-foreign

begin-structure /ek
  field: ek-tag   field: ek-arity   \ the head: equal keys have equal heads
  field: ek-ref                     \ the declaration, or the text's offset
  field: ek-extra                   \ a projection's field, or the text's length
end-structure
/ek context-slab: elab-keys
1 chars context-slab: elab-texts

: ek ( k -- addr ) elab-keys slab-at ;
: elab-keys# ( -- n ) elab-keys slab-count ;
: elab-key-tag ( k -- tag ) ek ek-tag @ ;
: elab-key-decl ( k -- d ) ek ek-ref @ ;
: elab-key-idx ( k -- i ) ek ek-extra @ ;
\ Arrow (its domain) and a projection (its structure) add one term.
: ek-more ( tag -- n ) dup elab-key-arrow = swap elab-key-proj = or negate ;
: elab-key-arity ( k -- n ) ek dup ek-arity @ swap ek-tag @ ek-more + ;
: ek-texted? ( tag -- flag )
  dup elab-key-lit = over elab-key-str = or swap elab-key-foreign = or ;
: elab-key-text ( k -- c-addr u ) ek dup ek-ref @ elab-texts slab-at swap ek-extra @ ;

\ Equality: the heads (tag, arity field), then the texts of a texted key,
\ else the other two fields.
: ek-head= ( k1 k2 -- flag ) ek swap ek [ 2 cells ] literal tuck compare 0= ;
: ek-cells= ( k1 k2 -- flag ) ek swap ek /ek tuck compare 0= ;
: ek-texts= ( k1 k2 -- flag ) elab-key-text rot elab-key-text compare 0= ;
: elab-key= ( k1 k2 -- flag )
  2dup ek-head= 0= if 2drop false exit then
  over elab-key-tag ek-texted? if ek-texts= else ek-cells= then ;
: ek-head-hash ( k -- h ) ek dup ek-tag @ hash-fmix swap ek-arity @ hash-step ;
: ek-rest-hash ( k -- h )
  dup elab-key-tag ek-texted? if elab-key-text hash-bytes exit then
  ek dup ek-ref @ hash-fmix swap ek-extra @ hash-step ;
: elab-key-hash ( k -- h ) dup ek-head-hash swap ek-rest-hash hash-step ;

\ One term: open counts the terms still to come; it must stay above 0
\ until the last key and be 0 after it.
: ek-term-step ( open k -- open' ) elab-key-arity + 1- ;
: elab-one-term? ( k n -- flag )
  1 -rot over + swap ?do
    dup 0= if drop unloop false exit then i ek-term-step
  loop 0= ;

\ Making keys and texts.
: elab-key-new ( tag -- k outcome )
  1 elab-keys slab-claim dup ok? 0= if nip nip no-result exit then
  drop tuck ek dup /ek erase ek-tag ! outcome-ok ;
: elab-key-ref! ( x k -- ) ek ek-ref ! ;
: elab-key-arity! ( n k -- ) ek ek-arity ! ;
: elab-key-idx! ( i k -- ) ek ek-extra ! ;
: elab-text-room ( n -- addr outcome )
  elab-texts slab-claim dup ok? if swap elab-texts slab-at swap else nip no-result then ;
: ek-texts# ( -- n ) elab-texts slab-count ;
: elab-key-text-start ( k -- ) ek-texts# swap ek ek-ref ! ;
: elab-key-text-end ( k -- ) ek dup ek-ref @ ek-texts# swap - swap ek-extra ! ;
: elab-keys-clear ( -- ) elab-keys slab-clear elab-texts slab-clear ;

base !   \ the BASE this file was loaded with
