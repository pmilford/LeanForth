\ Packed 32-bit fields, for the compact store of ADR 0016 (proposed): the
\ one module that reads and writes memory in units of 32 bits. A packed
\ field holds an unsigned number from 0 to 2^32-1 and is read and written
\ only by u32@ and u32!, so its bytes are never seen. A packed record's
\ layout is therefore defined by arithmetic on numbers (bit fields are
\ shifts and masks of the value u32@ gives), not by byte order or cell
\ size. Packed memory itself is never written to a file; the file-format
\ words at the end convert to and from bytes in a fixed order (below).
\
\ Two implementations of the same two words. Where the host has Gforth's
\ l@ and l! (Gforth 0.7.3 and 1.0) and they pass a check while this file
\ loads, u32@ and u32! use them. Elsewhere, or when the word
\ lf-u32-portable is defined before this file loads, they use the
\ Forth-2012 versions u32-bytes@ and u32-bytes!, which keep a field as
\ four characters of 8 bits each, least significant first, in an order
\ this file fixes. The two versions may order the bytes differently;
\ that is invisible, since a field is only ever read by the version that
\ wrote it. Both versions are always compiled where the host allows, so
\ the tests run each on every host; modules use only u32@ and u32!.
\
\ File-format words (sectioned files, src/lib/sections.fs): u32-le! and
\ u32-le@ write and read one field as four bytes, least significant first,
\ on any host; u32s>le and le>u32s do so for n fields, copying the block
\ whole when the host keeps a packed field in memory in that same order
\ (checked once while loading: u32-block?), and field by field otherwise.
\ u32s>le-fields and le>u32s-fields, the field-by-field versions, are
\ public for the tests. Defining lf-u32-fields before this file loads
\ forces the field-by-field path, so a test can show both give the same
\ bytes. These are the only words that give a field a byte layout.
\ State: none. u32-native is a constant set while loading, by a check
\ that uses the 8-character buffer u32-trial once, then never again.
\ The file loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs

\ Address units of n packed fields, and the 32-bit mask: on a 64-bit host
\ 2^32-1; on a 32-bit host 2^32 wraps to 0 and the mask is -1, every bit.
: u32s ( n -- au ) 4 * chars ;
$10000 dup * 1- constant u32-mask
\ Bits 0 .. 7 of x, and bits 8i .. 8i+7 of u.
: u32-low ( x -- c ) $FF and ;
: u32-byte ( u i -- c ) 8 * rshift u32-low ;

\ Forth-2012 version, public for the tests only: four characters, least
\ significant byte first. u32-byte! stores byte i of u in character i at
\ addr; u32-byte+ shifts u up by 8 bits and adds character i at addr;
\ bits above 32 are dropped.
: u32-byte! ( u addr i -- ) >r swap r@ u32-byte swap r> chars + c! ;
: u32-bytes! ( u addr -- )
  2dup 0 u32-byte! 2dup 1 u32-byte! 2dup 2 u32-byte! 3 u32-byte! ;
: u32-byte+ ( u addr i -- u' ) chars + c@ u32-low swap 8 lshift or ;
: u32-bytes@ ( addr -- u )
  0 over 3 u32-byte+ over 2 u32-byte+ over 1 u32-byte+ swap 0 u32-byte+ ;

\ Whether a fetch and a store, given as xts, are unsigned 32-bit access:
\ a value with bits 0 and 31 set comes back unchanged, not sign-extended,
\ and the store leaves the four characters after the field as they were
\ (a store of a whole 64-bit cell would not). Checked once, while loading.
1 31 lshift 1+ constant u32-probe
create u32-trial 8 chars allot
: u32-trial! ( store-xt -- ) u32-trial 8 chars $FF fill u32-probe u32-trial rot execute ;
: u32-sound? ( fetch-xt store-xt -- flag )
  u32-trial! u32-trial swap execute u32-probe =
  u32-trial 4 chars + u32-bytes@ u32-mask = and ;
[defined] l@ [defined] l! and [defined] lf-u32-portable 0= and
[if] ' l@ ' l! u32-sound? [else] false [then]
constant u32-native

\ u32@ gives the field's value, 0 .. 2^32-1; u32! keeps only the low 32
\ bits of u. On a 32-bit host a value of 2^31 or more is a negative cell:
\ compare such values with U< and U>, never < and >.
\ Natively they are synonyms of l@ and l!, so where the host has
\ Forth-2012 SYNONYM (Gforth 1.0) a compiled u32@ is the primitive itself,
\ not a call of a colon definition around it: the checker reads term
\ fields through u32@ several times per unit of fuel (agent PERF1,
\ 2026-11-12). Elsewhere (Gforth 0.7.3) portability.fs's SYNONYM makes
\ them colon definitions calling l@ and l!.
u32-native [if]
synonym u32@ l@ ( addr -- u )
synonym u32! l! ( u addr -- )
[else]
: u32@ ( addr -- u ) u32-bytes@ ;
: u32! ( u addr -- ) u32-bytes! ;
[then]

\ One field as four bytes, least significant first: the byte order
\ u32-bytes@ and u32-bytes! already fix, so these are those words under
\ the names the file formats use.
: u32-le! ( u c-addr -- ) u32-bytes! ;
: u32-le@ ( c-addr -- u ) u32-bytes@ ;

\ Whether packed memory is already little-endian: the field 1 has its one
\ set bit in the first character and the fourth character is 0. Checked
\ once, while loading; lf-u32-fields forces false.
: u32-little? ( -- flag )
  1 u32-trial u32! u32-trial c@ 1 = u32-trial 3 chars + c@ 0= and ;
[defined] lf-u32-fields 0= [if] u32-little? [else] false [then]
constant u32-block?

\ n fields to 4n bytes (and back), field by field: public for the tests.
: u32s>le-fields ( addr c-addr n -- )
  0 ?do over u32@ over u32-le! swap 4 chars + swap 4 chars + loop 2drop ;
: le>u32s-fields ( c-addr addr n -- )
  0 ?do over u32-le@ over u32! swap 4 chars + swap 4 chars + loop 2drop ;

\ n packed fields at addr become 4n little-endian bytes at c-addr; and
\ the reverse. The two memory areas must not overlap.
: u32s>le ( addr c-addr n -- )
  u32-block? if 4 * chars move else u32s>le-fields then ;
: le>u32s ( c-addr addr n -- )
  u32-block? if 4 * chars move else le>u32s-fields then ;

base !   \ the BASE this file was loaded with
