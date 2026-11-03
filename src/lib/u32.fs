\ Packed 32-bit fields, for the compact store of ADR 0016 (proposed): the
\ one module that reads and writes memory in units of 32 bits. A packed
\ field holds an unsigned number from 0 to 2^32-1 and is read and written
\ only by u32@ and u32!, so its bytes are never seen. A packed record's
\ layout is therefore defined by arithmetic on numbers (bit fields are
\ shifts and masks of the value u32@ gives), not by byte order or cell
\ size, and packed memory is never written to a file.
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
\ the tests run each on every host.
\ State: none. u32-native is a constant set while loading.

require ./portability.fs

\ Address units of n packed fields, and the 32-bit mask: on a 64-bit host
\ 2^32-1; on a 32-bit host 2^32 wraps to 0 and the mask is -1, every bit.
: u32s ( n -- au ) 4 * chars ;
$10000 dup * 1- constant u32-mask
\ Bits 0 .. 7 of x, and bits 8i .. 8i+7 of u.
: u32-low ( x -- c ) $FF and ;
: u32-byte ( u i -- c ) 8 * rshift u32-low ;

\ Forth-2012 version: four characters, least significant byte first.
\ u32-byte! stores byte i of u in character i at addr; u32-byte+ shifts u
\ up by 8 bits and adds character i at addr; bits above 32 are dropped.
: u32-byte! ( u addr i -- ) >r swap r@ u32-byte swap r> chars + c! ;
: u32-bytes! ( u addr -- )
  2dup 0 u32-byte! 2dup 1 u32-byte! 2dup 2 u32-byte! 3 u32-byte! ;
: u32-byte+ ( u addr i -- u' ) chars + c@ u32-low swap 8 lshift or ;
: u32-bytes@ ( addr -- u )
  0 over 3 u32-byte+ over 2 u32-byte+ over 1 u32-byte+ swap 0 u32-byte+ ;

\ Whether the host's l@ and l! are unsigned 32-bit access: a value with
\ bits 0 and 31 set must come back unchanged, not sign-extended.
1 31 lshift 1+ constant u32-probe
[defined] l@ [defined] l! and [defined] lf-u32-portable 0= and
[if] u32-probe pad l! pad l@ u32-probe = [else] false [then]
constant u32-native

u32-native [if]
: u32@ ( addr -- u ) l@ ;
: u32! ( u addr -- ) l! ;
[else]
: u32@ ( addr -- u ) u32-bytes@ ;
: u32! ( u addr -- ) u32-bytes! ;
[then]
