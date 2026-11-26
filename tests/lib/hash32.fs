\ Unit tests of src/lib/hash32.fs: Murmur3's finaliser and FNV-1a against
\ values computed independently (Python, 32-bit arithmetic), the range of
\ every result, and a load under HEX. T{ }T checks results and depth.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/hash32.fs decimal

\ hash-fmix: 0 is fixed; known values, including the extremes of 32 bits.
T{ 0 hash-fmix 1 hash-fmix 2 hash-fmix -> 0 1364076727 821347078 }T
T{ u32-mask hash-fmix 1 31 lshift hash-fmix 12345 hash-fmix -> 2180083513 1832674720 1011272156 }T
\ hash-step mixes the low 32 bits of x after the hash.
T{ 7 hash-fmix 9 hash-step -> 226152347 }T
T{ 7 hash-fmix 9 u32-mask 1+ + hash-step -> 226152347 }T
\ hash-bytes: FNV-1a's offset basis for no bytes, then known texts.
T{ s" " hash-bytes s" a" hash-bytes s" foobar" hash-bytes -> 2166136261 3826002220 3214735720 }T
T{ s" Nat.succ" hash-bytes -> 1307409052 }T
create bytes256 256 chars allot
: bytes-fill ( -- ) 256 0 do i bytes256 i chars + c! loop ;
bytes-fill
T{ bytes256 256 hash-bytes -> 2426689733 }T
\ Every result is a 32-bit value, whatever the input.
variable hash-seed  20261103 hash-seed !
: hash-rnd ( -- u ) hash-seed @ 1103515245 * 12345 + u32-mask and dup hash-seed ! ;
: in-range? ( h -- flag ) u32-mask u> 0= ;
: ranges? ( -- flag )
  true 1000 0 do hash-rnd hash-fmix in-range? and hash-rnd hash-rnd hash-step in-range? and
  bytes256 hash-rnd 256 mod hash-bytes in-range? and loop ;
T{ ranges? -> true }T
T{ 5 ' hash-fmix rs-checked s" ab" ' hash-bytes rs-checked drop -> 5 hash-fmix }T
\ hash-fmix written out in one definition (plan 9.4.8z3) gives what the
\ chain of helpers it replaced gives, kept here as it was: on 0, -1, 2^k
\ and its neighbours for every bit k of a cell, 500,000 random 32-bit
\ values and 500,000 random cells (all 64 bits on a 64-bit host, whose
\ products the masks bring back to 32 bits).
: old-mul ( h m -- h' ) * u32-mask and ;
: old-shift ( h n -- h' ) over swap rshift xor ;
$85EB 16 lshift $CA6B or constant old-m1
$C2B2 16 lshift $AE35 or constant old-m2
: old-fmix ( h -- h' )
  16 old-shift old-m1 old-mul 13 old-shift old-m2 old-mul 16 old-shift ;
: fmix-same? ( h -- flag ) dup hash-fmix swap old-fmix = ;
: near-same? ( h -- flag ) dup fmix-same? over 1- fmix-same? and swap 1+ fmix-same? and ;
: edges-same? ( -- flag )
  0 fmix-same? -1 fmix-same? and 1 cells 8 * 0 do 1 i lshift near-same? and loop ;
: rnd-cell ( -- x ) hash-rnd 16 lshift 16 lshift hash-rnd xor ;
: randoms-same? ( -- flag )
  true 500000 0 do hash-rnd fmix-same? and rnd-cell fmix-same? and loop ;
T{ edges-same? randoms-same? u32-mask fmix-same? 1 31 lshift near-same? -> true true true true }T
\ Only the interface is public: helpers are private (ADR 0010).
T{ s" hash-mul" forth-wordlist search-wordlist s" hash-mul" lf-lib search-wordlist -> 0 0 }T
T{ s" hash-fmix" lf-lib search-wordlist nip -> -1 }T
\ hash-3 is the three-field mix it names, bit for bit, on 10,000 random
\ triples and at the ends of the range (it replaced terms.fs's
\ lf-fields-hash, whose values the term and level tables' layout follows).
: mix-3 ( a b c -- h ) >r >r hash-fmix r> hash-step r> hash-step ;
: hash-3-same? ( a b c -- flag ) 2 pick 2 pick 2 pick mix-3 >r hash-3 r> = ;
: hash-3-all? ( -- flag )
  true 10000 0 do hash-rnd hash-rnd hash-rnd hash-3-same? and loop ;
T{ hash-3-all? 0 0 0 hash-3-same? -1 -1 -1 hash-3-same? -> true true true }T
T{ 1 2 3 hash-3 3 2 1 hash-3 = 1 2 3 hash-3 in-range? -> false true }T
T{ 1 2 3 ' hash-3 rs-checked -> 1 hash-fmix 2 hash-step 3 hash-step }T
bye
