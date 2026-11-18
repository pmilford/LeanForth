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
