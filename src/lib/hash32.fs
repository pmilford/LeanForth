\ Portable 32-bit hashing (ADR 0016 C4): the same hash values on 32-bit and
\ 64-bit hosts, for open-addressing tables and hash-consing. A general tool
\ with no Lean knowledge; untrusted. A hash value is only a hint for finding
\ a record: it is never an identity, never written to a file and never
\ compared across programs.
\
\ hash-fmix is the 32-bit finaliser of Murmur3 (Austin Appleby, public
\ domain), a bijection on 0 .. 2^32-1 that spreads every input bit over the
\ whole value; every product is masked to 32 bits. hash-step mixes one more
\ 32-bit value into a hash; a record's hash is its fields mixed in turn.
\ hash-bytes is FNV-1a over bytes (Fowler, Noll, Vo; offset basis
\ 2166136261, prime 16777619), read one character at a time.
\
\ Example: the hash of a record of three 32-bit fields 1 2 3, below 2^32
\ on any host; FNV-1a of "a", 0xe40c292c; Murmur3's finaliser of 1.
\   1 hash-fmix 2 hash-step 3 hash-step u32-mask u> 0= .
\   s" a" hash-bytes .  1 hash-fmix .   \ prints: -1 3826002220 1364076727
\ Interface: hash-fmix, hash-step, hash-bytes. No state. Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./u32.fs
require ./module.fs

lf-lib-private module-open

\ Murmur3's two multipliers, and FNV-1a's basis and prime, built from
\ halves so that no literal needs more than 31 bits.
$85EB 16 lshift $CA6B or constant hash-m1
$C2B2 16 lshift $AE35 or constant hash-m2
$811C 16 lshift $9DC5 or constant fnv-basis
16777619 constant fnv-prime
: hash-mul ( h m -- h' ) * u32-mask and ;
: hash-shift ( h n -- h' ) over swap rshift xor ;

lf-lib set-current
\ Murmur3's finaliser: h is 0 .. 2^32-1, and so is the result.
: hash-fmix ( h -- h' )
  16 hash-shift hash-m1 hash-mul 13 hash-shift hash-m2 hash-mul 16 hash-shift ;
\ Mix the low 32 bits of x into the hash h.
: hash-step ( h x -- h' ) xor u32-mask and hash-fmix ;
\ FNV-1a of the u bytes at addr; 0 bytes give the basis.
: hash-bytes ( addr u -- h )
  fnv-basis -rot over + swap ?do i c@ xor fnv-prime hash-mul loop ;

module-close
base !   \ the BASE this file was loaded with
