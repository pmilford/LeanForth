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
\ Example: the hash of a record of three 32-bit fields 1 2 3, by hash-3
\ and by hand, below 2^32 on any host; FNV-1a of "a", 0xe40c292c;
\ Murmur3's finaliser of 1.
\   1 2 3 hash-3  dup 1 hash-fmix 2 hash-step 3 hash-step = .
\   u32-mask u> 0= .
\   s" a" hash-bytes .  1 hash-fmix .   \ prints: -1 -1 3826002220 1364076727
\ Interface: hash-fmix, hash-step, hash-3, hash-bytes. No state. Loads in decimal
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

lf-lib set-current
\ Murmur3's finaliser: h is 0 .. 2^32-1, and so is the result. Each step
\ h xor (h >> n), or h * m masked to 32 bits as hash-mul does, written out
\ in one definition: it runs for every hash (plan 9.4.8z2).
: hash-fmix ( h -- h' )
  dup 16 rshift xor hash-m1 * u32-mask and dup 13 rshift xor
  hash-m2 * u32-mask and dup 16 rshift xor ;
\ Mix the low 32 bits of x into the hash h.
: hash-step ( h x -- h' ) xor u32-mask and hash-fmix ;
\ A record of three fields a, b, c: a's finaliser, then b and c mixed in
\ (the hash of terms', levels' and stored names' records).
: hash-3 ( a b c -- h ) rot hash-fmix rot hash-step swap hash-step ;
\ FNV-1a of the u bytes at addr; 0 bytes give the basis.
: hash-bytes ( addr u -- h )
  fnv-basis -rot over + swap ?do i c@ xor fnv-prime hash-mul loop ;

module-close
base !   \ the BASE this file was loaded with
