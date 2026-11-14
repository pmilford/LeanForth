\ SHA-256, as FIPS 180-4 (August 2015) defines it, computed incrementally.
\ A standalone library for any Forth-2012 system with cells of at least
\ 32 bits and characters of 8 bits; it needs only portability.fs, which
\ supplies -rot and the Forth-2012 structure words where a host lacks
\ them, bits.fs (cell-bits, a cell's width), and module.fs, which keeps
\ its helpers in a private word list (ADR 0010). LeanForth uses it to check its exports (src/import/manifest.fs).
\ Untrusted until reviewed; the program track's plan is to prove it equal
\ to FIPS 180-4 (docs/project/PLAN_DRAFT.md, "Flagship program target").
\
\   sha256: hasher                \ a record holding one hash in progress
\   create digest 32 allot  create text 64 allot
\   hasher sha256-init
\   s" ab" hasher sha256-update  s" c" hasher sha256-update
\   digest hasher sha256-final  digest text sha256-hex  text 64 type
\
\ prints ba7816bf...f20015ad, the SHA-256 of "abc". The message may come in
\ pieces of any size, from 0 bytes on; the digest is the same however it
\ is split. Nothing fails: every input is a message. After sha256-final the
\ record holds the padded hash and must be given to sha256-init before
\ reuse.
\
\ Public words (word list lf-lib), each documented where it is defined:
\   /sha256 sha256: sha256-init sha256-update sha256-line sha256-final sha256-hex
\   sha-digest-bytes
\ and FIPS 180-4's functions, for the program track's proofs: sha-w32
\ (addition modulo 2^32), sha-shr, sha-rotr, sha-ch, sha-maj,
\ sha-big-sigma0, sha-big-sigma1, sha-small-sigma0, sha-small-sigma1.
\ Everything else (the round, the message schedule, the compression,
\ padding, the record's fields) is private (lf-lib-private); tests and
\ proofs reach it with `lf-lib-private order+`.
\
\ Words of 32 bits (FIPS 180-4, section 3.1) are held in a cell as an
\ unsigned number from 0 to 2^32-1, on any cell size. The named functions
\ take and give such numbers: wherever a step can set a bit above bit 31
\ (a sum, a shift left), its result is masked with sha-w32, which is
\ section 3.2's addition modulo 2^32. A sum of several words masked once
\ equals the sum taken modulo 2^32 at each step: (x + y) mod 2^32 =
\ ((x mod 2^32) + y) mod 2^32, and + wraps modulo the cell, a multiple of
\ 2^32. A message is a whole number of bytes; its words are read
\ big-endian (3.1, 5.2.1).
\
\ Speed. Hashing 64 bytes takes 64 rounds, so the round is written for
\ speed where that costs some clarity, each time with a comment saying
\ why: the eight working variables live in a table that one round steps
\ through instead of moving seven of them; and on cells of 64 bits or
\ more, the round and the message schedule have the functions written out
\ in place, with a rotation done as one shift of the word written twice,
\ and are checked against the plain definitions by the tests. Defining a
\ word named sha256-portable before this file loads selects the plain
\ definitions on every host, for the tests. Measured speeds:
\ docs/development/FORTH_LIBRARY.md, "SHA-256".
\
\ State: none of its own. All the state of one hash is in one record of
\ /sha256 address units, set up by sha256-init; separate records are
\ independent, and one record is used by one task at a time. The tables
\ sha-k and sha-h0 are filled while loading and never changed. Limit: a
\ message of fewer than 2^64 bits (5.1.1); a longer one is hashed with
\ its length taken modulo 2^64. The file loads in decimal whatever BASE
\ is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./bits.fs
require ./module.fs

lf-lib-private module-open

\ The width of a cell in bits: bits.fs's cell-bits, counted while loading.
cell-bits 32 < [if] .( sha256.fs needs cells of at least 32 bits) cr abort [then]
\ The mask 2^32-1; on a 32-bit cell 2^32 wraps to 0 and the mask is every
\ bit, so masking changes nothing there.
$10000 dup * 1- constant sha-mask

lf-lib set-current
\ 3.2, item 2: x modulo 2^32, the last step of an addition of words.
: sha-w32 ( x -- u ) sha-mask and ;

\ 3.2, items 3 and 4 (and 2.2.2): SHR^n(x) = x >> n, and ROTR^n(x) =
\ (x >> n) or (x << 32-n), for a word u and 0 < n < 32. The shift left
\ can set bits above bit 31, hence the mask.
: sha-shr ( u n -- u' ) rshift ;
: sha-rotr ( u n -- u' ) 2dup rshift -rot 32 swap - lshift or sha-w32 ;

\ 4.1.2, functions (4.2) and (4.3): Ch(x,y,z) = (x and y) xor (not x and
\ z), computed as z xor (x and (y xor z)); Maj(x,y,z) = (x and y) xor
\ (x and z) xor (y and z), computed as (x and y) or (z and (x or y)).
\ Each pair agrees on each bit (check the eight cases of three bits), and
\ none of them sets a bit above bit 31 of words.
: sha-ch ( x y z -- u ) tuck xor rot and xor ;
: sha-maj ( x y z -- u ) >r 2dup and -rot or r> and or ;

\ 4.1.2, functions (4.4) to (4.7).
: sha-big-sigma0 ( u -- u' )   \ ROTR^2(x) xor ROTR^13(x) xor ROTR^22(x)
  dup 2 sha-rotr over 13 sha-rotr xor swap 22 sha-rotr xor ;
: sha-big-sigma1 ( u -- u' )   \ ROTR^6(x) xor ROTR^11(x) xor ROTR^25(x)
  dup 6 sha-rotr over 11 sha-rotr xor swap 25 sha-rotr xor ;
: sha-small-sigma0 ( u -- u' )   \ ROTR^7(x) xor ROTR^18(x) xor SHR^3(x)
  dup 7 sha-rotr over 18 sha-rotr xor swap 3 sha-shr xor ;
: sha-small-sigma1 ( u -- u' )   \ ROTR^17(x) xor ROTR^19(x) xor SHR^10(x)
  dup 17 sha-rotr over 19 sha-rotr xor swap 10 sha-shr xor ;

\ The digest's size in bytes: 256 bits.
32 constant sha-digest-bytes
lf-lib-private set-current

\ 4.2.2: the constants K0 .. K63, the first 32 bits of the fractional
\ parts of the cube roots of the first 64 primes; 5.3.3: the initial hash
\ value H(0), those of the square roots of the first 8 primes. Each is
\ written as two 16-bit halves: a literal of 2^31 or more would assume
\ cells wider than 32 bits.
: sha-k, ( hi lo -- ) swap 16 lshift or , ;
create sha-k
  $428a $2f98 sha-k, $7137 $4491 sha-k, $b5c0 $fbcf sha-k, $e9b5 $dba5 sha-k,
  $3956 $c25b sha-k, $59f1 $11f1 sha-k, $923f $82a4 sha-k, $ab1c $5ed5 sha-k,
  $d807 $aa98 sha-k, $1283 $5b01 sha-k, $2431 $85be sha-k, $550c $7dc3 sha-k,
  $72be $5d74 sha-k, $80de $b1fe sha-k, $9bdc $06a7 sha-k, $c19b $f174 sha-k,
  $e49b $69c1 sha-k, $efbe $4786 sha-k, $0fc1 $9dc6 sha-k, $240c $a1cc sha-k,
  $2de9 $2c6f sha-k, $4a74 $84aa sha-k, $5cb0 $a9dc sha-k, $76f9 $88da sha-k,
  $983e $5152 sha-k, $a831 $c66d sha-k, $b003 $27c8 sha-k, $bf59 $7fc7 sha-k,
  $c6e0 $0bf3 sha-k, $d5a7 $9147 sha-k, $06ca $6351 sha-k, $1429 $2967 sha-k,
  $27b7 $0a85 sha-k, $2e1b $2138 sha-k, $4d2c $6dfc sha-k, $5338 $0d13 sha-k,
  $650a $7354 sha-k, $766a $0abb sha-k, $81c2 $c92e sha-k, $9272 $2c85 sha-k,
  $a2bf $e8a1 sha-k, $a81a $664b sha-k, $c24b $8b70 sha-k, $c76c $51a3 sha-k,
  $d192 $e819 sha-k, $d699 $0624 sha-k, $f40e $3585 sha-k, $106a $a070 sha-k,
  $19a4 $c116 sha-k, $1e37 $6c08 sha-k, $2748 $774c sha-k, $34b0 $bcb5 sha-k,
  $391c $0cb3 sha-k, $4ed8 $aa4a sha-k, $5b9c $ca4f sha-k, $682e $6ff3 sha-k,
  $748f $82ee sha-k, $78a5 $636f sha-k, $84c8 $7814 sha-k, $8cc7 $0208 sha-k,
  $90be $fffa sha-k, $a450 $6ceb sha-k, $bef9 $a3f7 sha-k, $c671 $78f2 sha-k,
create sha-h0
  $6a09 $e667 sha-k, $bb67 $ae85 sha-k, $3c6e $f372 sha-k, $a54f $f53a sha-k,
  $510e $527f sha-k, $9b05 $688c sha-k, $1f83 $d9ab sha-k, $5be0 $cd19 sha-k,

64 constant sha-rounds             \ rounds per block, and words of the schedule
64 constant sha-block-bytes        \ bytes per block: 512 bits

\ The round table. Row t holds W(t) and K(t) of round t (6.2.2, steps 1
\ and 3) and two working variables, A(t) and E(t). For speed, the eight
\ working variables do not move in each round, as FIPS's h=g, g=f, ...
\ would: in round t, a b c d are A(t+3) A(t+2) A(t+1) A(t) and e f g h
\ are E(t+3) E(t+2) E(t+1) E(t), and the round writes its new a and e as
\ A(t+4) and E(t+4). So round t reads rows t to t+3 and fills row t+4,
\ and FIPS's renaming is the step from row t to row t+1. Rows 0 to 3 hold
\ the variables of step 2, rows 64 to 67 those after round 63.
begin-structure /sha-row
  field: sha-row-a                 \ A(t): the variable a of round t-3
  field: sha-row-e                 \ E(t): the variable e of round t-3
  field: sha-row-w                 \ W(t), the message schedule's word t
  field: sha-row-k                 \ K(t), copied from sha-k by sha256-init
end-structure
: sha-rows ( n -- au ) /sha-row * ;
sha-rounds 4 + constant sha-table-rows

\ The record of one hash: its size is public, its fields private.
lf-lib set-current
begin-structure /sha256
  lf-lib-private set-current
  8 cells +field sha-h             \ the hash value H0 .. H7 (6.2.2, step 4)
  field: sha-used                  \ bytes waiting in sha-buffer, 0 to 63
  field: sha-length-hi             \ the message's length so far in bits, as
  field: sha-length-lo             \   two words: bits 63..32 and 31..0 (5.1.1)
  sha-block-bytes chars +field sha-buffer   \ the bytes of an incomplete block
  aligned
  sha-table-rows sha-rows +field sha-table  \ the round table
end-structure

\ Where round t finds its variables, as offsets from row t: a to d,
\ e to h, K(t) and W(t), and the new a and e in row t+4. W(t-2), W(t-7),
\ W(t-15) and W(t-16), the schedule's inputs, as offsets from row t.
3 sha-rows 0 sha-row-a + constant sha-win-a   3 sha-rows 0 sha-row-e + constant sha-win-e
2 sha-rows 0 sha-row-a + constant sha-win-b   2 sha-rows 0 sha-row-e + constant sha-win-f
1 sha-rows 0 sha-row-a + constant sha-win-c   1 sha-rows 0 sha-row-e + constant sha-win-g
0 sha-row-a constant sha-win-d                0 sha-row-e constant sha-win-h
0 sha-row-k constant sha-win-k                0 sha-row-w constant sha-win-w
4 sha-rows 0 sha-row-a + constant sha-win-a-next
4 sha-rows 0 sha-row-e + constant sha-win-e-next
-2 sha-rows 0 sha-row-w + constant sha-win-w-2
-7 sha-rows 0 sha-row-w + constant sha-win-w-7
-15 sha-rows 0 sha-row-w + constant sha-win-w-15
-16 sha-rows 0 sha-row-w + constant sha-win-w-16

\ 6.2.2, step 3, as FIPS writes it: T1 = h + Sigma1(e) + Ch(e,f,g) +
\ K(t) + W(t) and T2 = Sigma0(a) + Maj(a,b,c), each modulo 2^32; then
\ e = d + T1 and a = T1 + T2, modulo 2^32, written to row t+4, and the
\ step to row t+1 renames the other six variables. Row t waits on the
\ return stack.
: sha-t1 ( row -- u )
  >r r@ sha-win-h + @ r@ sha-win-e + @ sha-big-sigma1 +
  r@ sha-win-e + @ r@ sha-win-f + @ r@ sha-win-g + @ sha-ch +
  r@ sha-win-k + @ + r> sha-win-w + @ + sha-w32 ;
: sha-t2 ( row -- u )
  >r r@ sha-win-a + @ sha-big-sigma0
  r@ sha-win-a + @ r@ sha-win-b + @ r> sha-win-c + @ sha-maj + sha-w32 ;
: sha-round-plain ( row -- row' )
  dup sha-t1 >r  r@ over sha-win-d + @ + sha-w32 over sha-win-e-next + !
  r> over sha-t2 + sha-w32 over sha-win-a-next + !  /sha-row + ;

\ 6.2.2, step 1, as FIPS writes it: W(t) for 16 <= t <= 63 is
\ sigma1(W(t-2)) + W(t-7) + sigma0(W(t-15)) + W(t-16), modulo 2^32.
: sha-schedule-plain ( row -- u )
  dup sha-win-w-2 + @ sha-small-sigma1 over sha-win-w-7 + @ +
  over sha-win-w-15 + @ sha-small-sigma0 + swap sha-win-w-16 + @ + sha-w32 ;

\ For speed, on cells of 64 bits or more: the same round and schedule
\ word with the functions written out in place, which take about a
\ quarter of the time of the plain words, whose calls cost more than
\ their work (measured: FORTH_LIBRARY.md). A rotation is one shift of the
\ word written twice: dup 32 lshift or gives u + u * 2^32, and for
\ 0 <= n < 32 its bits n to n+31 are ROTR^n(u). Only the stored words are
\ masked. In between, the code uses +, xor, and, or, and right shifts of
\ doubled words fetched from the table (so of words below 2^32); bits 0
\ to 31 of x + y, x xor y, x and y and x or y depend only on bits 0 to 31
\ of x and y, so the bits above bit 31 never reach a stored word, and the
\ results equal the plain words' (the tests compare them).
[defined] sha256-portable cell-bits 64 < or 0= constant sha-doubling
sha-doubling [if]
\ Seven lines, one per part of the round, each commented: splitting the
\ round into two words cost about 10% of the hashing time (measured), and
\ a call per FIPS function three times as much.
: sha-round ( row -- row' )
  >r r@ sha-win-e + @ dup 32 lshift or                \ e, doubled
  dup 6 rshift over 11 rshift xor swap 25 rshift xor  \ Sigma1(e)
  r@ sha-win-e + @ r@ sha-win-f + @ r@ sha-win-g + @ tuck xor rot and xor +   \ + Ch
  r@ sha-win-h + @ + r@ sha-win-k + @ + r@ sha-win-w + @ +   \ T1 = .. + h + K + W
  dup r@ sha-win-d + @ + sha-mask and r@ sha-win-e-next + !   \ e' = d + T1
  r@ sha-win-a + @ dup 32 lshift or dup 2 rshift over 13 rshift xor swap 22 rshift xor
  r@ sha-win-a + @ r@ sha-win-b + @ r@ sha-win-c + @ >r 2dup and -rot or r> and or
  + + sha-mask and r@ sha-win-a-next + !  r> /sha-row + ;   \ a' = T1 + Sigma0 + Maj
: sha-schedule-word ( row -- u )   \ sigma1(W(t-2)) + W(t-7) + sigma0(W(t-15)) + W(t-16)
  dup sha-win-w-2 + @ dup 10 rshift swap dup 32 lshift or dup 17 rshift swap 19 rshift
  xor xor over sha-win-w-7 + @ +
  over sha-win-w-15 + @ dup 3 rshift swap dup 32 lshift or dup 7 rshift swap 18 rshift
  xor xor + swap sha-win-w-16 + @ + sha-mask and ;
[else]
: sha-round ( row -- row' ) sha-round-plain ;
: sha-schedule-word ( row -- u ) sha-schedule-plain ;
[then]

\ 6.2.2, step 1: W(0) to W(15) are the block's 16 words, big-endian
\ (3.1, 5.2.1); W(16) to W(63) follow from sha-schedule-word.
: sha-be@ ( c-addr -- u )
  dup c@ 24 lshift over char+ c@ 16 lshift or
  over 2 chars + c@ 8 lshift or swap 3 chars + c@ or ;
: sha-load ( c-addr table -- )   \ before pass i, rows 0 to i/4-1 hold their W
  sha-block-bytes 0 do over i chars + sha-be@ over sha-row-w ! /sha-row + 4 +loop 2drop ;
: sha-expand ( table -- )   \ before pass t, rows 0 to t-1 hold their W
  16 sha-rows + sha-rounds 16 do
    dup sha-schedule-word over sha-row-w ! /sha-row +
  loop drop ;

\ 6.2.2, step 2: a to d are H0 to H3, written to A(3) to A(0), and e to h
\ are H4 to H7, written to E(3) to E(0). Step 4: each Hi gets the
\ variable it started as, added modulo 2^32: H0 + A(67), ..., H3 + A(64),
\ H4 + E(67), ..., H7 + E(64). A pair is Hi and Hi+4 with one row.
: sha-set-pair ( h row -- ) over @ over sha-row-a ! swap 4 cells + @ swap sha-row-e ! ;
: sha-start ( sha -- )   \ pass i sets row 3-i from Hi and Hi+4
  dup sha-h swap sha-table 3 sha-rows +
  4 0 do 2dup sha-set-pair /sha-row - swap cell+ swap loop 2drop ;
: sha-h+! ( u addr -- ) tuck @ + sha-w32 swap ! ;
: sha-add-pair ( h row -- )
  2dup sha-row-a @ swap sha-h+! sha-row-e @ swap 4 cells + sha-h+! ;
: sha-finish ( sha -- )   \ pass i adds row 67-i to Hi and Hi+4
  dup sha-h swap sha-table sha-rounds 3 + sha-rows +
  4 0 do 2dup sha-add-pair /sha-row - swap cell+ swap loop 2drop ;

\ 6.2.2: compress the 64-byte block at c-addr into the hash value.
: sha-rounds-run ( table -- )   \ before pass t, rows 0 to t+3 hold round t's variables
  sha-rounds 0 do sha-round loop drop ;
: sha-compress ( c-addr sha -- )
  tuck sha-table sha-load  dup sha-table sha-expand  dup sha-start
  dup sha-table sha-rounds-run  sha-finish ;

\ 5.1.1: the message's length l in bits, as two words, grows by n bits
\ (n < 2^31): the low word wrapped when its new value is below its old
\ one, and then the high word grows by one.
: sha-length+ ( n sha -- )
  >r r@ sha-length-lo @ tuck + sha-w32 dup r@ sha-length-lo ! u>
  if r@ sha-length-hi @ 1+ sha-w32 r@ sha-length-hi ! then r> drop ;
\ A block of the message: compressed, and its 512 bits counted.
: sha-message-block ( c-addr sha -- ) tuck sha-compress 512 swap sha-length+ ;

\ 5.3.3 and 6.2.2: the K column of a record's table.
: sha-k! ( sha -- )   \ before pass i, rows 0 to i-1 hold their K
  sha-table sha-rounds 0 do sha-k i cells + @ over sha-row-k ! /sha-row + loop drop ;

\ Taking bytes. Whole blocks are compressed where they lie; the bytes of
\ an incomplete block wait in sha-buffer until a later update fills it.
: sha-free ( sha -- u ) sha-used @ sha-block-bytes swap - ;
: sha-buffer-end ( sha -- c-addr ) dup sha-buffer swap sha-used @ chars + ;
: sha-flush ( sha -- ) dup sha-buffer over sha-compress 0 swap sha-used ! ;
\ Move as many bytes of c-addr u as there is room for into the buffer;
\ when it is full, compress it as a block of the message.
: sha-take ( c-addr u sha -- c-addr' u' )
  >r 2dup r@ sha-free min tuck r@ sha-buffer-end swap chars move
  dup r@ sha-used +! /string
  r@ sha-free 0= if r@ sha-flush 512 r@ sha-length+ then r> drop ;
: sha-blocks ( c-addr u sha -- c-addr' u' )   \ each pass compresses one block
  >r begin dup sha-block-bytes < 0= while
    over r@ sha-message-block sha-block-bytes /string
  repeat r> drop ;

\ 5.1.1: padding. The byte $80 (a bit 1 and seven 0 bits), zero bytes up
\ to 8 bytes before a block boundary (through one more block when fewer
\ than 8 bytes are free), then l as 64 bits, big-endian: its high word,
\ then its low word. The padding blocks are not counted in l.
: sha-be! ( u c-addr -- )   \ pass i writes byte i, most significant first
  4 0 do over 24 i 8 * - rshift 255 and over i chars + c! loop 2drop ;
: sha-byte ( c sha -- ) tuck sha-buffer-end c! 1 swap sha-used +! ;
: sha-zeros ( n sha -- ) swap 0 ?do 0 over sha-byte loop drop ;
: sha-word ( u sha -- ) tuck sha-buffer-end sha-be! 4 swap sha-used +! ;
: sha-pad ( sha -- )
  $80 over sha-byte dup sha-free 8 < if dup sha-free over sha-zeros dup sha-flush then
  dup sha-free 8 - over sha-zeros
  dup sha-length-hi @ over sha-word dup sha-length-lo @ swap sha-word ;
\ The digest: H0 to H7 big-endian (6.2.2), 32 bytes at c-addr.
: sha-digest! ( c-addr sha -- )   \ pass i writes Hi
  sha-h swap 8 0 do over i cells + @ over sha-be! 4 chars + loop 2drop ;
: sha-hex-digit ( n -- c ) dup 10 < if [char] 0 else [char] a 10 - then + ;
: sha-hex-byte ( c c-addr -- )
  over 4 rshift sha-hex-digit over c! swap 15 and sha-hex-digit swap char+ c! ;

lf-lib set-current
\ Defining word: name ( -- sha ), a record of /sha256 address units to
\ give to sha256-init.
: sha256: ( "name" -- ) create here /sha256 dup allot erase ;
\ 5.3.3: start a hash in the record sha: H(0), and the round table's K.
: sha256-init ( sha -- )
  dup /sha256 erase  sha-h0 over sha-h 8 cells move  sha-k! ;
\ Add the bytes c-addr u to the message: complete a waiting block first,
\ then compress whole blocks in place, then keep the rest (fewer than 64).
: sha256-update ( c-addr u sha -- )
  dup >r sha-used @ if r@ sha-take then r@ sha-blocks r> sha-take 2drop ;
\ Add one line of text and then a line feed (10), as a hash of a text file
\ read line by line sees it: the same as sha256-update of c-addr u and of
\ the one byte 10.
: sha256-line ( c-addr u sha -- ) dup >r sha256-update s\" \n" r> sha256-update ;
\ Finish the hash: count the waiting bytes, pad, compress, and write the
\ 32-byte digest at c-addr.
: sha256-final ( c-addr sha -- )
  dup sha-used @ 8 * over sha-length+ dup sha-pad dup sha-flush sha-digest! ;
\ The 32 bytes of a digest at c-addr1 as 64 lowercase hexadecimal digits
\ at c-addr2, as sha256sum prints them.
: sha256-hex ( c-addr1 c-addr2 -- )   \ pass i writes byte i as two digits
  sha-digest-bytes 0 do over i chars + c@ over i 2* chars + sha-hex-byte loop 2drop ;

module-close
base !   \ the BASE this file was loaded with
