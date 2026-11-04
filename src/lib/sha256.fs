\ SHA-256, as FIPS 180-4 (August 2015) defines it, computed incrementally:
\ sha256-init, then sha256-update with the message's bytes in pieces of
\ any size, then sha256-final for the 32-byte digest. A general tool with
\ no Lean knowledge; the NDJSON import checks an export's SHA-256 with it
\ (src/import/manifest.fs). Untrusted, like the rest of the library.
\
\ Words (FIPS 180-4, section 3.1): a 32-bit word is held in a cell as an
\ unsigned number from 0 to 2^32-1. Every word this file stores or gives
\ is such a number, on any cell size of at least 32 bits. Where a step
\ can leave bits above bit 31 (a sum, a shift left), the result is masked
\ with u32-mask (sha-w32) before it is stored or given, which is the
\ addition modulo 2^32 of section 3.2: a sum of several words masked once
\ equals the sum taken modulo 2^32 at each step, since (x + y) mod 2^32 =
\ ((x mod 2^32) + y) mod 2^32 and + wraps modulo the cell, a multiple of
\ 2^32. Bytes are characters of 8 bits; a message is a whole number of
\ bytes, and its words are read big-endian (3.1, 5.2.1).
\
\ Speed. The round function is the hot path (64 rounds per 64 bytes), so
\ it is written for speed where that costs some clarity, each time with a
\ comment: the eight working variables live in a table of rows that one
\ round steps through, instead of moving seven of them each round; and on
\ cells of 64 bits or more, the rotations of Sigma and sigma use the word
\ written twice side by side (sha-doubled), so that a rotation is one
\ shift. Defining lf-sha256-portable before this file loads selects the
\ plain rotation of section 3.2 on every host, for the tests. Measured
\ speeds are in docs/development/FORTH_LIBRARY.md.
\
\ State: none of its own. All the state of one hash is in one record of
\ /sha256 address units, made by sha256: (or in memory the caller owns)
\ and set up by sha256-init; separate records are independent, and one
\ record is single-threaded. The constant tables sha-k and sha-h0 are
\ filled while loading and never changed after. Limits: a message of
\ fewer than 2^64 bits (5.1.1); a longer one is hashed with its length
\ taken modulo 2^64. After sha256-final the record holds the padded hash;
\ call sha256-init before using it again. The file loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./u32.fs

\ The width of a cell in bits, counted while loading.
: sha-count-bits ( -- n ) 0 1 begin ?dup while 1 lshift swap 1+ swap repeat ;
sha-count-bits constant sha-cell-bits
sha-cell-bits 32 < [if] .( sha256.fs needs cells of at least 32 bits) cr abort [then]

\ 3.2, item 2: the value of x modulo 2^32, the last step of every
\ addition of words, and of anything that can set bits above bit 31.
: sha-w32 ( x -- u ) u32-mask and ;

\ 3.2, items 3 and 4: SHR^n(x) = x >> n and ROTR^n(x) = (x >> n) or
\ (x << 32-n), for a word u and 0 < n < 32. The shift left can set bits
\ above bit 31, hence the mask.
: sha-shr ( u n -- u' ) rshift ;
: sha-rotr ( u n -- u' ) 2dup rshift -rot 32 swap - lshift or sha-w32 ;

\ 4.1.2, functions (4.2) and (4.3): Ch and Maj of three words. Ch(x,y,z)
\ = (x and y) xor (not x and z), computed as z xor (x and (y xor z));
\ Maj(x,y,z) = (x and y) xor (x and z) xor (y and z), computed as (x and
\ y) or (z and (x or y)). Each pair is equal bit by bit (check the eight
\ cases of a bit), and none sets a bit above bit 31 of words.
: sha-ch ( x y z -- u ) tuck xor rot and xor ;
: sha-maj ( x y z -- u ) >r 2dup and -rot or r> and or ;

\ 4.1.2, functions (4.4) to (4.7):
\   Sigma0(x) = ROTR^2(x) xor ROTR^13(x) xor ROTR^22(x)
\   Sigma1(x) = ROTR^6(x) xor ROTR^11(x) xor ROTR^25(x)
\   sigma0(x) = ROTR^7(x) xor ROTR^18(x) xor SHR^3(x)
\   sigma1(x) = ROTR^17(x) xor ROTR^19(x) xor SHR^10(x)
\ For speed, on cells of 64 bits or more: sha-doubled gives the word u
\ written twice, u + u * 2^32, and for 0 <= n < 32 bits 0 to 31 of that
\ shifted right by n are ROTR^n(u). The bits above bit 31 are discarded
\ by one mask at the end, since xor acts on each bit alone.
sha-cell-bits 64 < [defined] lf-sha256-portable or 0= constant sha-doubling
: sha-doubled ( u -- x ) dup 32 lshift or ;
sha-doubling [if]
: sha-big-sigma0 ( u -- u' )
  sha-doubled dup 2 rshift over 13 rshift xor swap 22 rshift xor sha-w32 ;
: sha-big-sigma1 ( u -- u' )
  sha-doubled dup 6 rshift over 11 rshift xor swap 25 rshift xor sha-w32 ;
: sha-small-sigma0 ( u -- u' )
  dup 3 sha-shr swap sha-doubled dup 7 rshift swap 18 rshift xor xor sha-w32 ;
: sha-small-sigma1 ( u -- u' )
  dup 10 sha-shr swap sha-doubled dup 17 rshift swap 19 rshift xor xor sha-w32 ;
[else]
: sha-big-sigma0 ( u -- u' ) dup 2 sha-rotr over 13 sha-rotr xor swap 22 sha-rotr xor ;
: sha-big-sigma1 ( u -- u' ) dup 6 sha-rotr over 11 sha-rotr xor swap 25 sha-rotr xor ;
: sha-small-sigma0 ( u -- u' ) dup 7 sha-rotr over 18 sha-rotr xor swap 3 sha-shr xor ;
: sha-small-sigma1 ( u -- u' ) dup 17 sha-rotr over 19 sha-rotr xor swap 10 sha-shr xor ;
[then]

\ 4.2.2: the 64 constants K0 .. K63, the first 32 bits of the fractional
\ parts of the cube roots of the first 64 primes. Each is written as its
\ two 16-bit halves, because a literal of 2^31 or more would assume cells
\ wider than 32 bits (scripts/check-portable-forth.py).
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
\ 5.3.3: the initial hash value H(0), the first 32 bits of the fractional
\ parts of the square roots of the first 8 primes.
create sha-h0
  $6a09 $e667 sha-k, $bb67 $ae85 sha-k, $3c6e $f372 sha-k, $a54f $f53a sha-k,
  $510e $527f sha-k, $9b05 $688c sha-k, $1f83 $d9ab sha-k, $5be0 $cd19 sha-k,

64 constant sha-rounds             \ rounds per block, and words of the schedule
64 constant sha-block-bytes        \ bytes per block: 512 bits
32 constant sha-digest-bytes       \ bytes of the digest: 256 bits

\ The round table. Row t holds W(t) and K(t) of round t (6.2.2, steps 1
\ and 3) and two working variables, A(t) and E(t). For speed, the eight
\ working variables are not moved in each round, as FIPS writes h=g,
\ g=f, ...: in round t, a b c d are A(t+3) A(t+2) A(t+1) A(t) and e f g h
\ are E(t+3) E(t+2) E(t+1) E(t), and the round writes its new a and e as
\ A(t+4) and E(t+4). So each round reads the rows t to t+3 and fills row
\ t+4, and FIPS's renaming is the step from row t to row t+1. Rows 0 to
\ 3 hold the variables of step 2; rows 64 to 67, those after round 63.
begin-structure /sha-row
  field: row-a                     \ A(t): the variable a of round t-3
  field: row-e                     \ E(t): the variable e of round t-3
  field: row-w                     \ W(t), the message schedule's word t
  field: row-k                     \ K(t), copied from sha-k by sha256-init
end-structure
: sha-rows ( n -- au ) /sha-row * ;
sha-rounds 4 + constant sha-table-rows

begin-structure /sha256
  8 cells +field sha-h             \ the hash value H0 .. H7 (6.2.2, step 4)
  field: sha-used                  \ bytes in sha-buffer, 0 to 63
  field: sha-length-hi             \ the message length so far in bits: bits
  field: sha-length-lo             \   63..32 and 31..0, two words (5.1.1)
  sha-block-bytes chars +field sha-buffer   \ the bytes of an incomplete block
  aligned
  sha-table-rows sha-rows +field sha-table  \ the round table
end-structure

\ Defining word: name ( -- sha ), a record to give to sha256-init.
: sha256: ( "name" -- ) create here /sha256 dup allot erase ;

\ Accessors of round t's window, given row t of the table. For speed
\ each is one addition of a constant (see the round table above).
: sha-a ( row -- addr ) [ 3 sha-rows 0 row-a + ] literal + ;
: sha-b ( row -- addr ) [ 2 sha-rows 0 row-a + ] literal + ;
: sha-c ( row -- addr ) [ 1 sha-rows 0 row-a + ] literal + ;
: sha-d ( row -- addr ) [ 0 row-a ] literal + ;
: sha-e ( row -- addr ) [ 3 sha-rows 0 row-e + ] literal + ;
: sha-f ( row -- addr ) [ 2 sha-rows 0 row-e + ] literal + ;
: sha-g ( row -- addr ) [ 1 sha-rows 0 row-e + ] literal + ;
: sha-h-var ( row -- addr ) [ 0 row-e ] literal + ;
: sha-a-next ( row -- addr ) [ 4 sha-rows 0 row-a + ] literal + ;
: sha-e-next ( row -- addr ) [ 4 sha-rows 0 row-e + ] literal + ;

\ 6.2.2, step 3: T1 = h + Sigma1(e) + Ch(e,f,g) + K(t) + W(t) and
\ T2 = Sigma0(a) + Maj(a,b,c), each modulo 2^32; row t waits on the
\ return stack.
: sha-t1 ( row -- u )
  >r r@ sha-e @ dup sha-big-sigma1 swap r@ sha-f @ r@ sha-g @ sha-ch +
  r@ sha-h-var @ + r@ row-k @ + r> row-w @ + sha-w32 ;
: sha-t2 ( row -- u )
  >r r@ sha-a @ dup sha-big-sigma0 swap r@ sha-b @ r> sha-c @ sha-maj + sha-w32 ;
\ One round: e = d + T1 and a = T1 + T2, modulo 2^32, written to row t+4;
\ the step to row t+1 renames the other six variables.
: sha-round ( row -- row' )
  dup sha-t1 >r  r@ over sha-d @ + sha-w32 over sha-e-next !
  r> over sha-t2 + sha-w32 over sha-a-next !  /sha-row + ;

\ 6.2.2, step 1: the message schedule. W(0) to W(15) are the block's 16
\ words, read big-endian (3.1, 5.2.1); W(t) for 16 <= t <= 63 is
\ sigma1(W(t-2)) + W(t-7) + sigma0(W(t-15)) + W(t-16), modulo 2^32.
: sha-be-byte ( u c-addr -- u' c-addr' ) tuck c@ swap 8 lshift or swap char+ ;
: sha-be@ ( c-addr -- u ) 0 swap sha-be-byte sha-be-byte sha-be-byte sha-be-byte drop ;
: sha-load ( c-addr table -- )   \ pass i stores word i/4 in row i/4
  sha-block-bytes 0 do over i chars + sha-be@ over row-w ! /sha-row + 4 +loop 2drop ;
: sha-w-ago ( row n -- u ) sha-rows - row-w @ ;
: sha-schedule-word ( row -- u )   \ W(t) of row t, from rows t-16 to t-2
  dup 2 sha-w-ago sha-small-sigma1 over 7 sha-w-ago +
  over 15 sha-w-ago sha-small-sigma0 + swap 16 sha-w-ago + sha-w32 ;
: sha-expand ( table -- )   \ before pass t, rows 0 to t-1 hold their W
  16 sha-rows + sha-rounds 16 do dup sha-schedule-word over row-w ! /sha-row + loop drop ;

\ 6.2.2, step 2: a to d are H0 to H3, written to A(3) to A(0), and e to h
\ are H4 to H7, written to E(3) to E(0). Step 4: each H(i) gets the
\ variable it started as, added modulo 2^32: H0 + A(67), ..., H3 + A(64),
\ H4 + E(67), ..., H7 + E(64). A pair is Hi and Hi+4 with one row.
: sha-set-pair ( h row -- ) over @ over row-a ! swap 4 cells + @ swap row-e ! ;
: sha-start ( sha -- )   \ pass i sets row 3-i from H(i) and H(i+4)
  dup sha-h swap sha-table 3 sha-rows +
  4 0 do 2dup sha-set-pair /sha-row - swap cell+ swap loop 2drop ;
: sha-h+! ( u addr -- ) tuck @ + sha-w32 swap ! ;
: sha-add-pair ( h row -- ) 2dup row-a @ swap sha-h+! row-e @ swap 4 cells + sha-h+! ;
: sha-finish ( sha -- )   \ pass i adds row 67-i to H(i) and H(i+4)
  dup sha-h swap sha-table sha-rounds 3 + sha-rows +
  4 0 do 2dup sha-add-pair /sha-row - swap cell+ swap loop 2drop ;

\ 6.2.2: compress one 64-byte block at c-addr into the hash value. The
\ 64 rounds step through the table; before pass t, rows 0 to t+3 hold
\ the working variables of round t.
: sha-rounds-run ( table -- ) sha-rounds 0 do sha-round loop drop ;
: sha-compress ( c-addr sha -- )
  tuck sha-table sha-load  dup sha-table sha-expand  dup sha-start
  dup sha-table sha-rounds-run  sha-finish ;

\ 5.1.1: the message length l in bits, as two words (the high and the
\ low 32 bits), grows by n bits (n < 2^31): the low word wrapped when its
\ new value is below its old one, and then the high word grows by one.
: sha-length+ ( n sha -- )
  >r r@ sha-length-lo @ tuck + sha-w32 dup r@ sha-length-lo ! u>
  if r@ sha-length-hi @ 1+ sha-w32 r@ sha-length-hi ! then r> drop ;
\ A block of the message itself: compressed, and its 512 bits counted.
: sha-message-block ( c-addr sha -- ) tuck sha-compress 512 swap sha-length+ ;

\ 5.3.3: start a hash. The table's K column is filled here.
: sha-k! ( sha -- )   \ pass i copies K(i) into row i
  sha-table sha-rounds 0 do sha-k i cells + @ over row-k ! /sha-row + loop drop ;
: sha256-init ( sha -- )
  dup /sha256 erase  sha-h0 over sha-h 8 cells move  sha-k! ;

\ Hashing bytes. Whole blocks are compressed where they lie; the bytes of
\ an incomplete block wait in sha-buffer until a later update fills it.
: sha-free ( sha -- u ) sha-used @ sha-block-bytes swap - ;
: sha-buffer-end ( sha -- c-addr ) dup sha-buffer swap sha-used @ chars + ;
: sha-flush ( sha -- ) dup sha-buffer over sha-compress 0 swap sha-used ! ;
\ Append to the buffer as many bytes of c-addr u as it has room for;
\ when that fills it, compress it as a block of the message.
: sha-buffer-block ( sha -- ) dup sha-flush 512 swap sha-length+ ;
: sha-take ( c-addr u sha -- c-addr' u' )
  >r 2dup r@ sha-free min tuck r@ sha-buffer-end swap chars move
  dup r@ sha-used +! /string r@ sha-free 0= if r@ sha-buffer-block then r> drop ;
: sha-blocks ( c-addr u sha -- c-addr' u' )   \ each pass compresses one block
  >r begin dup sha-block-bytes < 0= while
    over r@ sha-message-block sha-block-bytes /string
  repeat r> drop ;
\ Add the bytes c-addr u to the message: first complete a waiting block,
\ then compress whole blocks in place, then keep the rest (u < 64).
: sha256-update ( c-addr u sha -- )
  dup >r sha-used @ if r@ sha-take then r@ sha-blocks r> sha-take 2drop ;

\ 5.1.1: padding. The byte $80 (a bit 1 and seven 0 bits), then zero
\ bytes up to 8 bytes before a block boundary (a whole block more when
\ fewer than 8 bytes are free), then the length l in bits as 64 bits,
\ big-endian: the high word, then the low word. The padding blocks are
\ not counted in l.
: sha-be! ( u c-addr -- )   \ pass i writes byte i, most significant first
  4 0 do over 24 i 8 * - rshift 255 and over i chars + c! loop 2drop ;
: sha-byte ( c sha -- ) >r r@ sha-buffer-end c! 1 r> sha-used +! ;
: sha-zeros ( n sha -- ) swap 0 ?do 0 over sha-byte loop drop ;
: sha-word ( u sha -- ) >r r@ sha-buffer-end sha-be! 4 r> sha-used +! ;
: sha-pad ( sha -- )
  $80 over sha-byte dup sha-free 8 < if dup sha-free over sha-zeros dup sha-flush then
  dup sha-free 8 - over sha-zeros
  dup sha-length-hi @ over sha-word dup sha-length-lo @ swap sha-word ;
\ Finish the hash and write the digest, H0 to H7 big-endian (6.2.2), as
\ 32 bytes at c-addr. The bits of the incomplete block are counted first.
: sha-digest! ( c-addr sha -- )   \ pass i writes Hi
  sha-h swap 8 0 do over i cells + @ over sha-be! 4 chars + loop 2drop ;
: sha256-final ( c-addr sha -- )
  dup sha-used @ 8 * over sha-length+ dup sha-pad dup sha-flush sha-digest! ;

\ The 32 bytes of a digest at c-addr1 as 64 lowercase hexadecimal digits
\ at c-addr2, as sha256sum prints them.
: sha-hex-digit ( n -- c ) dup 10 < if [char] 0 else [ char a 10 - ] literal then + ;
: sha-hex-byte ( c c-addr -- )
  over 4 rshift sha-hex-digit over c! swap 15 and sha-hex-digit swap char+ c! ;
: digest>hex ( c-addr1 c-addr2 -- )   \ pass i writes byte i as two digits
  sha-digest-bytes 0 do over i chars + c@ over i 2* chars + sha-hex-byte loop 2drop ;

base !   \ the BASE this file was loaded with
