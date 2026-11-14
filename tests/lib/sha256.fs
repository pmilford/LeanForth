\ Unit tests of src/lib/sha256.fs: FIPS 180-4's examples and NIST's test
\ vectors, messages around every padding boundary, every split of a
\ message into updates (1-byte updates, splits at 55, 56, 63, 64 and 65
\ bytes, empty updates), the named functions against independent models
\ (rotation one bit at a time, the textbook Ch and Maj), the fast round
\ and schedule against the plain ones on random rows, the 64-bit length's
\ carry, and two interleaved hashes. tests/lib/sha256-plain.fs runs this
\ file with the plain definitions; tests/lib/test_sha256.py compares
\ random messages with Python's hashlib and loads the library from a
\ folder outside the project. The module is loaded under HEX: its
\ numbers must not depend on BASE, and it must leave BASE as it found it.
include ../support/tester.fs
hex require ../../src/lib/sha256.fs base @ decimal constant base-after-load
lf-lib-private order+   \ the helpers: the round, the schedule, padding, fields

T{ base-after-load -> 16 }T
T{ cell-bits 32 >= sha-mask 1+ sha-mask and -> true 0 }T

sha256: hasher
create digest 32 allot
create text 64 allot
: hex? ( c-addr u -- flag ) text 64 compare 0= ;
: digest-text ( -- ) digest hasher sha256-final digest text sha256-hex ;
: hashed ( c-addr u -- ) hasher sha256-init hasher sha256-update digest-text ;
: hashed? ( c-addr u c-addr2 u2 -- flag ) 2>r hashed 2r> hex? ;

\ FIPS 180-4's examples (and NIST's short and long vectors).
T{ s" " s" e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
   hashed? -> true }T
T{ s" abc" s" ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
   hashed? -> true }T
T{ s" abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
   s" 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" hashed? -> true }T
\ The 896-bit message, given in two updates of 56 bytes.
: two-updates ( c-addr1 u1 c-addr2 u2 -- )
  2>r hasher sha256-init hasher sha256-update 2r> hasher sha256-update digest-text ;
T{ s" abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn"
   s" hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" two-updates
   s" cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" hex? -> true }T

\ One million 'a', in 1,000 updates of 1,000 bytes.
create a-bytes 1000 allot  a-bytes 1000 char a fill
: million-a ( -- )
  hasher sha256-init 1000 0 do a-bytes 1000 hasher sha256-update loop digest-text ;
T{ million-a s" cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
   hex? -> true }T

\ n letters 'a' around the padding boundaries: 55 bytes leave room for
\ the length in the last block, 56 do not; 64 is one block exactly.
: a-hashed? ( n c-addr u -- flag ) 2>r a-bytes swap 2r> hashed? ;
T{ 55 s" 9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
   a-hashed? -> true }T
T{ 56 s" b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"
   a-hashed? -> true }T
T{ 63 s" 7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34"
   a-hashed? -> true }T
T{ 64 s" ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"
   a-hashed? -> true }T
T{ 65 s" 635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0"
   a-hashed? -> true }T
T{ 119 s" 31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb"
   a-hashed? -> true }T
T{ 120 s" 2f3d335432c70b580af0e8e1b3674a7c020d683aa5f73aaaedfdc55af904c21c"
   a-hashed? -> true }T
T{ 127 s" c57e9278af78fa3cab38667bef4ce29d783787a2f731d4e12200270f0c32320a"
   a-hashed? -> true }T
T{ 128 s" 6836cf13bac400e9105071cd6af47084dfacad4e5e302c94bfed24e013afb73e"
   a-hashed? -> true }T
T{ 129 s" c12cb024a2e5551cca0e08fce8f1c5e314555cc3fef6329ee994a3db752166ae"
   a-hashed? -> true }T

\ Every split. A message of every length u from 0 to 200 bytes (byte i is
\ 7i + 3 modulo 256) is hashed whole, then in two updates at every split
\ point, then one byte at a time, then with an empty add-bytes before and
\ after every byte, and in three updates at each pair of the boundaries
\ 55, 56, 63, 64 and 65 up to u; every digest must equal the whole one.
200 constant longest
create message longest allot
: message-fill ( -- ) longest 0 do i 7 * 3 + 255 and message i + c! loop ;
message-fill
create expected 64 allot
: expect-digest ( u -- ) message swap hashed text expected 64 move ;
: same? ( -- flag ) expected 64 hex? ;
: add-bytes ( c-addr u -- ) hasher sha256-update ;
: piece ( from to -- ) over - swap message + swap add-bytes ;   \ bytes from to to-1
: split-at ( u i -- ) hasher sha256-init 0 over piece swap piece digest-text ;
: splits? ( u -- flag ) true over 1+ 0 do over i split-at same? and loop nip ;
: bytewise ( u -- ) hasher sha256-init 0 ?do message i + 1 add-bytes loop digest-text ;
: with-empties ( u -- )
  hasher sha256-init 0 ?do message i + 0 add-bytes message i + 1 add-bytes loop
  message 0 add-bytes digest-text ;
: three-way ( u i j -- )
  hasher sha256-init 0 2 pick piece 2dup piece nip swap piece digest-text ;
create boundaries 55 , 56 , 63 , 64 , 65 ,
: boundary ( i -- n ) cells boundaries + @ ;
: pair-ok? ( u i j -- u flag )
  2 pick over < if 2drop true else 2 pick -rot three-way same? then ;
: three-ways? ( u -- flag )   \ every pair i < j of boundaries, j at most u
  true 5 0 do 5 i 1+ ?do over j boundary i boundary pair-ok? nip and loop loop nip ;
: length-ok? ( u -- flag )
  dup expect-digest dup splits? over bytewise same? and over with-empties same? and
  swap three-ways? and ;
: all-lengths? ( -- flag ) true longest 1+ 0 do i length-ok? and loop ;
T{ all-lengths? -> true }T

\ The named functions against independent models: a rotation as n
\ rotations by one bit, a shift as n shifts by one bit, and the textbook
\ Ch and Maj (4.2, 4.3). Random words from a 32-bit xorshift generator.
variable word-seed  88172645 word-seed !
: next-word ( -- u )
  word-seed @ dup 13 lshift xor sha-mask and dup 17 rshift xor
  dup 5 lshift xor sha-mask and dup word-seed ! ;
: rotr1 ( u -- u' ) dup 1 and 31 lshift swap 1 rshift or ;
: rotr-model ( u n -- u' ) 0 ?do rotr1 loop ;
: shr-model ( u n -- u' ) 0 ?do 1 rshift loop ;
: not32 ( u -- u' ) invert sha-mask and ;
: ch-model ( x y z -- u ) >r over and swap not32 r> and xor ;
: maj-model ( x y z -- u ) >r 2dup and -rot r@ and swap r> and xor xor ;
: sigma-model ( u r1 r2 r3 -- u' )
  >r >r >r dup r> rotr-model over r> rotr-model xor swap r> rotr-model xor ;
: small-model ( u r1 r2 s -- u' )
  >r >r >r dup r> rotr-model over r> rotr-model xor swap r> shr-model xor ;
: rotations? ( u -- flag )
  true 32 1 do over i sha-rotr 2 pick i rotr-model = and
    over i sha-shr 2 pick i shr-model = and loop nip ;
: sigmas? ( u -- flag )
  dup sha-big-sigma0 over 2 13 22 sigma-model =
  over sha-big-sigma1 2 pick 6 11 25 sigma-model = and
  over sha-small-sigma0 2 pick 7 18 3 small-model = and
  swap dup sha-small-sigma1 swap 17 19 10 small-model = and ;
: 3dup ( x y z -- x y z x y z ) 2 pick 2 pick 2 pick ;
: chmaj? ( -- flag )
  next-word next-word next-word 3dup sha-ch >r 3dup ch-model r> = >r
  3dup sha-maj >r maj-model r> = r> and ;
: functions? ( n -- flag )
  true swap 0 ?do next-word dup rotations? swap sigmas? and and chmaj? and loop ;
T{ 0 rotations? sha-mask rotations? 1 rotations? -> true true true }T
T{ 0 sigmas? sha-mask sigmas? 1 31 lshift sigmas? -> true true true }T
T{ 1 1 sha-rotr 1 31 lshift 31 sha-rotr 1 31 lshift 31 sha-shr -> 1 31 lshift 1 1 }T
T{ 0 0 0 sha-ch 0 sha-mask sha-mask sha-ch sha-mask 0 sha-mask sha-ch -> 0 sha-mask 0 }T
T{ sha-mask 0 0 sha-maj sha-mask sha-mask 0 sha-maj 0 sha-mask sha-mask sha-maj
   -> 0 sha-mask sha-mask }T
T{ 2000 functions? -> true }T

\ The fast round and schedule against the plain ones: two copies of a
\ table of random words, expanded and run through 64 rounds each way,
\ must end equal in every cell. Where the fast words are not compiled,
\ they are the plain ones and the check holds trivially.
create table-1 sha-table-rows sha-rows allot
create table-2 sha-table-rows sha-rows allot
: table-bytes ( -- u ) sha-table-rows sha-rows ;
: randomize ( -- )
  table-bytes 1 cells / 0 do next-word table-1 i cells + ! loop
  table-1 table-2 table-bytes move ;
: tables-equal? ( -- flag ) table-1 table-bytes table-2 over compare 0= ;
: expand-plain ( table -- )
  16 sha-rows + sha-rounds 16 do
    dup sha-schedule-plain over sha-row-w ! /sha-row +
  loop drop ;
: rounds-plain ( table -- ) sha-rounds 0 do sha-round-plain loop drop ;
: fast-equal? ( -- flag )
  randomize table-1 sha-expand table-2 expand-plain tables-equal?
  table-1 sha-rounds-run table-2 rounds-plain tables-equal? and ;
: fast-trials? ( n -- flag ) true swap 0 ?do fast-equal? and loop ;
T{ 500 fast-trials? -> true }T
T{ table-1 sha-round-plain table-1 sha-round - -> 0 }T

\ The message length's carry: 512 bits added to 2^32-512 give 2^32, a
\ high word of 1 and a low word of 0; padding writes the two words
\ big-endian as the last 8 bytes of the block.
T{ hasher sha256-init sha-mask 511 - hasher sha-length-lo ! 512 hasher sha-length+
   hasher sha-length-hi @ hasher sha-length-lo @ -> 1 0 }T
T{ hasher sha256-init $01020304 hasher sha-length-hi ! $05060708 hasher sha-length-lo !
   hasher sha-pad hasher sha-used @ hasher sha-buffer c@ -> 64 $80 }T
: buffer-byte ( i -- c ) hasher sha-buffer + c@ ;
T{ 56 buffer-byte 60 buffer-byte 63 buffer-byte -> 1 5 8 }T

\ Separate records are independent: two hashes interleaved.
sha256: other
create other-digest 32 allot
create other-text 64 allot
: interleaved ( -- )
  hasher sha256-init other sha256-init
  s" ab" hasher sha256-update s" xy" other sha256-update
  s" c" hasher sha256-update s" z" other sha256-update
  other-digest other sha256-final other-digest other-text sha256-hex digest-text ;
T{ interleaved s" ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" hex?
   s" xyz" hashed other-text 64 hex? -> true true }T

\ sha256-line adds the text, then one line feed: the SHA-256 (hashlib's) of
\ "abc\n", of "\n" and of "x\n\ny\n" given as the lines x, empty and y.
: lines-hashed ( c-addr u -- )   \ the digest of "abc" given as a line
  hasher sha256-init hasher sha256-line digest-text ;
T{ s" abc" lines-hashed s" edeaaff3f1774ad2888673770c6d64097e391bc362d7d6fb34982ddf0efd18cb"
   hex? -> true }T
T{ s" " lines-hashed s" 01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b"
   hex? -> true }T
: three-lines ( -- )
  hasher sha256-init s" x" hasher sha256-line s" " hasher sha256-line
  s" y" hasher sha256-line digest-text ;
T{ three-lines s" 9e999adc348bc9bf4cd26312129af41b3255e8a06b523e17b2398f808ef52fff"
   hex? -> true }T

bye
