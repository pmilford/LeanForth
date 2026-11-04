\ SHA-256's helper words (FIPS 180-4, sections 3.2 and 4.1.2) as program
\ words, for stage SHA-2 of the SHA-256 flagship (docs/project/PLAN_DRAFT.md;
\ ADR 0019 Amendment 1, A3). Each definition is the text of the word of
\ that name in src/lib/sha256.fs, character for character; that file
\ does not load this one yet (stage SHA-2's next step: the library then
\ runs exactly this code). Plain Forth: run mode is `include` (on a Forth
\ without -ROT, after src/lib/portability.fs, which defines it as ROT
\ ROT); correctness mode writes its IR 0.2, tests/program/ir/sha-words.ir,
\ and tests/reference/program-ir.lean (Part 8) proves, for every cell of
\ at least 33 bits, every 32-bit word and every count below 32, that
\ sha-rotr leaves FIPS 180-4's ROTR and sha-ch, sha-maj and sha-big-sigma0
\ leave Ch, Maj and Sigma0: checked by the Lean reference, not by
\ LeanForth.
\
\ A 32-bit word is a cell holding a number from 0 to 2^32 - 1; masking is
\ the words' own AND with sha-mask, never implicit. The words are not
\ standalone library code: their names are the library's. State: none.

\ The mask 2^32 - 1 (on a 32-bit cell 2^32 wraps to 0 and the mask is
\ every bit).
$10000 dup * 1- constant sha-mask

\ 3.2, item 2: x modulo 2^32, the last step of an addition of words.
: sha-w32 ( x -- u ) sha-mask and ;

\ 3.2, items 3 and 4: SHR^n(x) = x >> n and ROTR^n(x) = (x >> n) or
\ (x << 32-n), for a word u and 0 < n < 32; the shift left can set bits
\ above bit 31, hence the mask.
: sha-shr ( u n -- u' ) rshift ;
: sha-rotr ( u n -- u' ) 2dup rshift -rot 32 swap - lshift or sha-w32 ;

\ 4.1.2, (4.2) and (4.3): Ch(x,y,z) = (x and y) xor (not x and z), as
\ z xor (x and (y xor z)); Maj(x,y,z) = (x and y) xor (x and z) xor
\ (y and z), as (x and y) or (z and (x or y)).
: sha-ch ( x y z -- u ) tuck xor rot and xor ;
: sha-maj ( x y z -- u ) >r 2dup and -rot or r> and or ;

\ 4.1.2, (4.4): Sigma0(x) = ROTR^2(x) xor ROTR^13(x) xor ROTR^22(x).
: sha-big-sigma0 ( u -- u' )
  dup 2 sha-rotr over 13 sha-rotr xor swap 22 sha-rotr xor ;
