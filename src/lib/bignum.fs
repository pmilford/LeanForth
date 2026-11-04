\ Arbitrary-precision natural numbers, for the Nat literals that Lean's
\ kernel computes with directly (plan section 6.8, task 5.2.3, library
\ part). A general tool with no Lean knowledge. Untrusted until the review
\ gate of AGENTS.md; once the kernel's verdicts depend on it, it is trusted
\ code. The kernel integration (task 5.1.4, the literals ADR) is not here.
\
\ What Lean 4.35.0's kernel computes on literals (src/kernel/type_checker.cpp
\ at tag v4.35.0, reduce_nat, lines 672-703; called from whnf, line 732,
\ and from lazy_delta_reduction, lines 1060-1065, when neither side has
\ free variables). Arguments are reduced to weak head normal form first and
\ must then be literals or Nat.zero (is_nat_lit_ext, lines 607-612):
\
\   Lean           here         semantics
\   Nat.succ n     big+ with 1  n + 1
\   Nat.add        big+         a + b
\   Nat.sub        big-         a - b, or 0 when b > a (truncated)
\   Nat.mul        big*         a * b
\   Nat.div        big/         floor(a / b); a / 0 = 0
\   Nat.mod        big-mod      a mod b; a mod 0 = a
\   Nat.gcd        big-gcd      gcd; gcd(a, 0) = a, gcd(0, 0) = 0
\   Nat.beq        big=         Bool.true when a = b, else Bool.false
\   Nat.ble        big<=        Bool.true when a <= b, else Bool.false
\   Nat.land       big-and      bitwise and
\   Nat.lor        big-or       bitwise or
\   Nat.xor        big-xor      bitwise exclusive or
\   Nat.shiftLeft  big-lshift   a * 2^b; 0 shifted by anything is 0
\   Nat.shiftRight big-rshift   floor(a / 2^b); 0 for every b too large
\   Nat.pow        big-pow      a ^ b; a ^ 0 = 1, so 0 ^ 0 = 1
\
\ The semantics are those of Lean's runtime, which the kernel calls through
\ object.h lines 331-347: include/lean/lean.h of the 4.35.0 toolchain, lines
\ 1665-1676 (sub), 1694-1705 (div), 1721-1732 (mod), 1813-1822 (shiftRight),
\ and src/runtime/object.cpp lines 1427-1441, 1457-1470, 1488-1505, 1573-1627
\ and 1643-1655 (GMP's mpz_gcd). Nat.log2 is NOT computed by the 4.35.0
\ kernel (the runtime's lean_nat_log2, object.cpp 1657-1669, is never
\ called from type_checker.cpp); big-bits gives the bit length it would need.
\
\ Lean also refuses some computations with a kernel exception, which this
\ library leaves to the kernel integration, since only it knows Lean's
\ host-specific size measure. lean_nat_size_in_bytes (object.cpp 1671-1675,
\ mpz.cpp 232-234) is 8 for a value below 2^63 and 8 bytes per 64-bit limb
\ above; the limit is 128 MiB (type_checker.cpp 36), or LEAN_NAT_MAX_SIZE
\ (1266-1280). With the default, a numeral passes exactly when it has at
\ most 2^30 bits. The checks: every literal (infer_lit, 315-321); the
\ results of succ, add, sub and mul (681, 622-626); for pow, an exponent
\ above 2^32 - 1 even for base 0 or 1 (get_count_arg, 305-313, called
\ before any base test at 637), and a base above 1 with a nonzero exponent
\ k whose size exceeds max/k (640), an estimate; for shiftLeft of a nonzero
\ value, a shift above 2^32 - 1 and size(v) + shift/8 + 1 above the limit
\ (655-658), again an estimate. gcd, div, mod, the bit operations and
\ shiftRight are not checked: their results are no larger than an argument.
\
\ Representation. A number is the address of a cell holding its limb count
\ followed by that many limbs, least significant first. A limb is one cell,
\ read as unsigned: limb-bits is the cell's width, counted when this file
\ loads, so the code works the same on 32- and 64-bit cells and no result
\ depends on the cell size. A number is normalized: its top limb is not
\ zero, and 0 has no limbs. Numbers are never changed after they are made.
\ The layout is host memory and must never be serialized; decimal text is
\ the portable form.
\
\ Arenas. Numbers live in an arena, a /big-arena record over memory the
\ caller provides (ALLOCATE, or a region of a checker context), made with
\ big-arena-init. Every operation makes its result at the arena's top, with
\ any scratch it needs above the result, and gives the scratch back before
\ it returns. big-mark and big-release give back everything made since a
\ mark. A number stays valid until it is released; its address must not be
\ kept past that, nor across a move of the arena's memory.
\
\ Outcomes (src/lib/outcome.fs): ok; invalid for a malformed number (a
\ negative count or a zero top limb), a number reaching into the arena's
\ free part (released, so the result would overwrite it: big-live?), a
\ corrupted arena record, or text that is not decimal digits; full when
\ the arena has no room, or when the result would have more bits than the
\ arena's limit. The limit is big-lean-bits, 2^30, unless big-limit! sets
\ another (at most big-max-limit, 2^(cell bits - 2)). At the default this
\ library never refuses a value Lean 4.35.0 accepts or computes, given
\ room, because each of Lean's checks above admits only results of at
\ most 2^30 bits. A failure gives -1 in the result's place (big>decimal:
\ 0 0, an empty text) and leaves the arena's top where it was. The checks
\ are O(1): a released number whose memory was claimed again looks live.
\ Comparisons and big-bits trust their arguments: check numbers from
\ elsewhere with big-valid? first.
\
\ Algorithms: schoolbook multiplication, Karatsuba above karatsuba-limbs
\ limbs (measured, see docs/development/FORTH_LIBRARY.md); Knuth's algorithm
\ D for division (TAOCP vol. 2, 4.3.1); Lehmer's gcd with single-limb
\ leading parts (Knuth's algorithm L, 4.5.2); left-to-right binary powers;
\ quadratic decimal conversion in chunks of the largest power of ten that
\ fits a limb. Limb arithmetic uses Forth-2012's double-cell words UM*,
\ UM/MOD, D+, D- and DU<.
\
\ State: none of its own. Every word takes an arena or numbers in one, so
\ separate arenas are independent; one arena is single-threaded. The
\ constants computed while loading (limb-bits, chunk-base, chunk-digits)
\ are read-only. Loads in decimal whatever BASE is, and restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./bounds.fs
require ./outcome.fs
require ./portability.fs

\ ---- Limbs ----

\ Bits in a limb (a cell), counted rather than assumed.
: count-bits ( u -- n ) 0 swap begin dup while 1 rshift swap 1+ swap repeat drop ;
-1 count-bits constant limb-bits
\ Bits needed to write u, 0 for 0, by halving the width w that holds u:
\ when u >> ceil(w/2) is not 0, keep that and count ceil(w/2) bits.
: bit-length ( u -- n )
  0 swap limb-bits begin dup 1 > while 1+ 2/ 2dup rshift
  if >r r@ rshift swap r@ + swap r> then repeat drop + ;
\ The largest power of ten that fits a limb, and its number of digits.
: ten-power ( -- u n )
  1 0 begin over -1 0 10 um/mod nip u> 0= while swap 10 * swap 1+ repeat ;
ten-power constant chunk-digits constant chunk-base
cell negate constant back-cell
\ An unsigned quotient and remainder of cells.
: limb/ ( u1 u2 -- u ) 0 swap um/mod nip ;
: limb-mod ( u1 u2 -- u ) 0 swap um/mod drop ;

\ ---- Limb vectors: an address and a count of limbs ----

\ Loop bounds over the n limbs from addr: upward, for ?DO ... CELL +LOOP,
\ and downward from the top one (n at least 1), for DO ... BACK-CELL +LOOP.
: limb-range ( addr n -- end addr ) cells over + swap ;
: limbs-down ( addr n -- addr top ) 1- cells over + ;
\ The offset of src from dst, and the loop bounds over dst's n limbs.
: limbs-paired ( src dst n -- offset end dst ) >r tuck - swap r> limb-range ;
: copy-limbs ( src dst n -- ) cells move ;
: limbs-erase ( addr n -- ) cells erase ;

\ dst[0..n) += src[0..n): the carry out, 0 or 1.
: limbs+! ( src dst n -- carry )
  limbs-paired 0 -rot ?do over i + @ 0 rot 0 d+ i @ 0 d+ swap i ! cell +loop nip ;
\ dst[0..n) -= src[0..n): the borrow out, 0 or 1.
: limbs-! ( src dst n -- borrow )
  limbs-paired 0 -rot ?do
    over i + @ 0 rot 0 d+ i @ 0 2swap d- swap i ! negate cell +loop nip ;
\ Add a carry into the n limbs at addr, or take a borrow from them, stopping
\ once it is used up: what is left over at the top.
: carry+! ( carry addr n -- carry' )
  limb-range ?do dup 0= if leave then i @ 0 rot 0 d+ swap i ! cell +loop ;
: borrow-! ( borrow addr n -- borrow' )
  limb-range ?do dup 0= if leave then i @ 0 rot 0 d- swap i ! negate cell +loop ;
\ dst[0..m) += src[0..n) and -= src[0..n), for n <= m, carrying through
\ dst's higher limbs: what is left over at its top.
: vector+! ( src n dst m -- carry )
  2over nip - >r swap 2dup cells + >r limbs+! r> r> carry+! ;
: vector-! ( src n dst m -- borrow )
  2over nip - >r swap 2dup cells + >r limbs-! r> r> borrow-! ;

\ The inner loops of multiplication and division, each limb a double-cell
\ product plus a limb plus the carry, which cannot overflow two limbs.
\ They take four inputs, a multiplier, two vectors and a count, because
\ the loop needs all four at once; callers pass them from records.
\ dst[0..n) = m * src[0..n), and dst[0..n) += m * src[0..n): the carry
\ limb out. dst may be src for the first.
: limbs*! ( m src dst n -- carry )
  limbs-paired 0 -rot ?do 0 2over i + @ um* d+ swap i ! cell +loop nip nip ;
: limbs*+! ( m src dst n -- carry )
  limbs-paired 0 -rot ?do i @ 0 tuck d+ 2over i + @ um* d+ swap i ! cell +loop nip nip ;
\ dst[0..n) -= m * src[0..n): the borrow out, a limb.
: limbs*-! ( m src dst n -- borrow )
  limbs-paired 0 -rot ?do
    0 2over i + @ um* d+ swap i @ 2dup swap - i ! u> - cell +loop nip nip ;
\ The same two products with the carry stored as dst[n].
: limbs*row! ( m src dst n -- ) 2dup cells + >r limbs*! r> ! ;
: limbs*+row ( m src dst n -- ) 2dup cells + >r limbs*+! r> ! ;
\ addr[0..n) = addr[0..n) * m + c: the carry limb out.
: limbs-scale! ( m c addr n -- carry )
  limb-range ?do over i @ um* rot 0 d+ swap i ! cell +loop nip ;
\ addr[0..n) /= d (not 0), from the top limb down: the remainder.
: limbs/1! ( d addr n -- rem )
  dup 0= if 2drop drop 0 exit then limbs-down 0 -rot do over i @ -rot um/mod i !
  back-cell +loop nip ;
\ -1, 0 or 1 as u1 is below, equal to or above u2.
: limb-order ( u1 u2 -- n ) 2dup = if 2drop 0 exit then u< 2* 1+ ;
\ Compare a[0..n) with b[0..n) from the top limb down.
: limbs-compare ( a b n -- n )
  dup 0= if drop 2drop 0 exit then >r over - swap r> limbs-down 0 -rot do
  drop dup i + @ i @ swap limb-order dup if leave then back-cell +loop nip ;
\ Bitwise and, or and exclusive or of src into dst, limb by limb.
: limbs-and! ( src dst n -- ) limbs-paired ?do dup i + @ i @ and i ! cell +loop drop ;
: limbs-or! ( src dst n -- ) limbs-paired ?do dup i + @ i @ or i ! cell +loop drop ;
: limbs-xor! ( src dst n -- ) limbs-paired ?do dup i + @ i @ xor i ! cell +loop drop ;

\ ---- Numbers ----

: big-limbs ( big -- addr ) cell+ ;
: big-vector ( big -- addr n ) dup cell+ swap @ ;
\ The top limb's address (count at least 1), and the address after the number.
: big-top ( big -- addr ) dup @ cells + ;
: big-end ( big -- addr ) dup @ 1+ cells + ;
\ Copy a number's count and limbs to dst.
: big-move ( src dst -- ) over @ 1+ cells move ;
\ Copy a number's limbs into dst's first limbs.
: limbs-into ( big dst -- ) swap big-vector rot big-limbs swap copy-limbs ;
\ Whether a number is well formed: a count of at least 0 and, unless it is
\ 0, a top limb that is not 0.
: big-valid? ( big -- flag )
  dup @ dup 0< if 2drop false exit then if big-top @ 0<> else drop true then ;
\ Bits needed to write the number: 0 for 0.
: big-bits ( big -- n )
  dup @ 0= if drop 0 exit then dup @ 1- limb-bits * swap big-top @ bit-length + ;
\ The number as one cell, when it fits.
: big>u ( big -- u true | false )
  dup @ dup 0= if 2drop 0 true exit then 1 = if big-limbs @ true else drop false then ;
\ Drop leading zero limbs.
: top-zero? ( big -- flag ) dup @ 0> if big-top @ 0= else drop false then ;
: big-normalize ( big -- big ) begin dup top-zero? while -1 over +! repeat ;
: either-zero? ( a b -- flag ) @ 0= swap @ 0= or ;
\ Order two numbers by their count of limbs, the longer first.
: longer-first ( a b -- long short ) over @ over @ < if swap then ;
\ The limbs of r above x's count: their address and count.
: limbs-above ( x r -- addr n ) swap @ >r big-vector r@ - swap r> cells + swap ;
\ r += x and r -= x in place, through all of r's limbs: what is left over.
: big+! ( x r -- carry ) swap big-vector rot big-vector vector+! ;
: big-! ( x r -- borrow ) swap big-vector rot big-vector vector-! ;
\ -1, 0 or 1 as a is below, equal to or above b; big= and big<= are
\ Lean's Nat.beq and Nat.ble. They trust their arguments (big-valid?).
: size-order ( a b -- n ) @ swap @ swap 2dup = if 2drop 0 exit then < 2* 1+ ;
: big-compare ( a b -- n )
  2dup size-order ?dup if nip nip exit then over @ >r big-limbs swap big-limbs swap
  r> limbs-compare ;
: big= ( a b -- flag ) big-compare 0= ;
: big<= ( a b -- flag ) big-compare 1 < ;

\ ---- Arenas ----

begin-structure /big-arena
  field: arena-top         \ next free cell
  field: arena-end         \ address after the last whole cell
  field: arena-start       \ first cell
  field: arena-limit       \ most bits a result may have
end-structure

\ Lean 4.35.0's default numeral limit, 128 MiB, is exactly 2^30 bits (header).
1073741824 constant big-lean-bits
\ The largest limit an arena takes: sums of two bit counts then fit a cell.
max-n 2/ 1+ constant big-max-limit

\ Make an arena over the u address units at addr, empty, with the default
\ limit. A negative u gives an arena with no room.
: big-arena-init ( addr u arena -- )
  >r over + swap aligned tuck - 0 max cell / cells over +
  r@ arena-end ! dup r@ arena-start ! r@ arena-top ! big-lean-bits r> arena-limit ! ;
\ Set the most bits a result may have, kept between 0 and big-max-limit.
: big-limit! ( bits arena -- ) swap 0 max big-max-limit min swap arena-limit ! ;
\ Whether a <= b <= c, unsigned (addresses).
: addresses-ordered? ( a b c -- flag ) over u< 0= >r swap u< 0= r> and ;
: cell-aligned? ( addr -- flag ) dup aligned = ;
\ Whether an arena record is sound: start <= top <= end, top aligned, and
\ a limit in range.
: arena-span ( arena -- start top end )
  dup arena-start @ over arena-top @ rot arena-end @ ;
: arena-valid? ( arena -- flag )
  dup arena-span addresses-ordered? over arena-top @ cell-aligned? and
  swap arena-limit @ 0 big-max-limit between? and ;
\ A mark is the arena's top; big-release gives back everything made after
\ it, or is invalid, changing nothing, for a mark outside start..top.
: big-mark ( arena -- mark ) arena-top @ ;
: mark? ( mark arena -- flag )
  >r dup cell-aligned? swap r@ arena-start @ swap r> arena-top @ addresses-ordered? and ;
: big-release ( mark arena -- outcome )
  2dup mark? if arena-top ! outcome-ok else 2drop outcome-invalid then ;
\ Cells free above the top.
: arena-room ( arena -- n ) dup arena-end @ swap arena-top @ - cell / 0 max ;
\ Whether a number of limbs limbs fits, with its count cell.
: arena-room? ( limbs arena -- flag ) arena-room u< ;
\ Make a number of limbs limbs (count set, limbs not) at the top.
: arena-claim ( limbs arena -- big true | false )
  2dup arena-room? 0= if 2drop false exit then
  dup arena-top @ >r over 1+ cells swap arena-top +! r@ ! r> true ;
\ The failure of an operation that has no room.
: no-room ( -- -1 outcome ) outcome-full no-result ;
\ Go on with a and b when flag is true; otherwise drop them and fail.
: room-then? ( a b flag -- a b true | -1 outcome false )
  if true else 2drop no-room false then ;
\ Claim a result of n limbs above a and b, or drop them and fail.
: result-claim ( a b n arena -- a b c true | -1 outcome false )
  arena-claim if true else 2drop no-room false then ;
\ Whether a number has at most the arena's limit of bits.
: big-fits? ( big arena -- flag ) arena-limit @ swap big-bits < 0= ;
\ Normalize the number just made, keep it as the arena's newest (giving
\ back the scratch above it), or give it back too when it is over the limit.
: big-finish ( big arena -- big outcome )
  >r big-normalize dup r@ big-fits? if dup big-end r> arena-top ! outcome-ok exit then
  r> arena-top ! no-room ;
\ A number of one limb's value u; 0 has no limbs.
: cell-big ( u arena -- big outcome )
  1 over result-claim 0= if exit then rot over big-limbs ! swap big-finish ;
\ A copy of a number at the top.
: big-copy ( a arena -- c outcome )
  over @ over result-claim 0= if exit then rot over big-move swap big-finish ;
\ Whether a number stays clear of the arena's free part, from its top to
\ its end. One reaching into it was released (in part), and the result
\ would overwrite it. An O(1) test of addresses only: a released number
\ whose memory was claimed again cannot be told from a live one.
: big-live? ( big arena -- flag )
  >r dup big-end r@ arena-top @ u> 0= swap r> arena-end @ u< 0= or ;
\ Whether a number is well formed and live.
: operand? ( big arena -- flag ) over big-valid? if big-live? else 2drop false then ;
\ Whether two numbers and an arena are well formed, the numbers live.
: big-operands? ( a b arena -- a b arena flag )
  >r 2dup r@ operand? swap r@ operand? and r@ arena-valid? and r> swap ;
\ Run the operation xt ( a b arena -- c outcome ) on well-formed operands;
\ otherwise invalid.
: big-binary ( a b arena xt -- c outcome )
  >r big-operands? if r> execute else r> drop 2drop drop outcome-invalid no-result then ;

\ ---- Addition, subtraction, bit operations ----

\ r = long + short, where r has one limb more than long.
: add-into ( long short r -- r ) rot over limbs-into 0 over big-top ! tuck big+! drop ;
: add-core ( a b arena -- c outcome )
  >r longer-first over @ 1+ r@ result-claim 0= if r> drop exit then
  add-into r> big-finish ;
\ r = a - b, where a > b and r has a's count.
: sub-into ( a b r -- r ) rot over limbs-into tuck big-! drop ;
: sub-core ( a b arena -- c outcome )
  >r 2dup big-compare 0> 0= if 2drop 0 r> cell-big exit then
  over @ r@ result-claim 0= if r> drop exit then sub-into r> big-finish ;
: and-core ( a b arena -- c outcome )
  >r longer-first dup @ r@ result-claim 0= if r> drop exit then
  swap over limbs-into swap big-limbs over big-vector limbs-and! r> big-finish ;
\ A copy of the longer number, for or and xor to merge the shorter into.
: longer-copy ( a b arena -- short c true | -1 outcome false )
  >r longer-first over @ r> result-claim dup if >r rot over limbs-into r> then ;
: or-into ( short r -- ) swap big-vector >r swap big-limbs r> limbs-or! ;
: xor-into ( short r -- ) swap big-vector >r swap big-limbs r> limbs-xor! ;
: or-core ( a b arena -- c outcome )
  dup >r longer-copy if tuck or-into r> big-finish else r> drop then ;
: xor-core ( a b arena -- c outcome )
  dup >r longer-copy if tuck xor-into r> big-finish else r> drop then ;

\ ---- Multiplication ----

\ The rows of a schoolbook product r = a * b: for each limb m of b,
\ r[j..j+na] += m * a. A row job gives each row its arguments.
begin-structure /product
  field: product-a         \ a's limbs
  field: product-n         \ how many
  field: product-shift     \ address of r[j] less that of b[j]
end-structure
: row-args ( bj job -- m al rj na )
  >r dup @ r@ product-a @ rot r@ product-shift @ + r> product-n @ ;
: product-rows ( addr n job -- )
  -rot limb-range ?do i over row-args limbs*+row cell +loop drop ;

\ A product frame: r = a * b for a of n limbs, with scratch from the arena.
begin-structure /kara
  /product +field kara-rows  \ the rows' job: its product-a and product-n
  field: kara-b              \ b's limbs
  field: kara-r              \ the product's limbs
  field: kara-arena          \ where scratch is claimed
end-structure
/kara cell / constant kara-cells
\ a's limbs and their count n.
: kara-a ( frame -- addr ) kara-rows product-a ;
: kara-n ( frame -- addr ) kara-rows product-n ;
\ r[0..n+nb) = a * b by rows, for b of nb limbs.
: school ( nb frame -- )
  2dup kara-n @ + over kara-r @ swap limbs-erase dup kara-r @ over kara-b @ -
  over kara-rows product-shift ! dup kara-b @ -rot kara-rows product-rows ;

\ Karatsuba, for a and b of n >= karatsuba-limbs limbs each (measured, see
\ docs/development/FORTH_LIBRARY.md): with h = n / 2 and hi = n - h,
\ a = a1 B^h + a0 and b likewise; r[0..2h) = a0 b0, r[2h..2n) = a1 b1, and
\ z = (a0 + a1)(b0 + b1) - a0 b0 - a1 b1 is added at r[h]. Each step
\ claims a child frame with s = a0 + a1 and t = b0 + b1 (hi + 1 limbs each)
\ and z (2 hi + 2) above the arena's top and gives them back. Recursion
\ depth: about log2(n / karatsuba-limbs).
48 constant karatsuba-limbs
: kara-h ( frame -- h ) kara-n @ 2/ ;
: kara-hi ( frame -- hi ) dup kara-n @ swap kara-h - ;
\ Cells one step claims, and all the steps below a product of n limbs.
: step-cells ( hi -- cells ) 4 * 4 + kara-cells + 1+ ;
: kara-scratch ( n -- cells )
  0 swap begin dup karatsuba-limbs < 0= while
    dup 2/ - dup step-cells rot + swap 1+ repeat drop ;
\ The child frame, a copy of the frame. big-multiply checked the room for
\ every step (mul-cells) before the product began, so a refusal here is a
\ fault in this module, not an outcome: ABORT" stops the run rather than
\ write past the arena's end. It stays an ABORT" because an outcome would
\ need a test after each of kara's three recursive calls for a case the
\ room check excludes, and ADR 0018 (proposed, not yet approved) would
\ make it its throw-fault; the arena sweep in tests/lib/bignum.fs checks
\ that no room from 0 up reaches it.
: kara-child ( frame -- frame child )
  dup kara-hi step-cells 1- over kara-arena @ arena-claim
  0= abort" bignum: Karatsuba room" big-limbs 2dup /kara move ;
: kara-release ( child -- ) dup cell - swap kara-arena @ arena-top ! ;
\ The child's product: a0 b0, a1 b1, or s t into z.
: kara-shift ( u child -- ) 2dup kara-a +! 2dup kara-b +! swap 2* swap kara-r +! ;
: low-half ( frame child -- frame child ) 2dup /kara move over kara-h over kara-n ! ;
: high-half ( frame child -- frame child )
  2dup /kara move over kara-h cells over kara-shift over kara-hi over kara-n ! ;
\ The address after a child's field holding n limbs: s, then t, then z.
: kara-next ( child field-addr -- addr ) @ swap kara-n @ cells + ;
: middle ( frame child -- frame child )
  over kara-hi 1+ over kara-n ! dup /kara + over kara-a !
  dup dup kara-a kara-next over kara-b ! dup dup kara-b kara-next over kara-r ! ;
\ dst[0..hi] = x[0..h) + x[h..n), for x the frame's a or b.
: half-sum ( x dst frame -- )
  >r over r@ kara-h cells + over r@ kara-hi copy-limbs 0 over r@ kara-hi cells + !
  r@ kara-h swap r> kara-hi 1+ vector+! drop ;
\ s = a0 + a1 or t = b0 + b1, by the field xt (kara-a or kara-b).
: half-sum-of ( frame child xt -- frame child )
  >r over r@ execute @ over r> execute @ 2over drop half-sum ;
: middle-sums ( frame child -- frame child )
  ['] kara-a half-sum-of ['] kara-b half-sum-of ;
\ z -= a0 b0, z -= a1 b1, then r[h..2n) += z.
: kara-z ( child -- addr n ) dup kara-r @ swap kara-n @ 2* ;
: kara-low ( frame -- addr n ) dup kara-r @ swap kara-h 2* ;
: kara-high ( frame -- addr n ) dup kara-r @ over kara-h 2* cells + swap kara-hi 2* ;
: kara-mid ( frame -- addr n )
  dup kara-r @ over kara-h cells + over kara-n @ 2* rot kara-h - ;
: kara-fold ( frame child -- )
  kara-z rot >r 2dup r@ kara-low 2swap vector-! drop
  2dup r@ kara-high 2swap vector-! drop r> kara-mid vector+! drop ;
: kara ( frame -- )
  dup kara-n @ karatsuba-limbs < if dup kara-n @ swap school exit then
  kara-child low-half dup recurse high-half dup recurse middle middle-sums dup recurse
  tuck kara-fold kara-release ;

\ A longer factor of count limbs is cut into chunks of the shorter one's
\ count n, and each chunk's Karatsuba product with b (into T, 2 n limbs)
\ is added into r at the chunk's place. A tail of c limbs, 0 < c < n, is
\ multiplied by rows when c is below karatsuba-limbs. Otherwise the job
\ becomes b times the tail, at the tail's place in r, with b cut into
\ chunks of c: T and the Karatsuba scratch for n limbs hold those for c,
\ so it needs no more room, and the counts shrink as in Euclid's
\ algorithm. (Padding the tail to n limbs could double the work.)
begin-structure /chunks
  /kara +field chunks-frame  \ one chunk times b, into T
  field: chunks-long         \ the longer factor's limbs
  field: chunks-count        \ how many
  field: chunks-r            \ the product's limbs
end-structure
/chunks cell / constant chunks-cells
: chunks-n ( job -- n ) chunks-frame kara-n @ ;
\ The tail: its count, its first limb and its address.
: tail-size ( job -- c ) dup chunks-count @ swap chunks-n mod ;
: tail-limb ( job -- i ) dup chunks-count @ swap tail-size - ;
: tail-addr ( job -- addr ) dup tail-limb cells swap chunks-long @ + ;
\ Add T into r from limb i on, carrying to r's end: 2 n limbs, or the
\ c + n of a tail's rows.
: chunk-add ( i job -- )
  >r r@ chunks-count @ r@ chunks-n + over - swap cells r@ chunks-r @ + swap
  r@ chunks-frame kara-r @ over r> chunks-n 2* min 2swap vector+! drop ;
\ The chunk at limb i times b, into T, added into r.
: chunk-product ( i job -- )
  2dup chunks-long @ swap cells + over chunks-frame tuck kara-a ! kara chunk-add ;
: whole-chunks ( job -- )
  dup tail-limb 0 ?do i over chunk-product dup chunks-n +loop drop ;
\ The tail times b by rows (a := b, b := the tail), into T, added into r.
: tail-rows ( job -- )
  dup chunks-frame dup kara-b @ over kara-a ! over tail-addr swap kara-b !
  dup tail-size over chunks-frame school dup tail-limb swap chunk-add ;
\ The job becomes b times the tail: long := b (n limbs), b := the tail
\ (c limbs), and r starts at the tail's limb.
: tail-job! ( job -- )
  >r r@ tail-addr r@ tail-size r@ tail-limb cells r@ chunks-r +!
  r@ chunks-frame kara-b @ r@ chunks-long ! r@ chunks-n r@ chunks-count !
  r@ chunks-frame kara-n ! r> chunks-frame kara-b ! ;
: chunks-run ( job -- )
  begin dup whole-chunks dup tail-size karatsuba-limbs < 0= while dup tail-job! repeat
  dup tail-size if tail-rows else drop then ;

\ r = long * short (r erased, na + nb limbs), by rows or by Karatsuba, in
\ a frame or a job claimed above r (big-multiply checked the room) that
\ holds r: the frame's product, or the job's, with T after the job.
: rows-frame ( r arena -- frame )
  kara-cells swap arena-claim drop big-limbs swap big-limbs over kara-r ! ;
: kara-job ( r n arena -- job )
  >r 2* chunks-cells + r@ arena-claim drop big-limbs r> over chunks-frame kara-arena !
  swap big-limbs over chunks-r ! dup /chunks + over chunks-frame kara-r ! ;
\ The factors into the frame or job.
: frame! ( long short frame -- nb frame )
  >r big-vector swap r@ kara-b ! swap big-vector r@ kara-n ! r@ kara-a ! r> ;
: chunks! ( long short job -- job )
  >r big-vector r@ chunks-frame kara-n ! r@ chunks-frame kara-b !
  big-vector r@ chunks-count ! r@ chunks-long ! r> ;
\ Four inputs: the two factors, r and the arena that gives the frame.
: school-product ( long short r arena -- r ) over >r rows-frame frame! school r> ;
: kara-product ( long short r arena -- r )
  over >r >r over @ r> kara-job chunks! chunks-run r> ;
\ Cells a product needs: itself, then its frame or job, T and scratch.
: product-size ( a b -- limbs ) @ swap @ + ;
: mul-scratch ( short -- cells )
  @ dup karatsuba-limbs < if drop kara-cells 1+ exit then
  dup 2* chunks-cells + 1+ swap kara-scratch + ;
: mul-cells ( long short -- cells ) dup mul-scratch -rot product-size 1+ + ;
\ r = a * b at the top, with na + nb limbs, not yet normalized.
: big-multiply ( a b arena -- r true | false )
  >r longer-first 2dup mul-cells r@ arena-room > if 2drop r> drop false exit then
  2dup product-size r@ arena-claim drop dup big-vector limbs-erase
  over @ karatsuba-limbs < if r@ school-product else r@ kara-product then
  dup big-end r> arena-top ! true ;
\ Whether a product may fit the limit: its least possible size,
\ bits(a) + bits(b) - 1, is at most the limit.
: product-fits? ( a b arena -- flag )
  arena-limit @ swap big-bits - swap big-bits 1- < 0= ;
: mul-core ( a b arena -- c outcome )
  >r 2dup either-zero? if 2drop 0 r> cell-big exit then
  2dup r@ product-fits? room-then? 0= if r> drop exit then
  r@ big-multiply if r> big-finish else r> drop no-room then ;

\ ---- Division (Knuth's algorithm D) ----

\ The divisor v (n >= 2 limbs) and dividend u are scaled by 2^s, so that
\ v's top limb has its top bit set; u gains one limb. For each window
\ u[j..j+n], j from m = na - nb down to 0, the quotient limb is estimated
\ from the window's top three limbs and v's top two (never too small, at
\ most one too large), q * v is subtracted, and v added back if that went
\ below zero. The remainder is u[0..n) scaled back.
begin-structure /division
  field: division-u        \ the scaled dividend's limbs, na + 1 of them
  field: division-v        \ the scaled divisor's limbs, n of them
  field: division-n        \ n, at least 2
  field: division-m        \ na - n: the quotient has m + 1 limbs
  field: division-dq       \ address of the quotient's limbs less u's
  field: division-scale    \ 2^s
  field: division-v1       \ v's top limb
  field: division-v0       \ the limb below it
  field: division-qhat     \ the quotient limb being estimated
  field: division-rhat     \ its remainder against the window's top two limbs
end-structure
/division cell / constant division-cells

\ The job, then u, v and the quotient, in one block.
: division-size ( a b -- cells ) drop @ 2* 2 + division-cells + ;
: job-sizes! ( a b job -- ) >r @ dup r@ division-n ! swap @ swap - r> division-m ! ;
: un-cells ( job -- n ) dup division-m @ swap division-n @ + 1+ ;
: job-places! ( job -- )
  dup /division + 2dup swap division-u ! over un-cells cells + 2dup swap division-v !
  over division-n @ cells + over division-u @ - swap division-dq ! ;
\ 2^s for the divisor b, and m * b's limbs into dst: the carry limb.
: divisor-scale ( b -- u ) big-top @ bit-length limb-bits swap - 1 swap lshift ;
: scaled-into ( m big dst -- carry ) swap big-vector >r swap r> limbs*! ;
: un-top ( job -- addr ) dup division-u @ swap un-cells 1- cells + ;
: job-scale! ( a b job -- )
  >r dup divisor-scale dup r@ division-scale ! tuck swap r@ division-v @ scaled-into drop
  swap r@ division-u @ scaled-into r> un-top ! ;
: job-v1v0! ( job -- )
  dup division-v @ over division-n @ 2 - cells + 2@ rot tuck division-v0 ! division-v1 ! ;
\ Claim and fill a division job for a / b (b has at least two limbs, a >= b).
: div-setup ( a b arena -- job true | false )
  >r 2dup division-size r> arena-claim 0= if 2drop false exit then big-limbs
  >r 2dup r@ job-sizes! r@ job-places! r@ job-scale! r@ job-v1v0! r> true ;

\ The top limb u[j+n] of the window that starts at uj.
: window-top ( uj job -- addr ) division-n @ cells + ;
\ The first estimate from the window's top two limbs u2 u1: u2:u1 / v1,
\ or B - 1 when u2 = v1 (u2 is never larger), with rhat = u1 + v1. When
\ that rhat does not fit a limb the estimate needs no test: false.
: qhat-divide ( u1 u2 job -- )
  >r r@ division-v1 @ um/mod r@ division-qhat ! r> division-rhat ! ;
: qhat-max ( u1 job -- test? )
  -1 over division-qhat ! >r r@ division-v1 @ 0 tuck d+ swap r> division-rhat ! 0= ;
: qhat-first ( top job -- test? )
  >r dup @ swap cell - @ swap dup r@ division-v1 @ u<
  if r> qhat-divide true else drop r> qhat-max then ;
\ Whether qhat * v0 > rhat:u0, so that qhat is too large.
: qhat-big? ( u0 job -- flag )
  >r r@ division-qhat @ r@ division-v0 @ um* rot r> division-rhat @ 2swap du< ;
\ Lower qhat by one: rhat grows by v1; true when it no longer fits a limb.
: qhat-lower ( job -- overflow? )
  -1 over division-qhat +! dup division-v1 @ over division-rhat @ over + tuck u>
  >r swap division-rhat ! r> ;
\ Knuth's test, at most twice.
: qhat-refine ( u0 job -- )
  begin 2dup qhat-big? while dup qhat-lower if 2drop exit then repeat 2drop ;
: qhat-estimate ( top job -- q )
  2dup qhat-first if over 2 cells - @ over qhat-refine then nip division-qhat @ ;
\ Subtract a limb from the window's top: true when that went below zero.
: window-borrow! ( borrow top -- negative? ) dup @ rot 2dup u< >r - swap ! r> ;
\ window -= q * v: true when the window went below zero.
: window-! ( q uj job -- negative? )
  2dup window-top >r dup division-v @ swap division-n @ >r swap r> limbs*-!
  r> window-borrow! ;
\ window += v, dropping the carry out of its top (it cancels the borrow).
: window+! ( uj job -- )
  2dup window-top >r dup division-v @ -rot division-n @ limbs+! r> +! ;
\ One quotient limb.
: div-step ( uj job -- q )
  2dup window-top over qhat-estimate >r 2dup r@ -rot window-!
  if window+! r> 1- else 2drop r> then ;
\ Every quotient limb, from the top window down.
: div-run ( job -- )
  dup division-u @ over division-m @ 1+ limbs-down do
  i over div-step over division-dq @ i + ! back-cell +loop drop ;
\ Copy the quotient, or the remainder scaled back, into r.
: quotient-into ( r job -- r )
  dup division-u @ over division-dq @ + swap division-m @ 1+
  >r over big-limbs r> copy-limbs ;
: remainder-into ( r job -- r )
  dup division-scale @ over division-u @ rot division-n @ 2dup 2>r limbs/1! drop
  2r> >r over big-limbs r> copy-limbs ;
\ Whether the quotient is 0: b is 0 or a < b.
: div-trivial? ( a b -- flag ) dup @ 0= if 2drop true exit then big-compare 0< ;
\ Division by a one-limb b.
: short-div ( a b arena -- c outcome )
  >r big-limbs @ over @ r@ result-claim 0= if r> drop exit then
  rot over limbs-into tuck big-vector limbs/1! drop r> big-finish ;
: short-mod ( a b arena -- c outcome )
  >r big-limbs @ over @ r@ result-claim 0= if r> drop exit then
  rot over limbs-into tuck big-vector limbs/1! over big-limbs ! 1 over ! r> big-finish ;
\ Division by b of two limbs or more.
: long-div ( a b arena -- c outcome )
  >r 2dup @ swap @ swap - 1+ r@ result-claim 0= if r> drop exit then
  -rot r@ div-setup 0= if r> arena-top ! no-room exit then
  dup div-run quotient-into r> big-finish ;
: long-mod ( a b arena -- c outcome )
  >r dup @ r@ result-claim 0= if r> drop exit then
  -rot r@ div-setup 0= if r> arena-top ! no-room exit then
  dup div-run remainder-into r> big-finish ;
: div-core ( a b arena -- c outcome )
  >r 2dup div-trivial? if 2drop 0 r> cell-big exit then
  dup @ 1 = if r> short-div else r> long-div then ;
: mod-core ( a b arena -- c outcome )
  >r 2dup div-trivial? if drop r> big-copy exit then
  dup @ 1 = if r> short-mod else r> long-mod then ;

\ ---- Shifts ----

\ Whether a shifted left by s bits has at most the limit's bits: s is at
\ most limit - bits(a).
: shift-fits? ( a s arena -- flag )
  arena-limit @ rot big-bits - dup 0< if 2drop false exit then u> 0= ;
\ r = a * 2^s: s / B zero limbs, then a times 2^(s mod B).
: lshift-into ( a s r -- r )
  >r limb-bits /mod r@ big-limbs over limbs-erase cells r@ big-limbs + >r
  1 swap lshift swap big-vector r> swap limbs*row! r> ;
: lshift-size ( a s -- limbs ) limb-bits limb/ swap @ + 1+ ;
\ a * 2^s for a > 0 and s a cell.
: lshift-cell ( a s arena -- c outcome )
  >r 2dup r@ shift-fits? room-then? 0= if r> drop exit then
  2dup lshift-size r@ result-claim 0= if r> drop exit then lshift-into r> big-finish ;
: lshift-core ( a s arena -- c outcome )
  >r over @ 0= if 2drop 0 r> cell-big exit then
  big>u if r> lshift-cell else drop r> drop no-room then ;
\ The limbs of a from limb q on: their address and count.
: limbs-from ( q a -- addr n ) tuck @ swap - >r big-end r@ cells - r> ;
\ r = a / 2^s, where s / B is below a's count and r has the rest's count.
: rshift-into ( a s r -- r )
  >r limb-bits /mod rot limbs-from r@ big-limbs swap dup >r copy-limbs
  1 swap lshift r> r@ big-limbs swap limbs/1! drop r> ;
\ Whether a shift by s leaves nothing: s does not fit a cell, or s / B
\ reaches a's count.
: shifted-out? ( a s -- a s flag )
  2dup big>u if limb-bits limb/ swap @ < 0= else drop true then ;
: rshift-core ( a s arena -- c outcome )
  >r shifted-out? if 2drop 0 r> cell-big exit then big>u drop
  over @ over limb-bits limb/ - r@ result-claim 0= if r> drop exit then
  rshift-into r> big-finish ;

\ ---- Powers ----

\ x := x * y, where x is the arena's newest number: the product is made
\ above it and moved down. When that fails, x is given back too (full).
\ A product that cannot fit the limit is refused before it is made.
: give-back ( x arena -- outcome ) arena-top ! outcome-full ;
: big-settle ( p x arena -- outcome )
  >r swap big-normalize dup r@ big-fits? 0= if drop r> give-back exit then
  over big-move big-end r> arena-top ! outcome-ok ;
: big-times! ( x y arena -- outcome )
  >r 2dup r@ product-fits? 0= if drop r> give-back exit then
  over swap r@ big-multiply if swap r> big-settle else r> give-back then ;
\ x := x * x, then x := x * y unless y is 0.
: power-tail ( y x arena -- outcome )
  >r dup dup r@ big-times! dup ok? 0= if nip nip r> drop exit then drop
  over if swap r> big-times! else 2drop r> drop outcome-ok then ;
\ base ^ e for e >= 1, left to right over e's bits: x = base ^ (e / 2),
\ squared, times base when e is odd. Recursion depth: e's bit length.
: big-power ( base e arena -- x outcome )
  over 1 = if nip big-copy exit then
  >r 2dup 1 rshift r@ recurse ok-then? 0= if nip nip r> drop no-result exit then
  >r 1 and 0= if drop 0 then r> tuck r> power-tail ;
\ Whether base ^ e (base >= 2, e >= 1) may fit the limit: its least
\ possible size, (bits(base) - 1) * e + 1, is at most the limit.
: power-fits? ( base e arena -- flag ) arena-limit @ 1- 0 max rot big-bits 1- / u> 0= ;
: power-core ( base e arena -- c outcome )
  >r 2dup r@ power-fits? room-then? 0= if r> drop exit then
  r> big-power dup ok? 0= if nip no-result then ;
\ Whether a number is 0 or 1.
: unit? ( big -- flag ) big>u if 2 u< else false then ;
: pow-core ( base e arena -- c outcome )
  >r dup @ 0= if 2drop 1 r> cell-big exit then over unit? if drop r> big-copy exit then
  big>u if r> power-core else drop r> drop no-room then ;

\ ---- Greatest common divisor (Lehmer) ----

\ While v has two limbs or more, the leading p = limb-bits - 3 bits x of
\ u and y of v (at the same position) run Euclid's algorithm in single
\ cells with cofactors a b c d, as long as the quotients (x + a) / (y + c)
\ and (x + b) / (y + d) agree, so that each is the true quotient; then
\ u, v := a u + b v, c u + d v. When no step agreed (b = 0), one full
\ division: u, v := v, u mod v. Then single-limb Euclid. The cofactors stay
\ below 2^p in size, so every sum and product fits a signed cell.
\ A row of the cofactors' matrix: a b, or c d.
begin-structure /pair
  field: pair-p
  field: pair-q
end-structure
: pair! ( p q pair -- ) tuck pair-q ! pair-p ! ;
: pair@ ( pair -- p q ) dup pair-p @ swap pair-q @ ;
begin-structure /euclid
  field: euclid-u          \ u >= v
  field: euclid-v
  field: euclid-t          \ spare numbers for the next u and v
  field: euclid-w
  /pair +field euclid-ab   \ the next u is a u + b v
  /pair +field euclid-cd   \ the next v is c u + d v
  field: euclid-x          \ the leading bits of u and v
  field: euclid-y
end-structure
/euclid cell / constant euclid-cells
limb-bits 3 - constant lead-bits

\ The job and four numbers of n + 1 limbs, for u of n limbs.
: euclid-size ( u -- cells ) @ 2 + 4 * euclid-cells + ;
\ Store addr in the field at field-addr, and step it by size.
: place! ( size addr field-addr -- size addr' ) over swap ! over + ;
: euclid-places! ( n job -- )
  >r 2 + cells r@ /euclid + r@ euclid-u place! r@ euclid-v place! r@ euclid-t place!
  r> euclid-w place! 2drop ;
: euclid-setup ( u v arena -- job true | false )
  >r over euclid-size r> arena-claim 0= if 2drop false exit then big-limbs
  >r over @ r@ euclid-places! r@ euclid-v @ big-move r@ euclid-u @ big-move r> true ;
\ Limb i of a number, 0 above its top; limbs q and q + 1.
: limb@ ( i big -- u ) 2dup @ u< if big-limbs swap cells + @ else 2drop 0 then ;
: limb-pair@ ( q big -- lo hi ) 2dup limb@ -rot swap 1+ swap limb@ ;
\ The limb at bit s (below limb-bits) of the double limb hi:lo.
: funnel ( lo hi s -- u )
  ?dup 0= if drop exit then tuck limb-bits swap - lshift -rot rshift or ;
\ floor(big / 2^k) mod B.
: bits-at ( k big -- u ) swap limb-bits /mod rot limb-pair@ rot funnel ;
\ The leading bits, and the cofactors a b c d = 1 0 0 1.
: lehmer-leading! ( job -- )
  >r r@ euclid-u @ big-bits lead-bits - dup r@ euclid-u @ bits-at r@ euclid-x !
  r@ euclid-v @ bits-at r@ euclid-y ! 1 0 r@ euclid-ab pair! 0 1 r> euclid-cd pair! ;
\ A column of the cofactors, by the field xt: a and c (pair-p), or b and d.
: column ( job xt -- top bottom ) >r dup euclid-ab r@ execute swap euclid-cd r> execute ;
\ The two quotients of a step, when they agree and neither divisor is 0:
\ x + a over y + c, and x + b over y + d.
: lead-terms ( job xt -- num den )
  over >r column @ r@ euclid-y @ + swap @ r> euclid-x @ + swap ;
\ num / den for den > 0 and num >= 0. Knuth shows both always hold; a value
\ outside them ends the simulation rather than misleading it.
: lead-quotient ( num den -- q true | false )
  dup 0> if over 0< if 2drop false else limb/ true then else 2drop false then ;
: quotients-agree? ( job -- q true | false )
  dup ['] pair-p lead-terms lead-quotient 0= if drop false exit then
  swap ['] pair-q lead-terms lead-quotient 0= if drop false exit then
  over = if true else drop false then ;
\ addr1, addr2 := addr2, addr1 - q * addr2.
: cofactor-turn ( q addr1 addr2 -- ) >r dup @ rot r@ @ * - swap r@ @ swap ! r> ! ;
\ One step of Euclid's algorithm on both columns and the leading bits.
: euclid-step ( q job -- )
  2dup ['] pair-p column cofactor-turn 2dup ['] pair-q column cofactor-turn
  dup euclid-x swap euclid-y cofactor-turn ;
: lehmer-simulate ( job -- )
  begin dup quotients-agree? while over euclid-step repeat drop ;
\ dst = c * big, over dst's whole count; dst -= c * big, borrowing through
\ dst's higher limbs.
: term! ( c big dst -- )
  dup big-vector limbs-erase >r big-vector r> big-limbs swap limbs*row! ;
: term-! ( c big dst -- )
  2dup limbs-above 2>r >r big-vector r> big-limbs swap limbs*-! 2r> borrow-! drop ;
\ The cofactor pair p q (a b, or c d) as the positive term and the
\ subtracted one: p u - (-q) v, or q v - (-p) u; one of p and q is
\ positive and the other not.
: cofactor-terms ( pair job -- c1 big1 c2 big2 )
  >r pair@ over 0> if negate r@ euclid-u @ swap r> euclid-v @ exit then
  swap negate r@ euclid-v @ swap r> euclid-u @ ;
\ dst = a u + b v (or c u + d v), known to be at least 0, with u's count
\ + 1 limbs.
: cofactor-combine ( dst pair job -- )
  rot over euclid-u @ @ 1+ over ! -rot cofactor-terms
  2>r rot dup >r term! r> 2r> rot term-! ;
\ Exchange the cells at two addresses; u, v, t, w := t, w, u, v.
: exchange ( addr1 addr2 -- ) 2dup @ swap @ rot ! swap ! ;
: swap-pairs ( job -- )
  dup euclid-u over euclid-t exchange dup euclid-v swap euclid-w exchange ;
: combine-into ( dst pair job -- )
  rot dup >r -rot cofactor-combine r> big-normalize drop ;
\ u, v := a u + b v, c u + d v (made in t and w).
: lehmer-turn ( job -- )
  >r r@ euclid-t @ r@ euclid-ab r@ combine-into
  r@ euclid-w @ r@ euclid-cd r@ combine-into r> swap-pairs ;
\ t = u mod v, made at the arena's top and moved into t; then u, v, t := v, t, u.
: remainder>t ( job arena -- outcome )
  >r dup euclid-u @ over euclid-v @ r@ mod-core ok-then?
  if dup rot euclid-t @ big-move r> arena-top ! outcome-ok else nip r> drop then ;
: rotate-three ( job -- )
  >r r@ euclid-u @ r@ euclid-v @ r@ euclid-t @ r@ euclid-v ! r@ euclid-u ! r> euclid-t ! ;
: euclid-divide ( job arena -- outcome )
  over >r remainder>t r> over ok? if rotate-three else drop then ;
\ Whether no simulated step agreed: b is still 0.
: no-step? ( job -- flag ) euclid-ab pair-q @ 0= ;
: lehmer-round ( job arena -- outcome )
  over dup lehmer-leading! lehmer-simulate over no-step? if euclid-divide exit then
  drop lehmer-turn outcome-ok ;
: lehmer ( job arena -- outcome )
  begin over euclid-v @ @ 1 > while
    2dup lehmer-round dup ok? 0= if nip nip exit then drop repeat 2drop outcome-ok ;
\ Euclid on cells, and the end: v has at most one limb, u mod v in place.
: cell-gcd ( u1 u2 -- u ) begin dup while tuck limb-mod repeat drop ;
: u-mod-v ( job -- v u-mod-v )
  dup euclid-v @ big-limbs @ tuck swap euclid-u @ big-vector limbs/1! ;
: gcd-tail ( job -- )
  dup euclid-v @ @ 0= if drop exit then
  dup u-mod-v cell-gcd swap euclid-u @ tuck big-limbs ! 1 swap ! ;
: euclid-run ( r job arena -- c outcome )
  >r dup r@ lehmer dup ok? 0= if nip swap r> arena-top ! no-result exit then
  drop dup gcd-tail euclid-u @ over big-move r> big-finish ;
\ gcd(u, v) for u >= v > 0: the result (at most v's count) first, then the job.
: lehmer-gcd ( u v arena -- c outcome )
  >r dup @ r@ result-claim 0= if r> drop exit then
  -rot r@ euclid-setup 0= if r> arena-top ! no-room exit then r> euclid-run ;
: gcd-core ( a b arena -- c outcome )
  >r 2dup big-compare 0< if swap then
  dup @ 0= if drop r> big-copy else r> lehmer-gcd then ;

\ ---- Decimal text ----

: decimal-digit? ( c -- flag ) [char] 0 [char] 9 1+ within ;
\ Whether text is one or more decimal digits.
: digits? ( addr u -- flag )
  dup 0> 0= if 2drop false exit then chars over + swap
  ?do i c@ decimal-digit? 0= if unloop false exit then 1 chars +loop true ;
: skip-zeros ( addr u -- addr' u' )
  begin dup if over c@ [char] 0 = else false then while 1 /string repeat ;
\ The value of at most chunk-digits digits.
: chunk>u ( addr u -- u )
  0 -rot chars over + swap ?do 10 * i c@ [char] 0 - + 1 chars +loop ;
\ x := x * m + c in place, gaining a limb when the carry is not 0.
: big-scale! ( c m big -- )
  >r swap r@ big-vector limbs-scale! ?dup if r@ big-end ! 1 r@ +! then r> drop ;
: chunk+! ( big addr n -- ) chunk>u chunk-base rot big-scale! ;
\ Digits in the first chunk, so that the others are whole.
: first-chunk ( u -- n ) chunk-digits mod ?dup 0= if chunk-digits then ;
: parse-into ( addr u big -- big )
  >r 2dup first-chunk r@ -rot chunk+! dup first-chunk /string
  r> -rot chars over + swap ?do dup i chunk-digits chunk+! chunk-digits chars +loop ;
\ Whether u digits (no leading zero) may fit the limit: at least
\ 3.32 (u - 1) bits are needed, so u - 1 must be at most limit / 3.
: digits-fit? ( u arena -- flag ) swap 1- swap arena-limit @ 3 / > 0= ;
\ Limbs enough for u digits: fewer than 4 bits each.
: digit-limbs ( u -- limbs ) 4 * limb-bits / 1+ ;
: parse-decimal ( addr u arena -- big outcome )
  >r skip-zeros dup 0= if 2drop 0 r> cell-big exit then
  dup r@ digits-fit? room-then? 0= if r> drop exit then
  dup digit-limbs r@ result-claim 0= if r> drop exit then
  0 over ! parse-into r> big-finish ;
\ The number whose decimal digits are at addr u: invalid unless the text is
\ one or more digits 0-9 (leading zeros are allowed).
: decimal>big ( addr u arena -- big outcome )
  dup arena-valid? 0= if drop 2drop outcome-invalid no-result exit then
  >r 2dup digits? if r> parse-decimal else 2drop r> drop outcome-invalid no-result then ;

\ Write the chunk-digits digits of u (below chunk-base) before end.
: digits! ( u end -- start )
  chunk-digits 0 do 1 chars - swap 0 10 um/mod swap [char] 0 + rot tuck c! loop nip ;
\ Divide the copy by chunk-base and write the remainder's digits.
: chunk-out ( copy end -- copy end' )
  over >r chunk-base r@ big-vector limbs/1! r> big-normalize drop swap digits! ;
: digits-out ( copy end -- start ) begin over @ while chunk-out repeat nip ;
\ Cells for the text of a number: at most bits / 3 + 1 digits, and the
\ top chunk is written whole too, up to chunk-digits - 1 characters more.
: text-cells ( big -- n ) big-bits 3 / chunk-digits + chars cell+ 1- cell / ;
: text-room? ( big arena -- flag ) >r dup text-cells swap @ + 1+ r> arena-room? ;
: zero-text ( arena -- addr u outcome )
  1 swap arena-claim 0= if 0 0 outcome-full exit then
  big-limbs [char] 0 over c! 1 outcome-ok ;
\ The text block (claimed like a number of text-cells limbs, the text
\ written backwards from its end), then a copy of the number to divide
\ down to 0 (room checked): the address after the text, and the copy.
: text-and-copy ( big arena -- end copy )
  >r dup text-cells r@ arena-claim drop big-end
  over @ r> arena-claim drop rot over big-move ;
\ The digits are written backwards from the text's end; the copy is given
\ back.
: decimal-of ( big arena -- addr u outcome )
  2dup text-room? 0= if 2drop 0 0 outcome-full exit then
  dup >r text-and-copy over digits-out over r> arena-top !
  tuck - 1 chars / skip-zeros outcome-ok ;
\ The decimal digits of a number, without leading zeros ("0" for 0), at
\ the arena's top; they stay until released like a number. The number is
\ left as it was. A failure gives 0 0, an empty text.
: big>decimal ( big arena -- addr u outcome )
  2dup operand? over arena-valid? and 0= if 2drop 0 0 outcome-invalid exit then
  over @ 0= if nip zero-text else decimal-of then ;

\ ---- The operations ----

\ A number from one cell.
: u>big ( u arena -- big outcome )
  dup arena-valid? if cell-big else 2drop outcome-invalid no-result then ;
\ Lean's Nat operations on numbers a and b, each made at the arena's top
\ (the table in the header gives the semantics).
: big+ ( a b arena -- c outcome ) ['] add-core big-binary ;
: big- ( a b arena -- c outcome ) ['] sub-core big-binary ;
: big* ( a b arena -- c outcome ) ['] mul-core big-binary ;
: big/ ( a b arena -- c outcome ) ['] div-core big-binary ;
: big-mod ( a b arena -- c outcome ) ['] mod-core big-binary ;
: big-gcd ( a b arena -- c outcome ) ['] gcd-core big-binary ;
: big-and ( a b arena -- c outcome ) ['] and-core big-binary ;
: big-or ( a b arena -- c outcome ) ['] or-core big-binary ;
: big-xor ( a b arena -- c outcome ) ['] xor-core big-binary ;
: big-lshift ( a b arena -- c outcome ) ['] lshift-core big-binary ;
: big-rshift ( a b arena -- c outcome ) ['] rshift-core big-binary ;
: big-pow ( a b arena -- c outcome ) ['] pow-core big-binary ;

base !   \ the BASE this file was loaded with
