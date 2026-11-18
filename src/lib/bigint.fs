\ Signed big integers with the semantics of Lean 4.35.0's Int (plan step
\ FE1i-4; docs/design/FE1I_AUTOMATION.md, section 5.2), over the natural
\ numbers of src/lib/bignum.fs: for by-omega's coefficients and by-decide's
\ Int literals. A general tool with no Lean code (Lean only in comments);
\ untrusted.
\
\ What each word computes, as the definitions in Init/Data/Int of the 4.35.0
\ toolchain say (Basic.lean, DivMod/Basic.lean, Gcd.lean, Pow.lean). Lean's
\ / and % on Int are Int.ediv and Int.emod (the Div and Mod instances,
\ DivMod/Basic.lean 111-118); there is no Int.div any more (removed in
\ December 2024, lines 36-40). Int.tdiv, Int.fdiv and Int.bdiv are not here.
\
\   Lean            here             result
\   a + b, a - b    bigint+ bigint-  sum, difference
\   a * b           bigint*          product
\   -a              bigint-negate    negation
\   a / b           bigint-ediv      floor(a / b) for b > 0, ceil(a / b) for b < 0;
\                                    a / 0 = 0 (ediv, lines 73-78)
\   a % b           bigint-emod      a - b * (a / b), so 0 <= a % b < |b| for b <> 0;
\                                    a % 0 = a (emod, lines 103-105)
\   Int.bmod x m    bigint-bmod      r = x % m, then r if r < (m + 1) / 2, else r - m;
\                                    m is a natural number; x bmod 0 = x (318-323)
\   Int.gcd a b     bigint-gcd       gcd(|a|, |b|), a natural number (Gcd.lean 43)
\   a ^ e           bigint-pow       a^e for a natural number e; a^0 = 1 (Int.pow)
\   Int.natAbs a    bigint-natAbs    |a|, a natural number
\   Int.toNat a     bigint-toNat     a, or 0 for a < 0, a natural number
\   Int.sign a      bigint-sign      -1, 0 or 1, as a cell
\   compare a b     bigint-compare   -1, 0 or 1 as a < b, a = b, a > b
\   Int.ofNat n     nat>bigint       n
\   toString a      bigint>decimal   decimal digits, with a leading - when a < 0
\
\ Representation. An integer is the address of its sign cell, -1, 0 or 1,
\ followed by its magnitude, a number of bignum.fs (its count of limbs, then
\ the limbs). The sign is 0 exactly for 0, so every integer has one form.
\ bigint-magnitude gives the magnitude in place, a bignum valid as long as
\ the integer. Integers are never changed after they are made. Host memory:
\ never serialized; decimal text is the portable form.
\
\ Arenas, as in bignum.fs: every operation takes a bignum arena (/big-arena,
\ big-arena-init) and makes its result at the arena's top, giving back its
\ scratch; big-mark and big-release give back what was made since a mark.
\ An integer result is built in a /build record claimed at the top: the
\ magnitude is made above it and moved down at the end, so the record's
\ place becomes the integer (its first field is the sign cell). A
\ natural-number result (bigint-gcd, bigint-natAbs, bigint-toNat) takes the
\ record's place the same way. Printing a negative integer leaves its text
\ above a build record, which leaves room for the minus sign.
\
\ Outcomes (src/lib/outcome.fs): ok; invalid for a malformed integer (a sign
\ other than -1, 0 or 1, a malformed magnitude, or a sign that is 0 for a
\ magnitude that is not, or the reverse), a malformed natural number, an
\ operand or text reaching into the arena's free part (released), a
\ corrupted arena record, or text that is not an optional minus sign
\ followed by one or more decimal digits (leading zeros allowed; "-0" is
\ 0); full when the arena has no room or a magnitude would have more bits
\ than the arena's limit (bignum.fs: Lean's 2^30 unless big-limit! sets
\ another; no value on the way is longer than the result or an operand).
\ A failure gives -1 in the result's place (bigint>decimal: 0 0) and
\ leaves the arena's top where it was. The checks are O(1), as
\ bignum.fs's; bigint-compare, bigint-sign, bigint>n and bigint-magnitude
\ trust their argument (bigint-valid? first).
\
\ Example: (-12) / 7 and (-12) % 7, Lean's -2 and 2.
\   create ar /big-arena allot   65536 allocate throw 65536 ar big-arena-init
\   ar big-mark constant start
\   s" -12" ar decimal>bigint drop   s" 7" ar decimal>bigint drop
\   2dup ar bigint-ediv drop ar bigint>decimal drop type space    \ -2
\   ar bigint-emod drop ar bigint>decimal drop type               \ 2
\   start ar big-release drop                  \ prints: -2 2
\
\ Interface: bigint-valid? bigint-sign bigint-magnitude bigint-compare
\ bigint+ bigint- bigint* bigint-negate bigint-ediv bigint-emod bigint-bmod
\ bigint-gcd bigint-pow bigint-natAbs bigint-toNat nat>bigint n>bigint
\ bigint>n decimal>bigint bigint>decimal, in lf-lib; bignum.fs's words for
\ arenas and natural numbers. No host recursion (bignum.fs's own products
\ and powers recurse to a depth logarithmic in the size). State: none of
\ its own (the number 1 its steps use is made in the arena); separate
\ arenas are independent, one arena is single-threaded. Loads in decimal whatever BASE
\ is, and restores it. Requires bignum.fs, bounds.fs, outcome.fs,
\ portability.fs and module.fs.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./bignum.fs
require ./bounds.fs
require ./outcome.fs
require ./portability.fs
require ./module.fs

lf-lib-private module-open

\ ---- Integers ----

\ An integer's magnitude and the address after it.
: int-mag ( i -- big ) cell+ ;
: int-after ( i -- addr ) int-mag big-end ;
: mags ( a b -- ma mb ) int-mag swap int-mag swap ;
: signs ( a b -- sa sb ) @ swap @ swap ;
: negative? ( i -- flag ) @ 0< ;
\ -1, 0 or 1 as n is negative, 0 or positive.
: signum ( n -- s ) dup 0< swap 0> - ;
\ x - 1 and x + 1, with the number 1 made at the top first (it stays as
\ scratch, given back with the build it is made in).
: one-above ( x arena -- x one arena true | -1 outcome false )
  1 over cell-big ok-then? if swap true else nip nip no-result false then ;
: big-1- ( x arena -- y outcome ) one-above if big- then ;
: big-1+ ( x arena -- y outcome ) one-above if big+ then ;
\ Whether a natural number is odd.
: odd? ( big -- flag ) dup @ if big-limbs @ 1 and 0<> else drop false then ;

\ ---- Checks ----

: sign-sound? ( i -- flag ) @ -1 1 between? ;
\ Whether the sign is 0 exactly when the magnitude is.
: zero-agrees? ( i -- flag ) dup @ 0= swap int-mag @ 0= = ;
lf-lib set-current
\ Whether i is a well-formed integer: a sign of -1, 0 or 1, a well-formed
\ magnitude, and the sign 0 exactly for 0. O(1); it trusts the address.
: bigint-valid? ( i -- flag )
  dup sign-sound? over int-mag big-valid? and if zero-agrees? else drop false then ;
lf-lib-private set-current
\ Whether an integer stays clear of the arena's free part, as big-live?.
: int-live? ( i arena -- flag )
  over int-after over arena-top @ u> 0= -rot arena-end @ u< 0= or ;
: int-operand? ( i arena -- flag ) over bigint-valid? if int-live? else 2drop false then ;
\ Whether the arena is sound and a and b live in it, well formed: two
\ integers, or an integer and a natural number m.
: ints? ( a b arena -- flag )
  dup arena-valid? if tuck int-operand? -rot int-operand? and else drop 2drop false then ;
: int-nat? ( a m arena -- flag )
  dup arena-valid? if tuck operand? -rot int-operand? and else drop 2drop false then ;
\ The same for one integer, and for one natural number.
: int? ( i arena -- flag ) dup arena-valid? if int-operand? else 2drop false then ;
: nat? ( big arena -- flag ) dup arena-valid? if operand? else 2drop false then ;
\ The failure of malformed operands, with nothing made.
: refuse ( a b arena -- -1 outcome ) drop 2drop outcome-invalid no-result ;
: refuse-one ( x arena -- -1 outcome ) 2drop outcome-invalid no-result ;

\ ---- Builds ----

\ The record a result is built in, at the arena's top (see the header).
\ a and b are the operands as the operation takes them: integers, an
\ integer and a natural number, a cell, or text.
begin-structure /build
  field: build-sign        \ the result's sign; its sign cell at the end
  field: build-arena
  field: build-a
  field: build-b
end-structure
\ arena-claim counts a number's cells with its count cell.
/build cell / 1- constant build-limbs

: build-fill ( a b build arena -- build )
  over build-arena ! tuck build-b ! tuck build-a ! ;
\ Claim and fill a build at the top of a sound arena: or full.
: build-new ( a b arena -- build outcome )
  dup >r build-limbs swap result-claim if r> build-fill outcome-ok else r> drop then ;
\ Give back the build and everything above it.
: build-drop ( build -- ) dup build-arena @ arena-top ! ;
: given-back ( build outcome -- -1 outcome ) swap build-drop no-result ;
\ Move the number m down to dst and end the build there: the top after it.
\ The arena is read first: the move overwrites the build's fields.
: land ( build m dst -- dst )
  rot build-arena @ >r tuck big-move dup big-end r> arena-top ! ;
\ The sign becomes 0 for a magnitude 0.
: zero-fix ( i -- ) dup int-mag @ 0= if 0 swap ! else drop then ;
\ End the build with m as the integer's magnitude, or as a natural number
\ in the build's place; or, on failure, give back the build.
: int-land ( build m -- i ) over int-mag land cell - dup zero-fix ;
: settle ( build m outcome -- i outcome )
  ok-then? if int-land outcome-ok else given-back then ;
: nat-settle ( build m outcome -- big outcome )
  ok-then? if over land outcome-ok else given-back then ;
\ Run a step xt ( build -- c outcome ) on a build that was made; or pass on
\ the failure to make it.
: build-run ( build outcome xt -- c outcome ) swap ok-then? if execute then ;
\ Builds for two integers, an integer and a natural number, or any two
\ operands in a sound arena; malformed operands are invalid, nothing made.
: ints-build ( a b arena -- build outcome )
  >r 2dup r@ ints? r> swap if build-new else refuse then ;
: int-nat-build ( a m arena -- build outcome )
  >r 2dup r@ int-nat? r> swap if build-new else refuse then ;
: any-build ( a b arena -- build outcome )
  dup arena-valid? if build-new else refuse then ;
\ Run a step xt ( build -- c outcome ) on a build of two integers, or of
\ an integer and a natural number.
: int-binary ( a b arena xt -- c outcome ) >r ints-build r> build-run ;
: int-nat-binary ( a m arena xt -- c outcome ) >r int-nat-build r> build-run ;
\ The operands of a build and its arena: as given, as two magnitudes, or
\ as a magnitude and a natural number.
: build-args ( build -- a b arena ) dup build-arena @ >r dup build-a @ swap build-b @ r> ;
: int-args ( build -- ma mb arena ) build-args >r mags r> ;
: int-nat-args ( build -- mx m arena ) build-args >r swap int-mag swap r> ;
\ Run a magnitude step xt ( x y arena -- m outcome ) on them.
: run-step ( build xt -- m outcome ) >r int-args r> execute ;
: nat-run ( build xt -- m outcome ) >r int-nat-args r> execute ;

\ ---- Signs and magnitude steps ----

: sign! ( s build -- ) build-sign ! ;
: build-signs ( build -- sa sb ) dup build-a @ swap build-b @ signs ;
: a-sign ( build -- sa ) build-a @ @ ;
: b-sign ( build -- sb ) build-b @ @ ;
\ Whether |a| < |b|.
: smaller? ( build -- flag ) int-args drop big-compare 0< ;
\ The sign of a sum whose second term has the sign sb: sb when |a| < |b|,
\ else a's (0 when the terms cancel: zero-fix).
: sum-sign ( sb build -- ) dup smaller? 0= if nip dup a-sign swap then sign! ;
: add-sign ( build -- ) dup b-sign swap sum-sign ;
: sub-sign ( build -- ) dup b-sign negate swap sum-sign ;
: mul-sign ( build -- ) dup build-signs * swap sign! ;
\ a / b has b's sign, the other way for a negative a; a % b is positive,
\ or a's for b = 0, as a % 0 = a.
: ediv-sign ( build -- ) dup build-signs swap 0< if negate then swap sign! ;
: emod-sign ( build -- ) dup build-signs if drop 1 then swap sign! ;
: negate-sign ( build -- ) dup a-sign negate swap sign! ;
: keep-sign ( build -- ) dup a-sign swap sign! ;
: plus-sign ( build -- ) 1 swap sign! ;
\ a^e is negative for a negative a and an odd e (-1 or 1 makes -1).
: pow-sign ( build -- ) dup a-sign 0< over build-b @ odd? and 1 or swap sign! ;

\ The larger magnitude less the smaller.
: diff-mag ( x y arena -- m outcome ) >r 2dup big-compare 0< if swap then r> big- ;
\ A copy of the first, and 0.
: copy-first ( x y arena -- m outcome ) nip big-copy ;
: zero-mag ( x y arena -- m outcome ) nip nip 0 swap cell-big ;
\ ceil(x / y) for x, y >= 1, as (x - 1) / y + 1. Like every step's
\ scratch, the numbers on the way stay above the build until it ends.
: ceil-div ( x y arena -- m outcome )
  >r swap r@ big-1- ok-keep? if
    swap r@ big/ ok-then? if r> big-1+ exit then no-result
  then r> drop ;
\ The emod of -x by y, for x, y >= 1: 0 when y divides x, else y - (x mod y).
: neg-mod ( x y arena -- r outcome )
  >r tuck r@ big-mod ok-then? 0= if nip r> drop no-result exit then
  dup @ if r> big- else nip r> drop outcome-ok then ;

\ Whether a / b rounds away from zero: a negative a and b <> 0.
: away? ( build -- flag ) build-signs 0<> swap 0< and ;
\ Each operation's magnitude step, chosen by the operands' signs.
: add-step ( build -- xt ) build-signs * 0< if ['] diff-mag else ['] big+ then ;
: sub-step ( build -- xt ) build-signs * 0> if ['] diff-mag else ['] big+ then ;
: mul-step ( build -- xt ) drop ['] big* ;
: ediv-step ( build -- xt ) away? if ['] ceil-div else ['] big/ then ;
: emod-step ( build -- xt ) away? if ['] neg-mod else ['] big-mod then ;
: copy-step ( build -- xt ) drop ['] copy-first ;
: tonat-step ( build -- xt ) a-sign 0< if ['] zero-mag else ['] copy-first then ;
\ The emod of an integer x by a natural number m > 0.
: x-mod-step ( build -- xt ) a-sign 0< if ['] neg-mod else ['] big-mod then ;

\ ---- Operations ----

\ A signed operation: set the result's sign with sign-xt ( build -- ), run
\ the magnitude step that step-xt ( build -- xt ) chooses, end the build.
: signed-op ( build sign-xt step-xt -- c outcome )
  >r over swap execute dup dup r> execute run-step settle ;
: add-of ( build -- c outcome ) ['] add-sign ['] add-step signed-op ;
: sub-of ( build -- c outcome ) ['] sub-sign ['] sub-step signed-op ;
: mul-of ( build -- c outcome ) ['] mul-sign ['] mul-step signed-op ;
: ediv-of ( build -- c outcome ) ['] ediv-sign ['] ediv-step signed-op ;
: emod-of ( build -- c outcome ) ['] emod-sign ['] emod-step signed-op ;
: negate-of ( build -- c outcome ) ['] negate-sign ['] copy-step signed-op ;

\ x bmod m for m > 0: with r = x % m and d = m - r, r < (m + 1) / 2 holds
\ exactly when r < d (both say 2r < m); then r, else r - m = -d.
: bmod-pick ( build r d -- m )
  2dup big-compare 0< if drop nip else nip swap -1 swap sign! then ;
: m-less ( build r -- build r d outcome )
  over build-arena @ >r over build-b @ over r> big- ;
: bmod-mag ( build -- m outcome )
  dup dup x-mod-step nat-run ok-then? 0= if nip no-result exit then
  m-less ok-then? if bmod-pick outcome-ok else nip nip no-result then ;
: bmod-reduce ( build -- m outcome ) dup plus-sign bmod-mag ;
: x-copy ( build -- m outcome ) dup keep-sign ['] copy-first nat-run ;
: bmod-of ( build -- c outcome )
  dup dup build-b @ @ if bmod-reduce else x-copy then settle ;
: pow-of ( build -- c outcome ) dup pow-sign dup ['] big-pow nat-run settle ;
\ Natural-number results.
: gcd-of ( build -- g outcome ) dup ['] big-gcd run-step nat-settle ;
: natabs-of ( build -- big outcome ) dup ['] copy-first run-step nat-settle ;
: tonat-of ( build -- big outcome ) dup dup tonat-step run-step nat-settle ;
\ From a natural number, and from a cell n (|n| read unsigned, so that the
\ most negative cell is right too).
: nat-of ( build -- i outcome ) dup plus-sign dup build-args copy-first settle ;
: cell-sign ( build -- ) dup build-a @ signum swap sign! ;
: cell-mag ( n b arena -- m outcome ) nip swap abs swap cell-big ;
: cell-of ( build -- i outcome ) dup cell-sign dup build-args cell-mag settle ;

\ ---- Decimal text ----

\ The sign and digits of a text: -1 and what follows a leading minus sign,
\ else 1 and the whole text.
: minus? ( addr u -- flag ) 1 min s" -" compare 0= ;
: sign-split ( addr u -- addr' u' s ) 2dup minus? if 1 /string -1 else 1 then ;
: int-text? ( addr u -- flag ) sign-split drop digits? ;
\ Whether a text stays clear of the arena's free part, as int-live?: text
\ there (released) would be overwritten by the build before it is read.
: text-live? ( addr u arena -- flag )
  >r chars over + r@ arena-top @ u> 0= swap r> arena-end @ u< 0= or ;
: text? ( addr u arena -- flag ) >r 2dup int-text? -rot r> text-live? and ;
: text-sign ( build -- ) dup build-a @ over build-b @ sign-split nip nip swap sign! ;
: text-mag ( addr u arena -- m outcome ) >r sign-split drop r> decimal>big ;
: text-of ( build -- i outcome ) dup text-sign dup build-args text-mag settle ;
\ The text of a negative integer, made above a build: the minus sign goes
\ just before the magnitude's digits. On failure the build is given back.
: minus ( addr u -- addr' u' ) swap 1 chars - s" -" drop over 1 chars move swap 1+ ;
: no-text ( outcome -- 0 0 outcome ) >r 0 0 r> ;
: digits-of ( build -- addr u outcome )
  dup build-a @ int-mag swap build-arena @ big>decimal ;
: minus-of ( build -- addr u outcome )
  dup digits-of dup ok? if >r minus rot drop r> else >r 2drop build-drop r> no-text then ;
: minus-text ( i arena -- addr u outcome )
  over swap build-new ok-then? if minus-of else no-text then ;

\ ---- Other helpers ----

\ -1 or 1 as different signs sa and sb are in order or not.
: sign-order ( sa sb -- n ) < 2* 1+ ;
\ Whether a magnitude u fits a signed cell with the sign s: u <= max-n, or
\ u - 1 <= max-n for a negative s.
: n-fits? ( u s -- flag ) 0< if 1- then max-n u> 0= ;
: signed ( u s -- n ) 0< if negate then ;

\ ---- The interface ----

lf-lib set-current
\ The sign, -1, 0 or 1, and the magnitude, a bignum valid as long as i.
: bigint-sign ( i -- s ) @ ;
: bigint-magnitude ( i -- big ) int-mag ;
\ -1, 0 or 1 as a is below, equal to or above b. Trusts its arguments.
: bigint-compare ( a b -- n )
  2dup signs 2dup <> if sign-order nip nip exit then drop >r mags big-compare r> * ;
\ Lean's Int operations on integers a and b (the table in the header),
\ each made at the arena's top.
: bigint+ ( a b arena -- c outcome ) ['] add-of int-binary ;
: bigint- ( a b arena -- c outcome ) ['] sub-of int-binary ;
: bigint* ( a b arena -- c outcome ) ['] mul-of int-binary ;
: bigint-ediv ( a b arena -- c outcome ) ['] ediv-of int-binary ;
: bigint-emod ( a b arena -- c outcome ) ['] emod-of int-binary ;
\ x bmod m and a^e take a natural number m or e (a bignum).
: bigint-bmod ( x m arena -- c outcome ) ['] bmod-of int-nat-binary ;
: bigint-pow ( a e arena -- c outcome ) ['] pow-of int-nat-binary ;
\ Natural-number results (bignums): gcd(|a|, |b|), |a|, and a or 0.
: bigint-gcd ( a b arena -- g outcome ) ['] gcd-of int-binary ;
: bigint-negate ( a arena -- c outcome ) over swap ints-build ['] negate-of build-run ;
: bigint-natAbs ( a arena -- big outcome ) over swap ints-build ['] natabs-of build-run ;
: bigint-toNat ( a arena -- big outcome ) over swap ints-build ['] tonat-of build-run ;
\ Conversions: from a natural number (a bignum) or a signed cell; to a
\ signed cell when it fits.
: nat>bigint ( big arena -- i outcome )
  2dup nat? if over swap any-build ['] nat-of build-run else refuse-one then ;
: n>bigint ( n arena -- i outcome ) 0 swap any-build ['] cell-of build-run ;
: bigint>n ( i -- n true | false )
  dup int-mag big>u 0= if drop false exit then
  swap @ 2dup n-fits? if signed true else 2drop false then ;
\ The integer whose decimal text is at addr u: an optional minus sign and
\ one or more digits 0-9; invalid otherwise, or when the text reaches into
\ the arena's free part.
: decimal>bigint ( addr u arena -- i outcome )
  >r 2dup r@ text? r> swap if any-build ['] text-of build-run else refuse then ;
\ The decimal text of an integer, a minus sign first when it is negative,
\ at the arena's top; it stays until released. A failure gives 0 0.
: bigint>decimal ( i arena -- addr u outcome )
  2dup int? 0= if 2drop outcome-invalid no-text exit then
  over negative? if minus-text else swap int-mag swap big>decimal then ;

module-close
base !   \ the BASE this file was loaded with
