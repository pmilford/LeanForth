\ Unit tests of src/lib/decimal.fs, numbers as decimal text and decimal
\ text as numbers, outside the checker, in the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md. Interfaces: the public words
\ and hidden helpers, the header's example, stack effects and the return
\ stack. Results: zero, one digit, the largest and the most negative
\ cells, double cells, under BASEs 2, 10 and 16. Errors and state: BASE
\ restored after a word that throws, the THROW passed on with its code;
\ digits too large for a cell refused, at the width of max-n and one past.
\ Loaded under HEX: the module must not depend on BASE and must restore
\ it. T{ }T checks results and data-stack depth.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/decimal.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T

\ ---- The interface (ADR 0010): the public words are found, the helpers
\ are not, until the test opens the private word list.
T{ [defined] in-decimal [defined] u>decimal [defined] n>decimal [defined] ud>decimal
   [defined] d>decimal [defined] digits>u -> true true true true true true }T
T{ [defined] decimal>u [defined] cell-digits -> true true }T
T{ [defined] ud>text [defined] d>text [defined] decimal-width [defined] digit+
   -> false false false false }T

\ ---- Text: the digits, a minus sign for a negative signed number, the
\ same whatever BASE is, and BASE left as it was.
: text= ( c-addr1 u1 c-addr2 u2 -- flag ) compare 0= ;
T{ 0 u>decimal s" 0" text= 7 u>decimal s" 7" text= 255 u>decimal s" 255" text= -> true true true }T
T{ hex ff u>decimal decimal s" 255" text= 2 base ! 101 u>decimal decimal s" 5" text= -> true true }T
T{ hex base @ 10 u>decimal 2drop base @ decimal -> 16 16 }T
T{ 0 n>decimal s" 0" text= -1 n>decimal s" -1" text= -123 n>decimal s" -123" text= -> true true true }T
T{ hex -10 n>decimal decimal s" -16" text= -> true }T
\ The largest and the most negative cells, against the host's own words.
: host-u ( u -- c-addr u ) 0 <# #s #> ;
create kept 64 allot
: keep ( c-addr u -- c-addr' u ) tuck kept swap move kept swap ;
T{ max-n u>decimal keep max-n host-u text= -1 u>decimal keep -1 host-u text= -> true true }T
T{ max-n n>decimal keep max-n host-u text= -> true }T
create kept2 64 allot
: min-n-digits ( -- c-addr u ) max-n 1+ host-u tuck kept2 swap move kept2 swap ;
T{ max-n 1+ n>decimal drop c@ char - = -> true }T
T{ max-n 1+ n>decimal 1 /string keep min-n-digits text= -> true }T
\ Double cells: ud as unsigned, d signed.
T{ 0 1 ud>decimal keep -1 0 1 0 d+ ud>decimal text= -> true }T
T{ 0 0 ud>decimal s" 0" text= -1 -1 d>decimal s" -1" text= 5 0 d>decimal s" 5" text= -> true true true }T
T{ -1 -1 ud>decimal nip cell-digits > -> true }T
T{ 7 ' u>decimal rs-checked s" 7" text= -5 ' n>decimal rs-checked s" -5" text= -> true true }T

\ ---- in-decimal: the word runs with BASE decimal, its results kept,
\ BASE given back; a THROW comes out with its code, BASE given back too.
: base-seen ( -- n ) base @ ;
T{ hex ' base-seen in-decimal base @ decimal -> 10 16 }T
: sum3 ( a b c -- n ) + + ;
T{ 1 2 3 ' sum3 in-decimal 4 5 ' + ' in-decimal rs-checked -> 6 9 }T
: thrower ( -- ) base @ 10 <> abort" not decimal" -77 throw ;
T{ hex ' thrower ' in-decimal catch nip base @ decimal -> -77 16 }T
T{ 2 base ! ' thrower ' in-decimal catch nip base @ decimal -> -77 2 }T
\ A reader of numbers: >NUMBER in decimal whatever BASE is.
T{ hex 0 0 s" 123x" ' >number in-decimal decimal nip -> 123 0 1 }T

\ ---- .decimal prints n>decimal's text, no space after it.
create printed 64 allot  variable printed#
: catch-type ( c-addr u -- ) tuck printed printed# @ + swap move printed# +! ;
: printing ( n -- c-addr u )
  0 printed# !  action-of type >r ['] catch-type is type .decimal r> is type printed printed# @ ;
T{ hex -1f printing decimal s" -31" text= 0 printing s" 0" text= -> true true }T

\ ---- decimal>number: >NUMBER from zero in decimal, whatever BASE is;
\ decimal-digits?: nonempty, decimal digits only.
T{ s" 123" decimal>number nip -> 123 0 0 }T
T{ hex s" 19af" decimal>number decimal 2 = swap c@ char a = -> 19 0 true true }T
T{ 2 base ! s" 99" decimal>number decimal nip -> 99 0 0 }T
T{ s" " decimal>number nip s" x1" decimal>number nip -> 0 0 0 0 0 2 }T
T{ s" 0" decimal-digits? s" 0123456789" decimal-digits? s" 007" decimal-digits? -> true true true }T
T{ s" " decimal-digits? s" 12a" decimal-digits? s" -1" decimal-digits? s" 1 " decimal-digits?
   -> false false false false }T
T{ hex s" ab" decimal-digits? s" 12" decimal-digits? decimal -> false true }T
T{ s" 42" ' decimal-digits? rs-checked s" 4x" ' decimal>number rs-checked nip -> true 4 0 1 }T

\ ---- digits>u: the fast loop, the double-cell path at the width of
\ max-n, and overflow (moved from tests/lib/json.fs with the words).
create text-buffer 64 allot
: max-n-text ( -- c-addr u ) max-n 0 <# #s #> ;
T{ s" 0" digits>u s" 42" digits>u -> 0 true 42 true }T
T{ max-n-text digits>u -> max-n true }T
T{ max-n-text drop cell-digits 1- digits>u nip -> true }T
: past-max-n ( -- c-addr u ) max-n-text text-buffer swap move text-buffer cell-digits
  2dup + 1- dup c@ 1+ swap c! ;
T{ past-max-n digits>u -> false }T
T{ s" 123456789012345678901234567890" digits>u -> false }T
T{ cell-digits max-n-text nip = -> true }T
\ Nothing depends on BASE: digits are decimal on every path.
T{ max-n-text 2 base ! digits>u decimal -> max-n true }T
T{ max-n-text hex digits>u decimal -> max-n true }T
T{ past-max-n hex digits>u decimal -> false }T
T{ s" 1000" 2 base ! decimal>u decimal -> 1000 }T
\ digit+ (private) at the edge of a cell.
lf-lib-private order+
T{ max-n 10 / max-n 10 mod char 0 + digit+ -> max-n true }T
T{ max-n 10 / max-n 10 mod char 1 + digit+ -> false }T
T{ 0 char 7 digit+ -> 7 true }T

\ The header's example.
T{ hex ff u>decimal s" 255" text= -10 n>decimal s" -16" text= decimal -> true true }T
T{ s" 1234" digits>u s" 99999999999999999999999" digits>u -> 1234 true false }T
: dot-text ( n -- c-addr u ) 0 <# #s #> ;
T{ hex 100 ' dot-text in-decimal decimal s" 256" text= base @ -> true 10 }T
bye
