\ Unit tests of src/lib/texts.fs, tables of short texts and their search,
\ outside the checker, in the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md. Interfaces: the public words
\ and hidden helpers, the header's example, stack effects. Results: an
\ empty table, one text, several lines of texts+, the first hit in table
\ order, x handed to the test unchanged, a test that never answers true,
\ the shortest and longest texts, a text of 0 or 256 characters refused
\ (abort) with nothing laid down, alignment after a table. Loaded under
\ HEX: the module must not depend on BASE. T{ }T checks results and stack
\ depth.
include ../support/tester.fs
hex require ../../src/lib/texts.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T

\ ---- The interface (ADR 0010).
T{ [defined] texts-begin [defined] texts+ [defined] text, [defined] texts-end
   [defined] text-next [defined] texts-find -> true true true true true true }T
T{ [defined] text-room [defined] texts-hit? -> false false }T

\ ---- The header's example.
texts-begin texts+ dup drop swap
texts-end constant stack-words
: starts? ( char c-addr u -- flag ) drop c@ = ;
T{ char s ' starts? stack-words texts-find count s" swap" compare -> 0 }T
T{ char r ' starts? stack-words texts-find -> 0 }T

\ ---- Order and x: the first hit wins; x reaches every call unchanged.
: same? ( c-addr1 c-addr u -- flag ) rot count compare 0= ;
create key-drop 4 c, char d c, char r c, char o c, char p c,
T{ key-drop ' same? stack-words texts-find text-next count s" swap" compare -> 0 }T
texts-begin texts+ ab abc ab
texts+ xyz
texts-end constant repeats
: first-a? ( char c-addr u -- flag ) drop c@ = ;
T{ char a ' first-a? repeats texts-find dup repeats = swap c@ -> true 2 }T
T{ char x ' first-a? repeats texts-find count s" xyz" compare -> 0 }T
variable calls
: never ( x c-addr u -- flag ) 2drop drop 1 calls +! false ;
T{ 0 calls ! 7 ' never repeats texts-find calls @ -> 0 4 }T

\ ---- The empty table and the edges of a text's length.
texts-begin texts-end constant none
T{ 0 calls ! 7 ' never none texts-find calls @ none c@ -> 0 0 0 }T
texts-begin s" q" text, 255 pad c! pad 1+ 255 char z fill pad 1+ 255 text, texts-end
  constant edges
T{ edges count nip edges text-next c@ -> 1 255 }T
T{ edges text-next text-next c@ -> 0 }T
\ Refused lengths abort before laying anything down (the 255 is kept: a
\ table under way, ended below).
: refused? ( c-addr u -- flag )
  here >r ['] text, catch dup if nip nip then 0<> here r> = and ;
T{ pad 0 refused? pad 256 refused? pad 255 refused? -> true true false }T
texts-end
\ The dictionary is aligned after a table.
texts-begin texts+ odd
texts-end constant odd-table
T{ here aligned here = odd-table c@ -> true 3 }T
\ A \ comment ends a line's texts (review reuse-front-a note 8); a text
\ that only starts with \ is a text.
texts-begin texts+ one \ two three
texts+ \x four \
texts-end constant commented
T{ commented count s" one" compare commented text-next count s" \x" compare -> 0 0 }T
T{ commented text-next text-next count s" four" compare -> 0 }T
T{ commented text-next text-next text-next c@ -> 0 }T

T{ depth -> 0 }T
cr .( texts.fs: all tests passed) cr
bye
