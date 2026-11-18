\ Tables of short texts laid down in the dictionary, and a search of one by
\ a caller's test (review F10 of 2026-11-18, s2-finish L1: the OR chains
\ of name comparisons in the front end). A general tool with no Lean
\ knowledge; untrusted.
\
\ A table is a run of counted texts (a count byte of 1 .. 255, then the
\ characters) ended by a zero count. texts-begin ( -- table ) starts one
\ at the aligned dictionary pointer; texts+ ( "text ..." -- ) lays down
\ every blank-separated text on the rest of the input line, up to a \
\ comment (a text that is \ alone ends the line's texts); text,
\ ( c-addr u -- ) lays down one (a length outside 1 .. 255 aborts, before
\ anything is laid down); texts-end ( -- ) ends the table and aligns.
\ Keep the table's address as a constant; a table is read-only once made,
\ so tasks may search one at once.
\
\ texts-find ( x xt table -- entry | 0 ) runs xt ( x c-addr u -- flag ) on
\ x and each text in order and gives the first entry (its counted text)
\ for which it answers true, else 0. text-next ( entry -- entry' ) steps
\ to the next entry (a zero count: the end). Cost: one call of xt per text
\ up to the first hit, a linear search meant for tables of tens of texts;
\ no memory beyond the table's bytes (one per text and per character, one
\ for the end, then alignment).
\
\ Example: which of three words starts with a given character?
\   texts-begin texts+ dup drop swap
\   texts-end constant stack-words
\   : starts? ( char c-addr u -- flag ) drop c@ = ;
\   char s ' starts? stack-words texts-find count type space
\   char r ' starts? stack-words texts-find .   \ prints: swap 0
\
\ Interface: texts-begin texts+ text, texts-end text-next texts-find.
\ State: none of its own; a table is dictionary space laid down while
\ loading. Requires portability.fs and module.fs; helpers are private in
\ lf-lib-private (ADR 0010). Loads in decimal whatever BASE is.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./module.fs

lf-lib-private module-open

: text-room ( u -- u ) dup 1 256 within 0= abort" text,: a text of 1 .. 255 characters" ;
: texts-hit? ( x xt entry -- x xt entry flag ) >r 2dup r@ count rot execute r> swap ;
\ The next text of the line; none (0 0) at its end or at a \ comment,
\ whose rest of the line is skipped.
: texts-comment? ( c-addr u -- flag ) s" \" compare 0= ;
: texts-word ( "text" -- c-addr u )
  parse-name 2dup texts-comment? if 2drop source nip >in ! 0 0 then ;

lf-lib set-current
: texts-begin ( -- table ) align here ;
: text, ( c-addr u -- ) text-room dup c, here swap chars dup allot move ;
\ Lay down every text on the rest of the line, up to a \ comment.
: texts+ ( "text ..." -- ) begin texts-word dup while text, repeat 2drop ;
: texts-end ( -- ) 0 c, align ;
: text-next ( entry -- entry' ) count chars + ;
: texts-find ( x xt table -- entry | 0 )
  begin dup c@ while texts-hit? if nip nip exit then text-next repeat
  2drop drop 0 ;

module-close
base !   \ the BASE this file was loaded with
