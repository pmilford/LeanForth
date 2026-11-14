\ A declaration's name as display text, for the command line's text and
\ JSON reports (cli/leanforth.fs, cli/check-json.fs): Lean's own
\ Name.toString (Lean 4.35.0, Init/Data/ToString/Name.lean), its
\ components joined by dots from the root, numeric ones in decimal, a
\ component that is not an identifier between « and » (an empty one as
\ «»), the anonymous name as [anonymous]; names of any depth. Three
\ differences make the text show exactly what the name holds, so that no
\ name can start a line of its own, look like the start of another line
\ or reorder what follows it:
\ 1. a component that is not an identifier is always between « and »:
\    Lean leaves out « » for a component that holds », and for a whole
\    name with macro scopes (x._@._hyg), an inaccessible one (holding ✝)
\    or pseudo-syntax (_, or a root that starts with # or ?), so spaces
\    and colons would pass through and a line could begin with
\    "fake: accepted"; here x._@._hyg shows as x.«_@»._hyg;
\ 2. inside « », every character the run records' text rule bans (C0 and
\    C1 controls, format characters such as bidirectional controls, line
\    and paragraph separators; lib/text-rule.fs's tr-banned?) and » itself
\    show as \u{X}, the code point in hexadecimal, so the component ends
\    at the first »; a byte that does not start UTF-8 as \x{X};
\ 3. a backslash shows as \\, so that the text of an escape in a name is
\    never read as an escape.
\ An identifier is as Lean's isIdFirst and isIdRest have it
\ (Init/Meta/Defs.lean). The components are gathered in a heap block,
\ from the name up to the root, so there is no fixed limit but the heap's.
\ Untrusted presentation; LeanForth-specific (Lean's names and identifier
\ rules).
\
\ nt-name ( id -- c-addr u flag ) the display text of name id; flag false
\ when the heap had no room for it (the text must then not be shown).
\ nt-text ( c-addr u -- c-addr' u' flag ) any bytes with the escapes of 2
\ and 3, without « » (an export's file name). A text stays valid until the
\ next call. nt-free frees the heap blocks; the command line does not
\ call it: one process runs one command, the blocks are as large as the
\ longest name shown, and the host takes them back when the process
\ leaves. A Forth session that wants the memory back calls it; the next
\ call makes them again.
\ State: one shared record, nt-state (/nt): two slabs, the text's bytes
\ and the name's components, and whether a byte found no room. One text at
\ a time, in any context. It reads bytes (c@) to decode UTF-8. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/bytes.fs
require ../lib/decimal.fs
require ../lib/text-rule.fs
require ../core/names.fs

begin-structure /nt
  /slab +field nts-text      \ the text's bytes
  /slab +field nts-parts     \ the name's component IDs, from the name to the root
  field: nts-short           \ true once a byte found no room
end-structure
create nt-state /nt allot  nt-state /nt erase
: nt-out ( -- slab ) nt-state nts-text ;
: nt-parts ( -- slab ) nt-state nts-parts ;
: nt-short ( -- addr ) nt-state nts-short ;
\ The slabs, made when first used, freed by nt-free.
: nt-make ( unit slab -- )
  dup slab-live? if 2drop exit then over slab-limit-max swap slab-init drop ;
: nt-unmade ( slab -- ) dup slab-free /slab erase ;
: nt-free ( -- ) nt-out nt-unmade nt-parts nt-unmade ;
: nt-start ( -- )
  1 chars nt-out nt-make 1 cells nt-parts nt-make nt-out slab-clear false nt-short ! ;

\ ---- The text being built: bytes added, a refused one marks it short.
: nt-put ( c-addr u -- )
  dup nt-out slab-claim ok? if nt-out slab-at swap move exit then
  drop 2drop true nt-short ! ;
: nt-text@ ( -- c-addr u flag ) 0 nt-out slab-at nt-out slab-count nt-short @ 0= ;
: nt-digits ( u -- ) 0 <# #s #> nt-put ;
: nt-decimal ( u -- ) u>decimal nt-put ;
: nt-hex ( u -- ) base @ >r hex nt-digits r> base ! ;
\ An escape: its prefix, the number in hexadecimal, then }.
: nt-escape ( u c-addr u -- ) nt-put nt-hex s" }" nt-put ;

\ ---- Characters. The first character of a text: its code point and
\ length, or the byte and 0 when it does not start a UTF-8 sequence.
: nt-char ( c-addr u -- code n )
  over swap utf8-length ?dup if tuck utf8-decode swap else c@ 0 then ;
\ Ranges ( lo , hi , ) of code points. Lean's isIdFirst: ASCII letters,
\ _ and isLetterLike (Greek but λ, Π and Σ, Coptic, Greek Extended, the
\ letterlike block, Latin-1 letters but × and ÷, Latin Extended-A,
\ mathematical Latin).
create nt-first
  $41 , $5a ,  $5f , $5f ,  $61 , $7a ,  $c0 , $d6 ,  $d8 , $f6 ,  $f8 , $17f ,
  $391 , $39f ,  $3a1 , $3a2 ,  $3a4 , $3a9 ,  $3b1 , $3ba ,  $3bc , $3fb ,
  $1f00 , $1ffe ,  $2100 , $214f ,  $1d49c , $1d59f ,
here nt-first - 2 cells / constant nt-first#
\ isIdRest adds digits, ' ! ? and isSubScriptAlnum: subscript digits
\ ₀-₉, letters ₐ-ₜ and ᵢ-ᵪ, and ⱼ (not the subscript signs ₊ ₋ ₌ ₍ ₎).
create nt-rest
  $21 , $21 ,  $27 , $27 ,  $30 , $39 ,  $3f , $3f ,
  $2080 , $2089 ,  $2090 , $209c ,  $1d62 , $1d6a ,  $2c7c , $2c7c ,
here nt-rest - 2 cells / constant nt-rest#
: nt-first? ( code -- flag ) nt-first nt-first# in-ranges? ;
: nt-rest? ( code -- flag )
  dup nt-first? if drop true else nt-rest nt-rest# in-ranges? then ;
\ Whether every character of c-addr u is valid UTF-8 and satisfies xt
\ ( code -- flag ).
: nt-all? ( c-addr u xt -- flag )
  >r begin dup while
    2dup nt-char dup 0= if 2drop 2drop r> drop false exit then
    swap r@ execute 0= if drop 2drop r> drop false exit then /string
  repeat 2drop r> drop true ;
\ An identifier: not empty, its first character isIdFirst, the rest isIdRest.
: nt-ident? ( c-addr u -- flag )
  dup 0= if 2drop false exit then 2dup nt-char dup 0= if 2drop 2drop false exit then
  >r nt-first? 0= if r> drop 2drop false exit then r> /string ['] nt-rest? nt-all? ;

\ ---- Escaped text, one character at a time (see the header).
: nt-escaped? ( code -- flag ) dup tr-banned? swap $bb = or ;
\ The character code, n bytes at the start of c-addr u: escaped, a
\ backslash doubled, or as it is; then the rest.
: nt-shown ( c-addr u code n -- c-addr' u' )
  >r dup nt-escaped? if s" \u{" nt-escape r> /string exit then
  [char] \ = if s" \\" nt-put else over r@ nt-put then r> /string ;
: nt-out-char ( c-addr u -- c-addr' u' )
  2dup nt-char ?dup if nt-shown else s" \x{" nt-escape 1 /string then ;
: nt-escaped ( c-addr u -- ) begin dup while nt-out-char repeat 2drop ;

\ ---- Components: a string one as it is when an identifier, else escaped
\ between « and »; a numeric one in decimal.
: nt-quoted ( c-addr u -- ) s" «" nt-put nt-escaped s" »" nt-put ;
: nt-str ( c-addr u -- ) 2dup nt-ident? if nt-put else nt-quoted then ;
: nt-str? ( id -- flag ) lf-name-tag@ lf-name-tag-str = ;
: nt-component ( id -- )
  dup nt-str? if lf-name-text nt-str else lf-name-payload nt-decimal then ;

\ The name's components, from the name up to the root (k = 0 the last);
\ full when the heap has no room for them.
: nt-gather ( id -- outcome )
  nt-parts slab-clear begin dup while
    dup nt-parts slab-push ok? 0= if drop outcome-full exit then lf-name-prefix@
  repeat drop outcome-ok ;
: nt-count ( -- n ) nt-parts slab-count ;
: nt-part ( k -- id ) nt-parts slab-at @ ;
\ Root first, joined by dots.
: nt-dot ( k -- ) nt-count 1- <> if s" ." nt-put then ;
: nt-components ( -- ) 0 nt-count 1- do i nt-dot i nt-part nt-component -1 +loop ;
: nt-name ( id -- c-addr u flag )
  nt-start ?dup 0= if s" [anonymous]" true exit then
  nt-gather ok? 0= if nt-text@ drop false exit then nt-components nt-text@ ;
: nt-text ( c-addr u -- c-addr' u' flag ) nt-start nt-escaped nt-text@ ;

base !   \ the BASE this file was loaded with
