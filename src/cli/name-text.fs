\ A declaration's name as display text, for the command line's text and
\ JSON reports (cli/leanforth.fs, cli/check-json.fs): Lean's own
\ Name.toString (Lean 4.35.0, Init/Data/ToString/Name.lean): components
\ joined by dots from the root, numeric ones in decimal, a component that
\ is not an identifier between « and » (an empty one as «»), the
\ anonymous name as [anonymous]. Two changes make the text show exactly
\ what the name holds, so that a crafted name can never start a line or
\ reorder what follows it: in a component that is not an identifier, a
\ backslash shows as \\, every character the run records' text rule bans
\ (C0 and C1 controls, format characters such as bidirectional controls,
\ line and paragraph separators; lib/text-rule.fs) as \u{X}, its code
\ point in hexadecimal, and a byte that does not start UTF-8 as \x{X}.
\ As Lean does, «» is not added to a component that holds », nor to a
\ name with macro scopes, an inaccessible name or pseudo-syntax (_, or a
\ root starting with # or ?); the escapes are made all the same. Names of
\ any depth: the components are gathered in a heap block, from the name up
\ to the root, so there is no fixed limit but the heap's. Untrusted
\ presentation; LeanForth-specific (Lean's names and identifier rules).
\
\ nt-name ( id -- c-addr u flag ) the display text of name id; flag false
\ when the heap had no room for it (the text must then not be shown).
\ nt-text ( c-addr u -- c-addr' u' flag ) any bytes, with the same escapes
\ and no «» (an export's file name). A text stays valid until the next
\ call; nt-free frees the heap blocks.
\ State: two shared slabs, nt-out (the text's bytes) and nt-parts (the
\ name's components), and the flag nt-short: one text at a time, in any
\ context. It reads bytes (c@) to decode UTF-8. Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/bytes.fs
require ../lib/text-rule.fs
require ../core/names.fs

create nt-out /slab allot  nt-out /slab erase
create nt-parts /slab allot  nt-parts /slab erase
variable nt-short   \ true once a byte found no room
: nt-free ( -- ) nt-out slab-free nt-parts slab-free nt-out /slab erase nt-parts /slab erase ;
\ The slabs, made when first used: bytes of the text, component IDs.
: nt-make ( unit slab -- )
  dup slab-live? if 2drop exit then over slab-limit-max swap slab-init drop ;
: nt-start ( -- )
  1 chars nt-out nt-make 1 cells nt-parts nt-make nt-out slab-clear false nt-short ! ;

\ ---- The text being built: bytes added, a refused one marks it short.
: nt-put ( c-addr u -- )
  dup nt-out slab-claim ok? if nt-out slab-at swap move else drop 2drop true nt-short ! then ;
: nt-text@ ( -- c-addr u flag ) 0 nt-out slab-at nt-out slab-count nt-short @ 0= ;
: nt-digits ( u -- ) 0 <# #s #> nt-put ;
: nt-decimal ( u -- ) base @ >r decimal nt-digits r> base ! ;
: nt-hex ( u -- ) base @ >r hex nt-digits r> base ! ;
\ An escape: its prefix, the number in hexadecimal, then }.
: nt-escape ( u c-addr u -- ) nt-put nt-hex s" }" nt-put ;

\ ---- Characters. The first character of a text: its code point and
\ length, or the byte and 0 when it does not start a UTF-8 sequence.
: nt-lead ( byte n -- bits ) dup 1 = if drop exit then $ff swap 1+ rshift and ;
: nt-code ( addr n -- code )
  >r dup c@ r@ nt-lead swap r> 1 ?do dup i + c@ $3f and rot 6 lshift or swap loop drop ;
: nt-char ( c-addr u -- code n )
  over swap utf8-length dup if tuck nt-code swap else drop c@ 0 then ;
\ Ranges ( lo , hi , ) of code points, after their count.
: nt-range ( table k -- lo hi ) 2* 1+ cells + dup @ swap cell+ @ ;
: nt-among? ( code table -- flag )
  dup @ 0 ?do 2dup i nt-range between? if 2drop true unloop exit then loop 2drop false ;
\ Lean's isIdFirst: ASCII letters, _ and isLetterLike (Init/Meta/Defs.lean:
\ Greek but λ, Π and Σ, Coptic, Greek Extended, the letterlike block,
\ Latin-1 letters but × and ÷, Latin Extended-A, mathematical Latin).
create nt-first 14 ,
  $41 , $5a ,  $5f , $5f ,  $61 , $7a ,  $c0 , $d6 ,  $d8 , $f6 ,  $f8 , $17f ,
  $391 , $39f ,  $3a1 , $3a2 ,  $3a4 , $3a9 ,  $3b1 , $3ba ,  $3bc , $3fb ,
  $1f00 , $1ffe ,  $2100 , $214f ,  $1d49c , $1d59f ,
\ isIdRest adds digits, ' ! ? and isSubScriptAlnum.
create nt-rest 7 ,
  $21 , $21 ,  $27 , $27 ,  $30 , $39 ,  $3f , $3f ,  $1d62 , $1d6a ,  $2080 , $209c ,
  $2c7c , $2c7c ,
: nt-first? ( code -- flag ) nt-first nt-among? ;
: nt-rest? ( code -- flag ) dup nt-first? swap nt-rest nt-among? or ;
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
: nt-banned? ( c-addr n -- flag ) tr-rule? 0= ;
: nt-raw ( c-addr u n -- c-addr' u' ) >r over r@ nt-put r> /string ;
: nt-bad-byte ( c-addr u byte -- c-addr' u' ) s" \x{" nt-escape 1 /string ;
: nt-banned ( c-addr u code n -- c-addr' u' ) >r s" \u{" nt-escape r> /string ;
: nt-backslash ( c-addr u -- c-addr' u' ) s" \\" nt-put 1 /string ;
: nt-out-char ( c-addr u -- c-addr' u' )
  2dup nt-char dup 0= if drop nt-bad-byte exit then
  3 pick over nt-banned? if nt-banned exit then
  swap [char] \ = if drop nt-backslash else nt-raw then ;
: nt-escaped ( c-addr u -- ) begin dup while nt-out-char repeat 2drop ;

\ ---- Components. A string one: as it is when an identifier; else
\ escaped, and between « and » when the name is escaped and it holds no ».
: nt-holds? ( c-addr u c-addr2 u2 -- flag ) search nip nip ;
: nt-quoted ( c-addr u -- ) s" «" nt-put nt-escaped s" »" nt-put ;
: nt-str ( c-addr u escape? -- )
  >r 2dup nt-ident? if r> drop nt-put exit then
  2dup s" »" nt-holds? 0= r> and if nt-quoted else nt-escaped then ;
: nt-str? ( id -- flag ) lf-name-tag@ lf-name-tag-str = ;
: nt-component ( id escape? -- )
  over nt-str? if >r lf-name-text r> nt-str else drop lf-name-payload nt-decimal then ;

\ The name's components, from the name up to the root (k = 0 the last);
\ full when the heap has no room for them.
: nt-gather ( id -- outcome )
  nt-parts slab-clear begin dup while
    1 nt-parts slab-claim ok? 0= if 2drop outcome-full exit then
    over swap nt-parts slab-at ! lf-name-prefix@
  repeat drop outcome-ok ;
: nt-count ( -- n ) nt-parts slab-count ;
: nt-part ( k -- id ) nt-parts slab-at @ ;
: nt-root ( -- id ) nt-count 1- nt-part ;

\ Lean's escape switch: off for a name with macro scopes or an
\ inaccessible one (both read the last string component, past numeric
\ ones) and for pseudo-syntax.
: nt-is? ( id c-addr u -- flag )
  rot dup nt-str? if lf-name-text compare 0= else drop 2drop false then ;
: nt-has? ( id c-addr u -- flag )
  rot dup nt-str? if lf-name-text 2swap nt-holds? else drop 2drop false then ;
: nt-last-str ( -- id ) nt-count 0 ?do i nt-part dup nt-str? if unloop exit then drop loop 0 ;
: nt-inaccessible? ( -- flag ) nt-last-str dup s" ✝" nt-has? swap s" _inaccessible" nt-is? or ;
: nt-macro? ( -- flag ) nt-last-str s" _hyg" nt-is? ;
: nt-root-starts? ( c-addr u -- flag )
  nt-root dup nt-str? if lf-name-text 2over nip min compare 0= else drop 2drop false then ;
: nt-pseudo? ( -- flag )
  nt-count 1 = nt-root s" _" nt-is? and s" #" nt-root-starts? or s" ?" nt-root-starts? or ;
: nt-escape? ( -- flag ) nt-inaccessible? nt-macro? or nt-pseudo? or 0= ;

\ Root first, joined by dots.
: nt-components ( escape? -- )
  nt-count begin 1- dup 0< 0= while
    dup nt-count 1- <> if s" ." nt-put then dup nt-part 2 pick nt-component
  repeat 2drop ;
: nt-name ( id -- c-addr u flag )
  nt-start ?dup 0= if s" [anonymous]" true exit then
  nt-gather ok? 0= if nt-text@ drop false exit then nt-escape? nt-components nt-text@ ;
: nt-text ( c-addr u -- c-addr' u' flag ) nt-start nt-escaped nt-text@ ;

base !   \ the BASE this file was loaded with
