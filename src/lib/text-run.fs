\ Tools for running text in a vocabulary of one's own: what a program
\ needs when it hands the lines of a file to Forth's text interpreter (or
\ to a loop of its own over PARSE-NAME) with only its own word lists
\ visible, as cross compilers, assemblers and little languages do. A
\ general tool with no Lean or LeanForth knowledge; Forth-2012 words only.
\
\ - The interpreter's settings: the search order, the compilation word
\   list and BASE, saved into a /run-settings record and restored from it.
\ - A whole file read into a buffer the caller gives, once, as bytes, so
\   that a program runs, and may hash, exactly the bytes it read.
\ - Lines split at LF, and one CR just before an LF dropped.
\ - The plain-text rule: every character printable ASCII, a space or a tab.
\
\ Example: run one line of plain text with only the word list my-words
\ visible and BASE ten, and give the caller's settings back however the
\ line ends (tests/lib/text-run.fs runs it):
\
\   create saved /run-settings allot
\   wordlist constant my-words
\   : run-line ( c-addr u -- code )
\     2dup text-plain-at over <> if 2drop -1 exit then
\     saved run-settings-save 0= if 2drop -2 exit then
\     my-words 1 set-order decimal
\     ['] evaluate catch dup if nip nip then saved run-settings-restore ;
\   s" 1 2" run-line . . .                      \ 0 (no THROW) 2 1
\   : numeral? ( c -- flag ) [char] 0 - 10 u< ;
\   s" ab7c" ' numeral? text-scan .  s" abc" ' numeral? text-any? .
\   \ prints: 0 2 1 2 0
\
\ Interface (lf-lib): /run-settings, run-settings-order-max,
\ run-settings-save, run-settings-restore, text-file-slurp, text-scan,
\ text-any?, text-trim, text-line-end, text-cr-drop, text-plain-at, floats-depth,
\ floats-drop-to.
\ src/program/verify-runner.fs
\ is a complete user. Offsets into a text count characters (/STRING).
\ State: none; every word takes its record or buffer. Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./outcome.fs
require ./module.fs

lf-lib-private module-open
lf-lib set-current
\ The interpreter's settings. Forth-2012 requires room for at least eight
\ word lists in the search order; a record keeps up to sixteen.
16 constant run-settings-order-max

lf-lib-private set-current
begin-structure /run-settings-layout
  field: run-settings-base
  field: run-settings-current
  field: run-settings-order#
  run-settings-order-max cells +field run-settings-order
end-structure
\ Word list i of the saved search order; 0 is the one searched first.
: run-settings-wid ( i settings -- addr ) run-settings-order swap cells + ;
\ Keep the n word lists GET-ORDER gave, the first searched on top.
: run-settings-order! ( widn .. wid1 n settings -- )
  2dup run-settings-order# ! swap 0 ?do tuck i swap run-settings-wid ! loop drop ;
\ The saved search order on the stack, as SET-ORDER takes it.
: run-settings-wid@ ( settings i -- wid settings i ) 2dup swap run-settings-wid @ -rot ;
: run-settings-order@ ( settings -- widn .. wid1 n )
  dup run-settings-order# @ dup >r begin dup while 1- run-settings-wid@ repeat 2drop r> ;
: run-settings-keep ( settings -- )
  >r get-order r@ run-settings-order! base @ r@ run-settings-base !
  get-current r> run-settings-current ! ;
: run-settings-depth ( -- n ) get-order dup >r ndrop r> ;

lf-lib set-current
/run-settings-layout constant /run-settings
\ Save BASE, the compilation word list and the search order, and give
\ true; or, for a search order of more than run-settings-order-max word
\ lists, save nothing and give false.
: run-settings-save ( settings -- flag )
  run-settings-depth run-settings-order-max > if drop false exit then
  run-settings-keep true ;
\ Give back what run-settings-save kept.
: run-settings-restore ( settings -- )
  dup run-settings-order@ set-order dup run-settings-current @ set-current
  run-settings-base @ base ! ;

lf-lib-private set-current
\ Forth-2012's READ-FILE reads all the characters asked for unless the
\ file ends first, so one read fills the buffer or reads the whole file.
: text-file-read ( buf size fileid -- len ior ) read-file dup if nip 0 swap then ;
: text-file-open ( c-addr u -- fileid ior ) r/o bin open-file ;
\ The outcome of a read of len characters into a buffer of size.
: text-file-outcome ( len ior size -- len outcome )
  swap if 2drop 0 outcome-invalid exit then over > if outcome-ok else outcome-full then ;

lf-lib set-current
\ A whole file, read as bytes into the buffer buf of size characters: the
\ characters read and an outcome. ok: the file had fewer than size
\ characters, all read; full: it filled the buffer, so it may be longer,
\ and is refused (give one character more room than the longest file
\ wanted); invalid: it cannot be opened or read (len is then 0). The file
\ is opened as a binary file, so that no host translates its line ends,
\ and is closed again even when the read throws; the exception then
\ passes on.
: text-file-slurp ( c-addr u buf size -- len outcome )
  2swap text-file-open ?dup if 2drop 2drop 0 outcome-invalid exit then
  over >r dup >r ['] text-file-read catch r> close-file drop throw r> text-file-outcome ;

lf-lib-private set-current
\ The rest of c-addr u from its first character for which xt ( char --
\ flag ) is true, empty when there is none.
: text-from ( c-addr u xt -- c-addr' u' )
  >r begin dup while over c@ r@ execute 0= while 1 /string repeat then r> drop ;

lf-lib set-current
\ The offset, in characters, of the first character of c-addr u for which
\ xt ( char -- flag ) is true, or u when there is none. It is u less the
\ length that /STRING leaves, both counted in characters, so it never
\ depends on how many address units a character takes.
: text-scan ( c-addr u xt -- n ) over >r text-from nip r> swap - ;
\ Whether xt ( char -- flag ) is true for any character of c-addr u
\ (false for an empty text); text-any? 0= says it is true for none.
: text-any? ( c-addr u xt -- flag ) text-from nip 0<> ;

lf-lib-private set-current
: text-filled? ( char -- flag ) bl <> ;
lf-lib set-current
\ c-addr u without the spaces at its start and at its end (other
\ characters, tabs included, are kept; empty when it is all spaces).
: text-trim ( c-addr u -- c-addr' u' ) ['] text-filled? text-from -trailing ;

lf-lib-private set-current
10 constant text-lf
13 constant text-cr
9 constant text-tab
: text-lf? ( char -- flag ) text-lf = ;
: text-odd? ( char -- flag ) dup text-tab <> swap bl 127 within 0= and ;

lf-lib set-current
\ Lines. text-line-end gives the length of the first line of c-addr u and
\ whether an LF ends it; when none does, the line is all of the text.
: text-line-end ( c-addr u -- n lf? ) tuck ['] text-lf? text-scan tuck > ;
\ The line without one CR at its end (for a line that an LF ended).
: text-cr-drop ( c-addr u -- c-addr u' )
  dup if 2dup 1- chars + c@ text-cr = if 1- then then ;
\ Plain text: the offset of the first character that is not printable
\ ASCII (! to ~), a space or a tab, or u when every character is. Such
\ text reads the same on every host: no line end inside a line, no
\ control or multi-byte character whose treatment differs.
: text-plain-at ( c-addr u -- n ) ['] text-odd? text-scan ;
\ The floating-point stack a run's text may push numbers on: its depth
\ (0 on a host without one) when the run begins, and its items above
\ that depth dropped after an error (unchecked: n from 0 to the depth).
[defined] fdepth [if]
: floats-depth ( -- n ) fdepth ;
: floats-drop-to ( n -- ) begin fdepth over > while fdrop repeat drop ;
[else]
: floats-depth ( -- n ) 0 ;
: floats-drop-to ( n -- ) drop ;
[then]

module-close
base !   \ the BASE this file was loaded with
