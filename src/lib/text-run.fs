\ Tools for running text in a vocabulary of one's own: what a program
\ needs when it hands the lines of a file to Forth's text interpreter (or
\ to a loop of its own over PARSE-NAME) with only its own word lists
\ visible, as cross compilers, assemblers and little languages do. A
\ general tool with no Lean or LeanForth knowledge; Forth-2012 words only.
\
\ - The interpreter's settings: the search order, the compilation word
\   list and BASE, saved into a /run-settings record and restored from it.
\ - A whole file read into a buffer the caller gives, once, as bytes, so
\   that the program runs, and may hash, exactly the bytes it read.
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
\     saved run-settings-save my-words 1 set-order decimal
\     ['] evaluate catch dup if nip nip then saved run-settings-restore ;
\
\ src/program/verify-runner.fs is a complete user. State: none; every
\ word takes its record or buffer. Requires lib.fs (portability,
\ structures).

require ./lib.fs

\ The interpreter's settings. Forth-2012 requires room for at least eight
\ word lists in the search order; a record keeps up to sixteen.
16 constant run-settings-order-max
begin-structure /run-settings
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
\ Save BASE, the compilation word list and the search order. A search
\ order of more than run-settings-order-max word lists aborts.
: run-settings-save ( settings -- )
  >r get-order dup run-settings-order-max > abort" run-settings: search order too long"
  r@ run-settings-order! base @ r@ run-settings-base ! get-current r> run-settings-current ! ;
\ The saved search order on the stack, as SET-ORDER takes it.
: run-settings-wid@ ( settings i -- wid settings i ) 2dup swap run-settings-wid @ -rot ;
: run-settings-order@ ( settings -- widn .. wid1 n )
  dup run-settings-order# @ dup >r begin dup while 1- run-settings-wid@ repeat 2drop r> ;
\ Give back what run-settings-save kept.
: run-settings-restore ( settings -- )
  dup run-settings-order@ set-order dup run-settings-current @ set-current
  run-settings-base @ base ! ;

\ A whole file, read as bytes into the buffer buf of size characters: the
\ characters read, len, and the I/O result, nonzero when the file cannot
\ be opened or read (len is then 0). Forth-2012's READ-FILE reads all the
\ characters asked for unless the file ends first, so one read fills the
\ buffer or reads the whole file: give one character more room than the
\ longest file wanted, and refuse a file that fills the buffer. The file
\ is opened as a binary file, so that no host translates its line ends,
\ and is closed again even when the read throws; the exception then
\ passes on.
: file-read ( buf size fileid -- len ior ) read-file dup if nip 0 swap then ;
: file-slurp ( c-addr u buf size -- len ior )
  2swap r/o bin open-file ?dup if >r drop 2drop 0 r> exit then
  dup >r ['] file-read catch r> close-file drop throw ;

\ The offset of the first character of c-addr u for which xt ( char --
\ flag ) is true, or u when there is none.
: text-scan ( c-addr u xt -- n )
  over >r >r begin dup while over c@ r@ execute 0= while 1 /string repeat then
  nip r> drop r> swap - ;

\ Lines. text-line-end gives the length of the first line of c-addr u and
\ whether an LF ends it; when none does, the line is all of the text.
10 constant text-lf
13 constant text-cr
: text-lf? ( char -- flag ) text-lf = ;
: text-line-end ( c-addr u -- n lf? ) tuck ['] text-lf? text-scan tuck > ;
\ The line without one CR at its end (for a line that an LF ended).
: text-cr-drop ( c-addr u -- c-addr u' )
  dup if 2dup 1- chars + c@ text-cr = if 1- then then ;

\ Plain text: the offset of the first character that is not printable
\ ASCII (! to ~), a space or a tab, or u when every character is. Such
\ text reads the same on every host: no line end inside a line, no
\ control or multi-byte character whose treatment differs.
9 constant text-tab
: text-odd? ( char -- flag ) dup text-tab <> swap bl 127 within 0= and ;
: text-plain-at ( c-addr u -- n ) ['] text-odd? text-scan ;
