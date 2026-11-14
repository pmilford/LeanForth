\ The authoring runner (ADR 0017 §2, plan task 8.1.2): runs LeanForth text
\ through Forth's own text interpreter, one line at a time (EVALUATE),
\ with only LeanForth's wordlists in the search order and BASE decimal,
\ counting lines so that every node and every error has a position. The
\ caller's search order, compilation wordlist and BASE are restored
\ afterwards. The run is the authoring program's top level (ADR 0018): it
\ catches every THROW, records the first error (errors.fs) and gives its
\ outcome: ok, invalid (a mistake in the text), unsupported (a form the
\ term store cannot hold yet) or full (a store ran out of room). The only
\ numbers are plain decimals (source.fs): every other token Forth's
\ interpreter converts as a number is refused at its token, by the next
\ LeanForth word or at the end of its line (groups.fs); on Gforth 1.0 the
\ interpreter recognizes only words and plain decimals while a proof runs.
\ A token that is no LeanForth word and no number never reaches a word:
\ Forth's interpreter throws -13, and the runner reports the first token
\ after the last one a word read that is no plain decimal. So every host
\ refuses the same tokens with the same error at the same place. After an
\ error the run is over: begin a new one.
\
\ The rules for running in the checker's own Gforth (ADR 0017 Amendment 1,
\ A5; plan task 8.2.1a): a run starts only while Forth interprets, and
\ every line must end with Forth still interpreting (error 45); a line may
\ hold no control or format character, separator or bytes that are not
\ UTF-8, TAB aside (error 46, at the character's column, before anything
\ of the line runs); a Forth exception names the last token a word read,
\ or the line's first token; each text's lines count from 1. groups.fs
\ adds two: group words are made only with a dictionary reserve left, and
\ by an EVALUATE that sees only lfa-group:.
\
\ Untrusted: the words build terms, which only the checker can accept.
\ Since plan task 8.2.1c the command line loads this module in the
\ checker's Gforth (cli/check-lf.fs: leanforth check FILE.lf), which
\ hands the declarations a run made to the kernel through export.fs; the
\ kernel itself never loads it (tests/author/check_author.py checks that
\ src/core and src/kernel never require src/author). With a library
\ (library.fs) each line is looked ahead before it runs (see below).
\ State: one context record, lfa-run; the modules below have their own.
\
\ Public words:
\   lf-author-begin ( -- )                 a new run: empty stores and tables
\   lf-author-text ( c-addr u -- outcome )  run lines of text (LF or CR LF)
\   lf-author-file ( c-addr u -- outcome )  run the file named c-addr u
\   lf-author-count ( -- n )                declarations made so far
\   lf-author-decl ( i -- decl )            declaration i (print-forth.fs's /lf-fdecl)
\   lf-author-notes ( i -- first end )      the note-table indices of its notes
\   lf-author-print ( fuel -- outcome )     every declaration as words, through
\                                           the printer's sink (lf-print-setup)
\   lf-author-error. ( -- )  lf-author-code ( -- code )  (errors.fs)

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/text-run.fs
require ./words.fs
require ./export.fs

1024 constant lfa-line-capacity

begin-structure /lfa-run
  field: lfa-run-rest        \ text not yet run: address
  field: lfa-run-rest#       \ and length
  field: lfa-run-file        \ the file being run, or 0
  field: lfa-run-floats      \ floating-point stack depth when the line began
  field: lfa-run-base        \ the caller's BASE
  field: lfa-run-current     \ the caller's compilation wordlist
  field: lfa-run-recognizer  \ the host's recognizer (Gforth 1.0)
  field: lfa-run-order#      \ the caller's search order
  lfa-order-capacity cells +field lfa-run-order
  lfa-line-capacity +field lfa-run-line
end-structure
/lfa-run context-record: lfa-run

\ The host's recognizer. Gforth 1.0's interpreter recognizes more than
\ words and numbers ("x" strings, ->x and 'x forms, ${NAME} ...), and
\ some of those act at once; while a proof runs it recognizes only a word
\ of the search order or a string of digits. Hosts without recognizers
\ (Gforth 0.7.3, Forth-2012) convert numbers in more forms. On every host
\ the words then refuse each number that is no plain decimal (groups.fs).
[defined] rec-forth [if]
: lfa-decimal ( c-addr u -- translation )
  2dup dup 0<> -rot lfa-digits? and if rec-number else 2drop translate-none then ;
: lfa-recognize ( c-addr u -- translation )
  2dup rec-name dup translate-none = if drop lfa-decimal else 2swap 2drop then ;
: lfa-recognizer! ( -- )
  action-of rec-forth lfa-run lfa-run-recognizer ! ['] lfa-recognize is rec-forth ;
: lfa-recognizer-back ( -- ) lfa-run lfa-run-recognizer @ is rec-forth ;
[else]
: lfa-recognizer! ( -- ) ;
: lfa-recognizer-back ( -- ) ;
[then]

\ The caller's settings.
: lfa-saved-wid ( i -- addr ) cells lfa-run lfa-run-order + ;
: lfa-save ( -- )
  base @ lfa-run lfa-run-base ! get-current lfa-run lfa-run-current !
  get-order dup lfa-run lfa-run-order# ! 0 ?do i lfa-saved-wid ! loop lfa-recognizer! ;
: lfa-restore ( -- )
  lfa-recognizer-back
  lfa-run lfa-run-order# @ dup 0 ?do dup 1- i - lfa-saved-wid @ swap loop set-order
  lfa-run lfa-run-current @ set-current lfa-run lfa-run-base @ base ! ;

\ Floating-point numbers, on hosts whose interpreter reads them: dropped
\ after an error (a float token is refused like any number form).
\ (lib/text-run.fs's floats-depth and floats-drop-to, also on a host
\ without floating point).
: lfa-floats! ( -- ) floats-depth lfa-run lfa-run-floats ! ;
: lfa-floats-clear ( -- ) lfa-run lfa-run-floats @ floats-drop-to ;

\ Lines of text, split at LF; a CR before it is dropped.
: lfa-eol ( c-addr u -- n )
  dup >r 0 ?do dup i chars + c@ 10 = if drop i unloop r> drop exit then loop drop r> ;
: lfa-strip-cr ( c-addr u -- c-addr u' ) dup if 2dup + 1- c@ 13 = if 1- then then ;
: lfa-rest ( -- c-addr u ) lfa-run dup lfa-run-rest @ swap lfa-run-rest# @ ;
: lfa-rest! ( c-addr u -- ) lfa-run tuck lfa-run-rest# ! lfa-run-rest ! ;
: lfa-text-line ( -- c-addr u true | false )
  lfa-rest dup 0= if 2drop false exit then
  2dup lfa-eol >r over r@ lfa-strip-cr 2swap r> 1+ over min /string lfa-rest! true ;
\ Lines of a file, of fewer than lfa-line-capacity characters; a longer
\ one stops the run at its first token.
: lfa-buffer ( -- c-addr ) lfa-run lfa-run-line ;
: lfa-long ( c-addr u -- )
  lfa-line! lfa-the-line lfa-next-token lfa-token! 2drop lfa-e-line lfa-fail ;
: lfa-file-line ( -- c-addr u true | false )
  lfa-buffer lfa-line-capacity lfa-run lfa-run-file @ read-line 0= lfa-e-file lfa-must
  0= if drop false exit then lfa-buffer swap dup lfa-line-capacity < if true exit then
  lfa-long ;
: lfa-next-line? ( -- c-addr u true | false )
  lfa-run lfa-run-file @ if lfa-file-line else lfa-text-line then ;

\ Forth must be interpreting (ADR 0017 Amendment 1, A5 row 5): a run
\ started while it compiles, from an immediate word, would compile the
\ LeanForth words into the caller's definition instead of running them.
\ No LeanForth word changes STATE; it is checked after every line too.
: lfa-interpreting? ( -- flag ) state @ 0= ;
\ A line holds no character a line may not hold (source.fs); the error
\ points at the character's column, with no token shown, since the
\ character itself may be invisible or reorder the text around it.
: lfa-line-chars ( -- )
  lfa-the-line lfa-bad-offset dup 0< if drop exit then
  0 0 rot lfa-line swap 1+ lfa-pos lfa-e-character lfa-fail-at ;

\ The look-ahead (ADR 0017 Amendment 1, A4, the portable path; plan task
\ 8.2.1d): with a library (library.fs), before a line runs, each of its
\ tokens up to a \ comment, outside ( comments and notes, that no wordlist
\ of the run has and that is not number-like gets a group word in
\ LF-CONST, which when it runs resolves
\ the name as Lean does, the library's constants included. It decides
\ nothing: a token that names no constant stops there as unknown (error
\ 1), and the line's numbers are still checked as the words read it. The
\ current token is left as the line began.
: lfa-has-word? ( c-addr u wid -- flag ) search-wordlist dup if nip then 0<> ;
: lfa-worded? ( c-addr u -- flag )
  2dup lf-words lfa-has-word? if 2drop true exit then
  2dup lf-locals lfa-has-word? if 2drop true exit then lf-consts lfa-has-word? ;
: lfa-ahead? ( c-addr u -- flag )
  2dup lfa-number-like? if 2drop false else lfa-worded? 0= then ;
\ The token an error of the look-ahead points at; the line counts as read
\ only as far as before, so its numbers are still checked.
: lfa-token-at ( c-addr u -- )
  lfa-source lfa-source-length ! lfa-source lfa-source-text @ - 1+ lfa-source
  lfa-source-column ! ;
: lfa-group-ahead ( c-addr u -- )
  2dup lfa-ahead? if 2dup lfa-token-at lf-consts lfa-group drop else 2drop then ;
\ The text a parsing word reads is no token (review M1): \ ends the line's
\ tokens, ( skips to its ), note" and ai-note" to their " (words.fs).
: lfa-token= ( c-addr u c-addr2 u2 -- flag ) compare 0= ;
: lfa-comment? ( c-addr u -- flag ) s" \" lfa-token= ;
: lfa-quote? ( c-addr u -- flag )
  2dup s\" note\"" lfa-token= if 2drop true exit then s\" ai-note\"" lfa-token= ;
: lfa-closer ( c-addr u -- char|0 )
  2dup lfa-quote? if 2drop [char] " exit then s" (" lfa-token= [char] ) and ;
: lfa-past ( c-addr u char -- c-addr' u' ) byte-scan dup if 1 /string then ;
: lfa-read-text ( c-addr u token-addr token-u -- c-addr' u' )
  lfa-closer ?dup if lfa-past then ;
: lfa-look-ahead ( c-addr u -- )
  begin lfa-next-token dup while 2dup lfa-comment? if 2drop 2drop exit then
    2dup lfa-group-ahead lfa-read-text repeat 2drop 2drop ;
: lfa-ahead ( c-addr u -- )
  lfa-library-on? if lfa-look-ahead 1 lfa-source lfa-source-column !
    0 lfa-source lfa-source-length ! else 2drop then ;

\ Running: each line with LeanForth's order, its last numbers checked; at
\ the end, no declaration may be open and no value left.
: lfa-line-end ( -- )
  lfa-interpreting? lfa-e-compiling lfa-must lfa-the-line nip lfa-read-to ;
: lfa-eval-line ( c-addr u -- )
  2dup lfa-line! lfa-line-chars lfa-order! 2dup lfa-ahead lfa-floats! evaluate
  lfa-line-end ;
: lfa-ended ( -- ) depth lfa-floor = lfa-inside? 0= and lfa-e-unfinished lfa-must ;
: lfa-lines ( -- ) begin lfa-next-line? while lfa-eval-line repeat lfa-ended ;

\ After a THROW: Forth's -13 for a token no word has and no plain
\ decimal (the first such token after the last one a word read); any
\ other code that is not an authoring error is a Forth exception.
: lfa-undefined ( -- )
  lfa-the-line nip lfa-unread-to lfa-stray 2dup lfa-token! 2dup lfa-stray-code >r
  lfa-here r> lfa-record ;
\ Another exception names the last token a word read, or, when no word
\ read one on this line yet, the line's first token.
: lfa-first-token ( -- )
  lfa-token nip if exit then lfa-the-line lfa-next-token dup 0= if 2drop 2drop exit then
  lfa-token! 2drop ;
: lfa-foreign ( code -- )
  dup -13 = if drop lfa-undefined exit then
  lfa-first-token lfa-number! lfa-token lfa-here lfa-e-forth lfa-record ;
: lfa-caught ( code -- outcome )
  ?dup 0= if outcome-ok exit then
  dup lf-author-throw = if drop else lfa-foreign then
  lfa-floats-clear lfa-scope-close lf-author-code lf-author-outcome ;
\ Refused before anything runs: Forth is compiling.
: lfa-compiling ( -- outcome )
  0 0 0 lfa-e-compiling lfa-record lfa-e-compiling lf-author-outcome ;
\ Refused before anything runs: the caller's search order is too long to save
\ (an outcome, not an abort: the caller's own order is left alone).
: lfa-order-fits? ( -- flag )
  get-order dup >r 0 ?do drop loop r> lfa-order-capacity > 0= ;
: lfa-order-full ( -- outcome )
  0 0 0 lfa-e-search-order lfa-record lfa-e-search-order lf-author-outcome ;
\ A run: the lines of a new text, counted from 1.
: lfa-go ( -- outcome )
  lfa-error-reset lfa-interpreting? 0= if lfa-compiling exit then
  lfa-order-fits? 0= if lfa-order-full exit then
  lfa-lines-restart lfa-save decimal depth lfa-floor! ['] lfa-lines catch
    lfa-restore lfa-caught ;

\ Public words; see the header.
\ The term store's own hash-consing is turned off for the run (terms.fs):
\ authoring shares nodes itself and keeps a binder name, a position or a
\ note per node (build.fs), which one shared node could not hold.
: lfa-stores-reset ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-pres-reset lf-note-reset lf-ssession-begin drop ;
\ A run starts in natural form (form.fs).
: lf-author-begin ( -- )
  false lf-term-sharing! lfa-stores-reset lfa-scope-close lfa-items-reset
  lfa-groups-reset lfa-declarations-reset lfa-source-reset lfa-error-reset
  lfa-form-reset lfa-run-fresh lfa-declaration-fresh ;
\ The run's text is in the kernel form, as the marker kernel-form says
\ (form.fs): for callers that run the printer's words or kernel-form text
\ that has no marker, right after lf-author-begin.
: lf-author-kernel ( -- ) lfa-kernel-form! ;
: lf-author-text ( c-addr u -- outcome ) lfa-rest! 0 lfa-run lfa-run-file ! lfa-go ;
: lf-author-file ( c-addr u -- outcome )
  lfa-error-reset 2dup r/o open-file
  if drop 0 lfa-e-file lfa-record lfa-e-file lf-author-outcome exit then
  nip nip dup lfa-run lfa-run-file ! lfa-go swap close-file drop 0 lfa-run lfa-run-file
    ! ;
: lf-author-count ( -- n ) lfa-decl-count ;
: lf-author-decl ( i -- decl ) lfa-decl ;
: lf-author-notes ( i -- first end ) lfa-decl dup lfa-decl-notes @ swap
  lfa-decl-notes-end @ ;
\ The printer asks whether a name is a constant: any declaration of the
\ run, or of the checker's input, which the printer asks when it writes an
\ export (print --lf, in the same Gforth since plan task 8.2.1c).
: lfa-name-declared? ( name -- flag )
  dup lf-pf-input-const? if drop true exit then
  false lfa-decl-count 0 ?do over i lfa-decl lf-fdecl-name @ = or loop nip ;
' lfa-name-declared? is lf-pf-const-exists?
create lfa-blank-line 10 c,
\ A library constant's record (library.fs) is never printed.
: lfa-print-one ( fuel i -- outcome )
  dup lfa-library? if 2drop outcome-ok exit then
  dup if lfa-blank-line 1 lf-pp-emit then lfa-decl swap lf-print-forth-decl ;
: lfa-print-at ( fuel i -- fuel outcome ) over swap lfa-print-one ;
: lf-author-print ( fuel -- outcome ) lf-author-count ['] lfa-print-at ok-each nip ;
