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
\   lfa-token-on ( -- c-addr u )  the next token after the last one a word
\       read, reading on into the text's next lines when the line ends
\       (plan row TB2, batch 3c: a list over several lines, the owner's
\       wish of 2026-11-22), made the current token; an empty string at
\       the text's end. A \ skips the rest of its line and a ( comment
\       its text, as Forth's own words do.
\ Reading on (lfa-refill): the next line becomes the line being run, its
\ characters checked and its look-ahead made as for any line; the line
\ whose EVALUATE was running is spent, so when that EVALUATE ends the
\ runner runs the rest of the new line, after the last token a word read
\ (lfa-eval-on), and so on, with no nesting of EVALUATE. A file's line
\ buffer is reused: the spent line's text is gone, which nothing reads,
\ since its EVALUATE has reached its end.

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/text-run.fs
require ./words.fs
require ./export.fs

1024 constant lfa-line-capacity

begin-structure /lfa-run
  2 cells +field lfa-run-rest  \ text not yet run (2@: c-addr u)
  field: lfa-run-file        \ the file being run, or 0
  field: lfa-run-floats      \ floating-point stack depth when the line began
  field: lfa-run-recognizer  \ the host's recognizer (Gforth 1.0)
  field: lfa-run-on          \ true: a word read on into the next line (lfa-refill)
  /run-settings +field lfa-run-settings  \ the caller's BASE, order and current
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
  2dup decimal-digits? if rec-number else 2drop translate-none then ;
: lfa-recognize ( c-addr u -- translation )
  2dup rec-name dup translate-none = if drop lfa-decimal else 2swap 2drop then ;
: lfa-recognizer! ( -- )
  action-of rec-forth lfa-run lfa-run-recognizer ! ['] lfa-recognize is rec-forth ;
: lfa-recognizer-back ( -- ) lfa-run lfa-run-recognizer @ is rec-forth ;
[else]
: lfa-recognizer! ( -- ) ;
: lfa-recognizer-back ( -- ) ;
[then]

\ The caller's settings (lib/text-run.fs) and recognizer: false, nothing
\ saved, for a search order of more than run-settings-order-max lists.
: lfa-settings ( -- settings ) lfa-run lfa-run-settings ;
: lfa-save ( -- flag ) lfa-settings run-settings-save dup if lfa-recognizer! then ;
: lfa-restore ( -- ) lfa-recognizer-back lfa-settings run-settings-restore ;

\ Floating-point numbers, on hosts whose interpreter reads them: dropped
\ after an error (a float token is refused like any number form).
\ (lib/text-run.fs's floats-depth and floats-drop-to, also on a host
\ without floating point).
: lfa-floats! ( -- ) floats-depth lfa-run lfa-run-floats ! ;
: lfa-floats-clear ( -- ) lfa-run lfa-run-floats @ floats-drop-to ;

\ Lines of text, split at LF; a CR before it is dropped (lib/text-run.fs).
: lfa-rest ( -- c-addr u ) lfa-run lfa-run-rest 2@ ;
: lfa-rest! ( c-addr u -- ) lfa-run lfa-run-rest 2! ;
: lfa-text-line ( -- c-addr u true | false )
  lfa-rest dup 0= if 2drop false exit then
  2dup text-line-end drop >r over r@ text-cr-drop 2swap r> 1+ over min /string
  lfa-rest! true ;
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
\ The token an error of the look-ahead points at (source.fs lfa-token-at);
\ the line counts as read only as far as before, so its numbers are still
\ checked.
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
\ A line starts: the line being run, its characters checked, its look-ahead.
: lfa-line-start ( c-addr u -- ) 2dup lfa-line! lfa-line-chars lfa-order! lfa-ahead ;
: lfa-on? ( -- flag ) lfa-run lfa-run-on @ ;
: lfa-eval ( c-addr u -- ) false lfa-run lfa-run-on ! evaluate ;
\ The rest of the line being run, after the last token a word read.
: lfa-line-rest ( -- c-addr u ) lfa-the-line nip lfa-unread-to ;
: lfa-eval-on ( -- ) begin lfa-on? while lfa-line-rest lfa-eval repeat ;
: lfa-eval-line ( c-addr u -- )
  2dup lfa-line-start lfa-floats! lfa-eval lfa-eval-on lfa-line-end ;

\ Reading on (see the header): the next line, run once the EVALUATE
\ running now ends; false at the text's end.
: lfa-refill ( -- flag )
  lfa-next-line? 0= if false exit then lfa-line-start true lfa-run lfa-run-on ! true ;
\ The line read up to c-addr; on the line EVALUATE runs, >IN with it.
: lfa-in! ( c-addr -- ) lfa-on? if drop else source drop - >in ! then ;
: lfa-skip-to ( c-addr -- ) dup lfa-in! lfa-offset lfa-source lfa-source-end ! ;
: lfa-next-on ( -- c-addr u )
  lfa-line-rest lfa-next-token 2swap 2drop 2dup lfa-token! 2dup + lfa-in! ;
\ Comments: \ to the line's end, ( past its ) on the line (else error 28).
: lfa-comment-on? ( c-addr u -- flag ) 2dup lfa-comment? -rot s" (" lfa-token= or ;
: lfa-paren-end ( -- c-addr )
  lfa-line-rest [char] ) byte-scan 0<> lfa-e-comment-end lfa-must 1+ ;
: lfa-skip-on ( c-addr u -- )
  lfa-comment? if lfa-the-line + else lfa-paren-end then lfa-skip-to ;
: lfa-blank-on ( -- c-addr u )
  begin lfa-next-on 2dup lfa-comment-on? while lfa-skip-on repeat ;
: lfa-token-on ( -- c-addr u )
  begin lfa-blank-on dup 0= while 2drop lfa-refill 0= if 0 0 exit then repeat ;
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
\ A host stack, the dictionary or the heap ran out (THROW -3, -5, -8, or
\ ALLOCATE's or RESIZE's -59, -61): error 300, full (exit 3); any other
\ code is LeanForth's internal fault, error 41 (exit 5), never the text's.
: lfa-room-throw? ( code -- flag )
  case -3 of true endof -5 of true endof -8 of true endof
    -59 of true endof -61 of true endof false swap endcase ;
: lfa-forth-code ( code -- code' )
  lfa-room-throw? if lfa-e-forth-room else lfa-e-forth then ;
: lfa-thrown ( -- code ) lfa-error lfa-err-number @ lfa-forth-code ;
: lfa-foreign ( code -- )
  dup -13 = if drop lfa-undefined exit then
  lfa-first-token lfa-number! lfa-token lfa-here lfa-thrown lfa-record ;
: lfa-caught ( code -- outcome )
  ?dup 0= if outcome-ok exit then
  dup lf-author-throw = if drop else lfa-foreign then
  lfa-floats-clear lfa-scope-close lf-author-code lf-author-outcome ;
\ Refused before anything runs: Forth is compiling.
: lfa-compiling ( -- outcome )
  0 0 0 lfa-e-compiling lfa-record lfa-e-compiling lf-author-outcome ;
\ Refused before anything runs: the caller's search order is too long to save
\ (an outcome, not an abort: the caller's own order is left alone).
: lfa-order-full ( -- outcome )
  0 0 0 lfa-e-search-order lfa-record lfa-e-search-order lf-author-outcome ;
\ A run: the lines of a new text, counted from 1.
: lfa-go ( -- outcome )
  lfa-error-reset lfa-interpreting? 0= if lfa-compiling exit then
  lfa-save 0= if lfa-order-full exit then
  lfa-lines-restart decimal depth lfa-floor! ['] lfa-lines catch lfa-restore lfa-caught ;

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
  lfa-error-reset 2dup r/o bin open-file
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
