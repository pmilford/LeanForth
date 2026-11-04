\ Positions in the author's text (ADR 0017 §10): the line being run and
\ the token being acted on, so that every node and every error points at
\ the author's text. A LeanForth word finds its own token by re-reading
\ SOURCE back from >IN, where Forth's text interpreter leaves it just past
\ the token and at most one delimiter (Forth-2012 3.4.1); a word that reads
\ the token after it (a binder's name, a label) makes that the current
\ token. The runner keeps the line being run, so that an error found
\ after Forth has left the line (an unknown token) can still point into
\ it. A position is one nonnegative cell, the line times 65536 plus the
\ column, both counted from 1; a column beyond 65535 is recorded as 65535,
\ and on a 32-bit host lines beyond 32767 wrap. Untrusted authoring code.
\ State: one context record, lfa-source (ADR 0009).

require ../lib/lib.fs

65536 constant lfa-line-unit

begin-structure /lfa-source
  field: lfa-source-line     \ number of the line being run, from 1; 0 before the first
  field: lfa-source-text     \ the line being run: its address
  field: lfa-source-text#    \ and length
  field: lfa-source-column   \ column of the current token, from 1
  field: lfa-source-length   \ its length in characters
  field: lfa-source-end      \ characters of the line read up to the last token read
end-structure
/lfa-source context-record: lfa-source

: lfa-source-reset ( -- ) lfa-source /lfa-source erase ;
\ The line c-addr u starts: nothing of it has been read.
: lfa-line! ( c-addr u -- )
  lfa-source tuck lfa-source-text# ! tuck lfa-source-text ! 1 over lfa-source-line +!
  0 over lfa-source-end ! 1 over lfa-source-column ! 0 swap lfa-source-length ! ;
: lfa-line ( -- n ) lfa-source lfa-source-line @ ;
: lfa-the-line ( -- c-addr u ) lfa-source dup lfa-source-text @ swap lfa-source-text# @ ;

\ Positions.
: lfa-pos ( line column -- pos ) 65535 min swap lfa-line-unit * + ;
: lfa-pos> ( pos -- line column ) lfa-line-unit /mod swap ;
\ The position of the current token.
: lfa-here ( -- pos ) lfa-line lfa-source lfa-source-column @ lfa-pos ;

\ The token just read by the interpreter: back from >IN over one
\ delimiter, then over the token's characters (any character above a
\ space). >IN beyond the end of the input counts as the end.
: lfa-blank? ( char -- flag ) bl 1+ < ;
: lfa-char-before ( n -- char ) source drop + 1- c@ ;
: lfa-in ( -- n ) >in @ source nip min ;
: lfa-skip-delimiter ( n -- n' ) dup if dup lfa-char-before lfa-blank? if 1- then then ;
: lfa-token-start ( end -- start )
  begin dup while dup lfa-char-before lfa-blank? 0= while 1- repeat then ;
: lfa-invoked ( -- c-addr u )
  lfa-in lfa-skip-delimiter dup lfa-token-start tuck - >r source drop + r> ;

\ Make c-addr u, a token of the line being run, the current token, and
\ mark the line as read up to its end.
: lfa-token! ( c-addr u -- )
  2dup + lfa-source lfa-source-text @ - lfa-source lfa-source-end !
  lfa-source lfa-source-length ! lfa-source lfa-source-text @ - 1+ lfa-source
    lfa-source-column ! ;
\ The current token's text, while its line is kept; never beyond the line.
: lfa-token ( -- c-addr u )
  lfa-the-line lfa-source lfa-source-column @ 1- 0 max over min /string
  lfa-source lfa-source-length @ min ;
\ Read the name after a word, on the same line, as the current token; an
\ empty string when the line has no more tokens.
: lfa-parse-name ( -- c-addr u ) parse-name 2dup lfa-token! ;
\ The line has been read up to >IN (after a comment or a note's text).
: lfa-read! ( -- ) >in @ lfa-source lfa-source-end ! ;
\ The part of the line after the last token a LeanForth word read.
: lfa-unread ( -- c-addr u ) lfa-the-line lfa-source lfa-source-end @ 0 max over
  min /string ;
