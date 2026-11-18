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
\ and on a 32-bit host lines beyond 32767 wrap. It also reads token text:
\ the tokens of a line, the dots of a name, and which tokens are numbers
\ (only plain decimals) or look like one. Lines count from 1 in each text
\ a run is given (lfa-lines-restart), so an error points at the line of
\ that text. And it finds the first character a line may not hold
\ (ADR 0017 Amendment 1, A5 row 7): one that text-rule.fs bans, a control
\ or format character, a line or paragraph separator, or bytes that are
\ not UTF-8; TAB aside, which separates tokens as a space does. Forth
\ splits tokens at TAB, LF, VT, FF, CR and space only. So a token is the
\ text between those, which an editor shows as one word unless it holds a
\ character the rule allows that looks blank or joins: a Zs space (NBSP,
\ U+3000), a filler (U+3164, U+2800, U+115F) or a combining mark. Reading
\ back is exact either way; only the look of such a name can mislead.
\ Untrusted authoring code.
\ State: one context record, lfa-source (ADR 0009).

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/text-run.fs
require ../lib/decimal.fs
require ../lib/text-rule.fs

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
\ A new text starts: its first line will be line 1.
: lfa-lines-restart ( -- ) 0 lfa-source lfa-source-line ! ;
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
\ The part of the line after the last token a LeanForth word read, up to
\ offset n (clamped into the line).
: lfa-unread-to ( n -- c-addr u )
  lfa-the-line rot min 0 max lfa-source lfa-source-end @ 0 max over min /string ;
\ Is c-addr in the line being run (its end included)?
: lfa-on-line? ( c-addr -- flag ) lfa-the-line over + 1+ within ;
: lfa-offset ( c-addr -- n ) lfa-source lfa-source-text @ - ;

\ Tokens of a text, split at blanks.
: lfa-skip-blanks ( c-addr u -- c-addr' u' )
  begin dup while over c@ lfa-blank? while 1 /string repeat then ;
: lfa-word-end ( c-addr u -- n ) ['] lfa-blank? text-scan ;
: lfa-next-token ( c-addr u -- c-addr' u' token-addr token-u )
  lfa-skip-blanks 2dup lfa-word-end >r over r@ 2swap r> /string 2swap ;

\ Names in token text: parts between dots.
: lfa-dot-at? ( c-addr i -- flag ) chars + c@ [char] . = ;
: lfa-last-char ( c-addr u -- char ) + 1- c@ ;
\ The offset of the first dot, or u.
: lfa-dot? ( char -- flag ) [char] . = ;
: lfa-dot ( c-addr u -- n ) ['] lfa-dot? text-scan ;
\ The name without its last part (and the dot before it); empty for one part.
: lfa-cut ( c-addr u -- c-addr u' ) begin dup while 1- 2dup lfa-dot-at? until then ;
\ An empty part: a dot first, last or twice in a row, or no text.
: lfa-empty-part? ( c-addr u -- flag )
  dup 0= if 2drop true exit then
  over c@ [char] . = >r 2dup lfa-last-char [char] . = r> or if 2drop true exit then
  s" .." search nip nip ;

\ Numbers. The only LeanForth number is a plain decimal: one to nine
\ digits, exact in a cell on every host. A spelling is number-like when a
\ Forth host may read it as a number in some form: a digit first, or a
\ sign, base prefix or quote (- + # $ % & ') and more after it. No name
\ is number-like (groups.fs, declarations.fs), so no word ever stands
\ where a number is meant, and every number-like token that is no plain
\ decimal is refused (groups.fs).
9 constant lfa-digits-max
: lfa-plain-decimal? ( c-addr u -- flag )
  dup 1 lfa-digits-max 1+ within if decimal-digits? else 2drop false then ;
: lfa-prefix-char? ( char -- flag )
  dup [char] # [char] ' 1+ within over [char] + = or swap [char] - = or ;
: lfa-number-like? ( c-addr u -- flag )
  dup 0= if 2drop false exit then over c@ decimal-digit? if 2drop true exit then
  1 > swap c@ lfa-prefix-char? and ;

\ Characters a line may hold (see the header). The first character of
\ c-addr u and the rest; bytes that begin no valid UTF-8 character count
\ as one character, -1, which text-rule.fs bans.
9 constant lfa-tab
: lfa-char ( c-addr u -- c-addr' u' code )
  2dup utf8-length ?dup 0= if 1 /string -1 exit then
  >r over r@ utf8-decode -rot r> /string rot ;
: lfa-allowed? ( code -- flag ) dup lfa-tab = if drop true else tr-banned? 0= then ;
\ The offset in c-addr u of its first character a line may not hold, or -1.
: lfa-bad-offset ( c-addr u -- n|-1 )
  over >r begin dup while
    over >r lfa-char lfa-allowed? 0= if 2drop r> r> - exit then r> drop
  repeat 2drop r> drop -1 ;
