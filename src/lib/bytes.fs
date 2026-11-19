\ Bounded line reader over a Forth-2012 file, text framing rules and UTF-8
\ checks. A general text tool with no Lean knowledge. Untrusted: it decides
\ nothing about validity beyond the bytes it frames.
\ State: none of its own. Every reader word takes a reader record made by
\ reader:, so separate readers are independent; one reader is
\ single-threaded. The two byte tables below are constant after loading.
\
\ A reader keeps whole lines in one heap buffer (ALLOCATE); reader-init
\ frees the buffer of an earlier reader-init first, and reader-free frees
\ it at the end. A line longer than the buffer grows it (RESIZE), up to
\ the reader's line limit; a longer line is reported as full (out of
\ room), never cut. reader-line returns the next line without its line
\ feed. Those bytes stay valid, and the caller may change them in place,
\ until the next reader call. Reading past the end is invalid, as is an
\ unreadable file or a failed read; running out of heap is full.
\ reader-position gives the current line's number and file offset for
\ error messages. Offsets are doubles, so files beyond 2 GB work on
\ 32-bit hosts too.
\
\ Rules (reader-rules!, kept until reader-free): which text a reader
\ takes. A zeroed reader (reader:, reader-free) reads ordinary text, the
\ rules reader-text: a last line without a line feed is a line, a
\ carriage return before a line feed (or at the end of that last line)
\ is dropped, and a UTF-8 byte-order mark at the start of the first line
\ is dropped. Each rule bit keeps one of these strict instead:
\ reader-final-lf (a last line without its line feed is invalid),
\ reader-keep-cr (the carriage return stays in the line) and
\ reader-keep-bom (the mark stays in the line). reader-strict, all three,
\ is the framing of Lean's exports: every line ends with a line feed, and
\ the caller refuses carriage returns and the mark with text-framed. A
\ dropped byte still counts in the line limit and in the file offsets.
\ Only a line feed ends a line: a carriage return elsewhere is part of the
\ line. So in ordinary text a file ending in a line feed and then a lone
\ carriage return has one more line, empty once its carriage return is
\ dropped (as Python's universal newlines read it): every byte of the file
\ belongs to a line the caller sees, and none is lost silently.
\
\ Example: count the lines of a file, then check and decode a character.
\   reader: rd   4096 65536 rd reader-init drop
\   : lines ( c-addr u -- n ) rd reader-open drop 0
\     begin rd reader-more? while rd reader-line nip nip ok? - repeat
\     rd reader-close drop ;
\   s" lib/bytes.fs" lines 0> .  rd reader-free
\   s\" \xe2\x9c\x93" 2dup utf8-valid? . drop 3 utf8-decode .
\   \ prints: -1 -1 10003
\
\ Interface: /reader reader: reader-init reader-rules! reader-text
\ reader-strict reader-final-lf reader-keep-cr reader-keep-bom reader-free
\ reader-attach reader-open reader-close reader-line reader-more?
\ reader-position reader-line# byte-scan text-framed utf8-length utf8-valid?
\ utf8-decode utf8-size utf8-put counted, counted-next counted-nth counted-or-empty
\ fnv-step bytes-mix. Requires portability.fs, bounds.fs (between?),
\ outcome.fs, store.fs (store-zeroed,), blocks.fs (heap-claim and
\ heap-release) and module.fs; helpers are private in lf-lib-private
\ (ADR 0010). Loads in decimal whatever BASE is, then restores it at the
\ end of a successful load (a THROW while loading leaves BASE decimal:
\ Forth-2012 gives a file no way to restore it then).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./bounds.fs
require ./outcome.fs
require ./store.fs
require ./blocks.fs
require ./module.fs

lf-lib-private module-open

10 constant lf-byte                \ line feed
13 constant cr-byte                \ carriage return

lf-lib set-current
\ The rules: each bit set keeps one framing rule strict (see the header).
1 constant reader-final-lf         \ a last line without a line feed is invalid
2 constant reader-keep-cr          \ a carriage return before the line feed stays
4 constant reader-keep-bom         \ a byte-order mark starting the first line stays
0 constant reader-text             \ ordinary text
7 constant reader-strict           \ Lean's exports: all three
begin-structure /reader
lf-lib-private set-current
  field: reader-fid                \ the file being read, or 0
  field: reader-buffer             \ heap buffer, or 0
  field: reader-size               \ its size in bytes
  field: reader-limit              \ most bytes in one line, line feed excluded
  field: reader-rules              \ the rule bits, reader-text when zero
  field: reader-start              \ buffer offset of the first unread byte
  field: reader-end                \ buffer offset after the last byte read
  field: reader-eof                \ true once the file has no more bytes
  field: reader-lines              \ lines returned: the current line's number
  aligned 2 cells +field reader-base   \ file offset of buffer byte 0, a double
  aligned 2 cells +field reader-at     \ file offset of the current line, a double
lf-lib set-current
end-structure
lf-lib-private set-current

\ The fields from reader-start on describe progress through one file.
/reader 0 reader-start - constant /reader-progress

lf-lib set-current
\ Defining word: name ( -- reader ), zeroed, with no buffer and no file,
\ reading ordinary text.
: reader: ( "name" -- ) create /reader store-zeroed, drop ;
lf-lib-private set-current

\ heap-claim and heap-release: lib/blocks.fs (required above).
: reader-buffer! ( addr size reader -- ) tuck reader-size ! reader-buffer ! ;
: reader-release ( reader -- ) 0 over reader-size ! reader-buffer heap-release ;
lf-lib set-current
\ Give a reader a buffer of size bytes (at least one) for lines of at most
\ limit bytes, freeing its earlier buffer; a negative limit refuses every
\ line. Full, with no buffer, when the heap has no room. The rules stay.
: reader-init ( size limit reader -- outcome )
  dup reader-release tuck reader-limit ! swap 1 max dup heap-claim
  if swap rot reader-buffer! outcome-ok else 2drop outcome-full then ;
\ Set the reader's rules (reader-text, reader-strict, or bits of
\ reader-final-lf, reader-keep-cr and reader-keep-bom), before reading.
: reader-rules! ( rules reader -- ) reader-rules ! ;
\ Free the buffer and zero the record (its rules are reader-text again);
\ the caller closes the file first.
: reader-free ( reader -- ) dup reader-release /reader erase ;

\ Start reading an open file from its current position.
: reader-attach ( fid reader -- ) tuck reader-fid ! reader-start /reader-progress erase ;
\ Open a file by name for reading; invalid when it cannot be opened.
: reader-open ( c-addr u reader -- outcome )
  >r r/o bin open-file r> swap
  if 2drop outcome-invalid else reader-attach outcome-ok then ;
\ Close the file; invalid when the host reports an error.
: reader-close ( reader -- outcome )
  dup reader-fid @ swap 0 swap reader-fid ! ?dup 0= if outcome-ok exit then
  close-file 0= flag>outcome ;
lf-lib-private set-current

\ The rest of addr u from the first byte char on, empty when there is none:
\ Gforth's native SCAN where available (much faster), otherwise the
\ portable loop, which is always defined so tests can compare the two.
: byte-scan-portable ( addr u char -- addr' u' )
  >r begin dup while over c@ r@ <> while 1 /string repeat then r> drop ;
lf-lib set-current
s" gforth" environment? [if] 2drop
: byte-scan ( addr u char -- addr' u' ) scan ;
[else]
: byte-scan ( addr u char -- addr' u' ) byte-scan-portable ;
[then]
lf-lib-private set-current
\ The number of bytes before the first line feed, if there is one.
: lf-index ( addr u -- n true | false )
  tuck lf-byte byte-scan nip dup if - true else 2drop false then ;

\ Buffer views.
: reader-from ( offset reader -- addr ) reader-buffer @ + ;
: reader-unread ( reader -- addr u )
  dup reader-start @ over reader-from swap dup reader-end @ swap reader-start @ - ;
: reader-room ( reader -- addr u )
  dup reader-end @ over reader-from swap dup reader-size @ swap reader-end @ - ;
: reader-pending? ( reader -- flag ) reader-unread nip 0> ;
: reader-full? ( reader -- flag ) dup reader-end @ swap reader-size @ = ;

\ Whether a rule bit of the reader is set (that rule is strict).
: reader-rule? ( reader bit -- flag ) swap reader-rules @ and 0<> ;
\ A UTF-8 byte-order mark starting addr u.
: bom? ( addr u -- flag ) 3 min s\" \xEF\xBB\xBF" compare 0= ;
\ The line without a carriage return at its end, and without a mark at
\ its start when it is the first line, as the rules say.
: line-cr-drop ( addr n -- addr n' ) dup if 2dup + 1- c@ cr-byte = + then ;
: line-bom-drop ( addr n -- addr' n' ) 2dup bom? if 3 /string then ;
: reader-first? ( reader -- flag ) reader-lines @ 1 = ;
: reader-trim ( addr n reader -- addr' n' )
  dup reader-keep-cr reader-rule? 0= if >r line-cr-drop r> then
  dup reader-first? swap reader-keep-bom reader-rule? 0= and if line-bom-drop then ;

\ Taking a line: remember where it starts, then step past it and its line feed.
: reader-mark ( reader -- )
  >r r@ reader-base 2@ r@ reader-start @ m+ r@ reader-at 2! 1 r> reader-lines +! ;
: reader-skip ( n reader -- ) swap 1+ swap reader-start +! ;
: reader-take ( n reader -- addr n )
  dup reader-mark dup reader-unread drop -rot 2dup reader-skip reader-trim ;

\ Refilling. reader-shift moves the unread bytes to the front of the
\ buffer, adding the bytes before them to reader-base. A full buffer grows
\ to twice its size, but never past the limit plus one byte for the line
\ feed; a buffer already beyond the limit cannot grow (full).
: reader-base+ ( n reader -- ) reader-base dup >r 2@ rot m+ r> 2! ;
: reader-shift ( reader -- )
  >r r@ reader-unread tuck r@ reader-buffer @ swap move
  r@ reader-start @ r@ reader-base+ r@ reader-end ! 0 r> reader-start ! ;
: reader-growth ( reader -- n )
  dup reader-limit @ over reader-size @ - 1+ swap reader-size @ min ;
: reader-resize ( size reader -- outcome )
  2dup reader-buffer @ swap resize
  if 2drop drop outcome-full else -rot reader-buffer! outcome-ok then ;
: reader-grow ( reader -- outcome )
  dup reader-size @ over reader-limit @ > if drop outcome-full exit then
  dup reader-growth over reader-size @ + swap reader-resize ;
: reader-make-room ( reader -- outcome )
  dup reader-full? if reader-grow else drop outcome-ok then ;
: reader-room! ( reader -- outcome ) dup reader-shift reader-make-room ;
\ Read more bytes after the unread ones; no bytes at all means the end.
: reader-got ( u reader -- )
  over 0= if nip true swap reader-eof ! else reader-end +! then ;
: reader-read ( reader -- outcome )
  dup >r reader-room r@ reader-fid @ read-file r> swap
  if 2drop outcome-invalid else reader-got outcome-ok then ;
: reader-fill ( reader -- outcome ) dup reader-room! ok-then? if reader-read then ;

\ At the end of the file: a last line without its line feed is given one
\ after its bytes when the rules take it (full when the buffer cannot
\ grow for it); otherwise, or with no bytes left, invalid. The read that
\ found the end had room, and taking lines only frees more, so the buffer
\ is never full here today; the growth is kept as a guard, and its full
\ outcome is tested on a reader set up full.
: reader-lf! ( reader -- ) lf-byte over reader-room drop c! 1 swap reader-end +! ;
: reader-close-line ( reader -- outcome )
  dup reader-room! ok-then? if reader-lf! outcome-ok then ;
: reader-last ( reader -- outcome )
  dup reader-pending? over reader-final-lf reader-rule? 0= and
  if reader-close-line else drop outcome-invalid then ;
\ No line feed among the unread bytes: read more, unless the line is
\ already too long (full) or the file has ended (reader-last).
: reader-wait ( reader -- outcome )
  dup reader-unread nip over reader-limit @ > if drop outcome-full exit then
  dup reader-eof @ if reader-last exit then reader-fill ;
: reader-found ( n reader -- addr u outcome )
  2dup reader-limit @ > if 2drop 0 0 outcome-full else reader-take outcome-ok then ;

lf-lib set-current
\ The next line, without its line feed; on failure 0 0 and the outcome.
: reader-line ( reader -- addr u outcome )
  begin dup reader-unread lf-index 0= while
    dup reader-wait ok-then? 0= if 0 0 rot exit then
  repeat swap reader-found ;
\ True while bytes are left to read. A failed read also gives true, so
\ that the next reader-line reports the failure.
: reader-more? ( reader -- flag )
  dup reader-pending? if drop true exit then dup reader-eof @ if drop false exit then
  dup reader-fill ok? if reader-pending? else drop true then ;
\ The current line's number (1-based; 0 before the first line) and the
\ file offset of its first byte.
: reader-position ( reader -- d line ) dup reader-at 2@ rot reader-lines @ ;
\ The current line's number alone, as reader-position gives it.
: reader-line# ( reader -- n ) reader-lines @ ;

\ Compile a counted string of at most 255 bytes into the dictionary, then
\ align; a longer one aborts. For tables of names built while loading.
: counted, ( c-addr u -- )
  dup 255 > abort" counted, string too long" dup c, here swap dup allot move align ;
\ The address after a counted string counted, laid down: the next one of a
\ table of them.
: counted-next ( c-addr -- c-addr' ) count + aligned ;
\ The n-th counted string of such a table, from 0 (n >= 0; unchecked: the
\ table holds more than n).
: counted-nth ( c-addr n -- c-addr' ) 0 ?do counted-next loop ;
\ The text of a counted string, or empty text for 0 (an absent string: a
\ table entry, a field name or a reason not given).
: counted-or-empty ( c-addr|0 -- c-addr u ) ?dup if count else s" " then ;

\ Strict framing of one line: no carriage return anywhere (so no CRLF
\ line ends) and no UTF-8 byte-order mark at its start. UTF-8 validity is
\ left to the caller: utf8-valid? checks a whole line, and json.fs checks
\ it inside strings while allowing only ASCII outside them.
: text-framed ( addr u -- outcome )
  2dup bom? if 2drop outcome-invalid else cr-byte byte-scan nip 0= flag>outcome then ;
lf-lib-private set-current

\ UTF-8 (RFC 3629). Each lead byte selects a row: the length of its
\ sequence and the range allowed for its second byte, which excludes
\ overlong forms, surrogates and code points beyond U+10FFFF. Bytes that
\ cannot start a sequence select row 0, of length 0.
begin-structure /utf8-row
  field: row-lo                    \ smallest second byte
  field: row-hi                    \ largest second byte
  field: row-length                \ bytes in the sequence; 0 when invalid
end-structure
create utf8-rows
  0 ,   0 ,   0 ,     $00 , $ff , 1 ,   $80 , $bf , 2 ,   $a0 , $bf , 3 ,
  $80 , $bf , 3 ,     $80 , $9f , 3 ,   $90 , $bf , 4 ,   $80 , $bf , 4 ,
  $80 , $8f , 4 ,
create utf8-classes 256 allot  utf8-classes 256 erase
: utf8-class! ( lo hi row -- ) -rot 1+ swap ?do dup utf8-classes i + c! loop drop ;
$00 $7f 1 utf8-class!  $c2 $df 2 utf8-class!  $e0 $e0 3 utf8-class!
$e1 $ec 4 utf8-class!  $ee $ef 4 utf8-class!  $ed $ed 5 utf8-class!
$f0 $f0 6 utf8-class!  $f1 $f3 7 utf8-class!  $f4 $f4 8 utf8-class!

: utf8-row ( byte -- row ) utf8-classes + c@ /utf8-row * utf8-rows + ;
: continuation? ( byte -- flag ) $80 $bf between? ;
: utf8-second? ( addr row -- flag ) swap 1+ c@ over row-lo @ rot row-hi @ between? ;
\ Bytes three and four of a sequence are plain continuation bytes.
: utf8-tail? ( addr n -- flag )
  true -rot 2 ?do dup i + c@ continuation? rot and swap loop drop ;
: utf8-sequence? ( addr row -- flag )
  dup row-length @ 2 < if nip row-length @ 0<> exit then
  2dup utf8-second? -rot row-length @ utf8-tail? and ;
lf-lib set-current
\ The length (1 to 4) of the valid UTF-8 sequence at addr, or 0 when the
\ bytes there do not form one, including when u is too short for it.
: utf8-length ( addr u -- n )
  dup 0= if nip exit then over c@ utf8-row tuck row-length @ < if 2drop 0 exit then
  tuck utf8-sequence? if row-length @ else drop 0 then ;
\ True when all of addr u is valid UTF-8.
: utf8-valid? ( addr u -- flag )
  begin dup while
    2dup utf8-length ?dup 0= if 2drop false exit then /string
  repeat 2drop true ;
lf-lib-private set-current

\ Decoding the valid sequence of n bytes at addr (n as utf8-length gave
\ it, 1 to 4) into its code point: the lead byte's low bits, then six
\ bits of each byte after it.
\   s\" \xe2\x80\xae" drop 3 utf8-decode   \ $202E
: utf8-mask ( n -- mask )
  case 1 of $7f endof 2 of $1f endof 3 of $0f endof $07 swap endcase ;
: utf8-lead ( addr n -- bits ) swap c@ swap utf8-mask and ;
: utf8-tail-bits ( u addr -- u' ) c@ $3f and swap 6 lshift or ;
lf-lib set-current
: utf8-decode ( addr n -- u )
  2dup utf8-lead -rot chars over + swap char+ ?do i utf8-tail-bits loop ;

\ Encoding a code point u (at most $10FFFF and not a surrogate; the caller
\ checks) as 1 to 4 bytes at addr: utf8-size bytes, which utf8-put gives.
: utf8-size ( u -- n )
  dup $80 < if drop 1 exit then dup $800 < if drop 2 exit then $10000 < if 3 else 4 then ;
lf-lib-private set-current
: utf8-prefix ( n -- bits ) dup 1 = if drop 0 else $ff00 swap rshift $ff and then ;
: utf8-tail-byte ( u shift -- byte ) rshift $3f and $80 or ;
\ Continuation bytes, written backwards from end, the address after the last.
: utf8-put-tail ( u end n -- )
  1 ?do 2dup swap i 1- 6 * utf8-tail-byte swap i - c! loop 2drop ;
lf-lib set-current
: utf8-put ( u addr -- n )
  over utf8-size >r over r@ 1- 6 * rshift r@ utf8-prefix or over c!
  r@ + r@ utf8-put-tail r> ;

\ FNV-style mixing: fnv-step mixes x into the hash h, h xor x times
\ 16777619, modulo the cell; bytes-mix mixes the bytes addr u, one at a
\ time. The input fingerprint (src/core/input.fs) mixes cells with
\ fnv-step and gives the name bytes to bytes-mix, because only text
\ modules read bytes. A guard against mistakes, not forgery; valid within
\ one host only, never compared across machines or written out.
: fnv-step ( h x -- h' ) xor 16777619 um* drop ;
: bytes-mix ( h addr u -- h' ) 0 ?do dup c@ rot fnv-step swap char+ loop drop ;

module-close
base !   \ the BASE this file was loaded with (not reached when loading throws)
