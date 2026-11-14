\ Bounded line reader over a Forth-2012 file, strict text framing and UTF-8
\ checks. A general text tool with no Lean knowledge. Untrusted: it decides
\ nothing about validity beyond the bytes it frames.
\ Requires: lib.fs (portability, store-zeroed, outcome), blocks.fs (heap-claim and
\ heap-release, which its callers reach through this file).
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
\ until the next reader call. Every line must end with a line feed: a last
\ line without one is invalid, as is reading past the end; an unreadable
\ file or a failed read is invalid; running out of heap is full.
\ reader-position gives the current line's number and file offset for
\ error messages. Offsets are doubles, so files beyond 2 GB work on
\ 32-bit hosts too. The file loads in decimal whatever BASE is, then
\ restores it at the end of a successful load (a THROW while loading
\ leaves BASE decimal: Forth-2012 gives a file no way to restore it then).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./lib.fs
require ./blocks.fs

10 constant lf-byte                \ line feed
13 constant cr-byte                \ carriage return

begin-structure /reader
  field: reader-fid                \ the file being read, or 0
  field: reader-buffer             \ heap buffer, or 0
  field: reader-size               \ its size in bytes
  field: reader-limit              \ most bytes in one line, line feed excluded
  field: reader-start              \ buffer offset of the first unread byte
  field: reader-end                \ buffer offset after the last byte read
  field: reader-eof                \ true once the file has no more bytes
  field: reader-lines              \ lines returned: the current line's number
  aligned 2 cells +field reader-base   \ file offset of buffer byte 0, a double
  aligned 2 cells +field reader-at     \ file offset of the current line, a double
end-structure

\ The fields from reader-start on describe progress through one file.
/reader 0 reader-start - constant /reader-progress

\ Defining word: name ( -- reader ), zeroed, with no buffer and no file.
: reader: ( "name" -- ) create /reader store-zeroed, drop ;

\ heap-claim and heap-release: lib/blocks.fs (required above).
: reader-buffer! ( addr size reader -- ) tuck reader-size ! reader-buffer ! ;
: reader-release ( reader -- ) 0 over reader-size ! reader-buffer heap-release ;
\ Give a reader a buffer of size bytes (at least one) for lines of at most
\ limit bytes, freeing its earlier buffer; a negative limit refuses every
\ line. Full, with no buffer, when the heap has no room.
: reader-init ( size limit reader -- outcome )
  dup reader-release tuck reader-limit ! swap 1 max dup heap-claim
  if swap rot reader-buffer! outcome-ok else 2drop outcome-full then ;
\ Free the buffer and zero the record; the caller closes the file first.
: reader-free ( reader -- ) dup reader-release /reader erase ;

\ Start reading an open file from its current position.
: reader-attach ( fid reader -- ) tuck reader-fid ! reader-start /reader-progress erase ;
\ Open a file by name for reading; invalid when it cannot be opened.
: reader-open ( c-addr u reader -- outcome )
  >r r/o bin open-file
  if drop r> drop outcome-invalid else r> reader-attach outcome-ok then ;
\ Close the file; invalid when the host reports an error.
: reader-close ( reader -- outcome )
  dup reader-fid @ swap 0 swap reader-fid ! ?dup 0= if outcome-ok exit then
  close-file 0= flag>outcome ;

\ The rest of addr u from the first byte char on, empty when there is none:
\ Gforth's native SCAN where available (much faster), otherwise the
\ portable loop, which is always defined so tests can compare the two.
: byte-scan-portable ( addr u char -- addr' u' )
  >r begin dup while over c@ r@ <> while 1 /string repeat then r> drop ;
s" gforth" environment? [if] 2drop
: byte-scan ( addr u char -- addr' u' ) scan ;
[else]
: byte-scan ( addr u char -- addr' u' ) byte-scan-portable ;
[then]
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

\ Taking a line: remember where it starts, then step past it and its line feed.
: reader-mark ( reader -- )
  >r r@ reader-base 2@ r@ reader-start @ m+ r@ reader-at 2! 1 r> reader-lines +! ;
: reader-skip ( n reader -- ) swap 1+ swap reader-start +! ;
: reader-take ( n reader -- addr n )
  dup reader-mark dup reader-unread drop -rot over swap reader-skip ;

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
\ Read more bytes after the unread ones; no bytes at all means the end.
: reader-got ( u reader -- )
  over 0= if nip true swap reader-eof ! else reader-end +! then ;
: reader-read ( reader -- outcome )
  >r r@ reader-room r@ reader-fid @ read-file
  if drop r> drop outcome-invalid else r> reader-got outcome-ok then ;
: reader-fill ( reader -- outcome )
  dup reader-shift dup reader-make-room ok-then? if reader-read then ;

\ No line feed among the unread bytes: read more, unless the line is
\ already too long (full) or the file has ended (invalid: the last
\ line lacks its line feed, or there is no line left).
: reader-wait ( reader -- outcome )
  dup reader-unread nip over reader-limit @ > if drop outcome-full exit then
  dup reader-eof @ if drop outcome-invalid exit then reader-fill ;
: reader-found ( n reader -- addr u outcome )
  2dup reader-limit @ > if 2drop 0 0 outcome-full else reader-take outcome-ok then ;

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

\ Compile a counted string of at most 255 bytes into the dictionary, then
\ align; a longer one aborts. For tables of names built while loading.
: counted, ( c-addr u -- )
  dup 255 > abort" counted, string too long" dup c, here swap dup allot move align ;
\ The address after a counted string counted, laid down: the next one of a
\ table of them.
: counted-next ( c-addr -- c-addr' ) count + aligned ;
\ Compile text of any length as a cell-counted string (its length in a
\ cell, then its bytes), then align: for tables of names and messages
\ built while loading; bounds.fs's cell-count reads one back.
: cell-counted, ( c-addr u -- ) dup , here swap dup allot move align ;
\ The text of a counted string, or empty text for 0 (an absent string: a
\ table entry, a field name or a reason not given).
: counted-or-empty ( c-addr|0 -- c-addr u ) ?dup if count else s" " then ;

\ Strict framing of one line: no carriage return anywhere (so no CRLF
\ line ends) and no UTF-8 byte-order mark at its start. UTF-8 validity is
\ left to the caller: utf8-valid? checks a whole line, and json.fs checks
\ it inside strings while allowing only ASCII outside them.
: bom? ( addr u -- flag ) 3 min s\" \xEF\xBB\xBF" compare 0= ;
: text-framed ( addr u -- outcome )
  2dup bom? if 2drop outcome-invalid else cr-byte byte-scan nip 0= flag>outcome then ;

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

\ Decoding the valid sequence of n bytes at addr (n as utf8-length gave
\ it, 1 to 4) into its code point: the lead byte's low bits, then six
\ bits of each byte after it.
\   s\" \xe2\x80\xae" drop 3 utf8-decode   \ $202E
: utf8-mask ( n -- mask )
  case 1 of $7f endof 2 of $1f endof 3 of $0f endof $07 swap endcase ;
: utf8-lead ( addr n -- bits ) swap c@ swap utf8-mask and ;
: utf8-tail-bits ( u addr -- u' ) c@ $3f and swap 6 lshift or ;
: utf8-decode ( addr n -- u )
  2dup utf8-lead -rot chars over + swap char+ ?do i utf8-tail-bits loop ;

\ Encoding a code point u (at most $10FFFF and not a surrogate; the caller
\ checks) as 1 to 4 bytes at addr.
: utf8-size ( u -- n )
  dup $80 < if drop 1 exit then dup $800 < if drop 2 exit then $10000 < if 3 else 4 then ;
: utf8-prefix ( n -- bits ) dup 1 = if drop 0 else $ff00 swap rshift $ff and then ;
: utf8-tail-byte ( u shift -- byte ) rshift $3f and $80 or ;
\ Continuation bytes, written backwards from end, the address after the last.
: utf8-put-tail ( u end n -- )
  1 ?do 2dup swap i 1- 6 * utf8-tail-byte swap i - c! loop 2drop ;
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

base !   \ the BASE this file was loaded with (not reached when loading throws)
