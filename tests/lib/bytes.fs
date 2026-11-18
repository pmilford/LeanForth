\ Unit tests of src/lib/bytes.fs: UTF-8 checks and encoding against an
\ independent model, byte scanning, strict framing, counted strings, and
\ the line reader on repository fixtures (growth, limits, positions, end).
\ File-level framing failures (no final line feed, carriage returns) are
\ tested on temporary files by tests/core/test_ndjson_reader.py.
\ The module is loaded under HEX (and the heap watched): its numbers must
\ not depend on BASE, and it must leave BASE as it found it.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
hex require ../../src/lib/bytes.fs base @ decimal constant base-after-load
lf-lib-private order+   \ the tests reach helpers (ADR 0010)

T{ base-after-load lf-byte cr-byte -> 16 10 13 }T

\ A scratch buffer for byte sequences.
create bytes 64 allot
: b! ( c i -- ) bytes + c! ;
: bytes4 ( b0 b1 b2 b3 -- addr ) 3 b! 2 b! 1 b! 0 b! bytes ;

\ utf8-length on single cases: each sequence length and its boundaries.
T{ s\" a" utf8-length -> 1 }T
T{ s\" \x7f" utf8-length -> 1 }T
T{ s\" \xc2\x80" utf8-length -> 2 }T
T{ s\" \xdf\xbf" utf8-length -> 2 }T
T{ s\" \xe0\xa0\x80" utf8-length -> 3 }T
T{ s\" \xed\x9f\xbf" utf8-length -> 3 }T
T{ s\" \xee\x80\x80" utf8-length -> 3 }T
T{ s\" \xef\xbf\xbf" utf8-length -> 3 }T
T{ s\" \xf0\x90\x80\x80" utf8-length -> 4 }T
T{ s\" \xf4\x8f\xbf\xbf" utf8-length -> 4 }T
\ Not a sequence: continuation bytes, overlong forms, surrogates, beyond
\ U+10FFFF, bytes that never occur, truncation and bad continuations.
T{ s\" \x80" utf8-length -> 0 }T
T{ s\" \xbf" utf8-length -> 0 }T
T{ s\" \xc0\xaf" utf8-length -> 0 }T
T{ s\" \xc1\xbf" utf8-length -> 0 }T
T{ s\" \xe0\x9f\xbf" utf8-length -> 0 }T
T{ s\" \xed\xa0\x80" utf8-length -> 0 }T
T{ s\" \xed\xbf\xbf" utf8-length -> 0 }T
T{ s\" \xf0\x8f\xbf\xbf" utf8-length -> 0 }T
T{ s\" \xf4\x90\x80\x80" utf8-length -> 0 }T
T{ s\" \xf5\x80\x80\x80" utf8-length -> 0 }T
T{ s\" \xfe" utf8-length -> 0 }T
T{ s\" \xff" utf8-length -> 0 }T
T{ s\" \xc2" utf8-length -> 0 }T
T{ s\" \xe2\x82" utf8-length -> 0 }T
T{ s\" \xf0\x9f\x98" utf8-length -> 0 }T
T{ s\" \xc2\x41" utf8-length -> 0 }T
T{ s\" \xe2\x82\x41" utf8-length -> 0 }T
T{ s\" \xf0\x9f\x98\x41" utf8-length -> 0 }T
T{ s" " utf8-length -> 0 }T
T{ s\" \xc2\x80" drop 1 utf8-length -> 0 }T
T{ s\" \xc2\x80" ' utf8-length rs-checked -> 2 }T

\ An independent model: decode the code point and check it is in range
\ and not encodable in fewer bytes.
: model-size ( b0 -- n )
  dup $80 < if drop 1 exit then dup $c0 $df between? if drop 2 exit then
  dup $e0 $ef between? if drop 3 exit then $f0 $f7 between? if 4 else 0 then ;
: model-lead-bits ( b0 n -- bits )
  case 1 of endof 2 of $1f and endof 3 of $0f and endof swap $07 and swap endcase ;
: model-cont? ( addr n -- flag ) true swap 1 ?do over i + c@ $c0 and $80 = and loop nip ;
: model-code ( addr n -- code )
  over c@ over model-lead-bits swap 1 ?do 6 lshift over i + c@ $3f and or loop nip ;
: model-least ( n -- code ) case 1 of 0 endof 2 of $80 endof 3 of $800 endof $10000 swap endcase ;
: model-ok? ( code n -- flag )
  model-least over <= over $10ffff <= and swap $d800 $dfff between? 0= and ;
: model-length ( addr u -- n )
  dup 0= if nip exit then over c@ model-size dup 0= if nip nip exit then tuck < if 2drop 0 exit then
  2dup model-cont? 0= if 2drop 0 exit then tuck model-code over model-ok? and ;

\ Every first and second byte, with representative third and fourth bytes
\ and every length u from 1 to 4, against the model.
variable mismatches
create thirds $80 c, $bf c, $7f c, $c0 c,
create fourths $80 c, $bf c, $41 c,
: compare-u ( addr -- ) 5 1 do dup i utf8-length over i model-length <> if 1 mismatches +! then loop drop ;
: sweep-tail ( b0 b1 -- )
  4 0 do 3 0 do 2dup thirds j + c@ fourths i + c@ bytes4 compare-u loop loop 2drop ;
: sweep ( -- ) 0 mismatches ! 256 0 do 256 0 do j i sweep-tail loop loop ;
T{ sweep mismatches @ -> 0 }T

\ utf8-valid? over whole strings.
T{ s\" plain ascii" utf8-valid? -> true }T
T{ s\" caf\xc3\xa9 \xe2\x82\xac \xf0\x9f\x98\x80" utf8-valid? -> true }T
T{ s" " utf8-valid? -> true }T
T{ s\" ok\x80" utf8-valid? -> false }T
T{ s\" \xe2\x82" utf8-valid? -> false }T
T{ s\" a\xed\xa0\x80b" utf8-valid? -> false }T

\ utf8-size, utf8-put: sizes at the boundaries, and every encoding round
\ trips through utf8-length and the model's decoder.
T{ 0 utf8-size $7f utf8-size $80 utf8-size $7ff utf8-size -> 1 1 2 2 }T
T{ $800 utf8-size $ffff utf8-size $10000 utf8-size $10ffff utf8-size -> 3 3 4 4 }T
: round-trip? ( code -- flag )
  dup bytes utf8-put dup >r over utf8-size = bytes r@ utf8-length r@ = and
  bytes r> model-code rot = and ;
create codes 0 , $41 , $7f , $80 , $e9 , $7ff , $800 , $d7ff , $e000 , $fffd , $ffff ,
  $10000 , $1f600 , $10ffff ,
: all-round-trip? ( -- flag ) true 14 0 do codes i cells + @ round-trip? and loop ;
T{ all-round-trip? -> true }T
T{ $e9 bytes utf8-put bytes c@ bytes 1+ c@ -> 2 $c3 $a9 }T
T{ $1f600 bytes utf8-put bytes 3 + c@ -> 4 $80 }T
\ utf8-decode gives back every code point encoded, as the model does.
: decodes? ( code -- flag ) dup bytes utf8-put bytes swap utf8-decode = ;
: all-decode? ( -- flag ) true 14 0 do codes i cells + @ decodes? and loop ;
T{ all-decode? s\" \xe2\x80\xae" drop 3 utf8-decode -> true $202e }T

\ byte-scan agrees with the portable loop; lf-index finds the first line feed.
T{ s" abcabc" char c byte-scan nip -> 4 }T
T{ s" abcabc" char z byte-scan nip -> 0 }T
T{ s" " char a byte-scan nip -> 0 }T
T{ s" abcabc" char c byte-scan-portable nip s" abcabc" char c byte-scan nip -> 4 4 }T
: scans-agree? ( addr u -- flag )
  true -rot 256 0 do 2dup i byte-scan 2over i byte-scan-portable d= >r rot r> and -rot loop 2drop ;
T{ s\" a\nb\x00\xff\r\tz" scans-agree? -> true }T
T{ s\" one\ntwo\n" lf-index -> 3 true }T
T{ s\" \nx" lf-index -> 0 true }T
T{ s" no line feed" lf-index -> false }T
T{ s" " lf-index -> false }T

\ Strict framing: no carriage return, no byte-order mark at the start.
T{ s" {}" text-framed -> outcome-ok }T
T{ s" " text-framed -> outcome-ok }T
T{ s\" {}\r" text-framed -> outcome-invalid }T
T{ s\" a\rb" text-framed -> outcome-invalid }T
T{ s\" \xef\xbb\xbf{}" text-framed -> outcome-invalid }T
T{ s\" \xef\xbb" text-framed -> outcome-ok }T
T{ s\" x\xef\xbb\xbf" text-framed -> outcome-ok }T
T{ s\" \xef\xbb\xbf" bom? s\" \xef\xbb\xbe" bom? -> true false }T

\ counted, compiles a counted string and aligns; 255 bytes at most.
create greeting s" hello" counted,
T{ greeting count s" hello" compare -> 0 }T
T{ here aligned here = -> true }T
create long-name 256 allot
T{ long-name 255 counted, here aligned here = -> true }T
T{ long-name 256 ' counted, catch nip nip -> -2 }T
\ counted-next steps from one counted string of a table to the next.
create two-names s" ab" counted, s" " counted, s" xyz" counted,  here constant names-end
T{ two-names counted-next count s" " compare -> 0 }T
T{ two-names counted-next counted-next count s" xyz" compare -> 0 }T
T{ two-names counted-next counted-next counted-next names-end = -> true }T
\ counted-or-empty (reuse-out-2): a counted string's text, empty for 0.
T{ greeting counted-or-empty s" hello" compare 0 counted-or-empty nip -> 0 0 }T
T{ 0 ' counted-or-empty rs-checked nip -> 0 }T
\ cell-counted, (reuse-out-2): the length in a cell, any length, aligned;
\ bounds.fs's cell-count reads it back.
create cell-texts s" ab" cell-counted, s" " cell-counted, long-name 256 cell-counted,
T{ cell-texts cell-count s" ab" compare here aligned here = -> 0 true }T
T{ cell-texts cell-count + aligned cell-count nip -> 0 }T
T{ cell-texts cell-count + aligned cell-count + aligned cell-count nip -> 256 }T

\ The line reader on fixtures. composition.ndjson: 35 lines, 1,787 bytes,
\ the longest (the metadata, line 1) 172 bytes.
reader: rd
: fixture ( -- c-addr u ) s" tests/reference/composition.ndjson" ;
variable lines-read  variable bytes-read  variable offsets-ok
: line-seen ( u -- ) 1+ bytes-read +! 1 lines-read +! ;
\ Offsets: each line starts where the bytes before it end.
: offset-check ( -- ) rd reader-position drop bytes-read @ 0 d= offsets-ok @ and offsets-ok ! ;
: read-all ( -- outcome )
  0 lines-read ! 0 bytes-read ! true offsets-ok !
  begin rd reader-more? while
    rd reader-line ok-then? 0= if nip exit then offset-check nip line-seen
  repeat outcome-ok ;
: open-with ( size limit -- outcome ) rd reader-init drop fixture rd reader-open ;
: finish ( -- ) rd reader-close drop rd reader-free ;
\ A buffer far smaller than a line grows; every line and byte is read.
T{ 8 4096 open-with -> outcome-ok }T
T{ read-all lines-read @ bytes-read @ offsets-ok @ -> outcome-ok 35 1787 true }T
T{ rd reader-position nip nip -> 35 }T
T{ rd reader-more? -> false }T
T{ rd reader-line -> 0 0 outcome-invalid }T
T{ finish -> }T
\ A buffer larger than the file.
T{ 65536 4096 open-with read-all lines-read @ -> outcome-ok outcome-ok 35 }T
T{ finish -> }T
\ The limit is inclusive: 172 bytes pass, 171 bytes are full at line 1.
T{ 16 172 open-with read-all lines-read @ -> outcome-ok outcome-ok 35 }T
T{ finish -> }T
T{ 16 171 open-with read-all lines-read @ -> outcome-ok outcome-full 0 }T
T{ finish -> }T
T{ 4096 171 open-with read-all lines-read @ -> outcome-ok outcome-full 0 }T
T{ finish -> }T
\ A missing file is invalid; closing a closed reader is harmless.
T{ 16 16 rd reader-init s" tests/reference/no-such-file.ndjson" rd reader-open -> outcome-ok outcome-invalid }T
T{ rd reader-close rd reader-close -> outcome-ok outcome-ok }T
T{ rd reader-free rd reader-buffer @ -> 0 }T
\ The first line, read through a two-byte buffer.
T{ 2 4096 open-with -> outcome-ok }T
T{ rd reader-line rot drop -> 172 outcome-ok }T
T{ rd reader-line drop 9 min s\" {\"in\":1,\"" compare -> 0 }T
T{ rd reader-position -> 173 0 2 }T
T{ finish -> }T
T{ 8 64 rd ' reader-init rs-checked -> outcome-ok }T
T{ finish -> }T
\ reader-init again frees the earlier buffer first, and reader-free the
\ last: the heap holds exactly as many blocks as before.
variable blocks-before  variable first-buffer
T{ live-blocks @ blocks-before ! 16 16 rd reader-init rd reader-buffer @ first-buffer !
   live-blocks @ blocks-before @ - -> outcome-ok 1 }T
T{ 32 16 rd reader-init rd reader-size @ last-freed @ first-buffer @ =
   live-blocks @ blocks-before @ - -> outcome-ok 32 true 1 }T
T{ rd reader-buffer @ finish rd reader-size @ swap last-freed @ =
   live-blocks @ blocks-before @ - -> 0 true 0 }T
\ heap-claim and heap-release: freeing an empty cell is harmless.
variable claimed
T{ 16 heap-claim swap claimed ! -> true }T
T{ claimed heap-release claimed @ claimed heap-release claimed @ -> 0 0 }T

\ Rules. reader-rules.txt is a byte-order mark, "ab" CR LF, CR LF, a mark and "c" LF
\ and "d" CR without a line feed (16 bytes); reader-noeol.txt is "abcd".
\ The composition fixture reads the same under every rule (above: rules
\ 0 of a zeroed reader).
: rules-file ( -- c-addr u ) s" tests/lib/reader-rules.txt" ;
: open-rules ( rules size limit -- outcome )
  rd reader-init drop rd reader-rules! rules-file rd reader-open ;
: next= ( c-addr u -- flag ) rd reader-line ok? >r compare 0= r> and ;
T{ rd reader-free rd reader-rules @ -> 0 }T
T{ reader-text reader-strict reader-final-lf reader-keep-cr or reader-keep-bom or = -> 0 true }T
\ Ordinary text: the mark, each carriage return before a line feed and
\ the one ending the last line are dropped; the last line is a line.
T{ reader-text 4 64 open-rules -> outcome-ok }T
T{ s" ab" next= s" " next= s\" \xef\xbb\xbfc" next= rd reader-more? s" d" next= -> true true true true true }T
T{ rd reader-position -> 14 0 4 }T
T{ rd reader-more? rd reader-line -> false 0 0 outcome-invalid }T
T{ finish -> }T
\ Strict (Lean's exports): everything stays, and the last line is invalid.
T{ reader-strict 4 64 open-rules -> outcome-ok }T
T{ s\" \xef\xbb\xbfab\r" next= s\" \r" next= s\" \xef\xbb\xbfc" next= rd reader-more? -> true true true true }T
T{ rd reader-line -> 0 0 outcome-invalid }T
T{ finish -> }T
\ One bit at a time.
T{ reader-final-lf 4 64 open-rules -> outcome-ok }T
T{ s" ab" next= s" " next= s\" \xef\xbb\xbfc" next= rd reader-line -> true true true 0 0 outcome-invalid }T
T{ finish -> }T
T{ reader-keep-cr 4 64 open-rules -> outcome-ok }T
T{ s\" ab\r" next= s\" \r" next= s\" \xef\xbb\xbfc" next= s\" d\r" next= -> true true true true }T
T{ finish -> }T
T{ reader-keep-bom 4 64 open-rules -> outcome-ok }T
T{ s\" \xef\xbb\xbfab" next= s" " next= -> true true }T
T{ finish -> }T
\ A dropped byte counts in the limit: the first line is 6 bytes.
T{ reader-text 4 6 open-rules -> outcome-ok }T
T{ s" ab" next= -> true }T
T{ finish -> }T
T{ reader-text 4 5 open-rules -> outcome-ok }T
T{ rd reader-line -> 0 0 outcome-full }T
T{ finish -> }T
\ The rules survive reader-init and reader-open; reader-free clears them.
T{ reader-strict 4 64 open-rules finish -> outcome-ok }T
T{ 4 64 rd reader-init rules-file rd reader-open rd reader-rules @ -> outcome-ok outcome-ok 0 }T
T{ finish reader-keep-cr rd reader-rules! 4 64 rd reader-init rd reader-rules @ -> outcome-ok reader-keep-cr }T
T{ finish -> }T
\ A last line that fills the buffer: the line feed it is given grows it
\ (a buffer of 4 for "abcd", limit 4), or is full at the limit's end.
: open-noeol ( size limit -- outcome )
  rd reader-init drop s" tests/lib/reader-noeol.txt" rd reader-open ;
T{ 4 4 open-noeol s" abcd" next= rd reader-more? -> outcome-ok true false }T
T{ finish -> }T
T{ 1 4 open-noeol s" abcd" next= -> outcome-ok true }T
T{ finish -> }T
T{ 4 3 open-noeol rd reader-line -> outcome-ok 0 0 outcome-full }T
T{ finish -> }T
T{ reader-strict rd reader-rules! 4 4 open-noeol rd reader-line -> outcome-ok 0 0 outcome-invalid }T
T{ finish -> }T

\ FNV-style mixing: one step is h xor x, times 16777619, modulo the cell;
\ bytes-mix takes the bytes one at a time, in order, with that step.
T{ 0 0 fnv-step 1 0 fnv-step 0 1 fnv-step 3 3 fnv-step -> 0 16777619 16777619 0 }T
T{ 2 1 fnv-step 3 16777619 * = -> true }T
T{ 5 s" ab" bytes-mix 5 char a fnv-step char b fnv-step = -> true }T
T{ 5 s" ab" bytes-mix 5 s" ba" bytes-mix = 7 pad 0 bytes-mix -> false 7 }T

cases-done
bye
