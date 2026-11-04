\ Unit tests of src/lib/json-write.fs: every word's positive and negative
\ cases, sticky failures and the sink rules, every limit at and one past
\ its bound, sorted keys, independent writers and a writer as a context
\ member, a randomized round trip through src/lib/json.fs, jw-copy (also
\ 10,000 containers deep), and the NDJSON corpus copied back byte for
\ byte. The module is loaded under
\ HEX: its numbers must not depend on BASE, and it must leave BASE as it
\ found it; some writes also run under HEX.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/json-write.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T
T{ jw-scratch-size cell-digits 2 + aligned = jw-longest max-n 4 - 6 / = -> true true }T
T{ jw-most max-n /jw-header - = -> true }T

\ The test sink appends to a buffer, large enough for 10,000 nested arrays.
32768 constant sunk-size
create sunk sunk-size allot  variable sunk-length
: to-sunk ( c-addr u -- )
  dup sunk-length @ + sunk-size > abort" test sink overflow"
  tuck sunk sunk-length @ + swap move sunk-length +! ;
: output ( -- c-addr u ) sunk sunk-length @ ;
8 64 json-writer: w
: start ( -- ) 0 sunk-length ! ['] to-sunk w jw-start ;
\ End the text: its outcome, and whether the sink got exactly c-addr u.
: wrote= ( c-addr u -- outcome flag ) w jw-end -rot output compare 0= ;
\ Independent decimal text, through BASE and pictured output.
: dec-n ( n -- c-addr u ) base @ >r decimal dup abs 0 <# #s rot sign #> r> base ! ;
: dec-u ( u -- c-addr u ) base @ >r decimal 0 <# #s #> r> base ! ;
max-n invert constant min-n

\ Planning and making writers.
T{ 0 0 jw-plan? 8 64 jw-plan? -1 0 jw-plan? 0 -1 jw-plan? -> true true false false }T
T{ 0 jw-most jw-plan? 0 jw-most 1+ jw-plan? max-n 0 jw-plan? -> true false false }T
T{ jw-most /jw-nest / 0 jw-plan? jw-most /jw-nest / 1+ 0 jw-plan? -> true false }T
T{ 8 64 jw-size /jw-header 8 /jw-nest * + 64 + = -> true }T
create probe 512 allot
: probe-x ( -- ) probe 512 [char] x fill ;
: probe-untouched? ( -- flag ) true 512 0 do probe i + c@ [char] x = and loop ;
T{ probe-x -1 4 probe jw-init probe-untouched? 2 -1 probe jw-init probe-untouched? -> false true false true }T
T{ probe-x 2 4 probe jw-init probe jw-state @ probe jw-outcome probe jw-limit @ probe jw-sorted @
   -> true jw-idle outcome-ok max-n false }T
T{ probe jw-capacity @ probe jw-room @ probe jw-depth @ probe jw-written @ -> 2 4 0 0 }T
T{ 2 4 jw-size 512 < -> true }T
T{ s" -1 0 json-writer: bad-writer" ' evaluate catch nip nip -> -2 }T
T{ s" 0 -1 json-writer: bad-writer" ' evaluate catch nip nip -> -2 }T
T{ s" bad-writer" find-name -> 0 }T

\ An idle writer refuses every write; jw-end on it is invalid.
T{ 0 sunk-length ! 5 w jw-n w jw-outcome sunk-length @ w jw-end -> outcome-invalid 0 outcome-invalid }T
T{ ' to-sunk probe jw-start 5 probe jw-n probe jw-end -> outcome-ok }T

\ Integers, in decimal whatever BASE is.
T{ start 0 w jw-n s" 0" wrote= -> outcome-ok true }T
T{ start -12 w jw-n s" -12" wrote= -> outcome-ok true }T
T{ start max-n w jw-n max-n dec-n wrote= -> outcome-ok true }T
T{ start min-n w jw-n min-n dec-n wrote= -> outcome-ok true }T
T{ start 0 w jw-u s" 0" wrote= -> outcome-ok true }T
T{ start -1 w jw-u -1 dec-u wrote= -> outcome-ok true }T
T{ start min-n w jw-u min-n dec-u wrote= -> outcome-ok true }T
T{ start #10 hex w jw-n decimal s" 10" wrote= -> outcome-ok true }T
T{ start #-255 2 base ! w jw-n decimal s" -255" wrote= -> outcome-ok true }T
T{ start -1 hex w jw-u decimal -1 dec-u wrote= -> outcome-ok true }T
T{ -1 dec-u nip max-n dec-n nip - 0 1 between? -> true }T
\ Digit strings: an optional minus sign, then 0 or digits without a
\ leading zero, of any size; -0 is written 0.
T{ start s" 0" w jw-digits s" 0" wrote= -> outcome-ok true }T
T{ start s" -0" w jw-digits s" 0" wrote= -> outcome-ok true }T
T{ start s" -7" w jw-digits s" -7" wrote= -> outcome-ok true }T
: big ( -- c-addr u ) s" 123456789012345678901234567890123456789" ;
T{ start big w jw-digits big wrote= -> outcome-ok true }T
T{ start s" -98765432109876543210" w jw-digits s" -98765432109876543210" wrote= -> outcome-ok true }T
: bad-digits ( c-addr u -- outcome n ) start w jw-digits w jw-end sunk-length @ ;
T{ s" " bad-digits s" -" bad-digits s" 01" bad-digits s" -01" bad-digits
   -> outcome-invalid 0 outcome-invalid 0 outcome-invalid 0 outcome-invalid 0 }T
T{ s" +1" bad-digits s" 1.5" bad-digits s" 1e3" bad-digits s"  1" bad-digits
   -> outcome-invalid 0 outcome-invalid 0 outcome-invalid 0 outcome-invalid 0 }T
T{ s" 1a" bad-digits s" --1" bad-digits s" -00" bad-digits s" 1 " bad-digits
   -> outcome-invalid 0 outcome-invalid 0 outcome-invalid 0 outcome-invalid 0 }T

\ Literals.
T{ start true w jw-bool s" true" wrote= -> outcome-ok true }T
T{ start false w jw-bool s" false" wrote= -> outcome-ok true }T
T{ start w jw-null s" null" wrote= -> outcome-ok true }T
T{ start 1 w jw-bool w jw-end sunk-length @ -> outcome-invalid 0 }T
T{ start 5 w jw-bool w jw-end sunk-length @ -> outcome-invalid 0 }T

\ Strings: the canonical escapes, everything else as itself.
T{ start s" " w jw-string s\" \"\"" wrote= -> outcome-ok true }T
T{ start s" abc" w jw-string s\" \"abc\"" wrote= -> outcome-ok true }T
T{ start s\" \"\\/\x7f" w jw-string s\" \"\\\"\\\\/\x7f\"" wrote= -> outcome-ok true }T
T{ start s\" caf\xc3\xa9 \xe2\x82\xac \xf0\x9f\x98\x80 \xf4\x8f\xbf\xbf" w jw-string
   s\" \"caf\xc3\xa9 \xe2\x82\xac \xf0\x9f\x98\x80 \xf4\x8f\xbf\xbf\"" wrote= -> outcome-ok true }T
\ Every byte below 32, in order.
create controls 32 allot
: controls! ( -- ) 32 0 do i controls i + c! loop ;
controls!
: controls-1 ( -- c-addr u )
  s\" \"\\u0000\\u0001\\u0002\\u0003\\u0004\\u0005\\u0006\\u0007\\b\\t\\n\\u000b\\f\\r" ;
: controls-2 ( -- c-addr u )
  s\" \\u000e\\u000f\\u0010\\u0011\\u0012\\u0013\\u0014\\u0015\\u0016\\u0017\\u0018\\u0019" ;
: controls-3 ( -- c-addr u ) s\" \\u001a\\u001b\\u001c\\u001d\\u001e\\u001f\"" ;
create expected 512 allot  variable expected-length
: +expected ( c-addr u -- ) tuck expected expected-length @ + swap move expected-length +! ;
: expected-controls ( -- c-addr u )
  0 expected-length ! controls-1 +expected controls-2 +expected controls-3 +expected
  expected expected-length @ ;
T{ start controls 32 w jw-string expected-controls wrote= -> outcome-ok true }T
T{ start controls 32 hex w jw-string decimal expected-controls wrote= -> outcome-ok true }T
T{ start s\"  ~\x1f" w jw-string s\" \" ~\\u001f\"" wrote= -> outcome-ok true }T
\ Invalid UTF-8 is refused and never written, not even the comma before it.
: bad-string ( c-addr u -- outcome n ) start w jw-string w jw-end sunk-length @ ;
T{ s\" \x80" bad-string s\" \xc0\xaf" bad-string s\" \xed\xa0\x80" bad-string
   -> outcome-invalid 0 outcome-invalid 0 outcome-invalid 0 }T
T{ s\" \xe2\x82" bad-string s\" \xf4\x90\x80\x80" bad-string s\" \xff" bad-string
   -> outcome-invalid 0 outcome-invalid 0 outcome-invalid 0 }T
T{ s\" ab\xc3" bad-string s\" \xf8\x88\x80\x80\x80" bad-string -> outcome-invalid 0 outcome-invalid 0 }T
T{ start w jw-open-array 1 w jw-n s\" ok\x80" w jw-string 2 w jw-n w jw-close-array
   s" [1" wrote= -> outcome-invalid true }T
\ A string longer than jw-longest is full, before any byte is read.
T{ start sunk jw-longest 1+ w jw-string w jw-end sunk-length @ -> outcome-full 0 }T
T{ start sunk -1 w jw-string w jw-end sunk-length @ -> outcome-full 0 }T

\ Containers, commas and colons.
T{ start w jw-open-array w jw-close-array s" []" wrote= -> outcome-ok true }T
T{ start w jw-open-object w jw-close-object s" {}" wrote= -> outcome-ok true }T
: sample ( -- )
  w jw-open-object s" a" w jw-key 1 w jw-n s" b" w jw-key w jw-open-array 2 w jw-n
  w jw-open-object w jw-close-object w jw-null w jw-close-array s" c" w jw-key
  w jw-open-object s" d" w jw-key s" e" w jw-string w jw-close-object w jw-close-object ;
: sample-text ( -- c-addr u ) s\" {\"a\":1,\"b\":[2,{},null],\"c\":{\"d\":\"e\"}}" ;
T{ start sample sample-text wrote= -> outcome-ok true }T
T{ start hex sample decimal sample-text wrote= -> outcome-ok true }T
T{ start w jw-open-array w jw-open-array w jw-close-array w jw-open-array w jw-close-array
   w jw-close-array s" [[],[]]" wrote= -> outcome-ok true }T
T{ start w jw-open-object s\" k\"\n" w jw-key 0 w jw-n w jw-close-object
   s\" {\"k\\\"\\n\":0}" wrote= -> outcome-ok true }T
\ Calls sunk of order are invalid; the text keeps the prefix written before.
T{ start s" a" w jw-key s" " wrote= -> outcome-invalid true }T
T{ start w jw-open-array s" a" w jw-key s" [" wrote= -> outcome-invalid true }T
T{ start w jw-open-object 1 w jw-n s" {" wrote= -> outcome-invalid true }T
T{ start w jw-open-object s" a" w jw-key s" b" w jw-key s\" {\"a\":" wrote= -> outcome-invalid true }T
T{ start w jw-open-object s" a" w jw-key w jw-close-object s\" {\"a\":" wrote= -> outcome-invalid true }T
T{ start w jw-open-object w jw-close-array s" {" wrote= -> outcome-invalid true }T
T{ start w jw-open-array w jw-close-object s" [" wrote= -> outcome-invalid true }T
T{ start w jw-close-array s" " wrote= -> outcome-invalid true }T
T{ start 1 w jw-n w jw-close-object s" 1" wrote= -> outcome-invalid true }T
T{ start 1 w jw-n 2 w jw-n s" 1" wrote= -> outcome-invalid true }T
T{ start w jw-open-object w jw-close-object w jw-open-array s" {}" wrote= -> outcome-invalid true }T
\ jw-end before the value is complete, or twice, or a write after it.
T{ start s" " wrote= -> outcome-invalid true }T
T{ start w jw-open-array s" [" wrote= -> outcome-invalid true }T
T{ start w jw-open-object s" a" w jw-key s\" {\"a\":" wrote= -> outcome-invalid true }T
T{ start 1 w jw-n w jw-end w jw-end -> outcome-ok outcome-invalid }T
T{ start 1 w jw-n w jw-end 2 w jw-n w jw-outcome output s" 1" compare -> outcome-ok outcome-invalid 0 }T
\ Failure is sticky until jw-start; the first failure wins.
T{ start w jw-open-array s" a" w jw-key 1 w jw-n w jw-close-array s" [" wrote= -> outcome-invalid true }T
T{ start sunk -1 w jw-string s" a" w jw-key w jw-outcome -> outcome-full }T
T{ start sunk -1 w jw-string 5 w jw-bool s" 01" w jw-digits w jw-outcome -> outcome-full }T
T{ start 5 w jw-bool sunk -1 w jw-string w jw-reset w jw-outcome -> outcome-invalid }T
T{ start 3 w jw-n s" 3" wrote= -> outcome-ok true }T
\ jw-reset makes the writer idle with outcome invalid; a text that had
\ already failed keeps its first failure.
T{ start w jw-reset 1 w jw-n w jw-end sunk-length @ -> outcome-invalid 0 }T
T{ start sunk -1 w jw-string w jw-reset w jw-outcome w jw-state @
   -> outcome-full jw-idle }T

\ Nesting is bounded by the writer's depth: 8 here.
: opens ( n -- ) 0 ?do w jw-open-array loop ;
: closes ( n -- ) 0 ?do w jw-close-array loop ;
T{ start 8 opens 8 closes s" [[[[[[[[]]]]]]]]" wrote= -> outcome-ok true }T
T{ start 9 opens 9 closes w jw-end output nip -> outcome-full 8 }T
T{ start 8 opens 8 closes w jw-depth @ 8 opens w jw-depth @ -> 0 0 }T
0 0 json-writer: flat
T{ 0 sunk-length ! ' to-sunk flat jw-start 7 flat jw-n flat jw-end output s" 7" compare -> outcome-ok 0 }T
T{ 0 sunk-length ! ' to-sunk flat jw-start flat jw-open-array flat jw-end sunk-length @ -> outcome-full 0 }T

\ The byte limit: a text of exactly jw-limit bytes is ok; one byte more is
\ full, and nothing of the value that does not fit is written.
: limited ( n -- ) w jw-limit ! start ;
: unlimited ( -- ) max-n w jw-limit ! ;
T{ 4 limited s" ab" w jw-string s\" \"ab\"" wrote= -> outcome-ok true }T
T{ 3 limited s" ab" w jw-string s" " wrote= -> outcome-full true }T
T{ 4 limited s\" \n" w jw-string s\" \"\\n\"" wrote= -> outcome-ok true }T
T{ 3 limited s\" \n" w jw-string s" " wrote= -> outcome-full true }T
T{ 8 limited s\" \x01" w jw-string s\" \"\\u0001\"" wrote= -> outcome-ok true }T
T{ 7 limited s\" \x01" w jw-string s" " wrote= -> outcome-full true }T
T{ 5 limited w jw-open-array 1 w jw-n 2 w jw-n w jw-close-array s" [1,2]" wrote= -> outcome-ok true }T
T{ 4 limited w jw-open-array 1 w jw-n 2 w jw-n w jw-close-array s" [1,2" wrote= -> outcome-full true }T
T{ 3 limited w jw-open-array 1 w jw-n 2 w jw-n w jw-close-array s" [1" wrote= -> outcome-full true }T
: one-member ( -- ) w jw-open-object s" a" w jw-key 1 w jw-n w jw-close-object ;
T{ 7 limited one-member s\" {\"a\":1}" wrote= -> outcome-ok true }T
T{ 6 limited one-member s\" {\"a\":1" wrote= -> outcome-full true }T
T{ 4 limited one-member s" {" wrote= -> outcome-full true }T
T{ 5 limited one-member s\" {\"a\":" wrote= -> outcome-full true }T
T{ 2 limited -12 w jw-n s" " wrote= -> outcome-full true }T
T{ 0 limited w jw-open-array s" " wrote= -> outcome-full true }T
T{ -1 limited w jw-null s" " wrote= -> outcome-full true }T
T{ 4 limited true w jw-bool w jw-written @ s" true" wrote= -> 4 outcome-ok true }T
unlimited

\ Sorted keys: strictly increasing in byte order, per object.
: sorted ( -- ) true w jw-sorted ! ;
: unsorted ( -- ) false w jw-sorted ! ;
: member ( c-addr u n -- ) >r w jw-key r> w jw-n ;
: pair ( c-addr u c-addr u -- ) w jw-open-object 2swap 1 member 2 member w jw-close-object ;
T{ sorted start s" a" s" b" pair s\" {\"a\":1,\"b\":2}" wrote= -> outcome-ok true }T
T{ sorted start s" b" s" a" pair s\" {\"b\":1" wrote= -> outcome-invalid true }T
T{ sorted start s" a" s" a" pair s\" {\"a\":1" wrote= -> outcome-invalid true }T
T{ sorted start s" a" s" ab" pair w jw-end -> outcome-ok }T
T{ sorted start s" ab" s" a" pair w jw-end -> outcome-invalid }T
T{ sorted start s" Z" s" a" pair w jw-end -> outcome-ok }T
T{ sorted start s" " s" a" pair w jw-end -> outcome-ok }T
T{ sorted start s\" z" s\" \xc3\xa9" pair w jw-end -> outcome-ok }T
T{ sorted start s\" \xc3\xa9" s\" z" pair w jw-end -> outcome-invalid }T
T{ sorted start s\" \xef\xbf\xbf" s\" \xf0\x90\x80\x80" pair w jw-end -> outcome-ok }T
\ Inner objects have their own order; the outer one compares with its own last key.
: nested ( c-addr u c-addr u c-addr u -- )
  2>r 2swap w jw-open-object w jw-key w jw-open-object 0 member w jw-close-object
  2r> 1 member w jw-close-object ;
T{ sorted start s" b" s" zz" s" c" nested w jw-end -> outcome-ok }T
T{ sorted start s" b" s" a" s" a" nested w jw-end -> outcome-invalid }T
T{ sorted start s" b" s" a" s" c" nested output s\" {\"b\":{\"a\":0},\"c\":1}" compare w jw-end
   -> 0 outcome-ok }T
: in-array ( -- )
  w jw-open-object s" a" w jw-key w jw-open-array s" b" s" c" pair s" a" s" b" pair
  w jw-close-array s" b" 3 member w jw-close-object ;
T{ sorted start in-array s\" {\"a\":[{\"b\":1,\"c\":2},{\"a\":1,\"b\":2}],\"b\":3}" wrote=
   -> outcome-ok true }T
\ Unsorted, any order and duplicates are written as given.
T{ unsorted start w jw-open-object s" b" 1 member s" a" 2 member s" a" 3 member w jw-close-object
   s\" {\"b\":1,\"a\":2,\"a\":3}" wrote= -> outcome-ok true }T
\ Keys are checked as strings are, in either mode: invalid UTF-8 is
\ invalid, a key longer than jw-longest is full, and no byte of a refused
\ key is written, not even the comma before it.
: bad-key ( c-addr u -- outcome n )
  start w jw-open-object w jw-key w jw-end sunk-length @ ;
T{ s\" a\x80" bad-key s\" \xed\xa0\x80" bad-key s\" \xc3" bad-key
   -> outcome-invalid 1 outcome-invalid 1 outcome-invalid 1 }T
T{ sunk jw-longest 1+ bad-key sunk -1 bad-key -> outcome-full 1 outcome-full 1 }T
T{ sorted s\" \xc0\xaf" bad-key sunk jw-longest 1+ bad-key unsorted
   -> outcome-invalid 1 outcome-full 1 }T
T{ start w jw-open-object s" a" 1 member s\" \xf4\x90\x80\x80" w jw-key 2 w jw-n
   s\" {\"a\":1" wrote= -> outcome-invalid true }T
\ The key pool holds the open objects' last keys: 4 bytes here.
8 4 json-writer: tight
: tight-start ( -- ) 0 sunk-length ! ['] to-sunk tight jw-start true tight jw-sorted ! ;
: tight-key ( c-addr u -- ) tight jw-key 0 tight jw-n ;
T{ tight-start tight jw-open-object s" abcd" tight-key tight jw-close-object tight jw-end -> outcome-ok }T
T{ tight-start tight jw-open-object s" abcde" tight-key tight jw-close-object tight jw-end
   sunk-length @ -> outcome-full 1 }T
: tight-nested ( c-addr u -- )
  tight jw-open-object s" ab" tight jw-key tight jw-open-object tight-key
  tight jw-close-object tight jw-close-object ;
T{ tight-start s" cd" tight-nested tight jw-end -> outcome-ok }T
T{ tight-start s" cde" tight-nested tight jw-end -> outcome-full }T
T{ tight-start tight jw-open-object s" abcd" tight-key s" abce" tight-key tight jw-close-object
   tight jw-end -> outcome-ok }T
T{ tight-start false tight jw-sorted ! tight jw-open-object s" abcdefgh" tight-key
   tight jw-close-object tight jw-end -> outcome-ok }T
unsorted

\ The sink rules: a writer called from inside its own sink refuses the call
\ as invalid, and jw-start, jw-end and writes from there change nothing else.
variable sink-action
: meddling-sink ( c-addr u -- ) to-sunk sink-action @ ?dup if 0 sink-action ! execute then ;
: meddling ( xt -- ) sink-action ! 0 sunk-length ! ['] meddling-sink w jw-start ;
: nested-write ( -- ) 7 w jw-n ;
: nested-start ( -- ) ['] to-sunk w jw-start ;
: nested-end ( -- ) w jw-end drop ;
: nested-look ( -- ) w jw-outcome w jw-written @ 2drop ;
: one-array ( -- ) w jw-open-array 1 w jw-n w jw-close-array ;
T{ ' nested-write meddling one-array s" [" wrote= -> outcome-invalid true }T
T{ ' nested-start meddling w jw-open-array w jw-depth @ w jw-outcome -> 1 outcome-invalid }T
T{ ' nested-end meddling one-array s" [" wrote= -> outcome-invalid true }T
T{ ' nested-look meddling one-array s" [1]" wrote= -> outcome-ok true }T
\ jw-reset or jw-init from inside the sink would restart the writer under
\ the call that runs the sink: the text fails as invalid when the sink
\ returns, even after a new jw-start there, and nothing more is written.
: nested-reset ( -- ) w jw-reset ['] to-sunk w jw-start ;
: nested-init ( -- ) 8 64 w jw-init drop ;
: nested-init-start ( -- ) nested-init ['] to-sunk w jw-start ;
T{ ' nested-reset meddling one-array s" [" wrote= -> outcome-invalid true }T
T{ ' nested-init meddling one-array s" [" wrote= -> outcome-invalid true }T
T{ ' nested-init-start meddling one-array s" [" wrote= -> outcome-invalid true }T
T{ w jw-busy @ start 1 w jw-n s" 1" wrote= -> false outcome-ok true }T
\ A THROW sunk of the sink leaves the writer busy until jw-reset.
: throwing-sink ( c-addr u -- ) 2drop 99 throw ;
T{ ' throwing-sink w jw-start 5 w ' jw-n catch nip nip w jw-busy @ 0<> -> 99 true }T
T{ start 1 w jw-n w jw-end -> outcome-invalid }T
T{ w jw-reset w jw-busy @ start 1 w jw-n s" 1" wrote= -> false outcome-ok true }T

\ Writers are independent: two interleaved, each to its own sink.
create out2 64 allot  variable out2-length
: to-out2 ( c-addr u -- ) tuck out2 out2-length @ + swap move out2-length +! ;
8 64 json-writer: w2
T{ start 0 out2-length ! ' to-out2 w2 jw-start w jw-open-array w2 jw-open-object 1 w jw-n
   s" k" w2 jw-key 2 w jw-n s" v" w2 jw-string w jw-close-array w2 jw-close-object
   w2 jw-end out2 out2-length @ s\" {\"k\":\"v\"}" compare s" [1,2]" wrote=
   -> outcome-ok 0 outcome-ok true }T
\ A writer as a context member, formatted by a set-up word in every context.
4 16 jw-size context-record: cw
: cw-format ( -- ) 4 16 cw jw-init drop ;
' cw-format context-setup
T{ cw jw-capacity @ cw jw-room @ cw jw-state @ -> 4 16 jw-idle }T
context-new throw constant other-context
T{ other-context context-use 0 sunk-length ! ' to-sunk cw jw-start 1 cw jw-n cw jw-end
   context-main context-use cw jw-state @ cw jw-written @ output s" 1" compare
   -> outcome-ok jw-idle 0 0 }T
T{ other-context context-free -> 0 }T

\ Return-stack balance.
T{ start 1 w ' jw-n rs-checked s" x" w ' jw-string rs-checked w ' jw-end rs-checked
   -> outcome-invalid }T
T{ start w ' jw-open-object rs-checked s" k" w ' jw-key rs-checked w ' jw-null rs-checked
   w ' jw-close-object rs-checked s\" {\"k\":null}" wrote= -> outcome-ok true }T

\ Round trip with the reader: random strings and numbers written, parsed
\ back with json.fs and compared; then the parsed value copied again.
json: jv
T{ 64 jv json-init -> outcome-ok }T
create parse-buffer sunk-size allot
: parsed ( -- outcome ) output tuck parse-buffer swap move parse-buffer swap jv json-parse ;
variable rt-seed  20261102 rt-seed !
: rt-rnd ( n -- r )
  rt-seed @ 1103515245 * 12345 + dup rt-seed ! 16 rshift 32767 and swap mod ;
: rt-rnd-wide ( -- u ) 32768 rt-rnd 32768 * 32768 rt-rnd + ;
\ A random code point of each length, without surrogates.
: rt-rnd-special ( -- c ) 4 rt-rnd s\" \"\\/\x7f" drop + c@ ;
: rt-rnd-three ( -- u )
  $f800 rt-rnd $800 + dup $d800 $dfff between? if $800 + then ;
: rt-rnd-four ( -- u ) rt-rnd-wide $100000 mod $10000 + ;
: rt-rnd-code ( -- u )
  7 rt-rnd case 0 of 32 rt-rnd endof 1 of rt-rnd-special endof 2 of 95 rt-rnd 32 + endof
    3 of $780 rt-rnd $80 + endof 4 of rt-rnd-three endof 5 of rt-rnd-four endof
    >r 26 rt-rnd [char] a + r> endcase ;
create text 64 allot  variable text-length
: +code ( u -- ) text text-length @ + utf8-put text-length +! ;
: rt-rnd-text ( -- c-addr u )
  0 text-length ! 13 rt-rnd 0 ?do rt-rnd-code +code loop text text-length @ ;
: string-back? ( -- flag )
  rt-rnd-text 2dup start w jw-string w jw-end ok? parsed ok? and
  0 jv json-kind@ json-string = and -rot 0 jv json-text@ compare 0= and ;
\ The text written first, kept while the copy writes it again.
create first-text sunk-size allot
: copied-back? ( -- flag )
  output first-text swap move sunk-length @ >r start 0 jv w jw-copy w jw-end ok?
  first-text r> output compare 0= and ;
variable mismatches
: strings-back ( n -- )
  0 ?do string-back? copied-back? and 0= if 1 mismatches +! then loop ;
T{ 0 mismatches ! 2000 strings-back mismatches @ -> 0 }T
\ Numbers: jw-n and jw-u against the independent decimal text; json-u
\ reads back the nonnegative ones.
\ Any cell: three 30-bit draws, or one in four times a small number.
: rt-rnd-cell ( -- x )
  0 3 0 do 30 lshift rt-rnd-wide xor loop 4 rt-rnd 0= if 1000 mod then ;
: n-back? ( n -- flag )
  dup start w jw-n w jw-end ok? parsed ok? and swap dec-n output compare 0= and ;
: u-back? ( u -- flag )
  dup start w jw-u w jw-end ok? parsed ok? and over dec-u output compare 0= and
  swap dup 0< if drop else 0 jv json-u swap rot = and and then ;
: numbers-back ( n -- )
  0 ?do rt-rnd-cell dup n-back? swap u-back? and 0= if 1 mismatches +! then loop ;
T{ 0 mismatches ! 2000 numbers-back mismatches @ -> 0 }T
T{ 0 n-back? max-n n-back? min-n n-back? -> true true true }T
T{ -1 u-back? min-n u-back? max-n u-back? -> true true true }T

\ jw-copy: every kind, re-encoded canonically.
: parse-text ( c-addr u -- outcome )
  tuck parse-buffer swap move parse-buffer swap jv json-parse ;
: copied ( index -- outcome ) start jv w jw-copy w jw-end ;
: messy ( -- c-addr u )
  s\" { \"k\" : [1, -0, \"\\u0041\\/\\u00e9\\ud83d\\ude00\", {\"z\":null}], \"j\":true, \"f\":false }" ;
: tidy ( -- c-addr u )
  s\" {\"k\":[1,0,\"A/\xc3\xa9\xf0\x9f\x98\x80\",{\"z\":null}],\"j\":true,\"f\":false}" ;
T{ messy parse-text 0 copied output tidy compare -> outcome-ok outcome-ok 0 }T
T{ s\" [\"a\",[2,{\"b\":[]}],3]" parse-text 2 copied output s\" [2,{\"b\":[]}]" compare
   -> outcome-ok outcome-ok 0 }T
T{ 6 copied output s" []" compare -> outcome-ok 0 }T
T{ 99 copied sunk-length @ -1 copied sunk-length @ -> outcome-invalid 0 outcome-invalid 0 }T
T{ start sunk -1 w jw-string 99 jv w jw-copy 0 jv w jw-copy w jw-outcome -> outcome-full }T
T{ s\" [1,2.5,3]" parse-text 0 copied output s" [1" compare -> outcome-ok outcome-unsupported 0 }T
T{ s" 1e3" parse-text 0 copied -> outcome-ok outcome-unsupported }T
T{ s\" {\"b\":1,\"a\":2}" parse-text sorted 0 copied unsorted output s\" {\"b\":1" compare
   -> outcome-ok outcome-invalid 0 }T
T{ s" [[[[[[[[[1]]]]]]]]]" parse-text 0 copied output nip -> outcome-ok outcome-full 8 }T
T{ s" [[[[[[[[1]]]]]]]]" parse-text 0 copied -> outcome-ok outcome-ok }T
T{ s\" \"\\u001f\\u007f\"" parse-text 0 copied output s\" \"\\u001f\x7f\"" compare
   -> outcome-ok outcome-ok 0 }T
T{ s" [1,2]" parse-text start 0 jv w ' jw-copy rs-checked w jw-end -> outcome-ok outcome-ok }T
\ A close the copy cannot write (full here) stops it; nothing more is tried.
T{ s" [[1]]" parse-text 4 limited 0 jv w jw-copy unlimited output s" [[1]" compare
   w jw-end -> outcome-ok 0 outcome-full }T
T{ s\" {\"a\":{}}" parse-text 6 limited 0 jv w jw-copy unlimited w jw-end output nip
   -> outcome-ok outcome-full 6 }T
\ The copy closes only the containers it opened; the caller's stay open,
\ and in the caller's object a key is due, so a copied string is refused.
T{ s" []" parse-text start w jw-open-array 0 jv w jw-copy 0 jv w jw-copy
   w jw-close-array s" [[],[]]" wrote= -> outcome-ok outcome-ok true }T
T{ start w jw-open-object s" a" w jw-key 0 jv w jw-copy w jw-close-object
   s\" {\"a\":[]}" wrote= -> outcome-ok true }T
T{ s\" \"a\"" parse-text start w jw-open-object 0 jv w jw-copy s" {" wrote=
   -> outcome-ok outcome-invalid true }T
T{ s\" {\"a\":1}" parse-text start w jw-open-object 1 jv w jw-copy s" {" wrote=
   -> outcome-ok outcome-invalid true }T
\ Containers that end together close together, innermost first.
: together ( -- c-addr u ) s\" [{\"a\":[[{}]]},[[]]]" ;
T{ together parse-text 0 copied output together compare -> outcome-ok outcome-ok 0 }T

\ jw-copy is a loop, not a recursion: a value nested 10,000 deep is copied
\ whole by a writer as deep, with both stacks balanced, and one level
\ deeper is full after exactly 10,000 opens. (A recursive copy overflowed
\ the return stack after a few hundred levels.)
10000 constant very-deep
json: deep-view
T{ very-deep 1+ deep-view json-init -> outcome-ok }T
very-deep 0 jw-size allocate throw constant deep-writer
T{ very-deep 0 deep-writer jw-init -> true }T
\ n opening brackets, then n closing ones, in parse-buffer.
: fill-with ( addr n c-addr 1 -- ) drop c@ fill ;
: nest-text ( n -- c-addr u )
  >r parse-buffer r@ s" [" fill-with
  parse-buffer r@ + r@ s" ]" fill-with parse-buffer r> 2* ;
: deep-start ( n -- outcome )
  nest-text deep-view json-parse 0 sunk-length ! ['] to-sunk deep-writer jw-start ;
: deep-copy ( -- ) 0 deep-view deep-writer ['] jw-copy rs-checked ;
T{ very-deep deep-start ' deep-copy catch deep-writer jw-end -> outcome-ok 0 outcome-ok }T
T{ output very-deep nest-text compare -> 0 }T
T{ very-deep 1+ deep-start ' deep-copy catch deep-writer jw-end sunk-length @
   -> outcome-ok 0 outcome-full very-deep }T
T{ deep-view json-free deep-writer free -> 0 }T

\ The NDJSON corpus, copied back byte for byte in both key modes: every
\ line of the reference exports and tests/lib/json-write-corpus.ndjson,
\ which adds every other record kind of lean4export format 3.1.0. All of
\ them are canonical: compact, keys in increasing order, strings escaped
\ as above, integers without -0.
reader: rd
T{ 65536 65536 rd reader-init -> outcome-ok }T
create line-copy 65536 allot
: line-back? ( c-addr u -- flag )
  2dup tuck line-copy swap move line-copy swap jv json-parse ok? 0= if 2drop false exit then
  start 0 jv w jw-copy w jw-end ok? -rot output compare 0= and ;
variable lines-read
: lines-back ( -- )
  begin rd reader-more? while
    rd reader-line ok? 0= if 2drop 1 mismatches +! exit then
    1 lines-read +! line-back? 0= if 1 mismatches +! then
  repeat ;
: file-back ( c-addr u -- lines mismatches )
  0 lines-read ! 0 mismatches ! rd reader-open ok? if lines-back rd reader-close drop then
  lines-read @ mismatches @ ;
: corpus-back ( -- n1 m1 n2 m2 n3 m3 n4 m4 n5 m5 n6 m6 )
  s" tests/reference/composition.ndjson" file-back
  s" tests/reference/constant-fixture.ndjson" file-back
  s" tests/reference/identity.ndjson" file-back
  s" tests/reference/poly-identity.ndjson" file-back
  s" tests/reference/type-identity.ndjson" file-back
  s" tests/lib/json-write-corpus.ndjson" file-back ;
T{ unsorted corpus-back -> 35 0 32 0 12 0 30 0 29 0 16 0 }T
T{ sorted corpus-back unsorted -> 35 0 32 0 12 0 30 0 29 0 16 0 }T
T{ rd reader-free jv json-free -> }T

cases-done
bye
