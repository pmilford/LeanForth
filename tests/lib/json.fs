\ Unit tests of src/lib/json.fs: valid texts and their tokens, a corpus of
\ malformed texts that must all be invalid, escapes decoded in place,
\ numbers, every limit at and one past its bound, failure positions, and
\ the tape readers.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/json.fs

decimal
json: jv
T{ 8 jv json-init -> outcome-ok }T

\ Parse a copy of the text, so in-place decoding never touches a literal.
create text-buffer 512 allot
: parsed ( c-addr u -- outcome ) tuck text-buffer swap move text-buffer swap jv json-parse ;
: tokens ( -- n ) jv json-count @ ;
: kind ( index -- kind ) jv json-kind@ ;
: text ( index -- c-addr u ) jv json-text@ ;
: items ( index -- n ) jv json-items@ ;

\ Scalars.
T{ s" 0" parsed tokens 0 kind -> outcome-ok 1 json-integer }T
T{ s" -12" parsed 0 text s" -12" compare -> outcome-ok 0 }T
T{ s" 1.5" parsed 0 kind s" 1e5" parsed 0 kind -> outcome-ok json-real outcome-ok json-real }T
T{ s" -0.0E-3" parsed 0 kind 0 text nip -> outcome-ok json-real 7 }T
T{ s" true" parsed 0 kind s" false" parsed 0 kind s" null" parsed 0 kind
   -> outcome-ok json-true outcome-ok json-false outcome-ok json-null }T
T{ s\" \"abc\"" parsed 0 kind 0 text s" abc" compare -> outcome-ok json-string 0 }T
T{ s\" \"\"" parsed 0 text nip -> outcome-ok 0 }T
T{ s\"  \t\r\n 7 \n" parsed 0 text s" 7" compare -> outcome-ok 0 }T

\ Containers: item counts, extents and order.
T{ s" []" parsed tokens 0 items 0 jv json-next -> outcome-ok 1 0 1 }T
T{ s" {}" parsed 0 kind 0 items -> outcome-ok json-object 0 }T
T{ s" [1,[2,3],{}]" parsed tokens 0 items 2 items 2 kind -> outcome-ok 6 3 2 json-array }T
T{ s" [1,[2,3],{}]" parsed 2 jv json-next 5 kind 0 jv json-next -> outcome-ok 5 json-object 6 }T
T{ s\" {\"a\":1,\"b\":[true],\"c\":null}" parsed 0 items tokens -> outcome-ok 3 8 }T
T{ s" [[[[]]]]" parsed tokens 3 items -> outcome-ok 4 0 }T
T{ s\" [1,[2,3],{}]" parsed 0 jv json-contents -> outcome-ok 6 1 }T

\ Strings: escapes decoded in place, raw UTF-8 kept, surrogate pairs joined.
T{ s\" \"a\\nb\"" parsed 0 text s\" a\nb" compare -> outcome-ok 0 }T
T{ s\" \"\\\"\\\\\\/\\b\\f\\n\\r\\t\"" parsed 0 text s\" \"\\/\b\f\n\r\t" compare -> outcome-ok 0 }T
T{ s\" \"\\u0041\\u00e9\\u20AC\"" parsed 0 text s\" A\xc3\xa9\xe2\x82\xac" compare -> outcome-ok 0 }T
T{ s\" \"\\ud83d\\ude00!\"" parsed 0 text s\" \xf0\x9f\x98\x80!" compare -> outcome-ok 0 }T
T{ s\" \"\\u0000\"" parsed 0 text nip 0 text drop c@ -> outcome-ok 1 0 }T
T{ s\" \"caf\xc3\xa9 \xf0\x9f\x98\x80\"" parsed 0 text s\" caf\xc3\xa9 \xf0\x9f\x98\x80" compare -> outcome-ok 0 }T
T{ s\" [\"x\\ty\",\"\\u00e9z\",\"w\"]" parsed 1 text s\" x\ty" compare 2 text s\" \xc3\xa9z" compare 3 text s" w" compare
   -> outcome-ok 0 0 0 }T
T{ s\" \"\x7f\"" parsed 0 text nip -> outcome-ok 1 }T

\ A malformed corpus: every text is invalid.
create corpus-buffer 64 allot
variable accepted
: must-fail ( c-addr u -- ) parsed outcome-invalid <> if 1 accepted +! then ;
: corpus-structure ( -- )
  s" " must-fail  s"    " must-fail  s" {" must-fail  s" [" must-fail  s" }" must-fail
  s" ]" must-fail  s\" {\"a\"}" must-fail  s\" {\"a\":}" must-fail  s" {,}" must-fail
  s" [1,]" must-fail  s" [,1]" must-fail  s\" {\"a\":1,}" must-fail  s" [1 2]" must-fail
  s\" {\"a\":1 \"b\":2}" must-fail  s" {1:2}" must-fail  s" [}" must-fail  s" {]" must-fail
  s" 1 2" must-fail  s\" \"a\" \"b\"" must-fail  s\" {\"a\" 1}" must-fail  s" [1]]" must-fail
  s" {}}" must-fail  s\" {\"a\":1}x" must-fail  s" [[]" must-fail  s\" {\"a\"::1}" must-fail ;
: corpus-numbers ( -- )
  s" 01" must-fail  s" -" must-fail  s" 1." must-fail  s" .5" must-fail  s" 1e" must-fail
  s" 1e+" must-fail  s" +1" must-fail  s" --1" must-fail  s" 0x1" must-fail  s" -01" must-fail
  s" NaN" must-fail  s" Infinity" must-fail  s" 1.e5" must-fail  s" [01]" must-fail ;
: corpus-literals ( -- )
  s" tru" must-fail  s" nul" must-fail  s" True" must-fail  s" nulll" must-fail
  s" falsey" must-fail  s" t" must-fail  s" [tru]" must-fail ;
: corpus-strings ( -- )
  s\" \"abc" must-fail  s\" \"\\\"" must-fail  s\" \"\\x\"" must-fail  s\" \"\\u12\"" must-fail
  s\" \"\\uZZZZ\"" must-fail  s\" \"\\ud800\"" must-fail  s\" \"\\udc00\"" must-fail
  s\" \"\\ud800\\u0041\"" must-fail  s\" \"\\ud800x\"" must-fail  s\" \"a\nb\"" must-fail
  s\" \"\t\"" must-fail  s\" \"\x00\"" must-fail  s\" \"\x80\"" must-fail
  s\" \"\xc0\xaf\"" must-fail  s\" \"\xed\xa0\x80\"" must-fail  s\" \"\xe2\x82\"" must-fail
  s\" \"\\" must-fail  s\" '\'" must-fail ;
: corpus-bytes ( -- )
  s\" \xef\xbb\xbf{}" must-fail  s\" [\xc3\xa9]" must-fail  s\" \x00" must-fail
  s\" [1,\x0b2]" must-fail  s\" [1\x0c]" must-fail ;
T{ 0 accepted ! corpus-structure corpus-numbers corpus-literals corpus-strings corpus-bytes accepted @ -> 0 }T

\ Failure positions and reasons.
T{ s\" {\"a\":01}" parsed jv json-offset jv json-reason s" comma or closing bracket expected" compare
   -> outcome-invalid 6 0 }T
T{ s\" \"x" parsed jv json-reason s" unterminated string" compare -> outcome-invalid 0 }T
T{ s\" [\"\\q\"]" parsed jv json-offset -> outcome-invalid 2 }T
T{ s" " parsed jv json-reason s" unexpected end of text" compare -> outcome-invalid 0 }T
T{ s" [1] x" parsed jv json-reason s" text after the value" compare -> outcome-invalid 0 }T

\ Limits, each at its bound and one past it.
T{ s" [[[[[[[[1]]]]]]]]" parsed -> outcome-ok }T
T{ s" [[[[[[[[[1]]]]]]]]]" parsed jv json-reason s" nested too deeply" compare -> outcome-full 0 }T
T{ 3 jv json-string-limit ! s\" \"abc\"" parsed s\" \"abcd\"" parsed -> outcome-ok outcome-full }T
T{ s\" \"a\\nb\"" parsed s\" \"a\\nbc\"" parsed -> outcome-ok outcome-full }T
T{ max-n jv json-string-limit ! -> }T
T{ 3 jv json-digit-limit ! s" 123" parsed s" 1234" parsed s" -1.5" parsed s" -12" parsed
   -> outcome-ok outcome-full outcome-full outcome-ok }T
T{ max-n jv json-digit-limit ! -> }T
T{ 4 jv json-token-limit ! s" [1,2,3]" parsed s" [1,2,3,4]" parsed -> outcome-ok outcome-full }T
T{ max-n /token / jv json-token-limit ! -> }T
\ The tape grows beyond its first room.
create long-text 2400 allot
\ [1,1,...,1] with n elements; brackets by code, since a bare bracket
\ inside a definition confuses scripts/check-portable-forth.py.
91 constant open-bracket  93 constant close-bracket
: long-array ( n -- c-addr u )
  long-text open-bracket over c! 1+ swap 0 ?do [char] 1 over c! [char] , over 1+ c! 2 + loop
  1- close-bracket over c! 1+ long-text tuck - ;
T{ 1000 long-array jv json-parse tokens 0 items -> outcome-ok 1001 1000 }T

\ Readers of the tape.
T{ s\" {\"a\":1,\"b\":[true],\"a\":2}" parsed -> outcome-ok }T
: key-a c" a" ;  : key-b c" b" ;  : key-z c" z" ;
T{ key-a 0 jv json-find -> 2 true }T
T{ key-b 0 jv json-find drop kind -> json-array }T
T{ key-z 0 jv json-find -> false }T
T{ 2 jv json-u 5 jv json-bool 4 jv json-u -> 1 true true true false }T
T{ s" [false,null,7]" parsed 1 jv json-bool 2 jv json-bool -> outcome-ok false true false }T
: natural-is? ( index c-addr u -- flag ) rot jv json-natural if compare 0= else 2drop false then ;
T{ s" [0,-0,-1,1.5,12345]" parsed 2 s" 0" natural-is? 3 s" -1" natural-is? -> outcome-ok true false }T
T{ 1 jv json-u 2 jv json-u 3 jv json-u 4 jv json-u 5 jv json-u -> 0 true 0 true false false 12345 true }T
T{ s\" [\"7\"]" parsed 1 jv json-u -> outcome-ok false }T

\ digits>u: the fast loop, the double-cell path at the width of max-n, and overflow.
: max-n-text ( -- c-addr u ) max-n 0 <# #s #> ;
T{ s" 0" digits>u s" 42" digits>u -> 0 true 42 true }T
T{ max-n-text digits>u -> max-n true }T
T{ max-n-text drop cell-digits 1- digits>u nip -> true }T
: past-max-n ( -- c-addr u ) max-n-text text-buffer swap move text-buffer cell-digits
  2dup + 1- dup c@ 1+ swap c! ;
T{ past-max-n digits>u -> false }T
T{ s" 123456789012345678901234567890" digits>u -> false }T
T{ cell-digits max-n-text nip = -> true }T
\ Nothing depends on BASE: digits are decimal on every path.
T{ max-n-text 2 base ! digits>u decimal -> max-n true }T
T{ max-n-text hex digits>u decimal -> max-n true }T
T{ past-max-n hex digits>u decimal -> false }T
T{ s" 1000" 2 base ! decimal>u decimal -> 1000 }T
\ digit+ at the edge of a cell.
T{ max-n 10 / max-n 10 mod char 0 + digit+ -> max-n true }T
T{ max-n 10 / max-n 10 mod char 1 + digit+ -> false }T
T{ 0 char 7 digit+ -> 7 true }T

\ canonical-natural?: digits only, no leading zero except 0 itself.
T{ s" 0" canonical-natural? s" 10" canonical-natural? s" 123456789012345678901234567890" canonical-natural?
   -> true true true }T
T{ s" " canonical-natural? s" 01" canonical-natural? s" 1a" canonical-natural? s" -1" canonical-natural?
   -> false false false false }T

\ json-kind-at and json-items-of check the index and the kind.
T{ s" [1,{}]" parsed -> outcome-ok }T
T{ 0 json-array jv json-items-of 0 json-object jv json-items-of -> 2 true false }T
T{ 2 json-object jv json-items-of 1 json-array jv json-items-of -> 0 true false }T
T{ 3 json-array jv json-items-of -1 json-array jv json-items-of -> false false }T
T{ -1 jv json-kind-at 3 jv json-kind-at 1 jv json-kind-at -> -1 -1 json-integer }T

\ Stack and return-stack balance of a whole parse.
: copied ( c-addr u -- c-addr' u ) tuck text-buffer swap move text-buffer swap ;
T{ s" [1,{}]" copied jv ' json-parse rs-checked -> outcome-ok }T

\ json-init again frees the old memory first; json-free frees it all.
T{ 8 jv json-init 4 jv json-init jv json-depth-limit @ -> outcome-ok outcome-ok 4 }T
T{ jv json-free jv json-tape @ jv json-stack @ -> 0 0 }T
cases-done
bye
