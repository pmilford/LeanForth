\ Fail-closed JSON reader (RFC 8259) for one JSON text at a time, such as
\ one NDJSON line. A general tool with no Lean knowledge. Untrusted.
\ Requires: bytes.fs (UTF-8 checks, heap, line feed and carriage return).
\ State: none of its own. Every word takes a view record made by json:, so
\ separate views are independent; one view is single-threaded. The byte
\ tables below are constant after loading.
\
\ json-parse reads a whole text into the view's token tape, without
\ recursion: objects, arrays, strings, numbers, true, false and null, each
\ one token in document order. A container's token records how many
\ members or elements it has and the index of the first token after it, so
\ callers can skip over it; an object's members are a key token followed
\ by the value's tokens. String and number tokens point into the text
\ itself: escaped strings are decoded in place, which never needs more
\ room than the escape took, so the text bytes may change. Number tokens
\ keep their digits as text, whatever their size; json-natural and json-u
\ read natural numbers from them, always in decimal: nothing here depends
\ on BASE, and the file itself loads in decimal whatever BASE is, then
\ restores it at the end of a successful load (a THROW while loading
\ leaves BASE decimal: Forth-2012 gives a file no way to restore it then).
\
\ Failure is total: json-parse gives ok only for a complete, valid text,
\ and otherwise invalid (bad syntax, bad escape, invalid UTF-8, a control
\ byte in a string, text after the value, empty input) or full (too
\ deep, too many tokens, a string or number past its limit, no heap). The
\ tape is then meaningless. json-offset and json-reason say where and why.
\ The tape takes /token bytes per token and grows up to the token limit,
\ which json-init sets as large as memory; a caller that reads untrusted
\ text bounds it (json-token-limit) to bound the memory of one text.
\ Whitespace is space, tab, line feed and carriage return; outside strings
\ only ASCII is valid, so a text that parses is valid UTF-8. Duplicate
\ object keys are kept: json-find returns the first, and a caller that
\ needs unique keys checks them.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./bytes.fs

\ Token kinds.
0 constant json-object
1 constant json-array
2 constant json-string
3 constant json-integer            \ an optional minus sign and digits
4 constant json-real               \ a number with a fraction or an exponent
5 constant json-true
6 constant json-false
7 constant json-null

begin-structure /token
  field: token-kind
  field: token-text                \ scalar: address of its text
  field: token-size                \ scalar: length of its text
end-structure
\ A container uses the same two cells for its item count and its extent.
: token-items ( token -- addr ) token-text ;
: token-after ( token -- addr ) token-size ;

begin-structure /json
  field: json-tape                 \ heap array of tokens
  field: json-room                 \ tokens it holds now
  field: json-count                \ tokens parsed
  field: json-stack                \ heap array of the open containers' indices
  field: json-depth                \ containers open now
  field: json-token-limit          \ most tokens in one text
  field: json-depth-limit          \ deepest nesting of containers
  field: json-string-limit         \ longest string after decoding, in bytes
  field: json-digit-limit          \ longest number text, in bytes
  field: json-state                \ what the parser expects next
  field: json-start                \ first byte of the text
  field: json-pos                  \ next byte to read
  field: json-end                  \ address after the text
  field: json-out                  \ where a string's decoded bytes go
  field: json-mark                 \ start of the string or number being read
  field: json-why                  \ counted string: why parsing failed, or 0
end-structure

\ Parser states: what may come next.
0 constant st-value                \ any value
1 constant st-first-element        \ just after [: a value or ]
2 constant st-first-member         \ just after {: a key or }
3 constant st-member               \ after a comma in an object: a key, then a colon
4 constant st-after                \ after a value in a container: a comma or a bracket
5 constant st-done                 \ the whole value has been read

256 constant json-first-room       \ tokens in a new tape; it doubles as needed

\ Defining word: name ( -- view ), zeroed, without heap memory yet.
: json: ( "name" -- ) create /json store-zeroed, drop ;
: json-tape! ( room addr view -- ) tuck json-tape ! json-room ! ;
\ Limits: depth as given; tokens, strings and numbers as large as memory.
: json-limits! ( depth view -- )
  tuck json-depth-limit ! max-n over json-string-limit ! max-n over json-digit-limit !
  max-n /token / swap json-token-limit ! ;
: json-heap-stack ( view -- outcome )
  dup json-depth-limit @ 1 max cells heap-claim
  if swap json-stack ! outcome-ok else drop outcome-full then ;
: json-heap-tape ( view -- outcome )
  json-first-room dup /token * heap-claim
  if rot json-tape! outcome-ok else 2drop outcome-full then ;
\ Free a view's heap memory and zero it.
: json-free ( view -- )
  dup json-tape heap-release dup json-stack heap-release /json erase ;
\ Prepare a view for texts nested at most depth containers deep, freeing
\ the memory of an earlier json-init first. Full when the heap has no
\ room; json-free then releases what was allocated.
: json-init ( depth view -- outcome )
  dup json-free tuck json-limits! dup json-heap-stack ok-then? if json-heap-tape then ;

\ Failure: remember why, and give invalid or full.
: json-bad ( view c-addr -- outcome ) swap json-why ! outcome-invalid ;
: json-over ( view c-addr -- outcome ) swap json-why ! outcome-full ;
\ Where parsing stopped, as an offset into the text, and why it failed.
: json-offset ( view -- n ) dup json-pos @ swap json-start @ - ;
: json-reason ( view -- c-addr u ) json-why @ ?dup if count else s" none" then ;

\ Reading position.
: json-rest ( view -- end pos ) dup json-end @ swap json-pos @ ;
: json-remaining ( view -- addr u ) json-rest tuck - ;
: json-skip ( view -- ) 1 swap json-pos +! ;
\ The next byte, or -1 at the end of the text.
: json-peek ( view -- c ) json-rest 2dup u> if nip c@ else 2drop -1 then ;
: json-space? ( c -- flag ) dup bl = over 9 = or over lf-byte = or swap cr-byte = or ;
: spaces-end ( end addr -- end addr' )
  begin 2dup u> while dup c@ json-space? while 1+ repeat then ;
: json-skip-space ( view -- ) dup json-rest spaces-end nip swap json-pos ! ;

\ The token tape. A token's address is valid only until the next token is
\ added, because the tape may move when it grows; indices stay valid.
: json-token ( index view -- token ) json-tape @ swap /token * + ;
: json-last ( view -- index ) json-count @ 1- ;
: json-full? ( view -- flag ) dup json-count @ swap json-room @ < 0= ;
: json-can-grow? ( view -- flag ) dup json-room @ swap json-token-limit @ < ;
: json-grown ( view -- room ) dup json-room @ 2* swap json-token-limit @ min ;
: json-resize ( room view -- outcome )
  >r r@ json-tape @ over /token * resize
  if 2drop r> c" no memory for tokens" json-over else r> json-tape! outcome-ok then ;
: json-grow ( view -- outcome )
  dup json-can-grow? 0= if c" too many tokens" json-over exit then
  dup json-grown swap json-resize ;
: json-at-limit? ( view -- flag ) dup json-count @ swap json-token-limit @ < 0= ;
: json-room? ( view -- outcome )
  dup json-at-limit? if c" too many tokens" json-over exit then
  dup json-full? if json-grow else drop outcome-ok then ;
\ A new token of this kind, with zero text fields (no items yet, for a container).
: token-new ( kind token -- token )
  tuck token-kind ! 0 over token-text ! 0 over token-size ! ;
: token-text! ( addr u token -- ) tuck token-size ! token-text ! ;
: json-claim ( view -- index ) dup json-count @ 1 rot json-count +! ;
\ Append a token of this kind with zero text fields.
: json-add ( kind view -- token outcome )
  dup json-room? ok-then? 0= if nip 0 swap exit then
  dup json-claim swap json-token token-new outcome-ok ;
\ Append a scalar token of this kind whose text is the string addr u.
: json-scalar ( addr u kind view -- outcome )
  dup json-room? ok-then? 0= if nip nip nip exit then
  dup json-claim swap json-token tuck token-kind ! token-text! outcome-ok ;

\ Open containers: a stack of token indices.
: json-slot ( view -- addr ) dup json-depth @ cells swap json-stack @ + ;
: json-top ( view -- index ) dup json-depth @ 1- cells swap json-stack @ + @ ;
: json-innermost ( view -- token ) dup json-top swap json-token ;
: json-push ( index view -- ) tuck json-slot ! 1 swap json-depth +! ;
: json-pop ( view -- ) -1 swap json-depth +! ;
: json-deep? ( view -- flag ) dup json-depth @ swap json-depth-limit @ < 0= ;

\ A value is complete: the text ends, or its container counts one more item.
: json-done ( view -- outcome )
  dup json-depth @ 0= if st-done swap json-state ! outcome-ok exit then
  1 over json-innermost token-items +! st-after swap json-state ! outcome-ok ;
: json-then-done ( view outcome -- outcome ) ok-then? if json-done then ;
\ Open a container of this kind at its bracket; state says what may follow.
: json-open ( kind state view -- outcome )
  dup json-deep? if nip nip c" nested too deeply" json-over exit then
  tuck json-state ! tuck json-add nip ok-then?
  if dup json-last over json-push json-skip outcome-ok then ;
: json-end-token ( view -- ) dup json-count @ swap json-innermost token-after ! ;
\ Close the innermost container at its bracket; it must be of this kind.
: json-close ( kind view -- outcome )
  tuck json-innermost token-kind @ <> if c" mismatched bracket" json-bad exit then
  dup json-end-token dup json-pop dup json-skip json-done ;

\ Bytes inside strings, by class: 0 stands for itself, 1 is the closing
\ quote, 2 a backslash, 3 a control byte, 4 a byte of a multibyte
\ character. Escapes map the byte after a backslash to the byte it stands
\ for, or 0 when it is not a one-byte escape.
34 constant quote-byte
92 constant backslash
create json-string-classes 256 allot  json-string-classes 256 erase
create json-escapes 256 allot  json-escapes 256 erase
: json-classes! ( lo hi class -- )
  -rot 1+ swap ?do dup json-string-classes i + c! loop drop ;
0 31 3 json-classes!  quote-byte dup 1 json-classes!  backslash dup 2 json-classes!
128 255 4 json-classes!
: json-escape-byte! ( byte c -- ) json-escapes + c! ;
quote-byte quote-byte json-escape-byte!  backslash backslash json-escape-byte!
47 47 json-escape-byte!  8 char b json-escape-byte!  12 char f json-escape-byte!
9 char t json-escape-byte!  lf-byte char n json-escape-byte!
cr-byte char r json-escape-byte!
: string-class ( c -- class ) json-string-classes + c@ ;
: plain-end ( end addr -- end addr' )
  begin 2dup u> while dup c@ string-class 0= while 1+ repeat then ;

\ Decoding in place: json-out trails json-pos once an escape has been
\ decoded, and bytes read are copied back to it.
: json-moved? ( view -- flag ) dup json-pos @ swap json-out @ <> ;
: json-copy ( n view -- )
  dup json-moved? if dup json-pos @ over json-out @ 2over drop move then
  2dup json-pos +! json-out +! ;
: json-emit ( byte view -- ) tuck json-out @ c! 1 swap json-out +! ;
: json-run ( view -- ) dup json-rest plain-end nip over json-pos @ - swap json-copy ;
: json-utf8 ( view -- outcome )
  dup json-remaining utf8-length ?dup 0= if c" invalid UTF-8" json-bad exit then
  swap json-copy outcome-ok ;

\ Unicode escapes: \uXXXX, where a high surrogate must be followed by a
\ low one and the pair stands for one code point; a lone surrogate is
\ invalid, since UTF-8 cannot encode it.
: hex-digit ( c -- n )
  dup [char] 0 [char] 9 between? if [char] 0 - exit then
  32 or dup [char] a [char] f between? if [char] a - 10 + else drop -1 then ;
: hex4 ( addr -- u true | false )
  0 swap 4 0 do dup i + c@ hex-digit dup 0< if 2drop drop false unloop exit then
  rot 4 lshift or swap loop drop true ;
: u-escape? ( addr -- flag ) dup c@ backslash = swap 1+ c@ [char] u = and ;
\ The four hex digits of \uXXXX at addr u.
: u-escape ( addr u -- code true | false )
  6 < if drop false exit then dup u-escape? if 2 + hex4 else drop false then ;
: surrogate-high? ( u -- flag ) $d800 $dbff between? ;
: surrogate-low? ( u -- flag ) $dc00 $dfff between? ;
: pair-code ( high low -- code ) $dc00 - swap $d800 - 10 lshift + $10000 + ;
: unicode-pair ( high addr u -- code n )
  6 /string u-escape 0= if drop 0 0 exit then
  dup surrogate-low? if pair-code 12 else 2drop 0 0 then ;
\ The code point of the escape at addr u and the bytes it takes; n = 0 when invalid.
: unicode-escape ( addr u -- code n )
  2dup u-escape 0= if 2drop 0 0 exit then dup surrogate-low? if drop 2drop 0 0 exit then
  dup surrogate-high? if -rot unicode-pair else nip nip 6 then ;
: json-unicode ( view -- outcome )
  dup json-remaining unicode-escape
  ?dup 0= if drop c" bad unicode escape" json-bad exit then
  >r over json-out @ utf8-put over json-out +! r> swap json-pos +! outcome-ok ;
: json-escape ( view -- outcome )
  dup json-remaining 2 < if drop c" bad escape" json-bad exit then 1+ c@
  dup [char] u = if drop json-unicode exit then
  json-escapes + c@ ?dup 0= if c" bad escape" json-bad exit then
  over json-emit 2 swap json-pos +! outcome-ok ;

\ One byte that does not stand for itself: an escape, a multibyte
\ character, a control byte, or the end of the text.
: json-special ( view -- outcome )
  dup json-peek dup 0< if drop c" unterminated string" json-bad exit then
  string-class case 2 of json-escape endof 4 of json-utf8 endof
    >r c" control byte in string" json-bad r> endcase ;
: json-chars ( view -- outcome )
  begin dup json-run dup json-peek quote-byte <> while
    dup json-special ok-then? 0= if exit then
  repeat drop outcome-ok ;
: json-marked ( view -- addr u ) dup json-mark @ swap json-out @ over - ;
\ Append a string token, unless it is longer than the limit.
: json-string-token ( addr u view -- outcome )
  2dup json-string-limit @ > if nip nip c" string too long" json-over exit then
  json-string swap json-scalar ;
\ The slow path, from the first byte after the opening quote: decode in place.
: json-begin-string ( view -- ) dup json-pos @ 2dup swap json-mark ! swap json-out ! ;
: json-escaped-string ( view -- outcome )
  dup json-begin-string dup json-chars ok-then?
  if dup json-skip dup >r json-marked r> json-string-token then ;
\ The fast path: the plain bytes from the read position, and whether the
\ closing quote follows them, so that the token can point at them as they are.
: json-plain ( view -- addr u flag )
  json-rest tuck plain-end tuck u> if dup c@ quote-byte = else false then >r over - r> ;
\ A string at its opening quote, as one token.
: json-read-string ( view -- outcome )
  dup json-skip dup json-plain if rot >r 2dup + 1+ r@ json-pos ! r> json-string-token
  else 2drop json-escaped-string then ;

\ Numbers: -? (0 | [1-9][0-9]*) (. [0-9]+)? ([eE] [+-]? [0-9]+)?
: decimal-digit? ( c -- flag ) [char] 0 - 10 u< ;
: digits-end ( end addr -- end addr' )
  begin 2dup u> while dup c@ decimal-digit? while 1+ repeat then ;
: json-digits ( view -- n )
  >r r@ json-rest digits-end nip r@ json-pos @ over r> json-pos ! - ;
: json-skip-if ( c view -- flag ) tuck json-peek = dup if swap json-skip else nip then ;
\ The integer part on the stack, after an optional minus sign: 0, or a
\ nonzero digit and more digits.
: skip-minus ( end addr -- end addr' ) 2dup u> if dup c@ [char] - = if 1+ then then ;
: int-end ( end addr -- end addr' flag )
  2dup u> 0= if false exit then dup c@ [char] 0 = if 1+ true exit then
  dup >r digits-end dup r> <> ;
: json-fraction? ( view -- flag )
  [char] . over json-skip-if if json-digits 0> else drop true then ;
: json-sign ( view -- )
  [char] + over json-skip-if if drop else [char] - swap json-skip-if drop then ;
: json-e? ( view -- flag )
  [char] e over json-skip-if if drop true else [char] E swap json-skip-if then ;
: json-exponent? ( view -- flag )
  dup json-e? if dup json-sign json-digits 0> else drop true then ;
: json-integer? ( view -- flag )
  dup json-rest skip-minus int-end >r nip swap json-pos ! r> ;
: json-real? ( view -- flag ) dup json-fraction? swap json-exponent? and ;
: json-span ( view -- addr u ) dup json-mark @ swap json-pos @ over - ;
: json-number-done ( kind view -- outcome )
  dup >r json-span dup r@ json-digit-limit @ >
  if 2drop drop r> c" number too long" json-over exit then rot r> json-scalar ;
: real-start? ( c -- flag ) dup [char] . = swap 32 or [char] e = or ;
: json-real-part ( view -- outcome )
  dup json-real? if json-real swap json-number-done else c" bad number" json-bad then ;
\ A number, as one token: integer when it has neither fraction nor exponent.
: json-read-number ( view -- outcome )
  dup json-pos @ over json-mark !
  dup json-integer? 0= if c" bad number" json-bad exit then
  dup json-peek real-start? if json-real-part exit then
  json-integer swap json-number-done ;

\ true, false and null.
: literal-spelling ( kind -- c-addr u )
  case json-true of s" true" endof json-false of s" false" endof s" null" rot endcase ;
: json-matches? ( c-addr u view -- flag ) json-remaining 2over nip min compare 0= ;
: json-literal ( kind view -- outcome )
  >r dup literal-spelling tuck r@ json-matches?
  0= if 2drop r> c" unexpected character" json-bad exit then
  r@ json-pos @ over r@ json-pos +! swap rot r> json-scalar ;

\ Values, dispatched on their first byte through a table.
: json-unexpected ( view -- outcome ) c" unexpected character" json-bad ;
: json-open-object ( view -- outcome ) json-object st-first-member rot json-open ;
: json-open-array ( view -- outcome ) json-array st-first-element rot json-open ;
: json-string-value ( view -- outcome ) dup json-read-string json-then-done ;
: json-number-value ( view -- outcome ) dup json-read-number json-then-done ;
: json-true-value ( view -- outcome ) json-true over json-literal json-then-done ;
: json-false-value ( view -- outcome ) json-false over json-literal json-then-done ;
: json-null-value ( view -- outcome ) json-null over json-literal json-then-done ;
create value-actions 256 cells allot
: value-action! ( xt lo hi -- ) 1+ swap ?do dup value-actions i cells + ! loop drop ;
' json-unexpected 0 255 value-action!
' json-open-object char { dup value-action!
' json-open-array char [ dup value-action!
' json-string-value quote-byte dup value-action!
' json-number-value char - dup value-action!
' json-number-value char 0 char 9 value-action!
' json-true-value char t dup value-action!
' json-false-value char f dup value-action!
' json-null-value char n dup value-action!
\ The next byte that is not whitespace, or -1 at the end of the text.
\ Whitespace bytes are at most the space character, so most bytes need
\ one comparison.
: json-byte ( view -- c )
  dup json-peek dup bl > if nip exit then
  dup json-space? if drop dup json-skip-space json-peek else nip then ;

\ The parser's states, each given the next byte c that is not whitespace.
: json-value ( c view -- outcome ) swap cells value-actions + @ execute ;
: json-element ( c view -- outcome )
  over [char] ] = if nip json-array swap json-close else json-value then ;
\ A key, then its colon; a value must follow.
: json-colon ( view -- outcome )
  dup json-byte [char] : <> if c" colon expected" json-bad exit then
  st-value over json-state ! json-skip outcome-ok ;
: json-key ( c view -- outcome )
  swap quote-byte <> if c" key expected" json-bad exit then
  dup json-read-string ok-then? if json-colon then ;
: json-first-member ( c view -- outcome )
  over [char] } = if nip json-object swap json-close else json-key then ;
: json-comma ( view -- outcome )
  dup json-skip dup json-innermost token-kind @ json-object =
  if st-member else st-value then swap json-state ! outcome-ok ;
: json-after ( c view -- outcome )
  swap case [char] , of json-comma endof [char] } of json-object swap json-close endof
    [char] ] of json-array swap json-close endof
    >r c" comma or closing bracket expected" json-bad r> endcase ;
create json-steps   \ indexed by state
  ' json-value , ' json-element , ' json-first-member , ' json-key , ' json-after ,
\ One step: act on the next byte in the current state.
: json-step ( view -- outcome )
  dup json-byte dup 0< if drop c" unexpected end of text" json-bad exit then
  over json-state @ dup st-after u> if 2drop c" corrupted parser state" json-bad exit then
  >r swap r> cells json-steps + @ execute ;

: json-begin ( addr u view -- )
  >r over + r@ json-end ! dup r@ json-start ! r@ json-pos !
  0 r@ json-count ! 0 r@ json-depth ! 0 r@ json-why ! st-value r> json-state ! ;
: json-parsing? ( view -- flag ) json-state @ st-done <> ;
: json-finish ( view -- outcome )
  dup json-skip-space dup json-peek 0< if drop outcome-ok exit then
  c" text after the value" json-bad ;
\ Parse the text addr u into the view's tape; see the header for outcomes.
\ Escaped strings are decoded in place inside addr u.
: json-parse ( addr u view -- outcome )
  dup >r json-begin r>
  begin dup json-parsing? while
    dup json-step ok-then? 0= if exit then
  repeat json-finish ;

\ Reading the tape after a successful parse. Token 0 is the whole value.
\ Indices are not checked, except by json-kind-at and json-items-of:
\ callers stay within json-count and within the extents recorded in
\ container tokens, and read json-items@ only from a container.
: json-kind@ ( index view -- kind ) json-token token-kind @ ;
: json-text@ ( index view -- addr u ) json-token dup token-text @ swap token-size @ ;
: json-items@ ( index view -- n ) json-token token-items @ ;
\ The kind of the token at any index, or -1 outside the tape.
: json-kind-at ( index view -- kind )
  2dup json-count @ u< if json-kind@ else 2drop -1 then ;
\ The item count of the token at any index, when it is a container of
\ this kind (json-object or json-array).
: json-items-of ( index kind view -- n true | false )
  >r over r@ json-kind-at = if r> json-items@ true else r> 2drop false then ;
\ The index after the value at index, skipping a container's contents.
: json-next ( index view -- index' )
  over swap json-token dup token-kind @ json-array >
  if drop 1+ else nip token-after @ then ;
\ The tokens inside a container: from first up to, but not including, end.
: json-contents ( index view -- end first ) over swap json-token token-after @ swap 1+ ;
\ The value of the first member of an object whose key is the counted string.
: json-key= ( c-addr key view -- flag ) json-text@ rot count compare 0= ;
: json-member-next ( key view -- key' ) swap 1+ swap json-next ;
: json-find ( c-addr object view -- value true | false )
  tuck json-contents -rot swap 2>r
  begin dup 2r@ drop < while
    2dup 2r@ nip json-key= if nip 1+ true 2r> 2drop exit then 2r@ nip json-member-next
  repeat 2drop 2r> 2drop false ;
\ A boolean token.
: json-bool ( index view -- flag true | false )
  json-kind@ dup json-true = if drop true true exit then
  json-false = if false true else false then ;

\ Natural numbers. A natural is an integer token without a minus sign, or
\ -0 (which JSON allows and which equals 0).
: natural-text ( addr u -- addr u true | false )
  over c@ [char] - <> if true exit then
  2dup s" -0" compare if 2drop false else 1 /string true then ;
\ The digits of the natural number at index.
: json-natural ( index view -- addr u true | false )
  2dup json-kind@ json-integer <> if 2drop false exit then json-text@ natural-text ;
\ Decimal digits of the largest cell, computed once.
: decimal-width ( u -- n ) 0 swap begin swap 1+ swap 10 / dup 0= until drop ;
max-n decimal-width constant cell-digits
\ Decimal numbers, read by hand, so that BASE never matters. Unchecked:
\ addr u holds only decimal digits, as json-natural returns.
\ decimal>u is the value modulo the cell size, exact whenever it fits in
\ an unsigned cell, which is always so for fewer digits than max-n has.
: decimal>u ( addr u -- u ) 0 -rot over + swap ?do 10 * i c@ [char] 0 - + loop ;
\ Ten times u plus the digit c, when that fits in a nonnegative cell.
: digit+ ( u c -- u' true | false )
  [char] 0 - 2dup max-n swap - 10 / > if 2drop false exit then swap 10 * + true ;
\ The value of decimal digits that fit in a nonnegative cell; false when larger.
: digits>u ( addr u -- u true | false )
  dup cell-digits < if decimal>u true exit then dup cell-digits > if 2drop false exit then
  1- 2dup decimal>u -rot + c@ digit+ ;
\ The natural number at index as a cell; false when it is not a natural
\ number or does not fit.
: json-u ( index view -- u true | false ) json-natural if digits>u else false then ;
\ Digits as a natural number in canonical form: nonempty, decimal, and
\ without a leading zero unless it is 0 itself.
: canonical-natural? ( addr u -- flag )
  dup 0= if 2drop false exit then over c@ [char] 0 = over 1 > and if 2drop false exit then
  over + swap digits-end = ;

base !   \ the BASE this file was loaded with (not reached when loading throws)
