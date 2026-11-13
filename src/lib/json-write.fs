\ Deterministic JSON writer (RFC 8259) for one JSON text at a time, such as
\ one NDJSON line, written to the caller's sink. A general tool with no Lean
\ knowledge, for receipts, the derivation log, the API and the round trip
\ of decoded export records. Untrusted.
\ Requires: json.fs (the integer grammar and token tapes, for jw-copy) and
\ bytes.fs (UTF-8 checks), which json.fs loads; outcome.fs.
\ State: none of its own. Every word takes a writer record made by
\ json-writer: or jw-init, so separate writers are independent; one writer
\ is single-threaded. A writer may be a context member: declare it with
\ jw-size context-record: and format it with jw-init in a set-up word. The
\ byte tables below are constant after loading.
\
\ The caller writes a text with jw-start, then one value: scalars
\ (jw-string, jw-n, jw-u, jw-digits, jw-bool, jw-null), or containers
\ (jw-open-object, jw-key and a value per member, jw-close-object;
\ jw-open-array, values, jw-close-array), or jw-copy of a value read by
\ json.fs; then jw-end gives the outcome. Each call passes its bytes to the
\ sink, an xt ( c-addr u -- ) like TYPE, in order; the writer keeps no
\ copy of the text but each open object's last key in sorted mode. The
\ settings jw-limit, jw-sorted and jw-lean are changed only between texts.
\
\ The bytes are deterministic, one canonical form for each value:
\ - no whitespace; members in the order the caller writes them;
\ - with jw-sorted set, each object's keys must strictly increase in byte
\   order (for UTF-8, code point order), so the text is canonical; the
\   writer keeps each open object's last key in its key pool to compare;
\ - integers in decimal whatever BASE is: jw-n a signed cell, jw-u an
\   unsigned cell, jw-digits integer text of any size as json.fs keeps it
\   (an optional minus sign, then 0 or digits without a leading zero;
\   -0 is written 0); no real numbers;
\ - strings escaped one way: \" \\ \b \f \n \r \t for those bytes, \u00xx
\   (lowercase hex) for every other byte below 32, every other byte as
\   itself, valid UTF-8 included. These are the bytes of Python's
\   json.dumps(value, separators=(",", ":"), ensure_ascii=False). With
\   the setting jw-lean set, they are the bytes of Lean's Json.compress
\   instead (Lean 4.35.0, Lean/Data/Json/Printer.lean, escapeAux): only
\   \" \\ \n \r by letter, so backspace, tab and form feed are \u0008,
\   \u0009 and \u000c.
\
\ Failure is sticky: the first call that fails writes nothing, records its
\ outcome, and every later call does nothing until the next jw-start;
\ jw-outcome reads it at any time and jw-end returns it. The sink then
\ holds a prefix of the text, which the caller discards. Outcomes:
\ - invalid: a call out of order (a value where a key is due, a key
\   outside an object, a second value, a close that does not match its
\   open or follows a key, jw-end before the value is complete, any write
\   before jw-start or after jw-end), invalid UTF-8, integer text not in
\   the grammar, a flag that is neither true nor false, a key not above
\   the last one in sorted mode, any call from inside the writer's sink;
\ - full: the text would pass jw-limit bytes, a container would nest
\   deeper than the writer's depth, a key would not fit the key pool in
\   sorted mode, or a string is longer than jw-longest bytes;
\ - unsupported: jw-copy of a real number.
\ So jw-end gives ok only for a complete text, exactly one valid JSON
\ value, and the sink never receives bytes that are not a prefix of one.
\ A caller writing into a buffer of n bytes sets jw-limit to n: a full
\ buffer then gives full before any byte past it is written.
\
\ Sink rules. The sink uses or copies its text before returning: the text
\ may lie in the writer's scratch or in the caller's string. It calls no
\ word of the same writer but jw-outcome and jw-written: any other is
\ refused, failing the text as invalid, and jw-reset or jw-init, which
\ would restart the writer under the call that runs the sink, fail the
\ text as invalid when the sink returns. It should not THROW.
\ THROWs. After a THROW out of the sink the writer is busy and refuses
\ everything until jw-reset. A THROW from anywhere else in a writer word
\ (an interrupt, a stack overflow) is not marked: the writer may still
\ look ok although the text stops part way through a call. So a caller
\ that catches a THROW from a writer word discards the text and calls
\ jw-reset, or jw-start, before writing again.
\ Unchecked: the sink is such an xt and writes over neither the string
\ nor the view being written (it could otherwise turn valid UTF-8 into
\ invalid bytes after the check); strings are real memory; the record
\ keeps the capacity and room jw-init gave it; a view given to jw-copy
\ holds a successful parse. The file loads in decimal whatever BASE is,
\ then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./json.fs
require ./outcome.fs

\ Writer states: what may come next.
0 constant jw-idle                 \ nothing: before jw-start, or after jw-end
1 constant jw-want-value           \ a value: the text's own, or a member's after its key
2 constant jw-want-element         \ in an array: a value, or the array's end
3 constant jw-want-key             \ in an object: a key, or the object's end
4 constant jw-want-end             \ the text's value is complete: jw-end

\ Room for the decimal digits of any cell and a sign, or for one escape.
cell-digits 2 + aligned constant jw-scratch-size

begin-structure /jw-header
  field: jw-sink                   \ xt ( c-addr u -- ) receiving the text
  field: jw-status                 \ ok, or the first failure since jw-start
  field: jw-state                  \ what may come next
  field: jw-busy                   \ true while the sink runs
  field: jw-written                \ bytes given to the sink since jw-start
  field: jw-limit                  \ setting: most bytes in one text
  field: jw-sorted                 \ setting: true when keys must increase
  field: jw-lean                   \ setting: true for Lean's string escapes
  field: jw-depth                 \ containers open
  field: jw-capacity               \ most containers open at once
  field: jw-room                   \ bytes in the key pool
  jw-scratch-size +field jw-scratch   \ digits or an escape being written
end-structure

\ One open container. An object's last key lies in the key pool, after the
\ keys of the objects around it; an array holds no key, so its offset is
\ that of the next object inside it. A container jw-copy opens records
\ where it ends in the view being copied; one the caller opens records -1.
begin-structure /jw-nest
  field: jw-nest-kind              \ json-object or json-array
  field: jw-nest-items             \ members or elements written
  field: jw-nest-key               \ offset of the last key in the pool
  field: jw-nest-key-size          \ its length
  field: jw-nest-end               \ jw-copy's: index of the token after it; else -1
end-structure

\ A record: the header, depth nests, then room bytes of key pool.
: jw-nests ( writer -- addr ) /jw-header + ;
: jw-pool ( writer -- addr ) dup jw-capacity @ /jw-nest * swap jw-nests + ;
\ The innermost open container; unchecked: one is open.
: jw-nest ( writer -- nest ) dup jw-depth @ 1- /jw-nest * swap jw-nests + ;

\ Making a writer for depth nested containers and room bytes of key pool
\ (both at least 0, with a size that fits in a cell). jw-init formats
\ jw-size bytes at writer: idle, outcome ok, keys in any order, Python's
\ escapes, jw-limit max-n; for a bad plan it gives false and writes
\ nothing. json-writer: defines name ( -- writer ) in the dictionary and
\ aborts on a bad plan. jw-sorted, jw-lean and jw-limit are settings the
\ caller may store; they are kept from text to text. The nests and key
\ pool take at most jw-most bytes, so that a record's size fits in a cell.
max-n /jw-header - constant jw-most
: jw-size ( depth room -- u ) swap /jw-nest * + /jw-header + ;
: jw-plan? ( depth room -- flag )
  dup 0 jw-most between? 0= if 2drop false exit then jw-most swap - /jw-nest / upto? ;
: jw-format ( depth room writer -- )
  >r 2dup jw-size r@ swap erase r@ jw-room ! r@ jw-capacity ! max-n r> jw-limit ! ;
: jw-init ( depth room writer -- flag )
  >r 2dup jw-plan? if r> jw-format true else 2drop r> drop false then ;
: json-writer: ( depth room "name" -- )
  2dup jw-plan? 0= abort" json-writer: bad depth or key room"
  create 2dup jw-size here swap allot jw-init drop ;

\ Outcomes. The first failure since jw-start wins.
: jw-outcome ( writer -- outcome ) jw-status @ outcome-sane ;
: jw-fail ( outcome writer -- ) jw-status outcome-first! ;
: jw-invalid ( writer -- ) outcome-invalid swap jw-fail ;
\ Keep a true flag; for a false one, fail the writer with outcome.
: jw-check ( flag outcome writer -- flag ) rot if 2drop true else jw-fail false then ;
: jw-expect ( flag writer -- flag ) outcome-invalid swap jw-check ;
: jw-within ( flag writer -- flag ) outcome-full swap jw-check ;
\ The writer may act: nothing failed, its record is sane, and it is not
\ called from inside its own sink (which fails it as invalid).
: jw-sane? ( writer -- flag )
  dup jw-depth @ over jw-capacity @ upto?
  swap jw-state @ jw-idle jw-want-end between? and ;
: jw-ready? ( writer -- flag )
  dup jw-busy @ over jw-sane? 0= or if jw-invalid false exit then jw-outcome ok? ;

\ Starting and ending a text. jw-start begins a new text for the sink; a
\ call from inside the sink is refused. jw-reset, after a THROW out of a
\ writer word, makes the writer idle and not busy, and fails the text as
\ invalid; a text that had already failed keeps its first failure, so a
\ full text stays full.
: jw-start ( sink writer -- )
  dup jw-busy @ if nip jw-invalid exit then
  tuck jw-sink ! outcome-ok over jw-status ! jw-want-value over jw-state !
  0 over jw-written ! 0 swap jw-depth ! ;
: jw-reset ( writer -- ) false over jw-busy ! jw-idle over jw-state ! jw-invalid ;
\ Ok only once the text's value is complete; the writer is then idle.
: jw-end ( writer -- outcome )
  dup jw-ready? if dup jw-state @ jw-want-end = over jw-expect
    if jw-idle over jw-state ! then then jw-outcome ;

\ Giving bytes to the sink, counting them; busy while it runs. A sink that
\ cleared busy has called jw-reset or jw-init, restarting the writer under
\ the call that gave it the bytes: the text fails as invalid.
: jw-unbusy ( writer -- ) dup jw-busy @ 0= if dup jw-invalid then false swap jw-busy ! ;
: jw-type ( c-addr u writer -- )
  >r dup r@ jw-written +! true r@ jw-busy ! r@ jw-sink @ execute r> jw-unbusy ;
\ Room for n more bytes within jw-limit, else full.
: jw-fits? ( n writer -- flag ) dup jw-limit @ swap jw-written @ - > 0= ;
: jw-room? ( n writer -- flag ) tuck jw-fits? swap jw-within ;

\ Commas: one before every element or member after the first.
: jw-listing? ( writer -- flag ) jw-state @ dup jw-want-element = swap jw-want-key = or ;
: jw-comma? ( writer -- flag )
  dup jw-listing? if jw-nest jw-nest-items @ 0<> else drop false then ;
: jw-comma ( writer -- ) dup jw-comma? if s" ," rot jw-type else drop then ;
\ n bytes, and one more for a comma when one is due.
: jw-with-comma ( n writer -- n' ) jw-comma? if 1+ then ;

\ A container's marks: the bytes that open and close it, "{}" or "[]",
\ and what may come next inside it.
: jw-marks ( kind -- c-addr state )
  json-object = if s" {}" drop jw-want-key else s" []" drop jw-want-element then ;
: jw-inside ( kind -- state ) jw-marks nip ;

\ A value is complete: the text's own, or one more item of its container.
: jw-done ( writer -- )
  dup jw-depth @ 0= if jw-want-end swap jw-state ! exit then
  dup jw-nest 1 over jw-nest-items +! jw-nest-kind @ jw-inside swap jw-state ! ;

\ Whether a value of n bytes may come next (else invalid), with room for
\ it and a comma when one is due (else full).
: jw-value-state? ( writer -- flag )
  jw-state @ dup jw-want-value = swap jw-want-element = or ;
: jw-value-next? ( writer -- flag )
  dup jw-ready? if dup jw-value-state? swap jw-expect else drop false then ;
: jw-value? ( n writer -- flag )
  dup jw-value-next? if tuck jw-with-comma swap jw-room? else 2drop false then ;
\ Write a value whose bytes are c-addr u.
: jw-scalar ( c-addr u writer -- )
  2dup jw-value? if dup jw-comma dup >r jw-type r> jw-done else drop 2drop then ;

\ Literals. jw-bool takes a flag, true or false; any other value is invalid.
: jw-null ( writer -- ) s" null" rot jw-scalar ;
: jw-flag? ( x -- flag ) dup true = swap false = or ;
: jw-bool-text ( flag -- c-addr u ) if s" true" else s" false" then ;
: jw-bool ( flag writer -- )
  over jw-flag? if swap jw-bool-text rot jw-scalar else nip jw-invalid then ;

\ Integers, in decimal whatever BASE is: digits built backwards from the
\ end of the scratch by division, without BASE or pictured output.
: jw-scratch-end ( writer -- addr ) jw-scratch jw-scratch-size + ;
: jw-digit-down ( u addr -- u' addr' ) >r 0 10 um/mod swap [char] 0 + r> 1- tuck c! ;
: jw-u>text ( u end -- c-addr n ) dup >r begin jw-digit-down over 0= until nip r> over - ;
: jw-minus ( c-addr n -- c-addr' n' ) swap 1- [char] - over c! swap 1+ ;
: jw-n>text ( n end -- c-addr n )
  over 0< if swap negate swap jw-u>text jw-minus else jw-u>text then ;
: jw-n ( n writer -- )
  dup jw-ready? if tuck jw-scratch-end jw-n>text rot jw-scalar else 2drop then ;
: jw-u ( u writer -- )
  dup jw-ready? if tuck jw-scratch-end jw-u>text rot jw-scalar else 2drop then ;
\ Integer text of any size: an optional minus sign, then 0 or digits
\ without a leading zero (canonical-natural?); -0 is written 0.
: jw-minus? ( c-addr u -- flag ) if c@ [char] - = else drop false then ;
: jw-integer? ( c-addr u -- flag ) 2dup jw-minus? if 1 /string then canonical-natural? ;
: jw-unminus-zero ( c-addr u -- c-addr' u' ) 2dup s" -0" compare 0= if 1 /string then ;
: jw-digits ( c-addr u writer -- )
  >r 2dup jw-integer? if jw-unminus-zero r> jw-scalar else 2drop r> jw-invalid then ;

\ String escapes, by byte, in a table for each style: 256 letters after
\ the backslash (u for \u00xx), or 0 for a byte that stands for itself;
\ then 256 counts of the bytes the escape adds. Both styles escape the
\ same bytes: every byte below 32, the quote and the backslash.
create jw-json-escapes 512 allot  jw-json-escapes 512 erase
create jw-lean-escapes 512 allot  jw-lean-escapes 512 erase
: jw-extra-of ( letter -- n ) [char] u = if 5 else 1 then ;
: jw-escape! ( letter byte table -- ) + 2dup c! swap jw-extra-of swap 256 + c! ;
: jw-controls! ( table -- ) 32 0 do [char] u i 2 pick jw-escape! loop drop ;
: jw-letter! ( letter byte -- )
  2dup jw-json-escapes jw-escape! jw-lean-escapes jw-escape! ;
jw-json-escapes jw-controls!  jw-lean-escapes jw-controls!
char n lf-byte jw-letter!  char r cr-byte jw-letter!
quote-byte quote-byte jw-letter!  backslash backslash jw-letter!
char b 8 jw-json-escapes jw-escape!  char t 9 jw-json-escapes jw-escape!
char f 12 jw-json-escapes jw-escape!
: jw-escapes ( writer -- table ) jw-lean @ if jw-lean-escapes else jw-json-escapes then ;
: jw-letter ( byte table -- letter ) + c@ ;
: jw-extra ( byte table -- n ) + 256 + c@ ;
\ Whether a byte stands for itself, in either style.
: jw-plain? ( byte -- flag ) jw-json-escapes jw-extra 0= ;

\ Strings no longer than jw-longest bytes have an escaped size, with its
\ quotes, a comma and a colon, that fits in a cell.
max-n 4 - 6 / constant jw-longest
\ The escaped size of a string, quotes included, with the escapes table.
: jw-escaped-size ( c-addr u table -- n )
  >r dup 2 + -rot r> -rot over + swap ?do i c@ over jw-extra rot + swap loop drop ;
\ Text a string or key may hold: not too long (else full) and valid UTF-8
\ (else invalid).
: jw-text? ( c-addr u writer -- flag )
  >r dup jw-longest u> if 2drop false r> jw-within exit then utf8-valid? r> jw-expect ;
\ A string or key that may not be written: drop it and its writer.
: jw-refuse ( c-addr u writer -- false ) drop 2drop false ;

\ Writing a string: the plain bytes in runs, each other byte as its escape,
\ built in the scratch.
: jw-hex-digit ( n -- c ) dup 10 < if [char] 0 else [char] a 10 - then + ;
: jw-hex-pair ( byte addr -- )
  over 4 rshift jw-hex-digit over c! swap 15 and jw-hex-digit swap char+ c! ;
: jw-unicode-escape ( byte scratch -- c-addr 6 )
  >r s" \u00" r@ swap move r@ 4 + jw-hex-pair r> 6 ;
: jw-short-escape ( letter scratch -- c-addr 2 ) backslash over c! tuck char+ c! 2 ;
: jw-escape-text ( byte letter scratch -- c-addr u )
  over [char] u = if nip jw-unicode-escape exit then rot drop jw-short-escape ;
: jw-run-end ( end addr -- end addr' )
  begin 2dup u> while dup c@ jw-plain? while char+ repeat then ;
: jw-run ( end addr writer -- end addr' )
  >r 2dup jw-run-end nip tuck over - ?dup if r@ jw-type else drop then r> drop ;
: jw-escape ( end addr writer -- end addr' )
  >r dup c@ dup r@ jw-escapes jw-letter r@ jw-scratch jw-escape-text r> jw-type char+ ;
: jw-escaped ( c-addr u writer -- )
  >r over + swap begin 2dup u> while r@ jw-run 2dup u> if r@ jw-escape then repeat
  2drop r> drop ;
create jw-quote-mark quote-byte c,
: jw-quote ( writer -- ) jw-quote-mark 1 rot jw-type ;
: jw-quoted ( c-addr u writer -- ) dup jw-quote dup >r jw-escaped r> jw-quote ;
\ A string value.
: jw-string? ( c-addr u writer -- flag )
  dup jw-value-next? 0= if jw-refuse exit then
  >r 2dup r@ jw-text? 0= if r> jw-refuse exit then
  r@ jw-escapes jw-escaped-size r> jw-value? ;
: jw-string ( c-addr u writer -- )
  >r 2dup r@ jw-string? if r@ jw-comma r@ jw-quoted r> jw-done else 2drop r> drop then ;

\ Keys. In sorted mode a key must come after its object's last key (else
\ invalid) and fit in the key pool after the keys of the objects around
\ it (else full); it is kept there once written.
: jw-last-key ( writer -- c-addr u )
  dup jw-nest >r jw-pool r@ jw-nest-key @ + r> jw-nest-key-size @ ;
: jw-after-last? ( c-addr u writer -- flag )
  dup jw-nest jw-nest-items @ 0= if drop 2drop true exit then
  jw-last-key 2swap compare 0< ;
: jw-pool-left ( writer -- n ) dup jw-room @ swap jw-nest jw-nest-key @ - ;
: jw-key-after? ( c-addr u writer -- flag ) dup >r jw-after-last? r> jw-expect ;
: jw-key-fits? ( u writer -- flag ) tuck jw-pool-left > 0= swap jw-within ;
: jw-ordered? ( c-addr u writer -- flag )
  dup jw-sorted @ 0= if drop 2drop true exit then
  >r 2dup r@ jw-key-after? if nip r> jw-key-fits? else r> jw-refuse then ;
: jw-keep-key ( c-addr u writer -- )
  dup jw-sorted @ 0= if drop 2drop exit then
  >r dup r@ jw-nest jw-nest-key-size ! r@ jw-pool r> jw-nest jw-nest-key @ + swap move ;
\ A key may come next: in an object, after its { or a member's value.
: jw-key-next? ( writer -- flag )
  dup jw-ready? if dup jw-state @ jw-want-key = swap jw-expect else drop false then ;
: jw-key-text? ( c-addr u writer -- flag )
  >r 2dup r@ jw-text? if r> jw-ordered? else r> jw-refuse then ;
\ The key's bytes: a comma when due, the quoted key and a colon.
: jw-key-size ( c-addr u writer -- n )
  >r r@ jw-escapes jw-escaped-size 1+ r> jw-with-comma ;
: jw-key? ( c-addr u writer -- flag )
  dup jw-key-next? 0= if jw-refuse exit then
  >r 2dup r@ jw-key-text? if r@ jw-key-size r> jw-room? else r> jw-refuse then ;
: jw-colon ( writer -- ) s" :" rot jw-type ;
: jw-member ( c-addr u writer -- )
  >r r@ jw-comma 2dup r@ jw-quoted r@ jw-colon r@ jw-keep-key
  jw-want-value r> jw-state ! ;
\ The key of the next member; its value follows.
: jw-key ( c-addr u writer -- )
  >r 2dup r@ jw-key? if r> jw-member else 2drop r> drop then ;

\ Containers. An open is a value that nests one level deeper (else full);
\ a close must match the innermost open and may not follow a key.
: jw-key-top ( writer -- offset )
  dup jw-depth @ 0= if drop 0 exit then
  jw-nest dup jw-nest-key @ swap jw-nest-key-size @ + ;
\ One level deeper: a container of kind that ends before token end (-1
\ when jw-copy does not open it), its key after the keys around it.
: jw-push ( kind end writer -- )
  dup jw-key-top swap 1 over jw-depth +! jw-nest
  dup /jw-nest erase tuck jw-nest-key ! tuck jw-nest-end ! jw-nest-kind ! ;
: jw-deeper? ( writer -- flag ) dup jw-depth @ over jw-capacity @ < swap jw-within ;
: jw-open? ( writer -- flag ) 1 over jw-value? if jw-deeper? else drop false then ;
: jw-open-to ( kind end writer -- )
  dup jw-open? 0= if drop 2drop exit then
  >r over r@ jw-comma jw-marks swap 1 r@ jw-type -rot r@ jw-push r> jw-state ! ;
: jw-closable? ( kind writer -- flag )
  dup jw-depth @ 0= if 2drop false exit then
  tuck jw-nest jw-nest-kind @ = swap jw-state @ jw-want-value <> and ;
: jw-close? ( kind writer -- flag )
  dup jw-ready? 0= if 2drop false exit then
  tuck jw-closable? over jw-expect if 1 swap jw-room? else drop false then ;
: jw-closer ( kind -- c-addr 1 ) jw-marks drop char+ 1 ;
: jw-close ( kind writer -- )
  2dup jw-close? if >r jw-closer r@ jw-type -1 r@ jw-depth +! r> jw-done else 2drop then ;
: jw-open-object ( writer -- ) json-object -1 rot jw-open-to ;
: jw-close-object ( writer -- ) json-object swap jw-close ;
: jw-open-array ( writer -- ) json-array -1 rot jw-open-to ;
: jw-close-array ( writer -- ) json-array swap jw-close ;

\ Copying the value at a token index of a json.fs view, with everything in
\ it, as the calls above would write it: keys in the tape's order (in
\ sorted mode they must increase), strings and integers re-encoded in
\ canonical form, a real number unsupported, an index outside the tape
\ invalid. The copy is a loop over the value's tokens, one call per
\ token, without recursion: a container it opens records the index of the
\ token after it, and closes when the copy reaches that token. So the
\ data and return stacks hold a few cells at any depth, which only the
\ writer's depth bounds. Copying stops at the first failure.

\ The copiers of values, by token kind: a container opens, recording
\ where it ends; any other token is written whole.
: jw-copy-object ( index view writer -- ) >r json-next json-object swap r> jw-open-to ;
: jw-copy-array ( index view writer -- ) >r json-next json-array swap r> jw-open-to ;
: jw-copy-string ( index view writer -- ) >r json-text@ r> jw-string ;
: jw-copy-integer ( index view writer -- ) >r json-text@ r> jw-digits ;
: jw-copy-real ( index view writer -- )
  nip nip dup jw-ready? if outcome-unsupported swap jw-fail else drop then ;
: jw-copy-true ( index view writer -- ) nip nip true swap jw-bool ;
: jw-copy-false ( index view writer -- ) nip nip false swap jw-bool ;
: jw-copy-null ( index view writer -- ) nip nip jw-null ;
create jw-copiers 8 cells allot   \ indexed by token kind
: jw-copier! ( xt kind -- ) cells jw-copiers + ! ;
' jw-copy-object json-object jw-copier!  ' jw-copy-array json-array jw-copier!
' jw-copy-string json-string jw-copier!  ' jw-copy-integer json-integer jw-copier!
' jw-copy-real json-real jw-copier!  ' jw-copy-true json-true jw-copier!
' jw-copy-false json-false jw-copier!  ' jw-copy-null json-null jw-copier!
: jw-copier ( index view -- xt ) json-kind@ cells jw-copiers + @ ;

\ Where the innermost container ends, as a token index, when jw-copy
\ opened it; -1 when the caller did, or none is open.
: jw-innermost-end ( writer -- index )
  dup jw-depth @ 0> if jw-nest jw-nest-end @ else drop -1 then ;
\ A key is due: inside an object jw-copy opened, after its { or a member.
\ In an object the caller opened, a token is a value, and so refused.
: jw-key-due? ( writer -- flag )
  dup jw-state @ jw-want-key = swap jw-innermost-end 0>= and ;
\ One token: a key when one is due, else a value.
: jw-copy-key ( index view writer -- ) >r json-text@ r> jw-key ;
: jw-copy-value ( index view writer -- ) >r 2dup jw-copier r> swap execute ;
: jw-copy-token ( index view writer -- )
  dup jw-key-due? if jw-copy-key else jw-copy-value then ;
\ Close each container the copy opened that ends at token i.
: jw-copy-ends? ( i writer -- flag ) tuck jw-innermost-end = swap jw-outcome ok? and ;
: jw-close-innermost ( writer -- ) dup jw-nest jw-nest-kind @ swap jw-close ;
: jw-copy-closes ( i writer -- )
  begin 2dup jw-copy-ends? while dup jw-close-innermost repeat 2drop ;
\ Copy token i, then close what ends after it.
: jw-copy-step ( view writer i -- view writer )
  >r 2dup r@ -rot jw-copy-token r> 1+ over jw-copy-closes ;
\ Copy the tokens first .. end-1 in order, stopping at the first failure.
: jw-copy-tokens ( end first view writer -- )
  2swap ?do i jw-copy-step dup jw-outcome ok? 0= if leave then loop 2drop ;
: jw-token? ( index view -- flag ) json-kind-at json-object json-null between? ;
: jw-copy ( index view writer -- )
  >r 2dup jw-token? if 2dup json-next -rot r> jw-copy-tokens
  else 2drop r> jw-invalid then ;

base !   \ the BASE this file was loaded with
