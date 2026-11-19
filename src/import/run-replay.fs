\ Replay of run records (plan task 2.2.5): a record written earlier is
\ compared, field by field, with the record of a new run of the same
\ input, written by run-record.fs (the driver, tests/support/run-records.fs,
\ checks the input again and calls rr-write first). The answer is a
\ replay report, one JSON text in the format leanforth-replay-report,
\ version 0.1 (schemas/replay-report-0.1.schema.json;
\ docs/programming/RUN_RECORDS.md lists the codes). LeanForth-specific and
\ untrusted; it decides no verdict.
\
\ rp-replay ( c-addr u -- outcome ) reads the old record from the file
\ named c-addr u (rp-replay-text takes it as a text in memory instead)
\ and compares it with the new one, rr-text: ok when they agree in every
\ field, so the record is confirmed; rejected when they differ, with one
\ finding per difference (rp-total counts them); invalid when the old record
\ cannot be compared at all (unreadable or larger than rp-room, not JSON,
\ not a run record of rr-version) or the new one is not there.
\ rp-report ( -- outcome ) then writes the report with TYPE, whole or not
\ at all, and gives the writer's outcome. Nothing is ever confirmed
\ silently: a different input hash, manifest, export, LeanForth commit,
\ host or setting is a finding as much as a different verdict, and only a
\ report without findings says "confirmed".
\
\ How values compare: strings by their decoded text, so an escape such as
\ a equals the letter a and whitespace between tokens is no
\ difference; numbers by their text, so 100000.0 or 1e5 differs from
\ 100000; members by key, whatever their order; array elements in order.
\
\ The new record leads the comparison. For each member of each object in
\ it, the old record must have exactly one member of the same key
\ (missing-field, duplicate-key) with an equal value: of the same JSON
\ kind, the same text for a string or number, the same number of
\ elements for an array, element by element. Each old member whose key the
\ new object lacks is unknown-field. An object with a verdict member (a
\ declaration) compares its verdict first, and nothing else of it when
\ the verdicts differ: accepted-not-established when the old record says
\ accepted and the new run did not accept, else verdict-differs. Other
\ differences are named by the section they are in (input-differs,
\ export-differs, tool-differs, settings-differ, run-differs,
\ declarations-differ), and within a declaration by its member
\ (verdict-differs for its axioms, reason-differs for its
\ diagnostic). The old record is untrusted: it is read only within the
\ new record's shape, so the comparison's depth is the new record's, and
\ JSON nesting deeper than rp-depth is refused as not-json. Paths are
\ JSON paths from $, such as $.declarations[0].verdict; an old key that
\ goes into a path is cut at the path's room, between two characters. The
\ first rp-kept findings are kept; all are counted.
\
\ Requires: run-record.fs (and through it the JSON reader and writer).
\ State: one shared record, run-replay: the two texts, their JSON views
\ (heap memory while rp-replay runs), the path, the current code and the
\ findings; one replay at a time, not re-entrant. The tables are constant
\ after loading. The file loads in decimal whatever BASE is, then restores
\ it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/json.fs
require ../lib/json-write.fs
require ./run-record.fs

rr-text-room 2* constant rp-room   \ largest old record read: room for whitespace
16384 constant rp-token-limit      \ most JSON tokens in either record
8 constant rp-depth                \ deepest nesting of either record
128 constant rp-path-room          \ longest path kept
32 constant rp-kept                \ findings kept
\ Room for the longest report: rp-kept findings whose paths are escaped
\ at six bytes a byte (\u00xx), each with its code and punctuation.
rp-path-room 6 * 64 + rp-kept * 256 + constant rp-report-room
: rp-schema ( -- c-addr u ) s" leanforth-replay-report" ;
: rp-version ( -- c-addr u ) s" 0.1" ;

\ Finding codes, and the names the report gives them.
0 constant rp-unreadable           \ the old record cannot be read, or is too large
1 constant rp-not-json             \ not one JSON text within the limits
2 constant rp-unknown-schema       \ not a leanforth-run-record of rr-version
3 constant rp-rerun-failed         \ the input could not be checked again
4 constant rp-missing-field
5 constant rp-unknown-field
6 constant rp-duplicate-key
7 constant rp-input-differs
8 constant rp-export-differs
9 constant rp-tool-differs
10 constant rp-settings-differ
11 constant rp-run-differs
12 constant rp-declarations-differ
13 constant rp-verdict-differs
14 constant rp-accepted-not-established
15 constant rp-reason-differs
16 constant rp-top                 \ no finding: the record's own level, before a section

\ Tables of entries: a code, a name's length and characters, aligned;
\ the last entry has code -1.
: rp-entry, ( code c-addr u -- ) rot , cell-counted, ;
: rp-entry-code ( entry -- code ) @ ;
: rp-entry-name ( entry -- c-addr u ) cell+ cell-count ;
: rp-entry-next ( entry -- entry' ) rp-entry-name + aligned ;
\ The entry with this name, or the last entry.
: rp-named ( c-addr u table -- entry )
  begin dup rp-entry-code 0< 0= while
    >r 2dup r@ rp-entry-name compare 0= if 2drop r> exit then r> rp-entry-next
  repeat nip nip ;
\ The entry with this code, or the last entry.
: rp-coded ( code table -- entry )
  begin dup rp-entry-code dup 0< 0= swap 3 pick <> and while rp-entry-next repeat nip ;

create rp-names
  rp-unreadable s" unreadable" rp-entry,  rp-not-json s" not-json" rp-entry,
  rp-unknown-schema s" unknown-schema" rp-entry,
  rp-rerun-failed s" rerun-failed" rp-entry,
  rp-missing-field s" missing-field" rp-entry,
  rp-unknown-field s" unknown-field" rp-entry,
  rp-duplicate-key s" duplicate-key" rp-entry,
  rp-input-differs s" input-differs" rp-entry,
  rp-export-differs s" export-differs" rp-entry,
  rp-tool-differs s" tool-differs" rp-entry,
  rp-settings-differ s" settings-differ" rp-entry,
  rp-run-differs s" run-differs" rp-entry,
  rp-declarations-differ s" declarations-differ" rp-entry,
  rp-verdict-differs s" verdict-differs" rp-entry,
  rp-accepted-not-established s" accepted-not-established" rp-entry,
  rp-reason-differs s" reason-differs" rp-entry,  -1 s" ?" rp-entry,
: rp-code-name ( code -- c-addr u ) rp-names rp-coded rp-entry-name ;

\ The code of a difference within a record's section, by the section's key.
create rp-sections
  rp-unknown-schema s" schema" rp-entry,  rp-unknown-schema s" schemaVersion" rp-entry,
  rp-input-differs s" input" rp-entry,  rp-export-differs s" export" rp-entry,
  rp-tool-differs s" leanforth" rp-entry,  rp-tool-differs s" host" rp-entry,
  rp-settings-differ s" settings" rp-entry,  rp-run-differs s" check" rp-entry,
  rp-declarations-differ s" declarations" rp-entry,  -1 s" " rp-entry,
\ ... and within a declaration, by the member's key; others keep the code.
create rp-members
  rp-verdict-differs s" verdict" rp-entry,  rp-verdict-differs s" axioms" rp-entry,
  rp-reason-differs s" diagnostic" rp-entry,  -1 s" " rp-entry,

begin-structure /rp-finding
  field: finding-code
  field: finding-size
  rp-path-room +field finding-path
end-structure

begin-structure /rp
  /json +field rp-old-view
  /json +field rp-new-view
  field: rp-old-size
  rp-room 1+ +field rp-old-buf
  aligned rr-text-room +field rp-new-buf
  aligned field: rp-code              \ the code of a difference here
  field: rp-path-size
  rp-path-room +field rp-path-buf
  aligned field: rp-total             \ findings, all counted
  rp-kept /rp-finding * +field rp-findings
  aligned rp-depth 0 jw-size +field rp-writer
  field: rp-report-size
  rp-report-room +field rp-report-buf  \ the report, typed only once it is complete
end-structure
create run-replay /rp allot  run-replay /rp erase
rp-depth 0 run-replay rp-writer jw-init 0= [if] .( run-replay.fs: writer) cr abort [then]
: rp-old ( -- view ) run-replay rp-old-view ;
: rp-new ( -- view ) run-replay rp-new-view ;

\ The path, and the code of a difference at it: saved and restored around
\ each member and element.
\ Each text buffer of the record is its size field and, after it, its
\ bytes (bounds.fs's cell-counted words read and write it).
: rp-path ( -- c-addr u ) run-replay rp-path-size cell-count ;
\ The bytes of the whole characters of c-addr u that fit in n bytes: a
\ cut never splits a character (review F2). c-addr u is valid UTF-8, as
\ the JSON reader checked; at an invalid byte the cut stops.
: rp-whole ( c-addr u n -- u' )
  >r 0 -rot begin dup while 2dup utf8-length ?dup 0= if 2drop r> drop exit then
    3 pick over + r@ > if drop 2drop r> drop exit then
    dup >r /string rot r> + -rot repeat 2drop r> drop ;
: rp-cut ( c-addr u n -- c-addr u' ) 2 pick -rot rp-whole ;
: rp-path+ ( c-addr u -- )   \ append, cut between characters at the path's room
  rp-path-room run-replay rp-path-size @ - rp-cut run-replay rp-path-size cell-counted+! ;
: rp-saved ( -- size code ) run-replay dup rp-path-size @ swap rp-code @ ;
: rp-restore ( size code -- ) run-replay tuck rp-code ! rp-path-size ! ;
: rp-key+ ( c-addr u -- ) s" ." rp-path+ rp-path+ ;
: rp-index+ ( n -- ) s" [" rp-path+ 0 ud>decimal rp-path+ s" ]" rp-path+ ;

\ Findings.
: rp-finding ( k -- finding ) /rp-finding * run-replay rp-findings + ;
: rp-keep ( code finding -- )
  tuck finding-code ! >r rp-path dup r@ finding-size ! r> finding-path swap move ;
: rp-count ( -- k ) run-replay rp-total dup @ 1 rot +! ;   \ findings before this one
: rp-found ( code -- ) rp-count dup rp-kept < if rp-finding rp-keep else 2drop then ;
\ A finding at the path with one more key, and at the path itself.
: rp-found-at ( code c-addr u -- ) rp-saved 2>r rp-key+ rp-found 2r> rp-restore ;
: rp-differs ( -- ) run-replay rp-code @ rp-found ;

\ The code for a member: a section's at the record's level (run-differs
\ for a key no section names), a member's in a declaration, else the
\ enclosing one.
: rp-or ( code default -- code' ) over 0< if nip else drop then ;
: rp-section-code ( c-addr u -- code )
  rp-sections rp-named rp-entry-code rp-run-differs rp-or ;
: rp-member-code ( c-addr u -- code )
  rp-members rp-named rp-entry-code rp-declarations-differ rp-or ;
: rp-code-for ( c-addr u -- code )
  run-replay rp-code @ dup rp-top = if drop rp-section-code exit then
  dup rp-declarations-differ = if drop rp-member-code else nip nip then ;

\ The first member whose key is c-addr u among the members of an object
\ in view from key token k up to token end: its value.
: rp-at-key? ( c-addr u end k view -- c-addr u end k flag )
  >r 2over 2over nip r> json-text@ compare 0= ;
: rp-step-key ( end k view -- end k' ) >r 1+ r> json-next ;
: rp-scan ( c-addr u end k view -- value true | false )
  >r begin 2dup > while r@ rp-at-key? if nip nip nip 1+ r> drop true exit then
    r@ rp-step-key repeat 2drop 2drop r> drop false ;
\ ... in the whole object at index in view.
: rp-find ( c-addr u object view -- value true | false )
  dup >r json-contents r> rp-scan ;
\ Whether the old object o has another member of key c-addr u after the
\ member whose value is v.
: rp-again? ( c-addr u v o -- flag )
  rp-old json-contents drop swap rp-old json-next rp-old rp-scan dup if nip then ;

defer rp-value ( n o -- )   \ compare value n of the new record with value o of the old

\ Scalars: the same text (decoded strings, integer digits, literals).
: rp-texts ( n o -- c-addr1 u1 c-addr2 u2 ) >r rp-new json-text@ r> rp-old json-text@ ;
: rp-scalar ( n o -- ) rp-texts compare if rp-differs then ;

\ Arrays: as many elements, then each pair, at [i].
: rp-element ( ne oe i -- ne' oe' )
  rp-saved 2>r rp-index+ 2dup rp-value 2r> rp-restore
  swap rp-new json-next swap rp-old json-next ;
: rp-length ( n -- u ) rp-new json-items@ ;
: rp-array ( n o -- )
  over rp-length over rp-old json-items@ <> if 2drop rp-differs exit then
  over rp-length >r 1+ swap 1+ swap r> 0 ?do i rp-element loop 2drop ;

\ Objects. A member of the new record found once in the old is compared
\ under its key; one found never or twice is a finding.
: rp-into ( k v -- )
  rp-saved 2>r over rp-new json-text@ 2dup rp-code-for run-replay rp-code ! rp-key+
  swap 1+ swap rp-value 2r> rp-restore ;
: rp-key-text ( k -- c-addr u ) rp-new json-text@ ;
: rp-new-found ( code k -- ) rp-key-text rp-found-at ;
: rp-twice? ( k o v -- k o v flag ) 2 pick rp-key-text 2 pick 4 pick rp-again? ;
\ Member k of the new record against the old object o: missing, there
\ twice (its value is not compared: which one counts is unclear), or
\ compared.
: rp-in-old ( k o -- k o v true | k o false ) 2dup swap rp-key-text rot rp-old rp-find ;
: rp-member ( k o -- )
  rp-in-old 0= if drop rp-missing-field swap rp-new-found exit then
  rp-twice? if 2drop rp-duplicate-key swap rp-new-found else nip rp-into then ;
: rp-new-members ( n o -- )
  swap rp-new json-contents
  begin 2dup > while dup 3 pick rp-member rp-new rp-step-key repeat 2drop drop ;
\ A member k of the old record whose key the new object n lacks.
: rp-unknown? ( k n -- flag ) >r rp-old json-text@ r> rp-new rp-find dup if nip then 0= ;
: rp-old-found ( code k -- ) rp-old json-text@ rp-found-at ;
: rp-old-member ( k n -- )
  over swap rp-unknown? if rp-unknown-field swap rp-old-found else drop then ;
: rp-old-members ( n o -- )
  rp-old json-contents
  begin 2dup > while dup 3 pick rp-old-member rp-old rp-step-key repeat 2drop drop ;
\ A declaration's verdict, compared first.
: rp-verdict-of ( object view -- value true | false ) >r >r s" verdict" r> r> rp-find ;
: rp-verdicts ( n o -- nv ov true | false )
  swap rp-new rp-verdict-of 0= if drop false exit then
  swap rp-old rp-verdict-of 0= if drop false exit then true ;
: rp-string? ( o -- flag ) rp-old json-string-at? ;
: rp-same-verdict? ( nv ov -- flag )
  dup rp-string? if rp-texts compare 0= else 2drop false then ;
: rp-accepted? ( value view -- flag ) json-text@ s" accepted" compare 0= ;
\ The old record claims accepted where the new run did not accept.
: rp-overclaim? ( nv ov -- flag )
  dup rp-string? 0= if 2drop false exit then
  rp-old rp-accepted? swap rp-new rp-accepted? 0= and ;
: rp-verdict-code ( nv ov -- code )
  rp-overclaim? if rp-accepted-not-established else rp-verdict-differs then ;
\ Whether the verdicts differ, recorded as a finding at .verdict.
: rp-verdict-differs? ( nv ov -- flag )
  2dup rp-same-verdict? if 2drop false exit then
  rp-verdict-code s" verdict" rp-found-at true ;
: rp-object ( n o -- )
  2dup rp-verdicts if rp-verdict-differs? if 2drop exit then then
  2dup rp-new-members rp-old-members ;

\ Any value: of the new record's kind, then by kind.
: rp-kinds ( n o -- kind-new kind-old ) rp-old json-kind@ swap rp-new json-kind@ swap ;
: rp-value-by-kind ( n o -- )
  over rp-new json-kind@ case
    json-object of rp-object endof json-array of rp-array endof
    >r rp-scalar r> endcase ;
: rp-compare-value ( n o -- )
  2dup rp-kinds <> if 2drop rp-differs else rp-value-by-kind then ;
' rp-compare-value is rp-value

\ Reading the old record whole, and parsing both texts.
: rp-old-text ( -- c-addr u ) run-replay rp-old-size cell-count ;
: rp-file-read ( fid -- u flag ) run-replay rp-old-buf rp-room 1+ rot read-file 0= ;
: rp-load-open ( fid -- outcome )
  dup rp-file-read rot close-file 0= and over rp-room > 0= and
  swap run-replay rp-old-size ! flag>outcome ;
: rp-load ( c-addr u -- outcome )
  r/o bin open-file if drop outcome-invalid else rp-load-open then ;
: rp-view ( c-addr u view -- outcome )
  >r rp-depth r@ json-init dup ok? if drop rp-token-limit r@ json-token-limit !
    r@ json-parse else nip nip then r> drop ;
: rp-new-text ( -- c-addr u )
  rr-text tuck run-replay rp-new-buf swap move run-replay rp-new-buf swap ;
\ The old record names this format: its schema and version members hold
\ the strings run-record.fs writes.
: rp-member= ( c-addr u key-addr key-u -- flag )
  0 rp-old rp-find 0= if 2drop false exit then
  dup rp-string? if rp-old json-text@ compare 0= else drop 2drop false then ;
: rp-format? ( -- flag )
  0 rp-old json-object json-kind-at? 0= if false exit then
  rr-schema s" schema" rp-member= rr-version s" schemaVersion" rp-member= and ;

\ The replay itself.
: rp-start ( -- )
  0 run-replay rp-total ! 0 run-replay rp-path-size ! s" $" rp-path+
  rp-top run-replay rp-code ! ;
: rp-refuse ( code -- outcome ) rp-found outcome-invalid ;
: rp-free ( -- ) rp-old json-free rp-new json-free ;
: rp-verdict ( -- outcome )
  run-replay rp-total @ if outcome-rejected else outcome-ok then ;
: rp-parsed ( -- outcome )
  rp-old-text rp-old rp-view ok? 0= if rp-not-json rp-refuse exit then
  rp-format? 0= if rp-unknown-schema rp-refuse exit then
  rp-new-text rp-new rp-view ok? 0= if rp-rerun-failed rp-refuse exit then
  0 0 rp-value rp-verdict ;
\ Compare the old record in the file named c-addr u with rr-text.
: rp-replay ( c-addr u -- outcome )
  rp-start rp-load ok? 0= if rp-unreadable rp-refuse exit then rp-parsed rp-free ;
\ The same for an old record given as the text c-addr u, which is copied
\ first (unreadable when longer than rp-room).
: rp-old! ( c-addr u -- flag ) run-replay rp-old-size rp-room cell-counted! ;
: rp-replay-text ( c-addr u -- outcome )
  rp-start rp-old! 0= if rp-unreadable rp-refuse exit then rp-parsed rp-free ;
\ When the input could not be checked again: the report says so.
: rp-rerun-refused ( -- outcome ) rp-start rp-rerun-failed rp-refuse ;

\ The report.
: rp-w ( -- writer ) run-replay rp-writer ;
: rp-key ( c-addr u -- ) rp-w jw-key ;
: rp-string ( c-addr u -- ) rp-w jw-string ;
: rp-kept# ( -- n ) run-replay rp-total @ rp-kept min ;
: rp-finding-out ( k -- )
  rp-finding rp-w jw-open-object
  s" code" rp-key dup finding-code @ rp-code-name rp-string
  s" path" rp-key dup finding-path swap finding-size @ rp-string rp-w jw-close-object ;
: rp-result ( -- c-addr u ) run-replay rp-total @ if s" refused" else s" confirmed" then ;
: rp-head-out ( -- )
  s" schema" rp-key rp-schema rp-string s" schemaVersion" rp-key rp-version rp-string
  s" result" rp-key rp-result rp-string ;
: rp-findings-out ( -- )
  s" findings" rp-key rp-w jw-open-array rp-kept# 0 ?do i rp-finding-out loop
  rp-w jw-close-array s" findingsTotal" rp-key run-replay rp-total @ rp-w jw-n ;
: rp-body ( -- ) rp-w jw-open-object rp-head-out rp-findings-out rp-w jw-close-object ;
\ Write the report of the last replay with TYPE, then a line feed.
\ The report is written into its buffer first and typed, with a line
\ feed, only when the writer ends ok: a failure types nothing, never part
\ of a text (review F2).
: rp-report-text ( -- c-addr u ) run-replay rp-report-size cell-count ;
: rp-report-sink ( c-addr u -- ) run-replay rp-report-size cell-counted+! ;
: rp-report ( -- outcome )
  0 run-replay rp-report-size ! rp-report-room rp-w jw-limit !
  ['] rp-report-sink rp-w jw-start rp-body rp-w jw-end
  dup ok? if rp-report-text type cr then ;

base !   \ the BASE this file was loaded with
