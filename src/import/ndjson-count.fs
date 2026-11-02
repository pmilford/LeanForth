\ Count the records of a Lean NDJSON export by kind, printing the same
\ report as docs/development/measurements/scale-2026-11-02/count.py, with
\ the Forth reader instead of Python. A development and measurement tool;
\ untrusted, like the reader. Usage:
\   gforth src/import/ndjson-count.fs -e 's" FILE" count-export bye'
\ On failure it prints one line starting "error:" with the outcome, the
\ reason, the field and the NDJSON line, and no counts.
\ Requires: ndjson.fs. State: one export record and one tally record,
\ reset by every count-export; not re-entrant.

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/json.fs
require ./ndjson.fs

\ Report categories in count.py's sorted order, and the category of each
\ record kind (-1 for the types, constructors and recursors of a block,
\ which count.py counts separately).
20 constant categories
create category-names
  s" decl.axiom" counted,  s" decl.def" counted,  s" decl.inductive" counted,
  s" decl.opaque" counted,  s" decl.quot" counted,  s" decl.thm" counted,
  s" expr.app" counted,  s" expr.bvar" counted,  s" expr.const" counted,
  s" expr.forallE" counted,  s" expr.lam" counted,  s" expr.letE" counted,
  s" expr.mdata" counted,  s" expr.natVal" counted,  s" expr.proj" counted,
  s" expr.sort" counted,  s" expr.strVal" counted,  s" level" counted,
  s" meta" counted,  s" name" counted,
6 constant first-expr-category     16 constant last-expr-category
17 constant level-category         19 constant name-category
create kind-categories   \ indexed by kind-meta ... kind-recursor
  18 , 19 , 19 , 17 , 17 , 17 , 17 , 7 , 15 , 8 , 6 , 10 , 9 , 11 , 14 , 13 , 16 , 12 ,
  0 , 1 , 5 , 3 , 4 , 2 , -1 , -1 , -1 ,
: category-name ( n -- c-addr u ) category-names swap 0 ?do count + aligned loop count ;
: kind-category ( kind -- n ) cells kind-categories + @ ;

\ Level-parameter counts are tallied exactly up to 255; larger ones
\ share the last bucket.
256 constant lp-buckets
begin-structure /tally
  categories cells +field tally-counts
  categories 2* cells +field tally-bytes   \ doubles
  aligned 2 cells +field tally-name-bytes  \ a double
  field: tally-max-us
  field: tally-max-lp
  field: tally-types
  field: tally-ctors
  field: tally-recursors
  lp-buckets cells +field tally-lp
end-structure
create tally /tally allot
export: counted-export

: bytes-of ( n -- addr ) 2* cells tally tally-bytes + ;
: count-of ( n -- addr ) cells tally tally-counts + ;
: d+! ( d addr -- ) dup >r 2@ d+ r> 2! ;
: max! ( n addr -- ) tuck @ max swap ! ;
: line-bytes ( record -- n ) record-export @ export-bytes @ ;
\ Every record is one line: count it and its bytes in its category.
: tally-category ( bytes n -- ) dup >r bytes-of 0 swap d+! 1 r> count-of +! ;
: tally-line ( record -- outcome )
  dup line-bytes swap record-kind @ kind-category tally-category outcome-ok ;
: lp-bucket ( n -- addr ) lp-buckets 1- min cells tally tally-lp + ;
: tally-params ( record -- )
  dup decl-params @ swap list-count dup tally tally-max-lp max! 1 swap lp-bucket +! ;

\ Handlers.
: on-name-str ( record -- outcome )
  dup name-part 2@ nip 0 tally tally-name-bytes d+! tally-line ;
: on-const ( record -- outcome )
  dup const-levels @ over list-count tally tally-max-us max! tally-line ;
: on-decl ( record -- outcome ) dup tally-params tally-line ;
: on-type ( record -- outcome )
  1 tally tally-types +! dup record-index @ 0= if tally-params else drop then outcome-ok ;
: on-ctor ( record -- outcome ) drop 1 tally tally-ctors +! outcome-ok ;
: on-recursor ( record -- outcome ) drop 1 tally tally-recursors +! outcome-ok ;
\ Set the handler of the kinds first to last.
: on-kinds ( xt last first -- )
  swap 1+ swap ?do dup i counted-export export-handler ! loop drop ;
: count-handlers ( -- )
  ['] tally-line kind-inductive kind-meta on-kinds
  ['] on-name-str kind-name-str dup on-kinds  ['] on-const kind-const dup on-kinds
  ['] on-decl kind-quot kind-axiom on-kinds  ['] on-type kind-type dup on-kinds
  ['] on-ctor kind-ctor dup on-kinds  ['] on-recursor kind-recursor dup on-kinds ;

\ Printing as Python formats numbers: digits grouped by commas, and an
\ average with one decimal, rounded half to even.
: #group ( ud -- ud' ) # 2dup d0= if exit then # 2dup d0= if exit then # ;
: grouped ( ud -- c-addr u ) <# begin #group 2dup d0= 0= while [char] , hold repeat #> ;
: right ( c-addr u width -- ) over - 0 max spaces type ;
: left ( c-addr u width -- ) over - 0 max >r type r> spaces ;
\ Round the quotient q up when twice the remainder exceeds the divisor n,
\ or equals it and q is odd.
: round-half-even ( rem q n -- u )
  rot 2* swap 2dup > -rot = rot dup 1 and rot and rot or if 1+ then ;
\ Ten times bytes per record, rounded half to even.
: tenths ( ud n -- u ) >r 10 1 m*/ r@ um/mod r> round-half-even ;
: .tenths ( u width -- ) >r 0 <# # [char] . hold #s #> r> right ;
: .category ( n -- )
  dup category-name 20 left space dup count-of @ dup >r 0 grouped 12 right space
  bytes-of 2@ 2dup grouped 14 right ."  B  " r> tenths 6 .tenths ."  B/rec" cr ;
: .categories ( -- ) categories 0 do i count-of @ if i .category then loop ;
: category-sum ( lo hi -- n ) 0 -rot 1+ swap ?do i count-of @ + loop ;
: total-bytes ( -- ud ) 0 0 categories 0 do i bytes-of 2@ d+ loop ;
\ One histogram entry as a Python tuple, with a separator unless it is the first.
: .bucket ( first i -- first' )
  dup lp-bucket @ ?dup 0= if drop exit then
  rot 0= if ." , " then ." (" swap 0 .r ." , " 0 .r ." )" false ;
: .histogram ( -- ) ." [" true lp-buckets 0 do i .bucket loop drop ." ]" ;
: .int ( n -- ) 0 .r ;
: .tables ( -- )
  ." names " name-category count-of @ .int ."  levels " level-category count-of @ .int
  ."  exprs " first-expr-category last-expr-category category-sum .int cr ;
: .bytes ( -- )
  ." total bytes " total-bytes 0 d.r
  ."  name string bytes " tally tally-name-bytes 2@ 0 d.r cr ;
: .maxima ( -- )
  ." max const universe args " tally tally-max-us @ .int
  ."  max decl level params " tally tally-max-lp @ .int ."  lp histogram " .histogram cr ;
: .blocks ( -- )
  ." inductive types " tally tally-types @ .int ."  ctors " tally tally-ctors @ .int
  ."  recursors " tally tally-recursors @ .int cr ;
: .report ( -- ) .categories .tables .bytes .maxima .blocks ;

\ Errors: the outcome's name, why, the field, the line and, for a JSON
\ syntax error, the byte within the line.
: .outcome ( outcome -- )
  case outcome-invalid of ." invalid" endof
    outcome-exhausted of ." exhausted (a limit)" endof
    outcome-unsupported of ." unsupported" endof
    outcome-unknown of ." unknown" endof
    outcome-rejected of ." rejected" endof
    ." internal fault" endcase ;
: .json-offset ( export -- )
  export-json dup json-why @ if ." , byte " json-offset .int else drop then ;
: .field ( c-addr u -- ) dup if ." field " type ." , " else 2drop then ;
: .why ( export -- )
  dup export-error ." : " type ."  (" .field ." line " .int .json-offset ." )" ;
: .count-error ( outcome -- ) ." error: " .outcome counted-export .why cr ;

\ Read the export named c-addr u with fresh counts; the outcome of the
\ read, or internal fault (-1) for any Forth exception.
: count-start ( -- outcome )
  tally /tally erase counted-export export-free counted-export export-init
  dup ok? if count-handlers then ;
: count-fault ( x x x -- -1 )
  2drop drop counted-export export-reader reader-close drop 0 counted-export export-key !
  c" a Forth exception" counted-export export-why ! -1 ;
: count-read ( c-addr u -- outcome )
  count-start ok-then? 0= if nip exit then
  counted-export ['] export-read catch if count-fault then ;
\ Print the report, or one error line.
: count-export ( c-addr u -- ) count-read dup ok? if drop .report else .count-error then ;
