\ Count the records of a Lean NDJSON export by kind, printing the same
\ report as docs/development/measurements/scale-2026-11-02/count.py, with
\ the Forth reader instead of Python. A development and measurement tool;
\ untrusted, like the reader. Usage:
\   gforth src/import/ndjson-count.fs -e 's" FILE" count-export bye'
\ The file is checked against its manifest, FILE.manifest.json, by
\ default (manifest.fs): a missing or wrong manifest is an error.
\ count-manifest ( c-addr u -- ) names another manifest file for the next
\ count; count-export-unchecked counts without the manifest, a choice the
\ caller makes explicitly. On failure it prints one line starting
\ "error:" with the outcome, the reason, the field and the NDJSON line
\ (0 for a manifest failure), and no counts, and Gforth exits at once with
\ status 1; after the report, BYE exits with status 0. count-report and
\ count-report-unchecked print the same without ever exiting, for a Forth
\ session or a batch of files in one process.
\ Requires: ndjson.fs, manifest.fs. State: the tally record, count-tally,
\ a member of the checker context (lib/context.fs), and one export record
\ and one manifest record, counted-export and counted-manifest, which stay
\ shared: they own heap buffers, which a context member may do only with
\ a teardown word (lib/context.fs, since 2026-11-03), and a counting tool
\ gains nothing from one per context; all are reset by every count, so one
\ count runs at a time, in any context.

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/json.fs
require ../lib/decimal.fs
require ./ndjson.fs
require ./manifest.fs

\ Report categories in count.py's sorted order.
20 constant categories
create category-names
  s" decl.axiom" counted,  s" decl.def" counted,  s" decl.inductive" counted,
  s" decl.opaque" counted,  s" decl.quot" counted,  s" decl.thm" counted,
  s" expr.app" counted,  s" expr.bvar" counted,  s" expr.const" counted,
  s" expr.forallE" counted,  s" expr.lam" counted,  s" expr.letE" counted,
  s" expr.mdata" counted,  s" expr.natVal" counted,  s" expr.proj" counted,
  s" expr.sort" counted,  s" expr.strVal" counted,  s" level" counted,
  s" meta" counted,  s" name" counted,
: category-name ( n -- c-addr u ) category-names swap 0 ?do count + aligned loop count ;
\ The number of the category named c-addr u, looked up while loading.
: category-of ( c-addr u -- n )
  categories 0 do 2dup i category-name compare 0= if 2drop i unloop exit then loop
  true abort" ndjson-count: unknown category" ;
s" expr.app" category-of constant first-expr-category
s" expr.strVal" category-of constant last-expr-category
s" level" category-of constant level-category
s" name" category-of constant name-category
\ The category of each record kind, or -1 for the types, constructors and
\ recursors of a block, which count.py counts separately. The table must
\ end at HERE with one cell per record kind (kind-count, ndjson.fs);
\ otherwise the load stops, as layout-fits does in ndjson.fs.
: category, ( c-addr u -- ) category-of , ;
: categories-fit ( table -- )
  here swap - kind-count cells <> abort" ndjson-count: one category per record kind" ;
create kind-categories   \ indexed by kind-meta ... kind-recursor
  s" meta" category,  s" name" category,  s" name" category,
  s" level" category,  s" level" category,  s" level" category,  s" level" category,
  s" expr.bvar" category,  s" expr.sort" category,  s" expr.const" category,
  s" expr.app" category,  s" expr.lam" category,  s" expr.forallE" category,
  s" expr.letE" category,  s" expr.proj" category,  s" expr.natVal" category,
  s" expr.strVal" category,  s" expr.mdata" category,  s" decl.axiom" category,
  s" decl.def" category,  s" decl.thm" category,  s" decl.opaque" category,
  s" decl.quot" category,  s" decl.inductive" category,  -1 , -1 , -1 ,
kind-categories categories-fit
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
/tally context-record: count-tally
export: counted-export
manifest: counted-manifest

: bytes-of ( n -- addr ) 2* cells count-tally tally-bytes + ;
: count-of ( n -- addr ) cells count-tally tally-counts + ;
: max! ( n addr -- ) tuck @ max swap ! ;
: line-bytes ( record -- n ) record-export @ export-bytes @ ;
\ Every record is one line: count it and its bytes in its category.
: tally-category ( bytes n -- ) dup >r bytes-of 0 swap d+! 1 r> count-of +! ;
: tally-line ( record -- outcome )
  dup line-bytes swap record-kind @ kind-category tally-category outcome-ok ;
: lp-bucket ( n -- addr ) lp-buckets 1- min cells count-tally tally-lp + ;
: tally-params ( record -- )
  dup decl-params @ swap list-count
  dup count-tally tally-max-lp max! 1 swap lp-bucket +! ;

\ Handlers, named for this module: src/main.fs loads it beside other
\ readers' handlers (through the command line).
: tally-name-str ( record -- outcome )
  dup name-part 2@ nip 0 count-tally tally-name-bytes d+! tally-line ;
: tally-const ( record -- outcome )
  dup const-levels @ over list-count count-tally tally-max-us max! tally-line ;
: tally-decl ( record -- outcome ) dup tally-params tally-line ;
: tally-type ( record -- outcome )
  1 count-tally tally-types +! dup record-index @ 0= if tally-params else drop then
  outcome-ok ;
\ One more record in the counter at addr.
: tally+ ( record addr -- outcome ) nip 1 swap +! outcome-ok ;
: tally-ctor ( record -- outcome ) count-tally tally-ctors tally+ ;
: tally-recursor ( record -- outcome ) count-tally tally-recursors tally+ ;
\ Set the handler of the kinds first to last.
: on-kinds ( xt last first -- )
  swap 1+ swap ?do dup i counted-export export-handler ! loop drop ;
: count-handlers ( -- )
  ['] tally-line kind-inductive kind-meta on-kinds
  ['] tally-name-str kind-name-str dup on-kinds  ['] tally-const kind-const dup on-kinds
  ['] tally-decl kind-quot kind-axiom on-kinds  ['] tally-type kind-type dup on-kinds
  ['] tally-ctor kind-ctor dup on-kinds  ['] tally-recursor kind-recursor dup on-kinds ;

\ Printing as Python formats numbers: digits grouped by commas, and an
\ average with one decimal, rounded half to even.
: #group ( ud -- ud' ) # 2dup d0= if exit then # 2dup d0= if exit then # ;
: grouped ( ud -- c-addr u ) <# begin #group 2dup d0= 0= while [char] , hold repeat #> ;
\ Round the quotient q up when twice the remainder exceeds the divisor n,
\ or equals it and q is odd.
: round-up? ( rem n q -- flag ) 1 and 0<> >r swap 2* 2dup < -rot = r> and or ;
: round-half-even ( rem q n -- u ) over >r swap round-up? r> swap - ;
\ Ten times bytes per record, rounded half to even.
: tenths ( ud n -- u ) >r 10 1 m*/ r@ um/mod r> round-half-even ;
: .tenths ( u width -- ) >r 0 <# # [char] . hold #s #> r> type-right ;
: .average ( ud count -- ) ."  B  " tenths 6 .tenths ."  B/rec" ;
: .category ( n -- )
  dup category-name 20 type-left space dup count-of @ dup >r 0 grouped 12 type-right
  space bytes-of 2@ 2dup grouped 14 type-right r> .average cr ;
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
  ."  name string bytes " count-tally tally-name-bytes 2@ 0 d.r cr ;
: .maxima ( -- )
  ." max const universe args " count-tally tally-max-us @ .int ."  max decl level params "
  count-tally tally-max-lp @ .int ."  lp histogram " .histogram cr ;
: .blocks ( -- )
  ." inductive types " count-tally tally-types @ .int
  ."  ctors " count-tally tally-ctors @ .int
  ."  recursors " count-tally tally-recursors @ .int cr ;
: .report ( -- ) .categories .tables .bytes .maxima .blocks ;

\ Errors: the outcome's name (outcome-text, lib/outcome.fs, which names
\ any value outside the vocabulary invalid), why, the field, the line and,
\ for a JSON syntax error, the byte within the line.
: .why ( export -- ) dup export-error ." : " type .export-where ;
: .count-error ( outcome -- ) ." error: " outcome-text type counted-export .why cr ;

\ Read the export named c-addr u with fresh counts, by xt ( c-addr u --
\ outcome ): checked against its manifest, or not. The outcome of the
\ read, or invalid (corrupted state) for any Forth exception, after which
\ export-read has closed the file.
: count-start ( -- outcome )
  count-tally /tally erase counted-export export-init dup ok?
  if drop count-handlers counted-export counted-manifest manifest-init then ;
: count-fault ( x x -- outcome )
  2drop 0 counted-export export-key !
  c" a Forth exception" counted-export export-why ! outcome-invalid ;
: count-checked-read ( c-addr u -- outcome ) counted-manifest manifest-read ;
: count-plain-read ( c-addr u -- outcome ) counted-export export-read ;
: count-read ( c-addr u xt -- outcome )
  >r count-start ok-then? 0= if nip r> drop exit then
  r> catch if count-fault then ;
\ Print the report, or one error line; true after the report.
: count-shown? ( c-addr u xt -- flag )
  count-read dup ok? if drop .report true else .count-error false then ;
: count-report ( c-addr u -- ) ['] count-checked-read count-shown? drop ;
: count-report-unchecked ( c-addr u -- ) ['] count-plain-read count-shown? drop ;
\ Name the manifest file of the next count; the string must stay
\ unchanged until then.
: count-manifest ( c-addr u -- ) counted-manifest manifest-use ;

\ Leaving the host with a failure status. Forth-2012 has no BYE with a
\ status; Gforth 0.7.3 and 1.0 (the CI hosts) both have (bye) ( n -- ),
\ which flushes the output and ends the process with status n (checked on
\ both, 2026-11-02). Elsewhere an uncaught THROW (ABORT) ends the run,
\ which a host running a command line reports as a failure.
[defined] (bye) [if]
  : exit-failure ( -- ) 1 (bye) ;
[else]
  : exit-failure ( -- ) -1 throw ;
[then]
\ The command line's words: print, and after an error line exit at once
\ with status 1. count-export checks the manifest; count-export-unchecked
\ is the explicit choice not to.
: count-by ( c-addr u read -- ) count-shown? 0= if exit-failure then ;
: count-export ( c-addr u -- ) ['] count-checked-read count-by ;
: count-export-unchecked ( c-addr u -- ) ['] count-plain-read count-by ;
