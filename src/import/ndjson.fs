\ Reader for Lean kernel exports in lean4export NDJSON format 3.1.0, the
\ format the pinned exporter writes (see docs/development/NDJSON_READER.md).
\ Untrusted and fail-closed: it decodes records, it checks nothing about
\ types or proofs, and nothing it hands over is a checked declaration.
\ Requires: lib/json.fs (and through it lib/bytes.fs and lib/lib.fs).
\ State: none of its own. Every word takes an export record made by
\ export:, which holds the line reader, the JSON view, the decoded records,
\ the handler table and the counters, so separate exports are independent;
\ one export is single-threaded. The tables below are constant after
\ loading. Nothing depends on BASE: numbers are read in decimal by hand,
\ and the file itself loads in decimal whatever BASE is, then restores it
\ at the end of a successful load (a THROW while loading leaves BASE
\ decimal: Forth-2012 gives a file no way to restore it then).
\
\ export-read reads a file line by line. Each line must be one JSON object
\ with strict framing (lib/bytes.fs) that is a complete, well-formed record
\ of the format: metadata first, then names, universe levels, expressions
\ and declarations. Each record is decoded and checked whole, then handed
\ to the handler the caller set for its kind, as a decoded record (see the
\ layouts below); an inductive block is handed over as the block and then
\ each of its types, constructors and recursors. A handler returns an
\ outcome; anything but ok stops reading with that outcome. A kind without
\ a handler stops reading as unsupported, so nothing is skipped silently.
\
\ The handler contract: a handler ( record -- outcome ) takes its record
\ and leaves exactly one outcome, nothing else (checked: anything else is
\ invalid, and taking more than the record throws -4 when it leaves fewer
\ items or changes one of the two cells under the record; deeper cells
\ are not checked); it does not call export-read or export-line on the
\ same export (checked: invalid), nor export-init, export-free or
\ export-restart (checked: they throw); it writes neither its record nor
\ the export (not checked, but the reader never reads a record back after
\ its handler: a block's kind is read before, its lists are found again
\ in the checked JSON view, and a view where they are missing is
\ invalid); it copies any text or list it keeps, since strings, digits
\ and lists are valid only until it returns; and a THROW from it passes
\ on to the caller of export-read after the file is closed, with the
\ export idle.
\
\ What is checked: exact field sets (no field missing, unknown or repeated);
\ value kinds; enumerations; index fields dense and in order (names and
\ levels from 1, after the implicit anonymous name and level zero;
\ expressions from 0); every name, level and expression reference to an
\ earlier record, and names that must not be anonymous; natural number
\ literals in canonical decimal; heights within UInt32; metadata naming the
\ pinned exporter 3.1.0, format 3.1.0 and Lean 4.35.0 (else unsupported).
\ Not checked, left to the consumer: distinct names in lists, a
\ declaration's presence in its own `all` list, universe parameter scope,
\ duplicate declaration names, and everything about types.
\
\ Outcomes: ok; invalid for malformed input; unsupported for other format,
\ exporter or Lean versions and for kinds without a handler; full for a
\ limit (a line past the reader's limit, nesting past the JSON depth
\ limit, more JSON tokens on one line than the token limit, a natural
\ number field beyond a cell, no heap). export-error reports the line, the
\ field and the reason.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/json.fs

\ Record kinds, the index of each kind's handler.
0 constant kind-meta
1 constant kind-name-str           2 constant kind-name-num
3 constant kind-succ               4 constant kind-max
5 constant kind-imax               6 constant kind-param
7 constant kind-bvar               8 constant kind-sort
9 constant kind-const              10 constant kind-app
11 constant kind-lam               12 constant kind-forall
13 constant kind-let               14 constant kind-proj
15 constant kind-natval            16 constant kind-strval
17 constant kind-mdata             18 constant kind-axiom
19 constant kind-def               20 constant kind-thm
21 constant kind-opaque            22 constant kind-quot
23 constant kind-inductive         24 constant kind-type
25 constant kind-ctor              26 constant kind-recursor
27 constant kind-count
\ A recursor rule, read with recursor-rule; never handed to a handler.
kind-count constant kind-rule

\ Decoded records. Every record starts with this header; the fields after
\ it depend on the kind. References are indices of earlier records; lists
\ are JSON arrays, kept as the array's token index inverted, below -1, so
\ that no reference or unset field reads as a list (read them with
\ list-count and list-item); texts are an address and a length (read them
\ with 2@); flags are flags.
\ Before each decode every field after the header is set to -1, so no
\ value survives from an earlier record. A record's own fields are all
\ written; a field of another kind reads -1 (as a flag: true) or, since
\ the layouts overlap, one of the record's own fields, so a handler reads
\ only the fields of its record's kind.
begin-structure /record-head
  field: record-kind               \ one of the kinds above
  field: record-index              \ own index; declarations, elements: from 0
  field: record-line               \ NDJSON line number
  field: record-export             \ the export being read
end-structure
/record-head 14 cells + constant /record
/record /record-head - constant /record-body
: text-field: ( n "name" -- n' ) aligned 2 cells +field ;
: layout-fits ( n -- ) /record > abort" ndjson: record layout too large" ;
\ A record body of -1 cells, copied over a record before each decode.
: unset-cells, ( n -- ) 0 ?do -1 , loop ;
create unset-body /record-body cell / unset-cells,
: record-unset ( record -- ) unset-body swap /record-head + /record-body move ;

/record-head                       \ name.str, name.num
  field: name-prefix               \ prefix name
  text-field: name-part            \ str: the component; num: its decimal digits
layout-fits
/record-head field: succ-of layout-fits                     \ level succ
/record-head field: max-left field: max-right layout-fits    \ level max, imax
/record-head field: param-name layout-fits                  \ level param
/record-head field: bvar-index layout-fits                  \ bvar
/record-head field: sort-level layout-fits                  \ sort
/record-head field: const-name field: const-levels layout-fits   \ const; a list
/record-head field: app-fn field: app-arg layout-fits       \ app
/record-head                       \ lam, forallE
  field: binder-name field: binder-type field: binder-body
  field: binder-info               \ 0 default, 1 implicit, 2 strict, 3 instance
layout-fits
/record-head                       \ letE
  field: let-name field: let-type field: let-value field: let-body field: let-nondep
layout-fits
/record-head field: proj-type-name field: proj-idx field: proj-struct layout-fits
/record-head text-field: literal-text layout-fits   \ natVal: digits; strVal: UTF-8
/record-head                       \ mdata; data: a JSON object's index
  field: mdata-expr field: mdata-data
layout-fits
/record-head                       \ meta
  text-field: meta-exporter text-field: meta-exporter-version
  text-field: meta-lean-githash text-field: meta-lean-version
  text-field: meta-format-version
layout-fits
\ Declarations; types, constructors and recursors share the first fields.
/record-head
  field: decl-name field: decl-params   \ params: a list of names
  field: decl-type
dup constant /decl-head
  field: decl-value
  field: decl-all                  \ a list of names
  field: decl-unsafe               \ axiom, opaque: a flag
  field: decl-hints                \ def: 0 opaque, 1 abbrev, 2 regular
  field: decl-height               \ def with regular hints: the height
  field: decl-safety               \ def: 0 safe, 1 unsafe, 2 partial
  field: decl-quot-kind            \ quot: 0 type, 1 ctor, 2 lift, 3 ind
layout-fits
/record-head                       \ inductive block: three lists of objects
  field: block-types field: block-ctors field: block-recursors
layout-fits
/decl-head                         \ inductive type
  field: type-num-params field: type-num-indices field: type-all field: type-ctors
  field: type-num-nested field: type-rec field: type-unsafe field: type-reflexive
layout-fits
/decl-head                         \ constructor
  field: ctor-induct field: ctor-cidx field: ctor-num-params field: ctor-num-fields
  field: ctor-unsafe
layout-fits
/decl-head                         \ recursor; rules: read with recursor-rule
  field: recursor-all field: recursor-num-params field: recursor-num-indices
  field: recursor-num-motives field: recursor-num-minors field: recursor-rules
  field: recursor-k field: recursor-unsafe
layout-fits
/record-head                       \ recursor rule
  field: rule-ctor field: rule-fields field: rule-rhs
layout-fits

begin-structure /export
  /reader +field export-reader
  /json +field export-json
  /record +field export-record     \ the record being decoded
  /record +field export-element    \ a type, constructor or recursor of a block
  /record +field export-rule       \ a recursor rule
  kind-count cells +field export-handlers
  field: export-busy               \ true while a handler runs; before export-names,
                                   \ so that export-restart never clears it
  field: export-bytes              \ bytes of the current line, with its line feed
  field: export-names              \ names so far, counting the anonymous name 0
  field: export-levels             \ levels so far, counting level 0 (zero)
  field: export-exprs              \ expressions so far
  field: export-decls              \ declaration records so far
  field: export-metas              \ metadata records so far
  field: export-ordinal            \ elements of the current block list so far
  field: export-key                \ counted string: the field at a failure, or 0
  field: export-why                \ counted string: why reading failed, or 0
  field: export-at                 \ lines so far: the current line's number
end-structure
\ The fields from export-names on describe progress through one file;
\ export-restart erases them and keeps every field before them.
/export 0 export-names - constant /export-progress

\ Failure: remember why, and give the outcome.
: export-bad ( export c-addr -- outcome ) swap export-why ! outcome-invalid ;
: export-over ( export c-addr -- outcome ) swap export-why ! outcome-full ;
: export-refuse ( export c-addr -- outcome ) swap export-why ! outcome-unsupported ;

\ Tables of named entries: the fields of an object, the kinds of a record
\ family, or the words of an enumeration. A table ends with an entry whose
\ key is empty. An entry's check ( value slot export -- outcome ) decodes a
\ JSON value into the field at slot.
begin-structure /table
  field: table-count               \ entries
  field: table-target              \ export offset of the record its entries fill
  field: table-kind                \ kind of the elements it decodes, or 0
  0 +field table-entries
end-structure
begin-structure /entry
  field: entry-check               \ xt ( value slot export -- outcome ), or 0
  field: entry-offset              \ export offset of the field it fills
  field: entry-kind                \ record kind, or enumeration code
  0 +field entry-key               \ counted string, then aligned
end-structure
: entry-next ( entry -- entry' ) entry-key count + aligned ;
: entry-last? ( entry -- flag ) entry-key count nip 0= ;
: entry-named? ( addr u entry -- flag ) entry-key count compare 0= ;
: entry-find ( addr u table -- entry true | false )
  table-entries begin dup entry-last? 0= while
    >r 2dup r@ entry-named? if 2drop r> true exit then r> entry-next
  repeat drop 2drop false ;

\ Defining tables while loading. shape: name ( -- table ) leaves the new
\ table on the stack for the entries that follow; end-shape closes it.
: shape: ( target kind "name" -- table ) create here >r 0 , swap , , r> ;
: named, ( table "key" -- table ) parse-name counted, 1 over table-count +! ;
\ A field: its offset in the record, its check, and its key.
: nd-member ( table offset xt "key" -- table ) , over table-target @ + , 0 , named, ;
\ A record kind: also its kind code.
: nd-variant ( table offset xt kind "key" -- table )
  >r , over table-target @ + , r> , named, ;
\ An enumeration word and its code.
: nd-choice ( table code "key" -- table ) 0 , 0 , , named, ;
: end-shape ( table -- ) drop 0 , 0 , 0 , 0 0 counted, ;

\ Decoding an object: its fields must be exactly the table's keys.
: export-fits? ( object table export -- flag )
  >r table-count @ swap json-object r> export-json json-items-of
  if = else drop false then ;
: export-entry ( object entry export -- outcome )
  >r dup entry-key r@ export-key ! tuck entry-key swap r@ export-json json-find
  if swap dup entry-offset @ r@ + swap entry-check @ r> swap execute
  else drop r> c" missing or unexpected field" export-bad then ;
: export-entries ( object table export -- outcome )
  >r table-entries begin dup entry-last? 0= while
    2dup r@ export-entry dup ok? 0= if nip nip r> drop exit then drop entry-next
  repeat 2drop r> drop outcome-ok ;
: export-shape ( object table export -- outcome )
  >r 2dup r@ export-fits? if r> export-entries exit then
  2drop r> c" unexpected fields" export-bad ;

\ Checks of single values ( value slot export -- outcome ). Each decodes
\ the JSON value at index value with a decoder ( value export -- x outcome ),
\ which gives the reason when it fails (x is then -1), and slot! stores x
\ into the field at slot when the outcome is ok.
: for-slot ( value slot export -- slot value export ) rot swap ;
: slot! ( slot x outcome -- outcome ) ok-then? if swap ! outcome-ok else nip then ;
\ Defining word: name ( value slot export -- outcome ), the check made
\ from the decoder xt.
: slot-check: ( xt "name" -- ) create , does> @ >r for-slot r> execute slot! ;
\ Natural numbers that fit in a cell.
: not-natural ( export -- -1 outcome )
  c" expected a natural number" export-bad no-result ;
: too-large ( export -- -1 outcome ) c" natural number too large" export-over no-result ;
: nat-of ( value export -- n outcome )
  tuck export-json json-natural 0= if not-natural exit then
  digits>u if nip outcome-ok else too-large then ;
\ References: the index of one of count earlier records.
: bad-ref ( export -- -1 outcome ) c" bad reference" export-bad no-result ;
: ref-below? ( count n outcome -- n flag ) ok? if tuck u> else nip false then ;
: ref-of ( value count export -- n outcome )
  >r swap r@ nat-of ref-below? if r> drop outcome-ok else drop r> bad-ref then ;
: name-of ( value export -- n outcome ) dup export-names @ swap ref-of ;
: anonymous? ( n outcome -- flag ) ok? swap 0= and ;
\ A name that is not the anonymous name 0.
: name+-of ( value export -- n outcome )
  tuck name-of 2dup anonymous? if 2drop bad-ref else rot drop then ;
: level-of ( value export -- n outcome ) dup export-levels @ swap ref-of ;
: expr-of ( value export -- n outcome ) dup export-exprs @ swap ref-of ;
: bool-of ( value export -- flag outcome )
  tuck export-json json-bool if nip outcome-ok exit then
  c" expected a boolean" export-bad no-result ;
' nat-of slot-check: v-nat  ' name-of slot-check: v-name  ' name+-of slot-check: v-name+
' level-of slot-check: v-level  ' expr-of slot-check: v-expr  ' bool-of slot-check: v-bool
\ Texts: their decoders give addr u true, or the outcome and false;
\ text-slot! stores the text with 2!, and text-check: makes their checks.
: string-at ( value export -- addr u true | false )
  export-json 2dup json-kind@ json-string = if json-text@ true else 2drop false then ;
: text-slot! ( slot addr u true | slot outcome false -- outcome )
  if rot 2! outcome-ok else nip then ;
: text-check: ( xt "name" -- ) create , does> @ >r for-slot r> execute text-slot! ;
: text-of ( value export -- addr u true | outcome false )
  tuck string-at if rot drop true else c" expected a string" export-bad false then ;
\ The digits of a natural number of any size.
: numeral-of ( value export -- addr u true | outcome false )
  tuck export-json json-natural if rot drop true else not-natural nip false then ;
\ A string holding a natural number in canonical decimal.
: literal-of ( value export -- addr u true | outcome false )
  dup >r text-of 0= if r> drop false exit then
  2dup canonical-natural? if r> drop true exit then
  2drop r> c" literal is not canonical decimal" export-bad false ;
' text-of text-check: v-text  ' numeral-of text-check: v-digits
' literal-of text-check: v-natlit
\ Enumerations: a string from the table, decoded as its code.
: choice-of ( value export table -- code outcome )
  >r tuck text-of 0= if nip r> drop no-result exit then
  r> entry-find if nip entry-kind @ outcome-ok exit then
  c" unknown enumeration value" export-bad no-result ;
0 0 shape: binder-infos
  0 nd-choice default  1 nd-choice implicit  2 nd-choice strictImplicit
  3 nd-choice instImplicit
end-shape
0 0 shape: safeties  0 nd-choice safe  1 nd-choice unsafe  2 nd-choice partial  end-shape
0 0 shape: quot-kinds
  0 nd-choice type  1 nd-choice ctor  2 nd-choice lift  3 nd-choice ind
end-shape
0 0 shape: hint-words  0 nd-choice opaque  1 nd-choice abbrev  end-shape
: binder-of ( value export -- code outcome ) binder-infos choice-of ;
: safety-of ( value export -- code outcome ) safeties choice-of ;
: quot-kind-of ( value export -- code outcome ) quot-kinds choice-of ;
: hint-of ( value export -- code outcome ) hint-words choice-of ;
' binder-of slot-check: v-binder  ' safety-of slot-check: v-safety
' quot-kind-of slot-check: v-quot-kind  ' hint-of slot-check: v-hint-word
\ Two level references into slot and the cell after it.
: pair? ( value export -- flag )
  export-json json-array swap json-items-of if 2 = else false then ;
: v-pair ( value slot export -- outcome )
  >r over r@ pair? 0= if 2drop r> c" expected two references" export-bad exit then
  swap 1+ swap 2dup r@ v-level ok-then? 0= if nip r> drop exit then
  swap 1+ swap cell+ r> v-level ;
\ Any JSON object, kept as its index (mdata's data).
: export-object? ( value export -- flag ) export-json json-kind@ json-object = ;
: object-of ( value export -- index outcome )
  2dup export-object? if drop outcome-ok exit then
  nip c" expected an object" export-bad no-result ;
' object-of slot-check: v-object
\ A reducibility height: a natural number within UInt32.
: uint32? ( addr u -- flag )
  dup 10 > if 2drop false exit then dup 10 < if 2drop true exit then
  s" 4294967295" compare 1 < ;
: height-of ( value export -- u outcome )
  tuck export-json json-natural 0= if not-natural exit then
  2dup uint32? if decimal>u nip outcome-ok exit then
  2drop c" height beyond UInt32" export-bad no-result ;
' height-of slot-check: v-height

\ Lists. A visit is an action ( item x export -- outcome ) with its x;
\ each-item applies it to every item of a JSON array in order and stops at
\ the first outcome that is not ok.
begin-structure /visit
  field: visit-action
  field: visit-x
end-structure
: visit: ( x xt "name" -- ) create , , ;
: visit-item ( item visit export -- outcome )
  swap dup visit-x @ swap visit-action @ >r swap r> execute ;
: each-item ( list visit export -- outcome )
  rot over export-json json-contents ?do
    2dup i -rot visit-item dup ok? 0= if nip nip unloop exit then drop
    dup export-json i swap json-next i - +loop 2drop outcome-ok ;
: export-array? ( value export -- flag ) export-json json-kind@ json-array = ;
: array-of ( value export -- list outcome )
  2dup export-array? if drop outcome-ok exit then
  nip c" expected a list" export-bad no-result ;
\ A list: a JSON array whose items all pass the visit, kept inverted (see
\ the decoded records).
: list-of ( value visit export -- list outcome )
  rot over array-of dup ok? 0= if 2swap 2drop exit then
  drop dup >r -rot each-item r> invert swap ;
\ Lists of references.
: in-list ( export outcome -- outcome )
  ok? if drop outcome-ok else c" bad reference in list" export-bad then ;
: ref-item ( item decoder export -- outcome ) dup >r swap execute nip r> swap in-list ;
' name+-of ' ref-item visit: name-refs
' level-of ' ref-item visit: level-refs
: names-of ( value export -- list outcome ) name-refs swap list-of ;
: levels-of ( value export -- list outcome ) level-refs swap list-of ;
' names-of slot-check: v-names  ' levels-of slot-check: v-levels
\ Defining words for checks of objects, name ( value slot export -- outcome ):
\ nd-nested decodes one object with the table, ignoring slot; nd-listed
\ decodes a list of such objects, kept in slot.
: nd-nested ( table "name" -- ) create , does> @ rot drop swap export-shape ;
: nd-listed ( table "name" -- )
  create ['] export-shape , , does> >r for-slot r> swap list-of slot! ;

\ The record shapes of format 3.1.0. Each line of a table is one field:
\ its offset in the record, its check and its key.
0 export-record 0 shape: regular-shape
  0 decl-height ' v-height nd-member regular
end-shape
regular-shape nd-nested v-regular-hints
: v-hints ( value slot export -- outcome )
  >r over r@ export-object? if 2 over ! r> v-regular-hints exit then r> v-hint-word ;

0 export-record 0 shape: exporter-shape
  0 meta-exporter ' v-text nd-member name
  0 meta-exporter-version ' v-text nd-member version
end-shape
0 export-record 0 shape: lean-shape
  0 meta-lean-githash ' v-text nd-member githash
  0 meta-lean-version ' v-text nd-member version
end-shape
0 export-record 0 shape: format-shape
  0 meta-format-version ' v-text nd-member version
end-shape
exporter-shape nd-nested v-exporter  lean-shape nd-nested v-lean
format-shape nd-nested v-format
0 export-record 0 shape: meta-shape
  0 ' v-exporter nd-member exporter
  0 ' v-format nd-member format
  0 ' v-lean nd-member lean
end-shape
meta-shape nd-nested v-meta
0 export-record 0 shape: meta-kinds  0 ' v-meta kind-meta nd-variant meta  end-shape

0 export-record 0 shape: str-shape
  0 name-prefix ' v-name nd-member pre
  0 name-part ' v-text nd-member str
end-shape
0 export-record 0 shape: num-shape
  0 name-prefix ' v-name nd-member pre
  0 name-part ' v-digits nd-member i
end-shape
str-shape nd-nested v-str-name  num-shape nd-nested v-num-name
0 export-record 0 shape: name-kinds
  0 ' v-str-name kind-name-str nd-variant str
  0 ' v-num-name kind-name-num nd-variant num
end-shape

0 export-record 0 shape: level-kinds
  0 succ-of ' v-level kind-succ nd-variant succ
  0 max-left ' v-pair kind-max nd-variant max
  0 max-left ' v-pair kind-imax nd-variant imax
  0 param-name ' v-name+ kind-param nd-variant param
end-shape

0 export-record 0 shape: const-shape
  0 const-name ' v-name+ nd-member name
  0 const-levels ' v-levels nd-member us
end-shape
0 export-record 0 shape: app-shape
  0 app-fn ' v-expr nd-member fn
  0 app-arg ' v-expr nd-member arg
end-shape
0 export-record 0 shape: binder-shape
  0 binder-name ' v-name nd-member name
  0 binder-type ' v-expr nd-member type
  0 binder-body ' v-expr nd-member body
  0 binder-info ' v-binder nd-member binderInfo
end-shape
0 export-record 0 shape: let-shape
  0 let-name ' v-name nd-member name
  0 let-type ' v-expr nd-member type
  0 let-value ' v-expr nd-member value
  0 let-body ' v-expr nd-member body
  0 let-nondep ' v-bool nd-member nondep
end-shape
0 export-record 0 shape: proj-shape
  0 proj-type-name ' v-name+ nd-member typeName
  0 proj-idx ' v-nat nd-member idx
  0 proj-struct ' v-expr nd-member struct
end-shape
0 export-record 0 shape: mdata-shape
  0 mdata-expr ' v-expr nd-member expr
  0 mdata-data ' v-object nd-member data
end-shape
const-shape nd-nested v-const  app-shape nd-nested v-app
binder-shape nd-nested v-binder-node  let-shape nd-nested v-let
proj-shape nd-nested v-proj  mdata-shape nd-nested v-mdata
0 export-record 0 shape: expr-kinds     \ most frequent first
  0 ' v-app kind-app nd-variant app
  0 ' v-binder-node kind-lam nd-variant lam
  0 ' v-binder-node kind-forall nd-variant forallE
  0 ' v-const kind-const nd-variant const
  0 ' v-let kind-let nd-variant letE
  0 ' v-proj kind-proj nd-variant proj
  0 sort-level ' v-level kind-sort nd-variant sort
  0 bvar-index ' v-nat kind-bvar nd-variant bvar
  0 literal-text ' v-natlit kind-natval nd-variant natVal
  0 literal-text ' v-text kind-strval nd-variant strVal
  0 ' v-mdata kind-mdata nd-variant mdata
end-shape

0 export-record 0 shape: axiom-shape
  0 decl-name ' v-name+ nd-member name
  0 decl-params ' v-names nd-member levelParams
  0 decl-type ' v-expr nd-member type
  0 decl-unsafe ' v-bool nd-member isUnsafe
end-shape
0 export-record 0 shape: def-shape
  0 decl-name ' v-name+ nd-member name
  0 decl-params ' v-names nd-member levelParams
  0 decl-type ' v-expr nd-member type
  0 decl-value ' v-expr nd-member value
  0 decl-hints ' v-hints nd-member hints
  0 decl-safety ' v-safety nd-member safety
  0 decl-all ' v-names nd-member all
end-shape
0 export-record 0 shape: thm-shape
  0 decl-name ' v-name+ nd-member name
  0 decl-params ' v-names nd-member levelParams
  0 decl-type ' v-expr nd-member type
  0 decl-value ' v-expr nd-member value
  0 decl-all ' v-names nd-member all
end-shape
0 export-record 0 shape: opaque-shape
  0 decl-name ' v-name+ nd-member name
  0 decl-params ' v-names nd-member levelParams
  0 decl-type ' v-expr nd-member type
  0 decl-value ' v-expr nd-member value
  0 decl-unsafe ' v-bool nd-member isUnsafe
  0 decl-all ' v-names nd-member all
end-shape
0 export-record 0 shape: quot-shape
  0 decl-name ' v-name+ nd-member name
  0 decl-params ' v-names nd-member levelParams
  0 decl-type ' v-expr nd-member type
  0 decl-quot-kind ' v-quot-kind nd-member kind
end-shape
0 export-element kind-type shape: type-shape
  0 decl-name ' v-name+ nd-member name
  0 decl-params ' v-names nd-member levelParams
  0 decl-type ' v-expr nd-member type
  0 type-num-params ' v-nat nd-member numParams
  0 type-num-indices ' v-nat nd-member numIndices
  0 type-all ' v-names nd-member all
  0 type-ctors ' v-names nd-member ctors
  0 type-num-nested ' v-nat nd-member numNested
  0 type-rec ' v-bool nd-member isRec
  0 type-unsafe ' v-bool nd-member isUnsafe
  0 type-reflexive ' v-bool nd-member isReflexive
end-shape
0 export-element kind-ctor shape: ctor-shape
  0 decl-name ' v-name+ nd-member name
  0 decl-params ' v-names nd-member levelParams
  0 decl-type ' v-expr nd-member type
  0 ctor-induct ' v-name+ nd-member induct
  0 ctor-cidx ' v-nat nd-member cidx
  0 ctor-num-params ' v-nat nd-member numParams
  0 ctor-num-fields ' v-nat nd-member numFields
  0 ctor-unsafe ' v-bool nd-member isUnsafe
end-shape
0 export-rule 0 shape: rule-shape
  0 rule-ctor ' v-name+ nd-member ctor
  0 rule-fields ' v-nat nd-member nfields
  0 rule-rhs ' v-expr nd-member rhs
end-shape
rule-shape nd-listed v-rules
0 export-element kind-recursor shape: recursor-shape
  0 decl-name ' v-name+ nd-member name
  0 decl-params ' v-names nd-member levelParams
  0 decl-type ' v-expr nd-member type
  0 recursor-all ' v-names nd-member all
  0 recursor-num-params ' v-nat nd-member numParams
  0 recursor-num-indices ' v-nat nd-member numIndices
  0 recursor-num-motives ' v-nat nd-member numMotives
  0 recursor-num-minors ' v-nat nd-member numMinors
  0 recursor-rules ' v-rules nd-member rules
  0 recursor-k ' v-bool nd-member k
  0 recursor-unsafe ' v-bool nd-member isUnsafe
end-shape
type-shape nd-listed v-type-list  ctor-shape nd-listed v-ctors
recursor-shape nd-listed v-recursors
\ A block declares at least one type.
: no-types? ( value export -- flag )
  export-json json-array swap json-items-of if 0= else false then ;
: v-types ( value slot export -- outcome )
  >r over r@ no-types?
  if 2drop r> c" inductive block without types" export-bad exit then r> v-type-list ;
0 export-record 0 shape: inductive-shape
  0 block-types ' v-types nd-member types
  0 block-ctors ' v-ctors nd-member ctors
  0 block-recursors ' v-recursors nd-member recs
end-shape
axiom-shape nd-nested v-axiom  def-shape nd-nested v-def  thm-shape nd-nested v-thm
opaque-shape nd-nested v-opaque  quot-shape nd-nested v-quot
inductive-shape nd-nested v-inductive
0 export-record 0 shape: decl-kinds     \ most frequent first
  0 ' v-thm kind-thm nd-variant thm
  0 ' v-def kind-def nd-variant def
  0 ' v-inductive kind-inductive nd-variant inductive
  0 ' v-opaque kind-opaque nd-variant opaque
  0 ' v-axiom kind-axiom nd-variant axiom
  0 ' v-quot kind-quot nd-variant quot
end-shape

\ Families of indexed records: the index key, the counter the index must
\ equal, and the table of kinds.
begin-structure /family
  field: family-kinds
  field: family-count              \ export offset of its counter
  0 +field family-key              \ counted string
end-structure
: nd-family ( kinds count "key" -- ) create swap , , parse-name counted, ;
expr-kinds 0 export-exprs nd-family expr-family ie
name-kinds 0 export-names nd-family name-family in
level-kinds 0 export-levels nd-family level-family il
create families expr-family , name-family , level-family ,   \ most frequent first
here families - cell / constant #families

\ Handlers ( record -- outcome ), one per kind; by default a kind is refused.
: handler-slot ( kind export -- addr ) export-handlers swap cells + ;
\ The cell that holds the handler of kind, which must be a record kind.
: export-handler ( kind export -- addr )
  over kind-count u< 0= abort" ndjson: no such record kind" handler-slot ;
: export-refused ( record -- outcome )
  record-export @ c" no handler for this record kind" export-refuse ;
: export-handlers-clear ( export -- )
  export-handlers kind-count 0 do ['] export-refused over i cells + ! loop drop ;

\ Calling a handler. It must leave exactly one outcome; anything it leaves
\ instead is dropped and the call gives invalid and false. While it runs
\ the export is busy, so that it cannot read the same export again, and
\ the two cells under the record hold the export as canaries: a handler
\ that took more than its record and left fewer items, or changed a
\ canary, has damaged its caller's data, and that throws -4 (stack
\ underflow). Deeper cells are not checked: Forth cannot isolate a
\ handler's stack. What the reader needs after a handler, the counter it
\ adds to and a declaration's kind, waits on the return stack, not under
\ the canaries. Every THROW from the handler, -4 too, ends the busy mark
\ and passes on.
-4 constant stack-underflow   \ the standard THROW code
: depth-to ( i*x n -- j*x ) begin depth 1- over > while nip repeat drop ;
: handler-call ( record xt -- outcome flag )
  depth 2 - >r execute depth r@ 1+ = if r> drop true exit then
  depth r@ < if stack-underflow throw then r> depth-to outcome-invalid false ;
: export-canaries ( canary canary export -- )
  tuck <> -rot <> or if stack-underflow throw then ;
: busy-call ( record xt export -- canary canary outcome flag )
  true over export-busy ! dup >r dup 2swap
  ['] handler-call catch 0 r> export-busy ! throw ;
: export-run ( record xt export -- outcome flag )
  dup >r busy-call 2swap r> export-canaries ;
\ The handler of the record's kind, or 0 for a kind out of range.
: record-handler ( record export -- xt | 0 )
  swap record-kind @ dup kind-count u< if swap handler-slot @ else 2drop 0 then ;
\ A failure without a reason of its own gets one.
: refusal ( outcome export -- outcome )
  over ok? over export-why @ or if drop exit then
  c" handler refused the record" swap export-why ! ;
: handler-broke ( export -- outcome )
  c" handler left no outcome or extra items" export-bad ;

\ Handing a decoded record over, with no field or reason left from decoding.
: export-line-number ( export -- n ) export-reader reader-lines @ ;
: record-stamp ( record export -- )
  2dup swap record-export ! export-at @ swap record-line ! ;
\ The failed field and the reason, and setting them.
: export-marks ( export -- key why ) dup export-key @ swap export-why @ ;
: export-marks! ( key why export -- ) tuck export-why ! export-key ! ;
: export-unmark ( export -- ) 0 0 rot export-marks! ;
: export-hand ( record export -- outcome )
  2dup record-stamp dup export-unmark 2dup record-handler ?dup 0=
  if nip c" corrupted record kind" export-bad exit then
  swap dup >r export-run if outcome-sane r> refusal else drop r> handler-broke then ;
\ Hand over the decoded record as number n of its family, n the count at
\ count-addr, then count it; the address waits on the return stack.
: record-numbered ( n export -- record ) export-record tuck record-index ! ;
: export-deliver ( count-addr export -- outcome )
  swap dup >r @ over record-numbered swap export-hand dup ok? if 1 r@ +! then r> drop ;

\ Decoding a record's single kind member at key: find its kind in the
\ table, then decode the value after the key into the unset record.
: export-payload ( value entry export -- outcome )
  >r dup entry-kind @ r@ export-record dup record-unset record-kind !
  dup entry-offset @ r@ + swap entry-check @ r> swap execute ;
: export-kind ( key table export -- outcome )
  >r swap tuck r@ export-json json-text@ rot entry-find
  if swap 1+ swap r> export-payload else drop r> c" unknown record kind" export-bad then ;

\ The metadata record must come first, exactly once, naming the pinned
\ versions.
: text= ( text-addr c-addr u -- flag ) rot 2@ compare 0= ;
: pinned-lean? ( record -- flag )
  dup meta-lean-version s" 4.35.0" text=
  swap meta-lean-githash s" eb6cafb7290e8bd5f2937522d8d804f58f02bafc" text= and ;
: pinned? ( record -- flag )
  dup meta-exporter s" lean4export" text= over meta-exporter-version s" 3.1.0" text= and
  over meta-format-version s" 3.1.0" text= and swap pinned-lean? and ;
: export-pinned ( export -- outcome )
  dup export-record pinned? if dup export-metas swap export-deliver exit then
  0 over export-key ! c" unsupported exporter, format or Lean version" export-refuse ;
: export-first ( export -- outcome )
  0 over export-json json-items@ 1 <>
  if c" first record is not metadata" export-bad exit then
  dup >r 1 meta-kinds r> export-kind ok-then? if export-pinned then ;

\ Names, levels and expressions: one index member, which must be the
\ family's next index, and one kind member. Records are top-level
\ objects, so the object is token 0; when the index member comes first,
\ its value is token 2 and the kind's key token 3, else the key is token 1.
: key-value ( c-addr export -- value true | false ) 0 swap export-json json-find ;
: export-family ( export -- value family true | false )
  #families 0 do families i cells + @ 2dup family-key swap key-value
    if rot drop swap true unloop exit then drop
  loop drop false ;
: family-count@ ( family export -- n ) swap family-count @ + @ ;
: index-is? ( count n outcome -- flag ) ok? -rot = and ;
: export-next-index? ( value family export -- flag )
  >r r@ family-count@ swap r@ nat-of index-is? 0 r> export-json json-items@ 2 = and ;
: kind-key ( value -- key ) 2 = if 3 else 1 then ;
: export-indexed ( value family export -- outcome )
  >r 2dup r@ export-next-index?
  0= if 2drop r> c" bad or out-of-order index" export-bad exit then
  swap kind-key over family-kinds @ r@ export-kind
  ok-then? if family-count @ r@ + r> export-deliver else r> drop then ;

\ Declarations: one kind member. An inductive block is followed by its
\ types, constructors and recursors, each as a record of its own kind
\ numbered within its list. They are decoded again from the checked
\ block, so this cannot fail on input. After the block's handler the
\ reader takes nothing from its record: the kind was read before, the
\ three lists are found again in the line's checked JSON view, and the
\ export counts the elements.
: element-start ( kind export -- )
  dup export-ordinal @ over export-element record-index ! 1 over export-ordinal +!
  export-element dup record-unset record-kind ! ;
: export-item ( element table export -- outcome )
  >r dup table-kind @ r@ element-start
  r@ export-shape dup ok? if drop r@ export-element r@ export-hand then r> drop ;
type-shape ' export-item visit: type-elements
ctor-shape ' export-item visit: ctor-elements
recursor-shape ' export-item visit: recursor-elements
: export-elements ( list visit export -- outcome ) 0 over export-ordinal ! each-item ;
\ The array at the counted string key in the block object, token 2 of
\ the line {"inductive":{...}}; invalid only when a handler changed the
\ export's JSON view.
2 constant block-token
: block-value ( c-addr export -- value true | false )
  block-token swap export-json json-find ;
: block-array ( c-addr export -- list true | outcome false )
  tuck block-value if 2dup swap export-array? if nip true exit then drop then
  c" handler changed the export" export-bad false ;
: export-list ( visit c-addr export -- outcome )
  tuck block-array if -rot export-elements else nip nip then ;
: export-types ( export -- outcome ) type-elements c" types" rot export-list ;
: export-ctors ( export -- outcome ) ctor-elements c" ctors" rot export-list ;
: export-recursors ( export -- outcome ) recursor-elements c" recs" rot export-list ;
: export-block ( kind export -- outcome )
  swap kind-inductive <> if drop outcome-ok exit then
  dup export-types ok-then? if dup export-ctors ok-then? if export-recursors then then ;
\ Hand the declaration over, then a block's elements; the kind waits on
\ the return stack.
: export-declared ( export -- outcome )
  dup export-record record-kind @ over 2>r dup export-decls swap export-deliver
  2r> rot ok-then2? if export-block then ;
: export-declaration ( export -- outcome )
  0 over export-json json-items@ 1 <> if c" unknown record kind" export-bad exit then
  dup >r 1 decl-kinds r> export-kind ok-then? if export-declared then ;

\ One parsed line: the metadata first, then the later records.
: export-object-line? ( export -- flag ) 0 swap export-object? ;
: export-later ( export -- outcome )
  dup export-family if rot export-indexed exit then
  c" meta" over key-value if drop c" repeated metadata" export-bad exit then
  export-declaration ;
: export-dispatch ( export -- outcome )
  dup export-object-line? 0= if c" record is not an object" export-bad exit then
  dup export-metas @ 0= if export-first else export-later then ;
: export-json-failed ( outcome export -- outcome )
  dup export-json json-why @ swap export-why ! ;
: export-parse ( addr u export -- outcome )
  >r 2dup text-framed ok? 0=
  if 2drop r> c" carriage return or byte-order mark" export-bad exit then
  r@ export-json json-parse dup ok? 0= if r@ export-json-failed then r> drop ;
: export-decode ( addr u export -- outcome )
  dup export-unmark over 1+ over export-bytes ! dup >r export-parse
  dup ok? if drop r@ export-dispatch then r> drop ;
\ Ok unless a handler of the export is running.
: export-idle ( export -- outcome )
  dup export-busy @ if c" export read again by its own handler" export-bad exit then
  drop outcome-ok ;
\ Check one line in memory and hand its records over, with no field or
\ reason left from an earlier line; the bytes may change in place. The
\ line is counted first: export-at, the lines since export-restart, is
\ the number its records and a failure carry.
: export-line ( addr u export -- outcome )
  dup export-idle ok-then? if 1 over export-at +! export-decode else nip nip then ;
\ Why the reader could not give a line.
: reader-reason ( outcome -- c-addr )
  outcome-full = if c" line too long, or no memory"
  else c" missing final line feed, or a read error" then ;
\ A line the reader cannot give: count it, and say why.
: export-reader-failed ( outcome export -- outcome )
  1 over export-at +! over reader-reason swap export-why ! ;
\ Read, check and hand over the next line of the file, counted from the
\ lines read so far.
: export-next ( export -- outcome )
  dup export-unmark dup export-line-number over export-at !
  >r r@ export-reader reader-line ok-then?
  if r> export-line else nip r> export-reader-failed then ;

\ Reading a whole file.
: export-end ( export -- outcome )
  dup export-line-number over export-at ! dup export-metas @ 0= over export-decls @ 0= or
  if c" missing metadata or declaration" export-bad else drop outcome-ok then ;
: export-lines ( export -- outcome )
  begin dup export-reader reader-more? while
    dup export-next ok-then? 0= if exit then
  repeat export-end ;
\ The words that reset or free an export refuse to run under one of its
\ handlers, where the export is in use: that throws.
: ?export-idle ( export -- export )
  dup export-busy @ abort" ndjson: export in use by its handler" ;
\ Start counting from the beginning of a file.
: export-restart ( export -- )
  ?export-idle dup export-names /export-progress erase
  1 over export-names ! 1 swap export-levels ! ;

1048576 constant export-buffer-size   \ initial line buffer; it grows for longer lines
67108864 constant export-line-limit   \ longest line accepted: 64 MiB
64 constant export-depth-limit        \ deepest JSON nesting accepted
\ Most JSON tokens on one line: 21 times Mathlib's most (3,051), which
\ bounds the token tape to 1.5 MiB with 64-bit cells.
65536 constant export-token-limit

\ Defining word: name ( -- export ), zeroed; export-init prepares it.
: export: ( "name" -- ) create /export store-zeroed, drop ;
\ Allocate the buffers, freeing those of an earlier export-init, and
\ refuse every kind until handlers are set. Full when the heap has no
\ room; export-free then releases what was allocated.
: export-buffers ( export -- outcome )
  export-buffer-size export-line-limit rot export-reader reader-init ;
: export-json-init ( export -- outcome )
  export-json export-depth-limit over json-init
  export-token-limit rot json-token-limit ! ;
: export-init ( export -- outcome )
  ?export-idle dup export-restart dup export-handlers-clear dup export-buffers
  ok-then? if export-json-init then ;
: export-free ( export -- )
  ?export-idle dup export-reader reader-free export-json json-free ;
\ Read every line, closing the file if a handler throws; the exception
\ then passes on, and the export is idle again.
: export-caught ( export -- outcome )
  dup ['] export-lines catch ?dup 0= if nip exit then
  nip swap export-reader reader-close drop throw ;
: export-open ( c-addr u export -- outcome )
  dup >r export-reader reader-open ok?
  if r> drop outcome-ok else r> c" cannot open the file" export-bad then ;
: export-file ( c-addr u export -- outcome )
  dup export-restart dup >r export-open dup ok? if drop r@ export-caught then
  r> export-reader reader-close over ok? if nip else drop then ;
\ Read the export file named c-addr u, handing every record to its handler.
: export-read ( c-addr u export -- outcome )
  dup export-idle ok-then? if export-file else nip nip then ;

\ After a failure: the line, the field being decoded (empty if none) and
\ the reason (empty if none). For a JSON error, json-offset of export-json
\ gives the byte within the line.
: counted-or-empty ( c-addr|0 -- c-addr u ) ?dup if count else s" " then ;
: export-error ( export -- line key-addr key-u why-addr why-u )
  >r r@ export-at @ r@ export-key @ counted-or-empty r> export-why @ counted-or-empty ;

\ Reading decoded records inside a handler.
: record-view ( record -- view ) record-export @ export-json ;
\ The JSON array of a list field, as a token index, and the record's view;
\ false when the field holds no list. Lists are kept inverted: a reference
\ (at least 0) inverts to an index outside the tape, and an unset field
\ (-1) to the line's object, token 0, so neither reads as an array.
: list-array ( list record -- index view true | false )
  record-view >r invert dup r@ json-kind-at json-array =
  if r> true else r> 2drop false then ;
\ The number of items of a list field; 0 when the field holds no list.
: list-count ( list record -- n ) list-array if json-items@ else 0 then ;
\ Whether i is the number of an item of the list field.
: list-has? ( i list record -- flag ) list-count u< ;
\ Whether every item of the array at index is a single token, as in a
\ list of references; a list of objects is not flat.
: flat? ( index view -- flag ) 2dup json-items@ >r json-contents - r> = ;
: flat-array ( list record -- index view true | false )
  list-array 0= if false exit then 2dup flat? if true else 2drop false then ;
: item-u ( index view -- u ) json-u 0= if -1 then ;
\ The token of item i of the flat array at index, with its view; false
\ when the array has no item i.
: nth-token ( i index view -- token view true | false )
  >r 2dup r@ json-items@ u< if + 1+ r> true else 2drop r> drop false then ;
\ Item i of a list of references; -1 when the field holds no flat list or
\ the list has no item i.
: list-item ( i list record -- u )
  flat-array 0= if drop -1 exit then nth-token if item-u else -1 then ;
\ Rule i of a recursor record, decoded into the export's rule record and
\ valid until the next call. Its header has kind-rule, index i, the line
\ and the export. 0 when the record is not a recursor or has no rule i,
\ or when no rule is there any more (a record kept after its handler).
\ export-error stays as it was.
: rule-at ( i index view -- index' )
  tuck json-contents nip swap rot 0 ?do tuck json-next swap loop drop ;
: rule-exists? ( i record -- flag )
  dup record-kind @ kind-recursor = >r dup recursor-rules @ swap list-has? r> and ;
: rule-object ( i record -- index ) dup recursor-rules @ invert swap record-view rule-at ;
: rule-start ( i export -- rule )
  dup export-rule dup record-unset tuck swap record-stamp
  kind-rule over record-kind ! tuck record-index ! ;
\ Decode the rule object at index, leaving the failed field and the
\ reason as they were.
: rule-decode ( index export -- outcome )
  dup export-marks 2>r tuck rule-shape swap export-shape swap 2r> rot export-marks! ;
\ Decode rule i of a recursor record that has it.
: rule-load ( i record -- rule outcome )
  2dup rule-object >r record-export @ tuck rule-start r> rot rule-decode ;
: recursor-rule ( i record -- rule | 0 )
  2dup rule-exists? 0= if 2drop 0 exit then rule-load ok? 0= if drop 0 then ;

base !   \ the BASE this file was loaded with (not reached when loading throws)
