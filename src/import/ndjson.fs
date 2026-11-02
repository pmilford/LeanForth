\ Reader for Lean kernel exports in lean4export NDJSON format 3.1.0, the
\ format the pinned exporter writes (see docs/development/NDJSON_READER.md).
\ Untrusted and fail-closed: it decodes records, it checks nothing about
\ types or proofs, and nothing it hands over is a checked declaration.
\ Requires: lib/json.fs (and through it lib/bytes.fs and lib/lib.fs).
\ State: none of its own. Every word takes an export record made by
\ export:, which holds the line reader, the JSON view, the decoded records,
\ the handler table and the counters, so separate exports are independent;
\ one export is single-threaded. The tables below are constant after
\ loading.
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
\ exporter or Lean versions and for kinds without a handler; exhausted for
\ a limit (a line past the reader's limit, nesting past the JSON depth
\ limit, a natural number field beyond a cell, no heap). export-error
\ reports the line, the field and the reason. Strings, digits and list
\ indices in a decoded record are valid only during its handler.

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

\ Decoded records. Every record starts with this header; the fields after
\ it depend on the kind. References are indices of earlier records; lists
\ are indices of JSON arrays (read them with list-count and list-item);
\ texts are an address and a length (read them with 2@); flags are flags.
begin-structure /record-head
  field: record-kind               \ one of the kinds above
  field: record-index              \ own index; declarations, elements: from 0
  field: record-line               \ NDJSON line number
  field: record-export             \ the export being read
end-structure
/record-head 14 cells + constant /record
: text: ( n "name" -- n' ) aligned 2 cells +field ;
: layout-fits ( n -- ) /record > abort" ndjson: record layout too large" ;

/record-head                       \ name.str, name.num
  field: name-prefix               \ prefix name
  text: name-part                  \ str: the component; num: its decimal digits
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
/record-head text: literal-text layout-fits   \ natVal: digits; strVal: UTF-8
/record-head                       \ mdata; data: a JSON object's index
  field: mdata-expr field: mdata-data
layout-fits
/record-head                       \ meta
  text: meta-exporter text: meta-exporter-version
  text: meta-lean-githash text: meta-lean-version text: meta-format-version
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
  field: export-names              \ names so far, counting the anonymous name 0
  field: export-levels             \ levels so far, counting level 0 (zero)
  field: export-exprs              \ expressions so far
  field: export-decls              \ declaration records so far
  field: export-metas              \ metadata records so far
  field: export-bytes              \ bytes of the current line, with its line feed
  field: export-key                \ counted string: the field at a failure, or 0
  field: export-why                \ counted string: why reading failed, or 0
  field: export-at                 \ line of the failure
end-structure

\ Failure: remember why, and give the outcome.
: export-bad ( export c-addr -- outcome ) swap export-why ! outcome-invalid ;
: export-over ( export c-addr -- outcome ) swap export-why ! outcome-exhausted ;
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
: member ( table offset xt "key" -- table ) , over table-target @ + , 0 , named, ;
\ A record kind: also its kind code.
: variant ( table offset xt kind "key" -- table )
  >r , over table-target @ + , r> , named, ;
\ An enumeration word and its code.
: choice ( table code "key" -- table ) 0 , 0 , , named, ;
: end-shape ( table -- ) drop 0 , 0 , 0 , 0 0 counted, ;

\ Decoding an object: its fields must be exactly the table's keys.
: export-fits? ( object table export -- flag )
  export-json >r over r@ json-kind@ json-object =
  -rot table-count @ swap r> json-items@ = and ;
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

\ Checks of single values ( value slot export -- outcome ). A natural
\ number cell is the value, or -1 when it does not fit, or -2 when the
\ value is not a natural number.
: export-cell ( value export -- n )
  export-json json-natural if digits>u 0= if -1 then else -2 then ;
: put-cell ( slot n export -- outcome )
  over -1 = if nip nip c" natural number too large" export-over exit then
  over 0< if nip nip c" expected a natural number" export-bad exit then
  drop swap ! outcome-ok ;
: v-nat ( value slot export -- outcome ) rot over export-cell swap put-cell ;
\ References: the index of one of count earlier records, else -1.
: ref-cell ( value count export -- n )
  rot swap export-cell dup rot 0 swap within 0= if drop -1 then ;
: put-ref ( slot n export -- outcome )
  over 0< if nip nip c" bad reference" export-bad else drop swap ! outcome-ok then ;
: name-cell ( value export -- n ) dup export-names @ swap ref-cell ;
: name+-cell ( value export -- n ) name-cell dup 0= if drop -1 then ;   \ not anonymous
: level-cell ( value export -- n ) dup export-levels @ swap ref-cell ;
: expr-cell ( value export -- n ) dup export-exprs @ swap ref-cell ;
: v-name ( value slot export -- outcome ) rot over name-cell swap put-ref ;
: v-name+ ( value slot export -- outcome ) rot over name+-cell swap put-ref ;
: v-level ( value slot export -- outcome ) rot over level-cell swap put-ref ;
: v-expr ( value slot export -- outcome ) rot over expr-cell swap put-ref ;
: v-bool ( value slot export -- outcome )
  rot over export-json json-bool 0= if nip c" expected a boolean" export-bad exit then
  rot ! drop outcome-ok ;
\ Texts.
: string-at ( value export -- addr u true | false )
  export-json 2dup json-kind@ json-string = if json-text@ true else 2drop false then ;
: put-text ( slot export addr u -- outcome ) rot drop rot 2! outcome-ok ;
: v-text ( value slot export -- outcome )
  rot over string-at if put-text else nip c" expected a string" export-bad then ;
: v-digits ( value slot export -- outcome )
  rot over export-json json-natural if put-text exit then
  nip c" expected a natural number" export-bad ;
: v-natlit ( value slot export -- outcome )
  rot over string-at 0= if nip c" expected a string" export-bad exit then
  2dup canonical-natural? if put-text exit then
  2drop nip c" literal is not canonical decimal" export-bad ;
\ Enumerations: a string from the table, stored as its code.
: v-choice ( value slot export table -- outcome )
  >r rot over string-at 0= if nip r> drop c" expected a string" export-bad exit then
  r> entry-find 0= if nip c" unknown enumeration value" export-bad exit then
  entry-kind @ rot ! drop outcome-ok ;
0 0 shape: binder-infos
  0 choice default  1 choice implicit  2 choice strictImplicit  3 choice instImplicit
end-shape
0 0 shape: safeties  0 choice safe  1 choice unsafe  2 choice partial  end-shape
0 0 shape: quot-kinds  0 choice type  1 choice ctor  2 choice lift  3 choice ind
end-shape
0 0 shape: hint-words  0 choice opaque  1 choice abbrev  end-shape
: v-binder ( value slot export -- outcome ) binder-infos v-choice ;
: v-safety ( value slot export -- outcome ) safeties v-choice ;
: v-quot-kind ( value slot export -- outcome ) quot-kinds v-choice ;
\ Two level references into slot and the cell after it.
: pair? ( value export -- flag )
  export-json 2dup json-kind@ json-array = -rot json-items@ 2 = and ;
: v-pair ( value slot export -- outcome )
  >r over r@ pair? 0= if 2drop r> c" expected two references" export-bad exit then
  swap 1+ swap 2dup r@ v-level ok-then? 0= if nip r> drop exit then
  swap 1+ swap cell+ r> v-level ;
\ Any JSON object, kept as its index (mdata's data).
: export-object? ( value export -- flag ) export-json json-kind@ json-object = ;
: v-object ( value slot export -- outcome )
  >r over r@ export-object? if ! r> drop outcome-ok exit then
  2drop r> c" expected an object" export-bad ;
\ A reducibility height: a natural number within UInt32.
: uint32? ( addr u -- flag )
  dup 10 > if 2drop false exit then dup 10 < if 2drop true exit then
  s" 4294967295" compare 1 < ;
: digits>cell ( addr u -- u ) 0 0 2swap >number 2drop drop ;
: v-height ( value slot export -- outcome )
  rot over export-json json-natural
  0= if nip c" expected a natural number" export-bad exit then
  2dup uint32? 0= if 2drop nip c" height beyond UInt32" export-bad exit then
  digits>cell nip swap ! outcome-ok ;

\ Lists. A list of references: every element's cell, from xt
\ ( value export -- n ), must be a reference; the slot keeps the list.
: refs-ok? ( list export xt -- flag )
  2>r 2r@ drop export-json json-contents begin 2dup > while
    dup 2r@ execute 0< if 2drop 2r> 2drop false exit then 1+
  repeat 2drop 2r> 2drop true ;
: export-array? ( value export -- flag ) export-json json-kind@ json-array = ;
: v-list ( value slot export xt -- outcome )
  >r >r over r@ export-array?
  0= if 2drop r> r> drop c" expected a list" export-bad exit then
  over swap ! r@ swap r> r> refs-ok? if drop outcome-ok exit then
  c" bad reference in list" export-bad ;
: v-names ( value slot export -- outcome ) ['] name+-cell v-list ;
: v-levels ( value slot export -- outcome ) ['] level-cell v-list ;
\ A list of objects, each decoded with the table.
: export-objects ( list table export -- outcome )
  swap 2>r 2r@ drop export-json json-contents begin 2dup > while
    dup 2r@ swap export-shape dup ok? 0= if nip nip 2r> 2drop exit then drop
    2r@ drop export-json json-next
  repeat 2drop 2r> 2drop outcome-ok ;
: v-objects ( value slot export table -- outcome )
  >r >r over r@ export-array?
  0= if 2drop r> r> drop c" expected a list" export-bad exit then
  over swap ! r> r> swap export-objects ;
\ Defining words for checks of nested objects: name ( value slot export -- outcome ).
: nested ( table "name" -- ) create , does> @ rot drop swap export-shape ;
: listed ( table "name" -- ) create , does> @ v-objects ;

\ The record shapes of format 3.1.0. Each line of a table is one field:
\ its offset in the record, its check and its key.
0 export-record 0 shape: regular-shape
  0 decl-height ' v-height member regular
end-shape
regular-shape nested v-regular-hints
: v-hints ( value slot export -- outcome )
  >r over r@ export-object? if 2 over ! r> v-regular-hints exit then
  r> hint-words v-choice ;

0 export-record 0 shape: exporter-shape
  0 meta-exporter ' v-text member name
  0 meta-exporter-version ' v-text member version
end-shape
0 export-record 0 shape: lean-shape
  0 meta-lean-githash ' v-text member githash
  0 meta-lean-version ' v-text member version
end-shape
0 export-record 0 shape: format-shape
  0 meta-format-version ' v-text member version
end-shape
exporter-shape nested v-exporter  lean-shape nested v-lean  format-shape nested v-format
0 export-record 0 shape: meta-shape
  0 ' v-exporter member exporter
  0 ' v-format member format
  0 ' v-lean member lean
end-shape
meta-shape nested v-meta
0 export-record 0 shape: meta-kinds  0 ' v-meta kind-meta variant meta  end-shape

0 export-record 0 shape: str-shape
  0 name-prefix ' v-name member pre
  0 name-part ' v-text member str
end-shape
0 export-record 0 shape: num-shape
  0 name-prefix ' v-name member pre
  0 name-part ' v-digits member i
end-shape
str-shape nested v-str-name  num-shape nested v-num-name
0 export-record 0 shape: name-kinds
  0 ' v-str-name kind-name-str variant str
  0 ' v-num-name kind-name-num variant num
end-shape

0 export-record 0 shape: level-kinds
  0 succ-of ' v-level kind-succ variant succ
  0 max-left ' v-pair kind-max variant max
  0 max-left ' v-pair kind-imax variant imax
  0 param-name ' v-name+ kind-param variant param
end-shape

0 export-record 0 shape: const-shape
  0 const-name ' v-name+ member name
  0 const-levels ' v-levels member us
end-shape
0 export-record 0 shape: app-shape
  0 app-fn ' v-expr member fn
  0 app-arg ' v-expr member arg
end-shape
0 export-record 0 shape: binder-shape
  0 binder-name ' v-name member name
  0 binder-type ' v-expr member type
  0 binder-body ' v-expr member body
  0 binder-info ' v-binder member binderInfo
end-shape
0 export-record 0 shape: let-shape
  0 let-name ' v-name member name
  0 let-type ' v-expr member type
  0 let-value ' v-expr member value
  0 let-body ' v-expr member body
  0 let-nondep ' v-bool member nondep
end-shape
0 export-record 0 shape: proj-shape
  0 proj-type-name ' v-name+ member typeName
  0 proj-idx ' v-nat member idx
  0 proj-struct ' v-expr member struct
end-shape
0 export-record 0 shape: mdata-shape
  0 mdata-expr ' v-expr member expr
  0 mdata-data ' v-object member data
end-shape
const-shape nested v-const  app-shape nested v-app  binder-shape nested v-binder-node
let-shape nested v-let  proj-shape nested v-proj  mdata-shape nested v-mdata
0 export-record 0 shape: expr-kinds     \ most frequent first
  0 ' v-app kind-app variant app
  0 ' v-binder-node kind-lam variant lam
  0 ' v-binder-node kind-forall variant forallE
  0 ' v-const kind-const variant const
  0 ' v-let kind-let variant letE
  0 ' v-proj kind-proj variant proj
  0 sort-level ' v-level kind-sort variant sort
  0 bvar-index ' v-nat kind-bvar variant bvar
  0 literal-text ' v-natlit kind-natval variant natVal
  0 literal-text ' v-text kind-strval variant strVal
  0 ' v-mdata kind-mdata variant mdata
end-shape

0 export-record 0 shape: axiom-shape
  0 decl-name ' v-name+ member name
  0 decl-params ' v-names member levelParams
  0 decl-type ' v-expr member type
  0 decl-unsafe ' v-bool member isUnsafe
end-shape
0 export-record 0 shape: def-shape
  0 decl-name ' v-name+ member name
  0 decl-params ' v-names member levelParams
  0 decl-type ' v-expr member type
  0 decl-value ' v-expr member value
  0 decl-hints ' v-hints member hints
  0 decl-safety ' v-safety member safety
  0 decl-all ' v-names member all
end-shape
0 export-record 0 shape: thm-shape
  0 decl-name ' v-name+ member name
  0 decl-params ' v-names member levelParams
  0 decl-type ' v-expr member type
  0 decl-value ' v-expr member value
  0 decl-all ' v-names member all
end-shape
0 export-record 0 shape: opaque-shape
  0 decl-name ' v-name+ member name
  0 decl-params ' v-names member levelParams
  0 decl-type ' v-expr member type
  0 decl-value ' v-expr member value
  0 decl-unsafe ' v-bool member isUnsafe
  0 decl-all ' v-names member all
end-shape
0 export-record 0 shape: quot-shape
  0 decl-name ' v-name+ member name
  0 decl-params ' v-names member levelParams
  0 decl-type ' v-expr member type
  0 decl-quot-kind ' v-quot-kind member kind
end-shape
0 export-element kind-type shape: type-shape
  0 decl-name ' v-name+ member name
  0 decl-params ' v-names member levelParams
  0 decl-type ' v-expr member type
  0 type-num-params ' v-nat member numParams
  0 type-num-indices ' v-nat member numIndices
  0 type-all ' v-names member all
  0 type-ctors ' v-names member ctors
  0 type-num-nested ' v-nat member numNested
  0 type-rec ' v-bool member isRec
  0 type-unsafe ' v-bool member isUnsafe
  0 type-reflexive ' v-bool member isReflexive
end-shape
0 export-element kind-ctor shape: ctor-shape
  0 decl-name ' v-name+ member name
  0 decl-params ' v-names member levelParams
  0 decl-type ' v-expr member type
  0 ctor-induct ' v-name+ member induct
  0 ctor-cidx ' v-nat member cidx
  0 ctor-num-params ' v-nat member numParams
  0 ctor-num-fields ' v-nat member numFields
  0 ctor-unsafe ' v-bool member isUnsafe
end-shape
0 export-rule 0 shape: rule-shape
  0 rule-ctor ' v-name+ member ctor
  0 rule-fields ' v-nat member nfields
  0 rule-rhs ' v-expr member rhs
end-shape
rule-shape listed v-rules
0 export-element kind-recursor shape: recursor-shape
  0 decl-name ' v-name+ member name
  0 decl-params ' v-names member levelParams
  0 decl-type ' v-expr member type
  0 recursor-all ' v-names member all
  0 recursor-num-params ' v-nat member numParams
  0 recursor-num-indices ' v-nat member numIndices
  0 recursor-num-motives ' v-nat member numMotives
  0 recursor-num-minors ' v-nat member numMinors
  0 recursor-rules ' v-rules member rules
  0 recursor-k ' v-bool member k
  0 recursor-unsafe ' v-bool member isUnsafe
end-shape
type-shape listed v-type-list  ctor-shape listed v-ctors
recursor-shape listed v-recursors
\ A block declares at least one type.
: v-types ( value slot export -- outcome )
  >r over r@ export-json json-items@ 0=
  if 2drop r> c" inductive block without types" export-bad exit then r> v-type-list ;
0 export-record 0 shape: inductive-shape
  0 block-types ' v-types member types
  0 block-ctors ' v-ctors member ctors
  0 block-recursors ' v-recursors member recs
end-shape
axiom-shape nested v-axiom  def-shape nested v-def  thm-shape nested v-thm
opaque-shape nested v-opaque  quot-shape nested v-quot
inductive-shape nested v-inductive
0 export-record 0 shape: decl-kinds     \ most frequent first
  0 ' v-thm kind-thm variant thm
  0 ' v-def kind-def variant def
  0 ' v-inductive kind-inductive variant inductive
  0 ' v-opaque kind-opaque variant opaque
  0 ' v-axiom kind-axiom variant axiom
  0 ' v-quot kind-quot variant quot
end-shape

\ Families of indexed records: the index key, the counter the index must
\ equal, and the table of kinds.
begin-structure /family
  field: family-kinds
  field: family-count              \ export offset of its counter
  0 +field family-key              \ counted string
end-structure
: family ( kinds count "key" -- ) create swap , , parse-name counted, ;
expr-kinds 0 export-exprs family expr-family ie
name-kinds 0 export-names family name-family in
level-kinds 0 export-levels family level-family il
create families expr-family , name-family , level-family ,   \ most frequent first

\ Handlers ( record -- outcome ), one per kind.
: export-handler ( kind export -- addr ) export-handlers swap cells + ;
: export-refused ( record -- outcome ) drop outcome-unsupported ;
: export-handlers-clear ( export -- )
  export-handlers kind-count 0 do ['] export-refused over i cells + ! loop drop ;

\ Handing a decoded record over.
: export-line-number ( export -- n ) export-reader reader-lines @ ;
: record-stamp ( record export -- )
  2dup swap record-export ! export-line-number swap record-line ! ;
: export-hand ( record export -- outcome )
  2dup record-stamp over record-kind @ dup kind-count u<
  0= if 2drop drop outcome-invalid exit then swap export-handler @ execute outcome-sane ;
\ Hand over the decoded record as number count of its family, then count it.
: export-deliver ( count-addr export -- outcome )
  >r dup @ r@ export-record record-index ! r@ export-record r@ export-hand
  ok-then? if 1 swap +! outcome-ok then r> drop ;

\ Decoding a record's single kind member at key: find its kind in the
\ table, then decode the value after the key.
: export-payload ( value entry export -- outcome )
  >r dup entry-kind @ r@ export-record record-kind !
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
  3 0 do families i cells + @ 2dup family-key swap key-value
    if rot drop swap true unloop exit then drop
  loop drop false ;
: family-count@ ( family export -- n ) swap family-count @ + @ ;
: export-next-index? ( value family export -- flag )
  >r r@ family-count@ swap r@ export-cell = 0 r> export-json json-items@ 2 = and ;
: kind-key ( value -- key ) 2 = if 3 else 1 then ;
: export-indexed ( value family export -- outcome )
  >r 2dup r@ export-next-index?
  0= if 2drop r> c" bad or out-of-order index" export-bad exit then
  swap kind-key over family-kinds @ r@ export-kind
  ok-then? if family-count @ r@ + r> export-deliver else r> drop then ;

\ Declarations: one kind member. An inductive block is followed by its
\ types, constructors and recursors, each as a record of its own kind
\ numbered within its list. They are decoded again from the checked
\ block, so this cannot fail on input.
: export-item ( element table export -- outcome )
  >r dup table-kind @ r@ export-element tuck record-kind ! 1 swap record-index +!
  r@ export-shape dup ok? if drop r@ export-element r@ export-hand then r> drop ;
: export-elements ( list table export -- outcome )
  -1 over export-element record-index ! swap 2>r 2r@ drop export-json json-contents
  begin 2dup > while
    dup 2r@ swap export-item dup ok? 0= if nip nip 2r> 2drop exit then drop
    2r@ drop export-json json-next
  repeat 2drop 2r> 2drop outcome-ok ;
: export-types ( export -- outcome )
  dup export-record block-types @ type-shape rot export-elements ;
: export-ctors ( export -- outcome )
  dup export-record block-ctors @ ctor-shape rot export-elements ;
: export-recursors ( export -- outcome )
  dup export-record block-recursors @ recursor-shape rot export-elements ;
: export-block ( export -- outcome )
  dup export-record record-kind @ kind-inductive <> if drop outcome-ok exit then
  dup export-types ok-then? if dup export-ctors ok-then? if export-recursors then then ;
: export-declared ( export -- outcome )
  dup export-decls over export-deliver ok-then? if export-block then ;
: export-declaration ( export -- outcome )
  0 over export-json json-items@ 1 <> if c" unknown record kind" export-bad exit then
  dup >r 1 decl-kinds r> export-kind ok-then? if export-declared then ;

\ One parsed line.
: export-object-line? ( export -- flag ) 0 swap export-object? ;
: export-dispatch ( export -- outcome )
  dup export-object-line? 0= if c" record is not an object" export-bad exit then
  dup export-metas @ 0= if export-first exit then
  dup export-family if rot export-indexed exit then
  c" meta" over key-value if drop c" repeated metadata" export-bad exit then
  export-declaration ;
: export-json-failed ( outcome export -- outcome )
  dup export-json json-why @ swap export-why ! ;
: export-parse ( addr u export -- outcome )
  >r 2dup text-framed ok? 0=
  if 2drop r> c" carriage return or byte-order mark" export-bad exit then
  r@ export-json json-parse dup ok? 0= if r@ export-json-failed then r> drop ;
: export-line ( addr u export -- outcome )
  over 1+ over export-bytes ! dup >r export-parse
  dup ok? if drop r@ export-dispatch then r> drop ;
: export-reader-failed ( outcome export -- outcome )
  over outcome-exhausted = if c" line too long, or no memory" else
  c" missing final line feed, or a read error" then swap export-why ! ;
\ Read, check and hand over the next line; export-at is its number.
: export-next ( export -- outcome )
  0 over export-key ! 0 over export-why ! dup export-line-number 1+ over export-at !
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
: export-restart ( export -- )
  1 over export-names ! 1 over export-levels ! 0 over export-exprs ! 0 over export-decls !
  0 over export-metas ! 0 over export-key ! 0 over export-why ! 0 swap export-at ! ;

1048576 constant export-buffer-size   \ initial line buffer; it grows for longer lines
67108864 constant export-line-limit   \ longest line accepted: 64 MiB
64 constant export-depth-limit        \ deepest JSON nesting accepted

\ Defining word: name ( -- export ), zeroed; export-init prepares it.
: export: ( "name" -- ) create /export store-zeroed, drop ;
\ Allocate the buffers and refuse every kind until handlers are set.
\ Exhausted when the heap has no room; export-free then releases what was
\ allocated.
: export-buffers ( export -- outcome )
  export-buffer-size export-line-limit rot export-reader reader-init ;
: export-init ( export -- outcome )
  dup export-handlers-clear dup export-buffers
  ok-then? if export-depth-limit swap export-json json-init then ;
: export-free ( export -- ) dup export-reader reader-free export-json json-free ;
\ Read the export file named c-addr u, handing every record to its handler.
: export-read ( c-addr u export -- outcome )
  dup export-restart >r r@ export-reader reader-open dup ok? if drop r@ export-lines then
  r> export-reader reader-close over ok? if nip else drop then ;

\ After a failure: the line, the field being decoded (empty if none) and
\ the reason (empty if none). For a JSON error, json-offset of export-json
\ gives the byte within the line.
: counted-or-empty ( c-addr|0 -- c-addr u ) ?dup if count else s" " then ;
: export-error ( export -- line key-addr key-u why-addr why-u )
  >r r@ export-at @ r@ export-key @ counted-or-empty r> export-why @ counted-or-empty ;

\ Reading decoded records inside a handler.
: record-view ( record -- view ) record-export @ export-json ;
\ The number of items of a list field, and its item i (unchecked index).
: list-count ( list record -- n ) record-view json-items@ ;
: list-item ( i list record -- u ) record-view >r + 1+ r> json-u 0= if -1 then ;
\ Rule i of a recursor record's rules (unchecked index), decoded into the
\ export's rule record, valid until the next call.
: rule-at ( i list view -- index )
  tuck json-contents nip swap rot 0 ?do tuck json-next swap loop drop ;
: recursor-rule ( i record -- rule )
  dup record-export @ >r recursor-rules @ r@ export-json rule-at
  rule-shape r@ export-shape drop r> export-rule ;
