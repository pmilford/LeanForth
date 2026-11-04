\ Re-exporter for Lean NDJSON exports (plan task 3.2.4): every record the
\ reader (ndjson.fs) hands over is written back as NDJSON, byte for byte
\ as lean4export 3.1.0, the exporter pinned with Lean 4.35.0, writes it.
\ Reading an export and writing it again closes a round trip that
\ scripts/ndjson-reexport.sh compares with the original, byte for byte
\ (docs/development/NDJSON_READER.md, "Re-export"). A development and test
\ tool; untrusted, like the reader, and never part of a check. Usage:
\   gforth-fast src/import/ndjson-emit.fs -e 's" IN" s" OUT" reexport bye'
\ It prints one line, the number of lines written or an error, and after
\ an error exits at once with status 1. OUT must not name IN.
\
\ The format, from the exporter's source in the pinned toolchain
\ (src/lean/LeanExport/Basic.lean, which prints each record's
\ Json.compress with IO.println) and Lean's JSON printer
\ (src/lean/Lean/Data/Json/Printer.lean and Basic.lean):
\ - one JSON object per line, then a line feed; no other white space;
\ - every object's keys in increasing order (a Lean Json object is a tree
\   map of its keys), so a name's, level's or expression's index key
\   comes before or after its kind key by the two keys alone:
\   {"app":{"arg":12,"fn":1},"ie":13} but {"ie":15,"lam":{...}};
\ - natural numbers in decimal without leading zeros (a JsonNumber with
\   exponent 0); a natVal literal as a string of such digits;
\ - strings as Lean's Json.escape writes them: " \ line feed and carriage
\   return as \" \\ \n \r, every other byte below 32 as \u00xx in
\   lowercase hex (so tab is \u0009, not \t), every other character as
\   its UTF-8 bytes: the JSON writer's jw-lean setting;
\ - an inductive block as {"inductive":{"ctors":[...],"recs":[...],
\   "types":[...]}}, each element an object with its keys in order;
\ - mdata's data as an object of strings (KVMap.toJson), also in key
\   order: its members are sorted here, whatever their order in the line.
\ The JSON writer (lib/json-write.fs) writes every value and checks that
\ each object's keys increase (jw-sorted), so a key written out of Lean's
\ order fails the line instead of being written.
\
\ An inductive block's types come from the reader before its constructors
\ and recursors but are written after them: they wait in their own buffer
\ until the block's last element. Lines wait in the output buffer and go
\ to the file a mebibyte at a time; a line that fails takes its bytes
\ back, and after a failure every later record is refused at once.
\
\ Outcomes: ok; any outcome of the reader; invalid for a record that
\ cannot be written in the format (an enumeration code out of range,
\ mdata's data with two equal keys or an object inside it out of order, a
\ block element outside a block, a line while a block is unfinished);
\ full when a buffer would pass reexport-buffer-limit, the heap has no
\ room, a key does not fit the writer's key pool (4,096 bytes, for mdata's
\ keys), mdata's data has more than data-most members, or writing or
\ closing the file fails (a full disk, say). A Forth exception while
\ reading is invalid.
\ Requires: ndjson.fs and lib/json-write.fs. State: the module record
\ reexporter (the writer, the output and types buffers, the counts, the
\ file written and mdata's sorted keys), reached through the accessors
\ below it, and one export record, reexported. Both stay shared, like
\ ndjson-count.fs's export record: they own heap buffers, which a context
\ member may do only with a teardown word (lib/context.fs, since
\ 2026-11-03), and a test tool gains nothing from one context each;
\ reexport-begin resets both, so one re-export runs at a time. The tables
\ below are constant after loading. The file loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/json.fs
require ../lib/json-write.fs
require ./ndjson.fs

\ Byte buffers on the heap: a block, its size and the bytes it holds, from
\ its start. A buffer grows by doubling, up to reexport-buffer-limit.
begin-structure /buffer
  field: buffer-addr               \ the heap block, or 0
  field: buffer-size               \ its size
  field: buffer-used               \ bytes held
end-structure
1048576 constant reexport-buffer-start   \ first size; and how much output waits
\ 256 MiB: four times the reader's longest line, since Lean's escapes make
\ a string at most three times as long as the JSON text it was read from.
268435456 constant reexport-buffer-limit
: buffer-text ( buffer -- c-addr u ) dup buffer-addr @ swap buffer-used @ ;
: buffer-end ( buffer -- addr ) buffer-text + ;
: buffer-left ( buffer -- n ) dup buffer-size @ swap buffer-used @ - ;
: buffer-empty ( buffer -- ) 0 swap buffer-used ! ;
: buffer-release ( buffer -- ) dup buffer-addr heap-release /buffer erase ;
\ A heap block of size bytes in place of the one at addr, 0 for none.
: block-resize ( addr size -- addr' ior ) over if resize else nip allocate then ;
\ The size to grow to for n more bytes: twice the size, or more.
: buffer-wanted ( n buffer -- size )
  dup buffer-used @ rot + swap buffer-size @ 2* max reexport-buffer-start max ;
\ Grow for n more bytes; false, the buffer unchanged, past the limit or
\ when the heap has no room.
: buffer-grow ( n buffer -- flag )
  tuck buffer-wanted dup reexport-buffer-limit > if 2drop false exit then
  over buffer-addr @ over block-resize if drop 2drop false exit then
  rot tuck buffer-addr ! buffer-size ! true ;
: buffer-room? ( n buffer -- flag )
  2dup buffer-left > if buffer-grow else 2drop true then ;
: buffer-append ( c-addr u buffer -- flag )
  2dup buffer-room? 0= if drop 2drop false exit then
  >r tuck r@ buffer-end swap move r> buffer-used +! true ;

\ The module record. The writer nests as deep as the reader's JSON, and
\ keeps each open object's last key for the order check.
64 constant reexport-depth
4096 constant reexport-key-room
256 constant data-most             \ most members of mdata's data
begin-structure /reexporter
  /buffer +field reexport-out      \ lines not yet written to the file
  /buffer +field reexport-types    \ an inductive block's types, until its end
  field: reexport-target           \ the buffer the writer's sink fills
  field: reexport-status           \ ok, or the first failure since reexport-begin
  field: reexport-fid              \ the file written; 0 keeps the lines in memory
  field: reexport-left             \ elements of the current block still to come
  field: reexport-recursors        \ recursors of the current block
  field: reexport-lines            \ lines written
  field: reexport-mark             \ the output's size where the current line starts
  data-most cells +field reexport-members   \ mdata's key tokens, sorted
  reexport-depth reexport-key-room jw-size +field reexport-writer
end-structure
create reexporter /reexporter allot  reexporter /reexporter erase
export: reexported
\ The state's accessors; nothing else names reexporter.
: emit-w ( -- writer ) reexporter reexport-writer ;
: emit-out ( -- buffer ) reexporter reexport-out ;
: emit-types ( -- buffer ) reexporter reexport-types ;
: emit-target ( -- addr ) reexporter reexport-target ;
: emit-outcome ( -- addr ) reexporter reexport-status ;
: emit-fid ( -- addr ) reexporter reexport-fid ;
: block-left ( -- addr ) reexporter reexport-left ;
: left-recursors ( -- addr ) reexporter reexport-recursors ;
: emit-lines ( -- addr ) reexporter reexport-lines ;
: emit-mark ( -- addr ) reexporter reexport-mark ;
: member ( i -- addr ) cells reexporter reexport-members + ;
\ Stop loading when a check made while loading fails.
: load-check ( flag -- ) 0= abort" ndjson-emit: inconsistent tables" ;
reexport-depth reexport-key-room emit-w jw-init load-check

\ Failure: the first one since reexport-begin stays.
: emit-status ( -- outcome ) emit-outcome @ ;
: emit-fail ( outcome -- ) emit-status ok? if emit-outcome ! else drop then ;
: emit-invalid ( -- ) outcome-invalid emit-fail ;
\ Bytes into a buffer; a buffer that cannot take them fails as full.
: emit-bytes ( c-addr u buffer -- ) buffer-append 0= if outcome-full emit-fail then ;
\ The writer's sink, and starting one text of the writer into a buffer.
: emit-sink ( c-addr u -- ) emit-target @ emit-bytes ;
: emit-text ( buffer -- ) emit-target ! ['] emit-sink emit-w jw-start ;

\ Writing values and members. A member's value is read from a record's
\ field at addr: a natural number, a flag, a text, a numeral's digits or
\ a list of references.
: emit-key ( c-addr u -- ) emit-w jw-key ;
: emit-u ( u -- ) emit-w jw-u ;
: emit-string ( text-addr -- ) 2@ emit-w jw-string ;
: emit-open ( -- ) emit-w jw-open-object ;
: emit-close ( -- ) emit-w jw-close-object ;
: emit-open-list ( -- ) emit-w jw-open-array ;
: emit-close-list ( -- ) emit-w jw-close-array ;
: u-member ( addr c-addr u -- ) emit-key @ emit-u ;
: flag-member ( addr c-addr u -- ) emit-key @ emit-w jw-bool ;
: text-member ( addr c-addr u -- ) emit-key emit-string ;
: digits-member ( addr c-addr u -- ) emit-key 2@ emit-w jw-digits ;
: emit-item ( list record i -- ) -rot list-item emit-u ;
: emit-items ( list record -- ) 2dup list-count 0 ?do 2dup i emit-item loop 2drop ;
: emit-list ( list record -- ) emit-open-list emit-items emit-close-list ;
: list-member ( record addr c-addr u -- ) emit-key @ swap emit-list ;

\ Enumerations, as the exporter spells them: a count, then the word of
\ each code from 0 as a counted string. A code out of range is invalid.
: enum-word ( code table -- c-addr u ) cell+ swap 0 ?do count + aligned loop count ;
: emit-enum ( code table -- )
  2dup @ u< if enum-word emit-w jw-string else 2drop emit-invalid then ;
: enum-member ( addr table c-addr u -- ) emit-key swap @ swap emit-enum ;
create binder-texts  4 ,
  s" default" counted,  s" implicit" counted,  s" strictImplicit" counted,
  s" instImplicit" counted,
create safety-texts  3 ,  s" safe" counted,  s" unsafe" counted,  s" partial" counted,
create quot-texts  4 ,
  s" type" counted,  s" ctor" counted,  s" lift" counted,  s" ind" counted,
create hint-texts  2 ,  s" opaque" counted,  s" abbrev" counted,
2 constant regular-hints           \ decl-hints of {"regular":height}

\ The value of each kind of record ( record -- ), its keys in order.
: str-json ( record -- )
  emit-open dup name-prefix s" pre" u-member name-part s" str" text-member emit-close ;
: num-json ( record -- )
  emit-open dup name-part s" i" digits-member name-prefix s" pre" u-member emit-close ;
: succ-json ( record -- ) succ-of @ emit-u ;
: pair-json ( record -- )
  emit-open-list dup max-left @ emit-u max-right @ emit-u emit-close-list ;
: param-json ( record -- ) param-name @ emit-u ;
: bvar-json ( record -- ) bvar-index @ emit-u ;
: sort-json ( record -- ) sort-level @ emit-u ;
: const-json ( record -- )
  emit-open dup const-name s" name" u-member
  dup const-levels s" us" list-member emit-close ;
: app-json ( record -- )
  emit-open dup app-arg s" arg" u-member app-fn s" fn" u-member emit-close ;
: binder-json ( record -- )
  emit-open dup binder-info binder-texts s" binderInfo" enum-member
  dup binder-body s" body" u-member dup binder-name s" name" u-member
  binder-type s" type" u-member emit-close ;
: let-json ( record -- )
  emit-open dup let-body s" body" u-member dup let-name s" name" u-member
  dup let-nondep s" nondep" flag-member dup let-type s" type" u-member
  let-value s" value" u-member emit-close ;
: proj-json ( record -- )
  emit-open dup proj-idx s" idx" u-member dup proj-struct s" struct" u-member
  proj-type-name s" typeName" u-member emit-close ;
: literal-json ( record -- ) literal-text emit-string ;

\ mdata's data, a JSON object of the line's view. The exporter writes it
\ as one object of strings in key order (KVMap.toJson), so its members
\ are written in key order whatever their order in the line, each value
\ copied (an object inside a value must already be in order, which Lean
\ never writes: the writer refuses it as invalid). Two equal keys are
\ invalid too; more than data-most members are full. The key tokens are
\ sorted by insertion, in the module record.
: key< ( key1 key2 view -- flag ) tuck json-text@ 2>r json-text@ 2r> compare 0< ;
: member-pair ( j -- addr-j addr-j-1 ) dup member swap 1- member ;
: member-smaller? ( j view -- flag ) >r member-pair @ swap @ swap r> key< ;
: members-exchange ( j -- ) member-pair 2dup @ swap @ rot ! swap ! ;
: member-insert ( j view -- )
  begin over 0> while 2dup member-smaller? while over members-exchange swap 1- swap repeat
  then 2drop ;
: members-sort ( n view -- )
  over 1 > if swap 1 ?do i over member-insert loop else nip then drop ;
\ The key of the next member: after the value that follows key.
: member-next ( key view -- key' ) swap 1+ swap json-next ;
: members-collect ( object view -- )
  2dup json-items@ >r tuck json-contents nip r> 0 ?do dup i member ! over member-next loop
  2drop ;
: member-write ( key view -- ) 2dup json-text@ emit-key swap 1+ swap emit-w jw-copy ;
: members-write ( n view -- ) swap 0 ?do i member @ over member-write loop drop ;
: data-members ( object view -- )
  2dup members-collect tuck json-items@ swap 2dup members-sort members-write ;
: data-object ( object view -- )
  2dup json-items@ data-most > if 2drop outcome-full emit-fail exit then
  emit-open data-members emit-close ;
: data-json ( record -- ) dup mdata-data @ swap record-export @ export-json data-object ;
: mdata-json ( record -- )
  emit-open s" data" emit-key dup data-json mdata-expr s" expr" u-member emit-close ;

\ The metadata.
: exporter-json ( record -- )
  emit-open dup meta-exporter s" name" text-member
  meta-exporter-version s" version" text-member emit-close ;
: format-json ( record -- )
  emit-open meta-format-version s" version" text-member emit-close ;
: lean-json ( record -- )
  emit-open dup meta-lean-githash s" githash" text-member
  meta-lean-version s" version" text-member emit-close ;
: meta-json ( record -- )
  emit-open s" exporter" emit-key dup exporter-json s" format" emit-key dup format-json
  s" lean" emit-key lean-json emit-close ;

\ Declarations: members that keep the record ( record -- record ).
: params-name ( record -- record )
  dup dup decl-params s" levelParams" list-member dup decl-name s" name" u-member ;
: type-member ( record -- record ) dup decl-type s" type" u-member ;
: value-member ( record -- record ) dup decl-value s" value" u-member ;
: all-member ( record -- record ) dup dup decl-all s" all" list-member ;
: unsafe-member ( record -- record ) dup decl-unsafe s" isUnsafe" flag-member ;
: hints-json ( record -- )
  dup decl-hints @ regular-hints <> if decl-hints @ hint-texts emit-enum exit then
  emit-open decl-height s" regular" u-member emit-close ;
: hints-member ( record -- record ) s" hints" emit-key dup hints-json ;
: safety-member ( record -- record ) dup decl-safety safety-texts s" safety" enum-member ;
: axiom-json ( record -- )
  emit-open unsafe-member params-name type-member drop emit-close ;
: def-json ( record -- )
  emit-open all-member hints-member params-name safety-member type-member value-member
  drop emit-close ;
: thm-json ( record -- )
  emit-open all-member params-name type-member value-member drop emit-close ;
: opaque-json ( record -- )
  emit-open all-member unsafe-member params-name type-member value-member
  drop emit-close ;
: quot-json ( record -- )
  emit-open dup decl-quot-kind quot-texts s" kind" enum-member params-name type-member
  drop emit-close ;

\ The elements of an inductive block.
: inductive-flags ( record -- record )
  dup type-rec s" isRec" flag-member dup type-reflexive s" isReflexive" flag-member
  dup type-unsafe s" isUnsafe" flag-member ;
: inductive-counts ( record -- record )
  dup type-num-indices s" numIndices" u-member dup type-num-nested s" numNested" u-member
  dup type-num-params s" numParams" u-member ;
: inductive-json ( record -- )
  emit-open dup dup type-all s" all" list-member dup dup type-ctors s" ctors" list-member
  inductive-flags params-name inductive-counts type-member drop emit-close ;
: ctor-head ( record -- record )
  dup ctor-cidx s" cidx" u-member dup ctor-induct s" induct" u-member
  dup ctor-unsafe s" isUnsafe" flag-member ;
: ctor-counts ( record -- record )
  dup ctor-num-fields s" numFields" u-member dup ctor-num-params s" numParams" u-member ;
: ctor-json ( record -- )
  emit-open ctor-head params-name ctor-counts type-member drop emit-close ;
: rule-json ( rule -- )
  emit-open dup rule-ctor s" ctor" u-member dup rule-fields s" nfields" u-member
  rule-rhs s" rhs" u-member emit-close ;
\ Rule i of a recursor; one the reader cannot give is invalid.
: emit-rule ( i record -- ) recursor-rule ?dup if rule-json else emit-invalid then ;
: rules-member ( record -- record )
  s" rules" emit-key emit-open-list
  dup recursor-rules @ over list-count 0 ?do i over emit-rule loop emit-close-list ;
: recursor-head ( record -- record )
  dup dup recursor-all s" all" list-member dup recursor-unsafe s" isUnsafe" flag-member
  dup recursor-k s" k" flag-member ;
: recursor-counts ( record -- record )
  dup recursor-num-indices s" numIndices" u-member
  dup recursor-num-minors s" numMinors" u-member
  dup recursor-num-motives s" numMotives" u-member
  dup recursor-num-params s" numParams" u-member ;
: recursor-json ( record -- )
  emit-open recursor-head params-name recursor-counts rules-member type-member
  drop emit-close ;

\ Ending a line: the writer's outcome, then a line feed and the count.
\ Output waits until a mebibyte is ready (never with fid 0).
: emit-write ( -- )
  emit-out buffer-text emit-fid @ write-file if outcome-full emit-fail then
  emit-out buffer-empty ;
: flush-due? ( -- flag )
  emit-fid @ 0<> emit-out buffer-used @ reexport-buffer-start < 0= and ;
: line-tallied ( -- ) 1 emit-lines +! flush-due? if emit-write then ;
: line-done ( -- ) s\" \x0a" emit-out emit-bytes emit-status ok? if line-tallied then ;
: line-end ( -- outcome ) emit-w jw-end emit-fail line-done emit-status ;

\ How each kind's line is written: the word that writes the kind's value
\ ( record -- ), its family's index key (in, il or ie; 0 for the metadata
\ and declarations) and its kind key. A line is one text of the writer;
\ no line may start while a block is unfinished.
begin-structure /line-form
  field: form-value                \ xt ( record -- )
  field: form-index                \ counted string, or 0
  0 +field form-key                \ counted string
end-structure
: index-member ( record form -- ) form-index @ count emit-key record-index @ emit-u ;
: kind-member ( record form -- ) dup form-key count emit-key form-value @ execute ;
: kind-first? ( form -- flag ) dup form-key count rot form-index @ count compare 0< ;
: indexed-members ( record form -- )
  dup kind-first? if 2dup kind-member index-member exit then
  2dup index-member kind-member ;
: line-members ( record form -- )
  dup form-index @ if indexed-members else kind-member then ;
: line-start ( -- ) block-left @ if emit-invalid then emit-out emit-text ;
: emit-line ( record form -- outcome )
  line-start emit-open line-members emit-close line-end ;
\ Defining word: name ( record -- outcome ), the handler of a kind.
: line-form: ( xt index "name" "key" -- )
  create swap , , parse-name counted, does> emit-line ;
create index-in s" in" counted,
create index-il s" il" counted,
create index-ie s" ie" counted,

' meta-json 0 line-form: meta-line meta
' str-json index-in line-form: str-line str
' num-json index-in line-form: num-line num
' succ-json index-il line-form: succ-line succ
' pair-json index-il line-form: max-line max
' pair-json index-il line-form: imax-line imax
' param-json index-il line-form: param-line param
' bvar-json index-ie line-form: bvar-line bvar
' sort-json index-ie line-form: sort-line sort
' const-json index-ie line-form: const-line const
' app-json index-ie line-form: app-line app
' binder-json index-ie line-form: lam-line lam
' binder-json index-ie line-form: forall-line forallE
' let-json index-ie line-form: let-line letE
' proj-json index-ie line-form: proj-line proj
' literal-json index-ie line-form: natval-line natVal
' literal-json index-ie line-form: strval-line strVal
' mdata-json index-ie line-form: mdata-line mdata
' axiom-json 0 line-form: axiom-line axiom
' def-json 0 line-form: def-line def
' thm-json 0 line-form: thm-line thm
' opaque-json 0 line-form: opaque-line opaque
' quot-json 0 line-form: quot-line quot

\ An inductive block. Its handler writes the line's start and counts the
\ elements to come; each element's object is one text of the writer, the
\ types into their own buffer. When only the recursors are left the
\ constructors' list closes, and after the last element the types follow.
: items-of ( record addr -- n ) @ swap list-count ;
: recursors-of ( record -- n ) dup block-recursors items-of ;
: elements-of ( record -- n )
  dup dup block-types items-of over dup block-ctors items-of + swap recursors-of + ;
: block-start ( record -- )
  block-left @ if emit-invalid then
  dup elements-of block-left ! recursors-of left-recursors ! emit-types buffer-empty ;
: block-line ( record -- outcome )
  block-start s\" {\"inductive\":{\"ctors\":[" emit-out emit-bytes emit-status ;
: block-end ( -- )
  s\" ],\"types\":[" emit-out emit-bytes emit-types buffer-text emit-out emit-bytes
  s" ]}}" emit-out emit-bytes line-done ;
: element-done ( -- )
  -1 block-left +! block-left @
  dup left-recursors @ = if s\" ],\"recs\":[" emit-out emit-bytes then
  0= if block-end then ;
\ An element of a block: a comma before all but the first of its list.
: element-begin ( record buffer -- )
  block-left @ 0= if emit-invalid then
  swap record-index @ if s" ," 2 pick emit-bytes then emit-text ;
: element-end ( -- outcome ) emit-w jw-end emit-fail element-done emit-status ;
: type-line ( record -- outcome )
  dup emit-types element-begin inductive-json element-end ;
: ctor-line ( record -- outcome ) dup emit-out element-begin ctor-json element-end ;
: recursor-line ( record -- outcome )
  dup emit-out element-begin recursor-json element-end ;

\ The handlers, by record kind; the table must end at HERE with one cell
\ per kind, otherwise the load stops.
create reexport-handlers
  ' meta-line , ' str-line , ' num-line , ' succ-line , ' max-line , ' imax-line ,
  ' param-line , ' bvar-line , ' sort-line , ' const-line , ' app-line , ' lam-line ,
  ' forall-line , ' let-line , ' proj-line , ' natval-line , ' strval-line ,
  ' mdata-line , ' axiom-line , ' def-line , ' thm-line , ' opaque-line , ' quot-line ,
  ' block-line , ' type-line , ' ctor-line , ' recursor-line ,
here reexport-handlers - kind-count cells = load-check
\ The handler the reader calls for every kind: after a failure it refuses
\ every record at once, writing nothing; else the kind's handler. A line
\ that fails takes its bytes back from the output: the output's size at
\ each line's first record (outside a block) is the mark.
: line-mark ( -- ) block-left @ 0= if emit-out buffer-used @ emit-mark ! then ;
: line-undone ( outcome -- outcome )
  dup ok? 0= if emit-mark @ emit-out buffer-used ! then ;
: emit-kind ( record -- outcome ) dup record-kind @ cells reexport-handlers + @ execute ;
: emit-record ( record -- outcome )
  emit-status ok? 0= if drop emit-status exit then line-mark emit-kind line-undone ;

\ Starting a re-export into fid (0 keeps the lines in memory, for tests):
\ empty buffers, nothing failed, the writer idle (even after a THROW out
\ of it) with Lean's escapes and key order.
: reexport-reset ( fid -- )
  emit-fid ! outcome-ok emit-outcome ! 0 block-left ! 0 emit-lines !
  emit-out buffer-empty emit-types buffer-empty ;
: emit-settings ( -- )
  emit-w jw-reset true emit-w jw-sorted ! true emit-w jw-lean ! max-n emit-w jw-limit ! ;
: reexport-handlers! ( -- )
  kind-count 0 do ['] emit-record i reexported export-handler ! loop ;
: reexport-begin ( fid -- outcome )
  reexport-reset emit-settings reexported export-init dup ok? if reexport-handlers! then ;
\ The lines written so far, and those still in memory.
: reexport-lines@ ( -- n ) emit-lines @ ;
: reexport-pending ( -- c-addr u ) emit-out buffer-text ;
\ Finishing: invalid while a block is unfinished; the last output written
\ unless something failed.
: write-due? ( -- flag ) emit-status ok? emit-fid @ 0<> and ;
: reexport-end ( -- outcome )
  block-left @ if emit-invalid then write-due? if emit-write then emit-status ;
: reexport-free ( -- )
  emit-out buffer-release emit-types buffer-release reexported export-free ;

\ Re-export the export file named c-addr u into fid: the reading's
\ outcome, then the writing's. A Forth exception is invalid, after which
\ export-read has closed the input. On a failure the file holds at most
\ the lines before the failing one; the caller discards it.
: reexport-fault ( x x x -- outcome )
  2drop drop 0 reexported export-key !
  c" a Forth exception" reexported export-why ! outcome-invalid ;
: reexport-ended ( outcome -- outcome ) dup ok? if drop reexport-end then ;
: reexport-file ( c-addr u fid -- outcome )
  reexport-begin dup ok? 0= if nip nip exit then drop
  reexported ['] export-read catch if reexport-fault then reexport-ended ;

\ The command line's word. Errors are reported as ndjson-count.fs does:
\ the outcome's name, why, the field, the line and, for a JSON error, the
\ byte within the line.
: .count ( n -- ) base @ >r decimal 0 .r r> base ! ;
: .json-byte ( -- )
  reexported export-json dup json-why @ if ." , byte " json-offset .count else drop then ;
: .key ( c-addr u -- ) dup if ." field " type ." , " else 2drop then ;
: .reexport-error ( outcome -- )
  ." error: " outcome-text type reexported export-error ." : " type ."  (" .key
  ." line " .count .json-byte ." )" cr ;
\ Leaving the host with status 1, as ndjson-count.fs does: Gforth's
\ (bye) where it exists (both CI hosts), else an uncaught THROW.
[defined] (bye) [if]
  : reexport-failed ( -- ) 1 (bye) ;
[else]
  : reexport-failed ( -- ) -1 throw ;
[then]
\ Re-export into fid, then close it; the first failure wins.
: closed ( fid -- outcome ) close-file if outcome-full else outcome-ok then ;
: reexport-into ( in-addr in-u fid -- outcome )
  dup >r reexport-file r> closed over ok? if nip else drop then ;
: reexport-report ( outcome -- )
  dup ok? if drop ." reexported " reexport-lines@ .count ."  lines" cr exit then
  .reexport-error ;
: create-refused ( c-addr u fid ior -- false )
  drop 2drop drop ." error: cannot create the output file" cr false ;
\ Re-export the export named in into a new file named out, print one
\ line (the lines written, or the error) and free the buffers; true when
\ ok. reexport, the command line's word, then exits after an error.
: reexported? ( in-addr in-u out-addr out-u -- flag )
  w/o bin create-file ?dup if create-refused exit then
  reexport-into dup reexport-report reexport-free ok? ;
: reexport ( in-addr in-u out-addr out-u -- ) reexported? 0= if reexport-failed then ;

base !   \ the BASE this file was loaded with
