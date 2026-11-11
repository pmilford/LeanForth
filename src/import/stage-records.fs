\ The importer stage's records (ADR 0016 C2, C9 step 2; plan task 3.2.1):
\ the stage record, the export-index maps and the 32-byte declaration
\ records, and the reader's handlers that fill them. import/stage.fs makes,
\ reads, rolls back and seals a stage; read its header first. Untrusted
\ [import] code, fail-closed; LeanForth-specific (Lean's records).
\
\ The export-index maps (loading aids, ADR 0016 C6) give the store number
\ of each export index: names and levels from 0 (the anonymous name and
\ level zero, made by tier-init), expressions from 0. export>name,
\ export>level and export>expr give staged-none for an index the map does
\ not hold, and every builder and the declaration check refuse staged-none,
\ so a bad reference is invalid even if the reader let one through.
\
\ A declaration record (/staged) is eight 32-bit fields, read and written
\ only through u32@ and u32! (lib/u32.fs):
\   staged-head    bits 0-4 the kind, the reader's code (kind-axiom ..
\                  kind-recursor; kind-inductive for a block); bits 5-15
\                  flags (below)
\   staged-name    its name; 0 for a block
\   staged-params  its universe parameters, a tuple of names; none for a block
\   staged-type    its type; none for a block
\   staged-value   the value of a definition, theorem or opaque; else none
\   staged-hint    a definition's height when its hints are regular; else 0
\   staged-more    a tuple (lib/pools.fs, in the tier's tuples) of the
\                  kind's other data, or none for an axiom or a quotient:
\     definition, theorem, opaque  the names of `all`
\     block        [types ctors recursors], the numbers of each that follow
\     type         [numParams numIndices all ctors numNested]
\     constructor  [induct cidx numParams numFields]
\     recursor     [all numParams numIndices numMotives numMinors rules],
\                  rules a tuple of [ctor nfields rhs] per rule
\                  (all and ctors are tuples of names; rhs an expression)
\   staged-prev    the declaration of the same name staged before it,
\                  plus one; 0 for none (ADR 0016 C4: the chain E5 reads)
\ Flags: staged-unsafe-bit (isUnsafe), the definition's safety (2 bits
\ from bit 6: 0 safe, 1 unsafe, 2 partial) and hints (2 bits from bit 8:
\ 0 opaque, 1 abbrev, 2 regular), a quotient's kind (2 bits from bit 10:
\ 0 type, 1 ctor, 2 lift, 3 ind), staged-k-bit, staged-rec-bit,
\ staged-reflexive-bit, and staged-marked-bit (a declaration whose type,
\ value or recursor rule holds an mdata expression, set by stage-seal).
\ Declarations are numbered from 0 in the order the reader hands them
\ over: an inductive block, then its types, constructors and recursors.
\ A declaration's fields are checked when it is kept (ADR 0016 C8): its
\ name, parameters, type, value and data are records of the tier, present
\ exactly for its kind; every name and expression in its data is checked
\ as it is gathered; a number beyond 32 bits is full.
\
\ A read that continues a tier (stage-continue, import/stage.fs) notes the
\ name of every constant it hands over (put-const-noted, a bitset in the
\ stage), so that sealing refuses an unknown constant only among them.
\
\ State: none of its own. Every word takes a stage record (/stage); the
\ handlers find it from their record's export, the stage's first field.
\ The tables below are constant after loading. Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/outcome.fs
require ../lib/u32.fs
require ../lib/slab.fs
require ../lib/cons.fs
require ../lib/pools.fs
require ../core/compact.fs
require ./ndjson.fs
require ./manifest.fs

\ A field that refers to nothing: never the number of a record.
u32-mask constant staged-none

\ The declaration record.
begin-structure /staged
  1 u32s +field staged-head
  1 u32s +field staged-name
  1 u32s +field staged-params
  1 u32s +field staged-type
  1 u32s +field staged-value
  1 u32s +field staged-hint
  1 u32s +field staged-more
  1 u32s +field staged-prev
end-structure
1 5 lshift constant staged-unsafe-bit
6 constant safety-shift
8 constant hints-shift
10 constant quot-shift
1 12 lshift constant staged-k-bit
1 13 lshift constant staged-rec-bit
1 14 lshift constant staged-reflexive-bit
1 15 lshift constant staged-marked-bit
\ The positions of the items of staged-more's tuple, by kind (the table
\ above), and of the three items of a recursor rule.
0 constant more-block-types  1 constant more-block-ctors  2 constant more-block-recursors
0 constant more-type-params  1 constant more-type-indices  2 constant more-type-all
3 constant more-type-ctors  4 constant more-type-nested
0 constant more-ctor-induct  1 constant more-ctor-cidx  2 constant more-ctor-params
3 constant more-ctor-fields
0 constant more-rec-all  1 constant more-rec-params  2 constant more-rec-indices
3 constant more-rec-motives  4 constant more-rec-minors  5 constant more-rec-rules
0 constant rule-ctor-item  1 constant rule-fields-item  2 constant rule-rhs-item
3 constant /rule-items

\ The stage: the reader first, so that a handler finds the stage from its
\ record's export.
begin-structure /stage
  /export +field stage-export        \ the NDJSON reader of the export
  /manifest +field stage-manifest    \ its manifest check
  /tier +field stage-tier            \ the input tier
  /slab +field stage-name-map        \ export name index -> name
  /slab +field stage-level-map       \ export level index -> level
  /slab +field stage-expr-map        \ export expression index -> expression
  /slab +field stage-decl-records    \ the declarations, /staged each
  /slab +field stage-by-name         \ name -> its newest declaration + 1, or 0
  /slab +field stage-lines           \ declaration -> its line in the export
  /tier-mark +field stage-start      \ the tier as stage-init left it
  field: stage-state                 \ staging-blank .. staging-broken
  field: stage-limit                 \ most bytes of heap blocks; 0: no limit
  field: stage-mdata                 \ mdata expressions staged
  field: stage-marks                 \ declarations marked
  field: stage-why                   \ counted string: why sealing failed, or 0
  field: stage-culprit               \ the name sealing failed on
  field: stage-reach                 \ while sealing: the mdata reach fields, or 0
  field: stage-item-count            \ items of the tuple being gathered
  8 cells +field stage-items
  field: stage-other                 \ true: the metadata names other versions
  5 cells +field stage-meta          \ then its texts, numbers in the tier's texts
  field: stage-continued             \ true: reads continue a tier (stage-continue)
  /slab +field stage-noted           \ then: the read's constant names, a bitset
end-structure
: export>stage ( export -- stage ) 0 stage-export - ;
: record>stage ( record -- stage ) record-export @ export>stage ;
: stage-tuples ( stage -- cons ) stage-tier tier-tuples ;

\ Slabs of 32-bit fields: the maps and the name-to-declaration array.
: fields-init ( limit slab -- outcome ) 1 u32s -rot slab-init ;
: fields@ ( i slab -- u ) slab-at u32@ ;
: fields! ( u i slab -- ) slab-at u32! ;
: fields-push ( u slab -- outcome )
  1 over slab-claim dup ok? if drop swap slab-at u32! outcome-ok else nip nip nip then ;
\ Map lookups: the store number of export index i, or staged-none.
: map> ( i map -- n ) 2dup slab-count u< if fields@ else 2drop staged-none then ;
: export>name ( i stage -- n ) stage-name-map map> ;
: export>level ( i stage -- l ) stage-level-map map> ;
: export>expr ( i stage -- e ) stage-expr-map map> ;

\ Heap blocks the stage holds (the tier, the maps, the reader's index maps of
\ an export whose indices are not dense, the declarations and their lines;
\ not the reader's line buffer and JSON view), and its limit.
: stage-allocated ( stage -- u )
  dup stage-export export-map-bytes
  over stage-tier tier-allocated + over stage-name-map slab-bytes +
  over stage-level-map slab-bytes + over stage-expr-map slab-bytes +
  over stage-decl-records slab-bytes + over stage-by-name slab-bytes +
  over stage-lines slab-bytes + swap stage-noted slab-bytes + ;
: stage-over? ( stage -- flag )
  dup stage-limit @ ?dup if swap stage-allocated u< else drop false then ;
\ After a record is kept: full, with the reason, once past the limit.
: limited ( outcome stage -- outcome )
  over ok? 0= if drop exit then dup stage-over? 0= if drop exit then
  nip stage-export c" memory limit of the stage reached" export-over ;
\ A number beyond 32 bits, where a field must hold it: full.
: too-wide ( stage -- -1 outcome )
  stage-export c" number beyond 32 bits" export-over no-result ;

\ Keeping a built record as its family's next export index.
: kept ( n outcome map -- outcome ) over ok? if nip fields-push else drop nip then ;
: names-kept ( n outcome stage -- outcome ) >r r@ stage-name-map kept r> limited ;
: levels-kept ( l outcome stage -- outcome ) >r r@ stage-level-map kept r> limited ;
: exprs-kept ( e outcome stage -- outcome ) >r r@ stage-expr-map kept r> limited ;

\ ---- The metadata. The pinned versions' needs nothing kept; one that
\ names others (the reader hands it over only after export-any-version!)
\ has its five texts interned in the tier, in the order of meta-fields,
\ and the stage marked (stage-other).
create meta-fields
  ' meta-exporter , ' meta-exporter-version , ' meta-format-version ,
  ' meta-lean-version , ' meta-lean-githash ,
here meta-fields - cell / constant #meta
: meta-text ( record k -- c-addr u ) cells meta-fields + @ execute 2@ ;
: meta-slot ( k stage -- addr ) stage-meta swap cells + ;
: meta-keep ( record k stage -- outcome )
  >r tuck meta-text r@ stage-tier tier-texts text-intern
  ok-then? if swap r> meta-slot ! outcome-ok else nip r> drop then ;
: metas-keep ( record stage -- outcome )
  #meta 0 do 2dup i swap meta-keep dup ok? 0= if nip nip unloop exit then drop loop
  true swap stage-other ! drop outcome-ok ;
: put-meta ( record -- outcome )
  dup pinned? if drop outcome-ok exit then
  dup record>stage tuck metas-keep swap limited ;

\ ---- Handlers ( record -- outcome ) of names, levels and expressions.
: put-name-str ( record -- outcome )
  dup record>stage >r dup name-prefix @ r@ export>name swap name-part 2@
  r@ stage-tier name-str r> names-kept ;
: digits>u32 ( addr u -- u true | false )
  digits>u if dup u32-mask u> if drop false else true then else false then ;
: put-name-num ( record -- outcome )
  dup record>stage >r dup name-prefix @ r@ export>name swap name-part 2@ digits>u32
  if r@ stage-tier name-num else drop r@ too-wide then r> names-kept ;

: put-succ ( record -- outcome )
  dup record>stage >r succ-of @ r@ export>level r@ stage-tier level-succ r> levels-kept ;
: level-pair ( record stage -- l1 l2 )
  >r dup max-left @ r@ export>level swap max-right @ r> export>level ;
: put-max ( record -- outcome )
  dup record>stage >r r@ level-pair r@ stage-tier level-max r> levels-kept ;
: put-imax ( record -- outcome )
  dup record>stage >r r@ level-pair r@ stage-tier level-imax r> levels-kept ;
: put-param ( record -- outcome )
  dup record>stage >r param-name @ r@ export>name r@ stage-tier level-param
  r> levels-kept ;

\ A reader list as a tuple of the tier: item k of each, translated and
\ checked by xt ( k list record -- n valid? ); invalid for an item that
\ is not valid, full when there is no room.
: list-name ( k list record -- n valid? )
  dup >r list-item r> record>stage tuck export>name tuck swap stage-tier name-valid? ;
: list-level ( k list record -- l valid? )
  dup >r list-item r> record>stage tuck export>level tuck swap stage-tier level-valid? ;
: tuple-add? ( u valid? stage -- outcome )
  swap if stage-tuples tuple-add else 2drop outcome-invalid then ;
: tuple-item, ( list record xt k -- list record xt outcome )
  >r 2 pick 2 pick r> -rot 3 pick execute 3 pick record>stage tuple-add? ;
: list-items, ( list record xt -- outcome )
  2 pick 2 pick list-count 0 ?do
    i tuple-item, dup ok? 0= if nip nip nip unloop exit then drop
  loop drop 2drop outcome-ok ;
: list>tuple ( list record xt -- t outcome )
  over record>stage stage-tuples tuple-start dup ok? 0= if nip nip nip no-result exit then
  drop over >r list-items, dup ok? if drop r> record>stage stage-tuples tuple-end
  else r> drop no-result then ;
: names>tuple ( list record -- t outcome ) ['] list-name list>tuple ;
: levels>tuple ( list record -- t outcome ) ['] list-level list>tuple ;

: put-bvar ( record -- outcome )
  dup record>stage >r bvar-index @ r@ stage-tier expr-bvar r> exprs-kept ;
: put-sort ( record -- outcome )
  dup record>stage >r sort-level @ r@ export>level r@ stage-tier expr-sort r> exprs-kept ;
: put-const ( record -- outcome )
  dup record>stage >r dup const-name @ r@ export>name swap dup const-levels @ swap
  levels>tuple ok-then? if r@ stage-tier expr-const else nip no-result then
  r> exprs-kept ;
\ The constant names of a read that continues a tier (stage-continue): a
\ bitset of 32-bit fields, one bit per name number, grown as names come;
\ the unknown-constant refusal is limited to the names it holds. A fresh
\ read keeps none (put-const is its handler).
: fields-cover ( i slab -- outcome )   \ fields 0 .. i in use, new ones 0
  >r 1+ r@ slab-count - dup 0> if
    dup r@ slab-claim dup ok? if drop r@ slab-at swap u32s erase outcome-ok
    else nip nip then
  else drop outcome-ok then r> drop ;
: noted-bit ( n -- mask i ) dup 31 and 1 swap lshift swap 5 rshift ;
: noted! ( n stage -- outcome )
  stage-noted >r noted-bit dup r@ fields-cover ok-then?
  if r@ slab-at dup u32@ rot or swap u32! outcome-ok else nip then r> drop ;
: noted? ( n stage -- flag )
  stage-noted >r noted-bit dup r@ slab-count u<
  if r@ slab-at u32@ and 0<> else 2drop false then r> drop ;
: const-noted ( record -- outcome )
  dup record>stage >r const-name @ r@ export>name r> noted! ;
: put-const-noted ( record -- outcome )
  dup put-const dup ok? if drop const-noted else nip then ;
: put-app ( record -- outcome )
  dup record>stage >r dup app-fn @ r@ export>expr swap app-arg @ r@ export>expr
  r@ stage-tier expr-app r> exprs-kept ;
\ A binder, its head made by xt ( name info -- head ): lam-head or pi-head.
: binder-head ( record stage xt -- head )
  >r over binder-name @ swap export>name swap binder-info @ r> execute ;
: binder-make ( record xt -- outcome )
  over record>stage >r over r@ rot binder-head over binder-type @ r@ export>expr
  rot binder-body @ r@ export>expr r@ stage-tier expr-make r> exprs-kept ;
: put-lam ( record -- outcome ) ['] lam-head binder-make ;
: put-forall ( record -- outcome ) ['] pi-head binder-make ;
\ A letE's head, and one of its expressions, the field xt of its record.
: let-head-of ( record stage -- head )
  over let-name @ swap export>name swap let-nondep @ let-head ;
: let-expr ( record stage xt -- e ) rot swap execute @ swap export>expr ;
: let-parts ( record stage -- head type value body )
  2>r 2r@ let-head-of 2r@ ['] let-type let-expr 2r@ ['] let-value let-expr
  2r> ['] let-body let-expr ;
: put-let ( record -- outcome )
  dup record>stage >r r@ let-parts r@ stage-tier expr-let r> exprs-kept ;
: proj-parts ( record stage -- head struct idx )
  >r dup proj-type-name @ r@ export>name proj-head over proj-struct @ r> export>expr
  rot proj-idx @ ;
: put-proj ( record -- outcome )
  dup record>stage >r dup proj-idx @ u32-mask u> if drop r@ too-wide
  else r@ proj-parts r@ stage-tier expr-make then r> exprs-kept ;
: literal-intern ( record stage -- t outcome )
  swap literal-text 2@ rot stage-tier tier-texts text-intern ;
: put-natval ( record -- outcome )
  dup record>stage >r r@ literal-intern ok-then?
  if r@ stage-tier expr-nat else no-result then
  r> exprs-kept ;
: put-strval ( record -- outcome )
  dup record>stage >r r@ literal-intern ok-then?
  if r@ stage-tier expr-str else no-result then
  r> exprs-kept ;
\ mdata: staged but marked; its key-value data is not kept.
: put-mdata ( record -- outcome )
  dup record>stage >r mdata-expr @ r@ export>expr r@ stage-tier expr-mdata
  dup ok? if 1 r@ stage-mdata +! then r> exprs-kept ;

\ ---- Declarations. The draft is the record being built, at the free end
\ of the declaration slab; it is kept, and linked to its name, only when
\ every field passed its check.
: draft ( stage -- addr ) stage-decl-records slab-top ;
: draft-kind ( stage -- kind ) draft staged-head u32@ head-tag ;
: draft-flags! ( bits stage -- ) draft staged-head dup u32@ rot or swap u32! ;
\ A flag of the reader's record as a head bit; a code of two bits (the
\ reader's enumerations give 0 .. 3) at a shift.
: head-flag ( flag bit stage -- ) >r swap 0<> and r> draft-flags! ;
: head-code ( code shift stage -- ) >r swap 3 and swap lshift r> draft-flags! ;
: draft-blank ( kind addr -- )
  tuck staged-head u32! 0 over staged-name u32! 0 over staged-hint u32!
  0 over staged-prev u32! staged-none over staged-params u32!
  staged-none over staged-type u32! staged-none over staged-value u32!
  staged-none swap staged-more u32! ;
\ Room for a draft of the record's kind, every field blank, and the line
\ of the export it came from kept (staged-line@; the presentation reads it,
\ the checker never does).
: draft-open ( record stage -- outcome )
  1 over stage-decl-records slab-room dup ok? 0= if nip nip exit then drop
  over record-line @ dup staged-none u< 0= if drop dup too-wide nip nip nip exit then
  over stage-lines fields-push dup ok? 0= if nip nip exit then drop
  swap record-kind @ swap draft draft-blank outcome-ok ;

\ Gathering a tuple's items in the stage, then making the tuple: full for
\ an item beyond 32 bits. At most six items (a recursor's).
: items-clear ( stage -- ) 0 swap stage-item-count ! ;
: item, ( u stage -- )
  dup >r stage-item-count @ cells r@ stage-items + ! 1 r> stage-item-count +! ;
: item@ ( k stage -- u ) stage-items swap cells + @ ;
: number-add ( u stage -- outcome )
  over u32-mask u> if nip too-wide nip else stage-tuples tuple-add then ;
: items-add ( stage -- outcome )
  dup stage-item-count @ 0 ?do
    i over item@ over number-add dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
: items>tuple ( stage -- t outcome )
  dup stage-tuples tuple-start dup ok? 0= if nip no-result exit then drop
  dup items-add dup ok? if drop stage-tuples tuple-end else nip no-result then ;
\ The gathered items as the draft's data.
: more-done ( stage -- outcome )
  dup items>tuple ok-then? if swap draft staged-more u32! outcome-ok else nip then ;
\ A list of names gathered as one item.
: names-item, ( record stage list -- record stage outcome )
  2 pick names>tuple ok-then? if over item, outcome-ok then ;
\ A name checked and added to the tuple being built; the same for an
\ expression.
: name-add ( i stage -- outcome )
  tuck export>name 2dup swap stage-tier name-valid? rot tuple-add? ;
: expr-add ( i stage -- outcome )
  tuck export>expr 2dup swap stage-tier expr-valid? rot tuple-add? ;

\ Steps ( record stage -- outcome ), each filling part of the draft.
: draft-common ( record stage -- outcome )
  over decl-name @ over export>name over draft staged-name u32!
  over decl-type @ over export>expr over draft staged-type u32!
  swap dup decl-params @ swap names>tuple
  ok-then? if swap draft staged-params u32! outcome-ok else nip then ;
: draft-value ( record stage -- outcome )
  swap decl-value @ over export>expr swap draft staged-value u32! outcome-ok ;
: draft-all ( record stage -- outcome )
  >r dup decl-all @ swap names>tuple ok-then? if r@ draft staged-more u32! outcome-ok then
  r> drop ;
: axiom-flags ( record stage -- outcome )
  swap decl-unsafe @ staged-unsafe-bit rot head-flag outcome-ok ;
: def-data ( record stage -- outcome )
  over decl-hints @ hints-shift 2 pick head-code
  over decl-safety @ safety-shift 2 pick head-code
  over decl-hints @ 2 = if over decl-height @ over draft staged-hint u32! then
  2drop outcome-ok ;
: quot-data ( record stage -- outcome )
  swap decl-quot-kind @ quot-shift rot head-code outcome-ok ;
: block-data ( record stage -- outcome )
  dup items-clear over block-types @ 2 pick list-count over item,
  over block-ctors @ 2 pick list-count over item,
  swap dup block-recursors @ swap list-count over item, more-done ;
: type-data ( record stage -- outcome )
  dup items-clear over type-num-params @ over item, over type-num-indices @ over item,
  over type-all @ names-item, ok-then2? 0= if exit then
  over type-ctors @ names-item, ok-then2? 0= if exit then
  over type-num-nested @ over item, over type-rec @ staged-rec-bit 2 pick head-flag
  over type-reflexive @ staged-reflexive-bit 2 pick head-flag
  swap type-unsafe @ staged-unsafe-bit 2 pick head-flag more-done ;
: ctor-data ( record stage -- outcome )
  dup items-clear over ctor-induct @ over export>name 2dup swap stage-tier name-valid?
  0= if 2drop drop outcome-invalid exit then over item,
  over ctor-cidx @ over item, over ctor-num-params @ over item,
  over ctor-num-fields @ over item,
  swap ctor-unsafe @ staged-unsafe-bit 2 pick head-flag more-done ;
\ A recursor's rules: [ctor nfields rhs] each, in one tuple.
: rule-add ( rule stage -- outcome )
  over rule-ctor @ over name-add ok-then2? 0= if exit then
  over rule-fields @ over number-add ok-then2? 0= if exit then
  swap rule-rhs @ swap expr-add ;
: rules-add ( record stage -- outcome )
  over recursor-rules @ 2 pick list-count 0 ?do
    over i swap recursor-rule ?dup 0= if 2drop outcome-invalid unloop exit then
    over rule-add dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
: rules>tuple ( record stage -- t outcome )
  dup stage-tuples tuple-start dup ok? 0= if nip nip no-result exit then drop
  tuck rules-add dup ok? if drop stage-tuples tuple-end else nip no-result then ;
: recursor-data ( record stage -- outcome )
  dup items-clear over recursor-all @ names-item, ok-then2? 0= if exit then
  over recursor-num-params @ over item, over recursor-num-indices @ over item,
  over recursor-num-motives @ over item, over recursor-num-minors @ over item,
  2dup rules>tuple ok-then? 0= if nip nip exit then over item,
  over recursor-k @ staged-k-bit 2 pick head-flag
  swap recursor-unsafe @ staged-unsafe-bit 2 pick head-flag more-done ;

\ The steps of each kind, in the reader's order of kinds (kind-axiom on).
create axiom-steps ' draft-common , ' axiom-flags , 0 ,
create def-steps ' draft-common , ' draft-value , ' def-data , ' draft-all , 0 ,
create thm-steps ' draft-common , ' draft-value , ' draft-all , 0 ,
create opaque-steps ' draft-common , ' draft-value , ' axiom-flags , ' draft-all , 0 ,
create quot-steps ' draft-common , ' quot-data , 0 ,
create block-steps ' block-data , 0 ,
create type-steps ' draft-common , ' type-data , 0 ,
create ctor-steps ' draft-common , ' ctor-data , 0 ,
create recursor-steps ' draft-common , ' recursor-data , 0 ,
create kind-steps axiom-steps , def-steps , thm-steps , opaque-steps , quot-steps ,
  block-steps , type-steps , ctor-steps , recursor-steps ,
: steps-of ( kind -- steps ) kind-axiom - cells kind-steps + @ ;
: steps-run ( record stage steps -- outcome )
  begin dup @ ?dup while
    >r 2 pick 2 pick r> execute dup ok? 0= if nip nip nip exit then drop cell+
  repeat drop 2drop outcome-ok ;

\ The draft's check (C8): every field present exactly for its kind, and a
\ record of the tier.
: none? ( u -- flag ) staged-none = ;
: tuple-ok? ( t stage -- flag ) stage-tuples cons-entry? ;
: expr-ok? ( e stage -- flag ) stage-tier expr-valid? ;
: valued? ( kind -- flag ) dup kind-def = over kind-thm = or swap kind-opaque = or ;
: more? ( kind -- flag ) dup kind-axiom <> swap kind-quot <> and ;
: either-ok? ( u stage need? xt -- flag ) swap if execute else 2drop none? then ;
: value-ok? ( stage -- flag )
  dup draft staged-value u32@ over dup draft-kind valued? ['] expr-ok? either-ok? nip ;
: more-ok? ( stage -- flag )
  dup draft staged-more u32@ over dup draft-kind more? ['] tuple-ok? either-ok? nip ;
: name-ok? ( stage -- flag )
  dup draft staged-name u32@ ?dup if swap stage-tier name-valid? else drop false then ;
: named-ok? ( stage -- flag )
  dup name-ok? over draft staged-params u32@ 2 pick tuple-ok? and
  over draft staged-type u32@ 2 pick expr-ok? and swap value-ok? and ;
: block-ok? ( stage -- flag )
  draft dup staged-name u32@ 0= over staged-params u32@ none? and
  over staged-type u32@ none? and swap staged-value u32@ none? and ;
: draft-valid? ( stage -- flag )
  dup draft-kind kind-inductive = if dup block-ok? else dup named-ok? then
  swap more-ok? and ;

\ Keeping the draft: the name-to-declaration array covers its name (new
\ entries 0), the draft's prev field takes the name's newest declaration,
\ then the draft is counted and becomes the newest. A block has no name.
: stage-decls ( stage -- n ) stage-decl-records slab-count ;
: by-name-cover ( n stage -- outcome ) stage-by-name fields-cover ;
: draft-chain ( n stage -- outcome )
  2dup by-name-cover dup ok? 0= if nip nip exit then drop
  tuck stage-by-name fields@ swap draft staged-prev u32! outcome-ok ;
: draft-keep ( stage -- d ) dup stage-decls 1 rot stage-decl-records slab-commit ;
: newest! ( d n stage -- ) >r swap 1+ swap r> stage-by-name fields! ;
: draft-close ( stage -- outcome )
  dup draft-valid? 0= if drop outcome-invalid exit then
  dup draft staged-name u32@ ?dup 0= if draft-keep drop outcome-ok exit then
  2dup swap draft-chain dup ok? 0= if nip nip exit then drop
  over draft-keep swap rot newest! outcome-ok ;
\ Stage a declaration record with the steps of its kind.
: put-decl ( record -- outcome )
  dup record>stage >r dup r@ draft-open dup ok? if
    drop dup r@ rot record-kind @ steps-of steps-run
  else nip then
  dup ok? if drop r@ draft-close then r> limited ;

\ The handler of each record kind.
create stage-handlers
  ' put-meta , ' put-name-str , ' put-name-num , ' put-succ , ' put-max , ' put-imax ,
  ' put-param , ' put-bvar , ' put-sort , ' put-const , ' put-app , ' put-lam ,
  ' put-forall , ' put-let , ' put-proj , ' put-natval , ' put-strval , ' put-mdata ,
  ' put-decl , ' put-decl , ' put-decl , ' put-decl , ' put-decl , ' put-decl ,
  ' put-decl , ' put-decl , ' put-decl ,
here stage-handlers - cell / kind-count <>
[if] .( stage-records.fs: one handler per record kind) cr abort [then]
: handlers-set ( stage -- )
  stage-export kind-count 0 do
    stage-handlers i cells + @ i 2 pick export-handler !
  loop drop ;

\ ---- Reading declarations (unchecked: give them numbers below
\ stage-decls, or check with stage-decl?).
: stage-decl? ( d stage -- flag ) stage-decls u< ;
: staged-at ( d stage -- addr ) stage-decl-records slab-at ;
: staged-flags@ ( d stage -- u ) staged-at staged-head u32@ ;
: staged-kind@ ( d stage -- kind ) staged-flags@ head-tag ;
: staged-name@ ( d stage -- n ) staged-at staged-name u32@ ;
: staged-params@ ( d stage -- t ) staged-at staged-params u32@ ;
: staged-type@ ( d stage -- e ) staged-at staged-type u32@ ;
: staged-value@ ( d stage -- e ) staged-at staged-value u32@ ;
: staged-hint@ ( d stage -- u ) staged-at staged-hint u32@ ;
: staged-more@ ( d stage -- t ) staged-at staged-more u32@ ;
: staged-prev@ ( d stage -- u ) staged-at staged-prev u32@ ;
\ The line of the export that declaration d came from, 0 for none.
: staged-line@ ( d stage -- line ) stage-lines map> dup staged-none = if drop 0 then ;
: staged-bit? ( d stage bit -- flag ) >r staged-flags@ r> and 0<> ;
: staged-unsafe? ( d stage -- flag ) staged-unsafe-bit staged-bit? ;
: staged-k? ( d stage -- flag ) staged-k-bit staged-bit? ;
: staged-rec? ( d stage -- flag ) staged-rec-bit staged-bit? ;
: staged-reflexive? ( d stage -- flag ) staged-reflexive-bit staged-bit? ;
: staged-marked? ( d stage -- flag ) staged-marked-bit staged-bit? ;
: staged-code@ ( d stage shift -- code ) >r staged-flags@ r> rshift 3 and ;
: staged-safety@ ( d stage -- code ) safety-shift staged-code@ ;
: staged-hints@ ( d stage -- code ) hints-shift staged-code@ ;
: staged-quot-kind@ ( d stage -- code ) quot-shift staged-code@ ;
\ The data tuple: its length, and its item i (from 0).
: staged-items ( d stage -- n ) tuck staged-more@ swap stage-tuples tuple-length ;
: staged-item ( i d stage -- u ) tuck staged-more@ swap stage-tuples tuple-item ;

base !   \ the BASE this file was loaded with
