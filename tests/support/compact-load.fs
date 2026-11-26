\ Test support: load a Lean export with the importer stage
\ (src/import/stage.fs) into a compact input tier, re-emit every record of
\ the stage in the reader's dump format (tests/core/ndjson-dump.fs), and
\ measure the load. Not a module of src/. One load at a time: the stage is
\ one record, compact-stage, with the inverse maps of the re-emission in
\ compact-loaded.
\
\ The re-emission prints the metadata (the pinned versions the reader
\ requires), then every name, level and expression record in export
\ order, then every declaration in stage order, which is file order: each
\ from the store, its references turned back into export indices through
\ inverse maps (the first export index of each store number). So a merge
\ of two different records by hash-consing, a dropped or reordered
\ declaration, or any field read back wrong shows as a changed line.
\
\ Entry words: compact-load ( c-addr u log2 -- outcome ) loads and seals,
\ checking the manifest (compact-load-unchecked without), the expression
\ table pre-sized to 2^log2 slots; compact-emit ( -- ) prints the dump
\ lines; compact-stats ( -- ) prints sizes and table statistics;
\ compact-lookups ( -- ) finds every declaration by its name through the
\ name-to-declaration array and by its text through a scratch tier;
\ compact-resolutions ( -- ) checks every constant's resolution against
\ the array; compact-free ( -- ); the drivers compact-dump and
\ compact-dump-unchecked ( c-addr u -- ), used by
\ tests/core/compact-verify.sh, and compact-measure ( c-addr u log2 -- ).
\ Continued reads and the saved tier (plan step SN2; tests/core/test_stage.py):
\ compact-continue-try and compact-continue-dump ( a-addr a-u b-addr b-u -- )
\ stage export A unsealed, continue it with B, seal, and report or dump;
\ compact-snap-continue-try and -dump ( a b f-addr f-u -- ) save A's sealed
\ tier to the file f, load it into a fresh stage, then continue with B;
\ compact-save ( f-addr f-u -- ) saves the loaded stage's tier;
\ compact-resave ( f1 f2 -- ) loads the tier file f1, seals and saves f2.
\ Name a manifest file first with `s" FILE" compact-manifest-use`. Uses Gforth's utime for
\ timings. Usage, for example:
\   gforth-fast tests/support/compact-load.fs -e 's" init.ndjson" 24 compact-measure bye'

require ../../src/import/stage.fs
require ../../src/import/snapshot-tier.fs

create compact-stage /stage allot
create compact-scratch /tier allot
: compact-tier ( -- tier ) compact-stage stage-tier ;
begin-structure /compact-load
  /slab +field name-inverse   \ store number -> first export index
  /slab +field level-inverse
  /slab +field expr-inverse
  /slab +field comp-stack     \ components of a name being looked up
end-structure
create compact-loaded /compact-load allot
compact-stage /stage erase  compact-loaded /compact-load erase

: export>name' ( i -- n ) compact-stage export>name ;
: export>level' ( i -- l ) compact-stage export>level ;
: export>expr' ( i -- e ) compact-stage export>expr ;

\ Loading.
: compact-start ( log2 -- outcome )
  compact-loaded /compact-load erase
  4 0 do cons-numbers-max compact-loaded i /slab * + fields-init drop loop
  compact-stage stage-init ;
: .load-error ( -- )
  compact-stage stage-error 2>r 2>r ." line " . ." field " 2r> type ."  why " 2r> type
  cr ;
: loaded ( outcome -- outcome ) dup ok? 0= if ." load failed: " dup . .load-error then ;
\ Load and seal the export named c-addr u, its expression table starting
\ at 2^log2 slots: ok, or the failing outcome after printing why.
\ The manifest file of the next compact-load, or none for the default name.
create compact-manifest 0 , 0 ,
: compact-manifest-use ( c-addr u -- ) compact-manifest 2! ;
: compact-manifest-named ( -- )
  compact-manifest 2@ dup if compact-stage stage-manifest-use else 2drop then
  0 0 compact-manifest 2! ;
: compact-load ( c-addr u log2 -- outcome )
  compact-start dup ok? 0= if nip nip exit then drop compact-manifest-named
  compact-stage stage-load loaded ;
: compact-load-unchecked ( c-addr u log2 -- outcome )
  compact-start dup ok? 0= if nip nip exit then drop compact-stage stage-load-unchecked
  loaded ;
: compact-free ( -- )
  compact-stage stage-free 4 0 do compact-loaded i /slab * + slab-free loop ;

\ ---- Re-emission in tests/core/ndjson-dump.fs's format.
: inverse-init ( count map -- outcome )
  dup slab-clear 2dup slab-claim nip dup ok? 0= if nip nip exit then drop
  swap 0 ?do u32-mask i 2 pick slab-at u32! loop drop outcome-ok ;
: inverse-note ( n i inverse -- )
  rot over slab-at dup u32@ u32-mask = if nip u32! else 2drop drop then ;
\ Fill inverse from map: the first export index of each of count numbers.
: inverse-build ( map count inverse -- outcome )
  tuck inverse-init dup ok? 0= if nip nip exit then drop
  over slab-count 0 ?do i 2 pick fields@ i 2 pick inverse-note loop 2drop outcome-ok ;
: inverses ( -- outcome )
  compact-stage stage-name-map compact-tier tier-names cons-numbers
  compact-loaded name-inverse inverse-build
  compact-stage stage-level-map compact-tier tier-levels cons-numbers
  compact-loaded level-inverse inverse-build or
  compact-stage stage-expr-map compact-tier tier-exprs cons-numbers
  compact-loaded expr-inverse inverse-build or 0= flag>outcome ;
: name-index ( n -- i ) compact-loaded name-inverse fields@ ;
: level-index ( l -- i ) compact-loaded level-inverse fields@ ;
: expr-index ( e -- i ) compact-loaded expr-inverse fields@ ;

: .int ( n -- ) space 0 .r ;
: .flag ( flag -- ) 0<> 1 and .int ;
: .hex-byte ( c -- ) base @ >r hex 0 <# # # #> type r> base ! ;
: .hex ( addr u -- ) space dup 0= if 2drop ." -" exit then over + swap ?do i c@
  .hex-byte loop ;
: .head ( i c-addr u -- ) type .int ;

: emit-meta ( -- )
  ." meta 0" pinned-exporter .hex pinned-exporter-version .hex pinned-lean-githash .hex
  pinned-lean-version .hex pinned-format-version .hex cr ;
: emit-name ( i -- )
  dup export>name' dup compact-tier name-tag@ tag-name-str =
  if swap s" name.str" .head dup compact-tier name-prefix@ name-index .int
    compact-tier name-text@ .hex
  else swap s" name.num" .head dup compact-tier name-prefix@ name-index .int
    compact-tier name-number@ .int then cr ;
: .level-a ( l -- ) compact-tier level-a@ level-index .int ;
: .level-b ( l -- ) compact-tier level-b@ level-index .int ;
: emit-level ( i -- )
  dup export>level' dup compact-tier level-tag@ case
    tag-level-succ of swap s" level.succ" .head .level-a endof
    tag-level-max of swap s" level.max" .head dup .level-a .level-b endof
    tag-level-imax of swap s" level.imax" .head dup .level-a .level-b endof
    tag-level-param of swap s" level.param" .head compact-tier level-name@ name-index .int
    endof
    nip ." level.?" swap .int endcase cr ;
: .e ( e -- ) expr-index .int ;
\ A tuple of the tier as a list, each item printed by xt ( u -- ).
: .items ( t xt -- )
  space ." [" swap compact-tier tier-tuples 2dup tuple-length 0 ?do
    i if ." ," then i 2 pick 2 pick tuple-item 3 pick execute loop 2drop drop ." ]" ;
: .level-item ( l -- ) level-index 0 .r ;
: .name-item ( n -- ) name-index 0 .r ;
: .names ( t -- ) ['] .name-item .items ;
: .payload-name ( e -- ) compact-tier expr-payload@ name-index .int ;
: emit-binder ( i e -- )
  dup compact-tier expr-tag@ tag-pi < if ." expr.lam" else ." expr.forallE" then
  swap .int dup .payload-name dup compact-tier expr-a@ .e dup compact-tier expr-b@ .e
  compact-tier expr-tag@ tag-lam - 3 and .int ;
: emit-let ( i e -- )
  ." expr.letE" swap .int dup .payload-name dup compact-tier expr-a@ .e
  dup compact-tier expr-b@ .e dup compact-tier expr-body@ .e
  compact-tier expr-tag@ tag-let-nondep = .flag ;
: emit-proj ( i e -- )
  ." expr.proj" swap .int dup .payload-name dup compact-tier expr-b@ .int
  compact-tier expr-a@ .e ;
: .text ( e -- addr u ) compact-tier expr-a@ compact-tier tier-texts text@ ;
: emit-other ( i e tag -- )
  case
    tag-bvar of ." expr.bvar" swap .int compact-tier expr-a@ .int endof
    tag-sort of ." expr.sort" swap .int compact-tier expr-a@ level-index .int endof
    tag-const of ." expr.const" swap .int dup compact-tier expr-a@ name-index .int
      compact-tier expr-b@ ['] .level-item .items endof
    tag-app of ." expr.app" swap .int dup compact-tier expr-a@ .e compact-tier expr-b@ .e
    endof
    tag-nat of ." expr.natVal" swap .int .text space type endof
    tag-str of ." expr.strVal" swap .int .text .hex endof
    tag-mdata of ." expr.mdata" swap .int compact-tier expr-a@ .e endof
    ." expr.?" >r 2drop r>
  endcase ;
: emit-expr ( i e -- )
  dup compact-tier expr-tag@ dup binder-tag? if drop emit-binder else
  dup let-tag? if drop emit-let else dup tag-proj = if drop emit-proj else emit-other
  then then then cr ;

\ Declarations: top-level ones numbered in order, a block's elements
\ within their list.
variable decl-top  variable types-seen  variable ctors-seen  variable recs-seen
: .item ( k d -- ) compact-stage staged-item .int ;
: .names-item ( k d -- ) compact-stage staged-item .names ;
: .decl ( d -- )
  dup compact-stage staged-name@ name-index .int dup compact-stage staged-params@ .names
  compact-stage staged-type@ .e ;
: .value ( d -- ) compact-stage staged-value@ .e ;
: .all-names ( d -- ) compact-stage staged-more@ .names ;
: top ( c-addr u -- ) type decl-top @ .int 1 decl-top +! ;
: element ( c-addr u counter -- ) >r type r@ @ .int 1 r> +! ;
: emit-def ( d -- )
  s" decl.def" top dup .decl dup .value dup compact-stage staged-hints@ .int
  dup compact-stage staged-hint@ .int dup compact-stage staged-safety@ .int .all-names ;
: emit-block ( d -- )
  s" decl.inductive" top 0 types-seen ! 0 ctors-seen ! 0 recs-seen !
  more-block-types over .item more-block-ctors over .item
  more-block-recursors swap .item ;
: emit-type ( d -- )
  s" ind.type" types-seen element dup .decl more-type-params over .item
  more-type-indices over .item more-type-all over .names-item
  more-type-ctors over .names-item more-type-nested over .item
  dup compact-stage staged-rec? .flag dup compact-stage staged-unsafe? .flag
  compact-stage staged-reflexive? .flag ;
: emit-ctor ( d -- )
  s" ind.ctor" ctors-seen element dup .decl
  more-ctor-induct over compact-stage staged-item name-index .int
  more-ctor-cidx over .item more-ctor-params over .item more-ctor-fields over .item
  compact-stage staged-unsafe? .flag ;
: rule-item ( k t -- u ) compact-tier tier-tuples tuple-item ;
\ The rule whose items start at k of the rules tuple t.
: .rule ( k t -- )
  over rule-ctor-item + over rule-item name-index 0 .r ." :"
  over rule-fields-item + over rule-item 0 .r ." :"
  swap rule-rhs-item + swap rule-item expr-index 0 .r ;
: .rules ( t -- )
  space ." [" dup compact-tier tier-tuples tuple-length 0 ?do
    i if ." ," then i over .rule /rule-items +loop drop ." ]" ;
: emit-recursor ( d -- )
  s" ind.rec" recs-seen element dup .decl more-rec-all over .names-item
  more-rec-params over .item more-rec-indices over .item more-rec-motives over .item
  more-rec-minors over .item dup compact-stage staged-k? .flag
  dup compact-stage staged-unsafe? .flag more-rec-rules swap compact-stage staged-item
  .rules ;
: emit-decl ( d -- )
  dup compact-stage staged-kind@ case
    kind-axiom of s" decl.axiom" top dup .decl compact-stage staged-unsafe? .flag endof
    kind-def of emit-def endof
    kind-thm of s" decl.thm" top dup .decl dup .value .all-names endof
    kind-opaque of s" decl.opaque" top dup .decl dup .value
      dup compact-stage staged-unsafe? .flag .all-names endof
    kind-quot of s" decl.quot" top dup .decl compact-stage staged-quot-kind@ .int endof
    kind-inductive of emit-block endof
    kind-type of emit-type endof
    kind-ctor of emit-ctor endof
    kind-recursor of emit-recursor endof
    ." decl.?" swap .int
  endcase cr ;

: emit-names ( -- ) compact-stage stage-name-map slab-count 1 ?do i emit-name loop ;
: emit-levels ( -- ) compact-stage stage-level-map slab-count 1 ?do i emit-level loop ;
: emit-exprs ( -- )
  compact-stage stage-expr-map slab-count 0 ?do i dup export>expr' emit-expr loop ;
: emit-decls ( -- ) 0 decl-top ! compact-stage stage-decls 0 ?do i emit-decl loop ;
\ Print every record, family by family, each in export order.
: compact-emit ( -- )
  inverses ok? 0= abort" compact-emit: no room for the inverse maps"
  emit-meta emit-names emit-levels emit-exprs emit-decls ;

\ ---- Timing and statistics.
: now ( -- us ) utime drop ;
: .ms ( us -- ) 500 + 1000 / 0 .r ." ms" ;
: .kv ( n c-addr u -- ) space type ." =" 0 .r ;
: .table ( cons c-addr u -- )
  type cons-table >r r@ htab-count s" entries" .kv r@ htab-slots s" slots" .kv
  r@ htab-stats rot s" finds" .kv swap s" compared" .kv s" grows" .kv
  ."  load%=" r@ htab-count 100 * r> htab-slots / 0 .r cr ;
: .family ( cons c-addr u -- )
  2dup type ." :" 2 pick cons-numbers s" numbers" .kv
  2 pick cons-records slab-used-bytes s" record-bytes" .kv
  2 pick cons-bytes slab-count s" text-bytes" .kv
  2 pick cons-table htab-slots u32s s" table-bytes" .kv cr ." table " .table ;
: decls-of-kind ( kind -- n )
  0 compact-stage stage-decls 0 ?do i compact-stage staged-kind@ 2 pick = - loop nip ;
: compact-stats ( -- )
  compact-tier tier-names s" names" .family compact-tier tier-levels s" levels" .family
  compact-tier tier-tuples s" tuples" .family compact-tier tier-texts s" texts" .family
  compact-tier tier-exprs s" exprs" .family
  ." input tier: bytes used=" compact-tier tier-used 0 .r
  ."  allocated=" compact-tier tier-allocated 0 .r cr
  ." declarations=" compact-stage stage-decls 0 .r
  ."  bytes=" compact-stage stage-decl-records slab-bytes 0 .r
  ."  name-array bytes=" compact-stage stage-by-name slab-bytes 0 .r
  ."  marked=" compact-stage stage-marks @ 0 .r ."  mdata=" compact-stage stage-mdata @
  0 .r
  cr ." kinds:" kind-recursor 1+ kind-axiom do space i decls-of-kind 0 .r loop cr
  ." export maps: names=" compact-stage stage-name-map slab-count 0 .r
  ."  levels=" compact-stage stage-level-map slab-count 0 .r
  ."  exprs=" compact-stage stage-expr-map slab-count 0 .r
  ."  bytes=" compact-stage stage-name-map slab-bytes compact-stage stage-level-map
  slab-bytes + compact-stage stage-expr-map slab-bytes + 0 .r cr
  ." stage allocated=" compact-stage stage-allocated 0 .r cr ;

\ ---- Finding every declaration by name. Through the array: the newest
\ declaration of its name, then back along the chain to it.
: chain-finds? ( d -- flag )
  dup compact-stage staged-name@ compact-stage stage-find 0= if drop false exit then
  begin 2dup <> while compact-stage stage-previous 0= if drop false exit then repeat
  2drop true ;
: named? ( d -- flag ) compact-stage staged-kind@ kind-inductive <> ;
: array-finds ( -- named found )
  0 0 compact-stage stage-decls 0 ?do
    i named? if swap 1+ swap i chain-finds? if 1+ then then loop ;
\ By text: each component of the name through a scratch tier over the
\ sealed input (no insertion), the name found must be the declaration's.
: comps ( -- stack ) compact-loaded comp-stack ;
: chain ( n -- ) comps slab-clear begin dup while dup comps fields-push drop
  compact-tier name-prefix@ repeat drop ;
: comp-step ( id comp -- id' true | false )
  dup compact-tier name-tag@ tag-name-str =
  if compact-tier name-text@ compact-scratch name-find-str
  else compact-tier name-number@ compact-scratch name-find-num then ;
: comp@ ( k -- comp ) comps slab-count 1- swap - comps fields@ ;
: resolve ( n -- n' true | false )
  chain name-anonymous comps slab-count 0 ?do
    i comp@ comp-step 0= if false unloop exit then
  loop true ;
: text-finds ( -- found )
  0 compact-stage stage-decls 0 ?do
    i named? if i compact-stage staged-name@ dup resolve if = if 1+ then else drop then
    then
  loop ;
: text-lookups ( -- found )
  compact-tier compact-scratch tier-extend ok? 0= abort" lookups: no scratch tier"
  text-finds compact-scratch tier-free ;
: compact-lookups ( -- )
  now >r array-finds now r> - >r
  ." name lookups through the array: declarations=" swap 0 .r ."  found=" 0 .r space r>
  .ms cr now text-lookups now rot - swap
  ." name lookups by text: found=" 0 .r space .ms cr ;

\ ---- Resolutions: every constant of the input against the array. One
\ declaration of its name: the payload names it; several: payload 0;
\ none: payload 0, a recursor Lean generates (ADR 0016 amendment 1), or,
\ after a continued read, a name only an earlier read contained.
: decls-named ( n -- k )
  compact-stage stage-find 0= if 0 exit then
  1 begin swap compact-stage stage-previous while swap 1+ repeat ;
: named-elsewhere? ( n -- flag )
  dup compact-stage generated-name? swap compact-stage earlier-name? or ;
: resolution-ok? ( e -- flag )
  dup compact-tier expr-a@ dup decls-named rot compact-tier expr-payload@
  over 1 = if nip ?dup if 1- compact-stage staged-name@ = else drop false then
  else 0= swap ?dup if 1 > and nip else swap named-elsewhere? and then then ;
: resolutions ( -- constants wrong )
  0 0 compact-tier tier-exprs cons-numbers 0 ?do
    i compact-tier expr-tag@ tag-const = if
      swap 1+ swap i resolution-ok? 0= if 1+ then
    then
  loop ;
: compact-resolutions ( -- )
  resolutions ." constants=" swap 0 .r ."  wrong=" 0 .r cr ;

\ ---- The derived data, checked silently: every named declaration found
\ through the array and by its text, every constant's resolution right.
\ Prints one line, which compact-verify.sh refuses, when anything misses.
: derived-misses ( -- named array text wrong )
  array-finds text-lookups resolutions nip ;
: derived-ok? ( named array text wrong -- flag ) 0= >r 2 pick = >r = r> and r> and ;
: compact-derived ( -- )
  derived-misses 2over 2over derived-ok? if 2drop 2drop exit then
  ." error: derived data: wrong=" 0 .r ."  by text=" 0 .r ."  by array=" 0 .r
  ."  named=" 0 .r cr ;

\ ---- Entry words.
\ Load the export named c-addr u, print its dump lines, then check the
\ derived data.
: compact-dump ( c-addr u -- )
  16 compact-load dup ok? 0= if ." error: " . cr exit then drop compact-emit
  compact-derived compact-free ;
: compact-dump-unchecked ( c-addr u -- )
  16 compact-load-unchecked dup ok? 0= if ." error: " . cr exit then drop
  compact-emit compact-derived compact-free ;
\ Load the export named c-addr u and report, for tests/core/test_stage.py:
\ "ok decls=N" with the lookups and resolutions; or, after the line
\ compact-load prints, "outcome=N" and for an unknown constant its name.
: .culprit ( -- )
  ." culprit=" compact-stage stage-culprit@ compact-tier name-text@ type cr ;
: tried ( outcome -- )
  dup ok? if drop ." ok decls=" compact-stage stage-decls 0 .r cr
    compact-lookups compact-resolutions
  else ." outcome=" 0 .r cr compact-stage stage-why @ if .culprit then then
  compact-free ;
: compact-try ( c-addr u -- ) 12 compact-load tried ;
: compact-try-unchecked ( c-addr u -- ) 12 compact-load-unchecked tried ;
\ Load with the expression table starting at 2^log2 slots, and report
\ time, sizes, tables, lookups and resolutions.
: compact-measure ( c-addr u log2 -- )
  now >r compact-load now r> - swap dup ok? 0= if ." error: " . drop cr exit then drop
  ." load, manifest check and seal: " .ms cr compact-stats compact-lookups
  compact-resolutions compact-free ;

\ ---- Continued reads and the saved tier (see the header).
create compact-tf /tier-file allot  compact-tf tier-file-init
: continued ( b-addr b-u outcome -- outcome )
  dup ok? 0= if nip nip exit then drop compact-stage stage-continue-unchecked
  dup ok? if drop compact-stage stage-seal then loaded ;
: compact-continue-load ( a-addr a-u b-addr b-u -- outcome )
  12 compact-start dup ok? 0= if nip nip nip nip exit then drop
  2swap compact-stage stage-read-unchecked loaded continued ;
: compact-saved ( f-addr f-u -- outcome ) compact-stage compact-tf tier-save ;
: compact-reload ( c-addr u f-addr f-u -- outcome )
  2swap 12 compact-load-unchecked dup ok? 0= if nip nip exit then drop
  2dup compact-saved dup ok? 0= if nip nip exit then drop
  compact-free 12 compact-start dup ok? 0= if nip nip exit then drop
  compact-stage compact-tf tier-load loaded ;
: compact-snap-continue-load ( a-addr a-u b-addr b-u f-addr f-u -- outcome )
  2rot 2swap compact-reload continued ;
: dumped ( outcome -- )
  dup ok? 0= if ." error: " . cr exit then drop compact-emit compact-free ;
: compact-continue-try ( a-addr a-u b-addr b-u -- ) compact-continue-load tried ;
: compact-continue-dump ( a-addr a-u b-addr b-u -- ) compact-continue-load dumped ;
: compact-snap-continue-try ( a b f -- ) compact-snap-continue-load tried ;
: compact-snap-continue-dump ( a b f -- ) compact-snap-continue-load dumped ;
: compact-save ( f-addr f-u -- ) compact-saved ." saved=" 0 .r cr ;
: compact-resave ( f1-addr f1-u f2-addr f2-u -- )
  2swap 12 compact-start drop compact-stage compact-tf tier-load
  dup ." loaded=" 0 .r cr ok? if compact-stage stage-seal ." sealed=" 0 .r cr compact-save
  else 2drop then compact-free ;
