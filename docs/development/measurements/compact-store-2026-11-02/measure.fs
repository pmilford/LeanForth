\ Prototype (ADR 0016, measurement code): measurements over a loaded compact store:
\ statistics, re-emission in the reader dump's format, traversals and name
\ lookups. Not a module of src/.
require ./load.fs

: now ( -- us ) utime drop ;
: .secs ( us -- ) s>f 1e6 f/ 3 set-precision f. ." s" ;
variable t0
: start ( -- ) now t0 ! ;
: lap ( c-addr u -- ) type ."  " now t0 @ - .secs cr ;

\ ---- statistics
create tag-counts #tags cells allot
: count-tags ( -- )
  tag-counts #tags cells erase e-count 0 ?do 1 i e-tag@ cells tag-counts + +! loop ;
: tags-range ( lo hi -- n ) 0 -rot swap ?do tag-counts i cells + @ + loop ;
: .n ( n -- ) 0 .r ;
: .kv ( n c-addr u -- ) type ." =" .n ."  " ;
: .tags ( -- )
  count-tags
  t-app dup 1+ tags-range s" app" .kv  t-lam t-forall tags-range s" lam" .kv
  t-forall t-let tags-range s" forallE" .kv  t-const dup 1+ tags-range s" const" .kv
  t-let t-let-nondep 1+ tags-range s" letE" .kv  t-proj dup 1+ tags-range s" proj" .kv
  t-strlit dup 1+ tags-range s" strVal" .kv  t-natlit dup 1+ tags-range s" natVal" .kv
  t-sort dup 1+ tags-range s" sort" .kv  t-bvar dup 1+ tags-range s" bvar" .kv
  t-let-body dup 1+ tags-range s" let-body" .kv cr ;
: .tab ( htab c-addr u -- )
  type ."  slots=" dup htab-slots .n ."  entries=" dup htab-count @ .n
  ."  load=" dup htab-count @ s>f dup htab-slots s>f f/ 3 set-precision f.
  ."  lookups=" dup htab-lookups @ .n ."  compared=" dup htab-probes @ .n
  ."  grows=" htab-grows @ .n cr ;
: .arena ( arena c-addr u -- )
  type ."  used=" dup arena-used-bytes .n ."  allocated=" arena-bytes .n cr ;
: .pool ( pool c-addr u -- ) type ."  used=" dup pool-used @ .n ."  allocated=" pool-cap @ .n cr ;
: tab-bytes ( htab -- n ) htab-slots u32s ;
: .bytes-per-node ( -- )
  ." exprs=" e-count .n ."  export-exprs=" emap arena-used @ .n
  ."  duplicates=" dups @ .n cr
  ." node bytes/export expr: records " exprs arena-used-bytes s>f emap arena-used @ s>f f/ f.
  ." table " expr-tab tab-bytes s>f emap arena-used @ s>f f/ f. cr ;
: .totals ( -- )
  exprs arena-bytes expr-tab tab-bytes + names arena-bytes + name-tab tab-bytes +
  name-bytes pool-cap @ + levels arena-bytes + level-tab tab-bytes + lists arena-bytes +
  list-tab tab-bytes + lits arena-bytes + lit-tab tab-bytes + lit-bytes pool-cap @ +
  decls arena-bytes + ." store allocated bytes (without load maps)=" .n
  ."  load maps=" emap arena-bytes nmap arena-bytes + lmap arena-bytes + .n cr ;
: .max-data ( -- )
  0 0 e-count 0 ?do i e-data@ tuck d-depth max >r d-range max r> loop
  swap ." max loose range=" .n ."  max depth (clamped 1023)=" .n cr ;
\ Sums over the data words of the expressions in export order, for
\ comparison with an independent computation (data_check.py).
variable sum-range  variable sum-depth  variable n-lp
: data-sums ( -- )
  0 sum-range ! 0 sum-depth ! 0 n-lp !
  emap arena-used @ 0 ?do i emap arena@ e-data@ dup d-range sum-range +!
    dup d-depth sum-depth +! lp-bit and if 1 n-lp +! then loop
  ." data: sum-range=" sum-range @ .n ."  sum-depth=" sum-depth @ .n
  ."  has-level-param=" n-lp @ .n cr ;
: stats ( -- )
  .tags .bytes-per-node
  ." names=" n-count .n ."  levels=" l-count .n ."  decls=" d-count .n
  ."  inductive blocks=" blocks @ .n ."  lists used quads=" lists arena-used @ .n cr
  expr-tab s" expr-table" .tab name-tab s" name-table" .tab level-tab s" level-table" .tab
  list-tab s" list-table" .tab lit-tab s" literal-table" .tab
  exprs s" exprs" .arena names s" names" .arena name-bytes s" name-bytes" .pool
  levels s" levels" .arena lists s" lists" .arena decls s" decls" .arena
  lit-bytes s" literal-bytes" .pool .totals .max-data data-sums ;

\ ---- re-emission, in tests/core/ndjson-dump.fs's format, in export order
: .int ( n -- ) space 0 .r ;
: .hex-byte ( c -- ) base @ >r hex 0 <# # # #> type r> base ! ;
: .hex ( addr u -- ) space dup 0= if 2drop ." -" exit then over + swap ?do i c@ .hex-byte loop ;
: emit-name ( i -- )
  dup n-tag@ name-str = if ." name.str" dup .int dup n-prefix@ .int n-text .hex
  else ." name.num" dup .int dup n-prefix@ .int n-b@ .int then cr ;
: emit-names ( -- ) n-count 1 ?do i emit-name loop ;
: emit-level ( i -- )
  dup l-head@ $F and case
    lv-succ of ." level.succ" dup .int dup l-a@ .int endof
    lv-max of ." level.max" dup .int dup l-a@ .int dup l-b@ .int endof
    lv-imax of ." level.imax" dup .int dup l-a@ .int dup l-b@ .int endof
    lv-param of ." level.param" dup .int dup l-head@ 4 rshift .int endof
  endcase drop cr ;
: emit-levels ( -- ) l-count 1 ?do i emit-level loop ;
\ Expressions: by export index; children are printed as the export index
\ of their first occurrence (einv).
arena: einv
: einv-build ( -- )
  e-count einv arena-init e-count einv arena-used ! einv arena-base @ e-count u32s $FF fill
  emap arena-used @ 0 ?do i emap arena@ einv arena-at dup u32@ u32-mask = if i swap u32!
  else drop then loop ;
: .e ( node -- ) einv arena@ .int ;
: .list ( id -- ) space ." [" dup list-n@ 0 ?do i if ." ," then i over list-item@ 0 .r loop drop ." ]" ;
: emit-binder ( i node c-addr u -- )
  type swap .int dup e-payload@ .int dup e-a@ .e dup e-b@ .e e-tag@ t-lam - 3 and .int ;
: emit-expr ( i node -- )
  dup e-tag@ case
    t-bvar of ." expr.bvar" swap .int e-a@ .int endof
    t-sort of ." expr.sort" swap .int e-a@ .int endof
    t-const of ." expr.const" swap .int dup e-a@ .int e-b@ .list endof
    t-app of ." expr.app" swap .int dup e-a@ .e e-b@ .e endof
    t-proj of ." expr.proj" swap .int dup e-payload@ .int dup e-b@ .int e-a@ .e endof
    t-natlit of ." expr.natVal" swap .int e-a@ lit-text space type endof
    t-strlit of ." expr.strVal" swap .int e-a@ lit-text .hex endof
    t-let of ." expr.letE" swap .int dup e-payload@ .int dup e-a@ .e dup e-b@ .e 1+ e-a@ .e
      0 .int endof
    t-let-nondep of ." expr.letE" swap .int dup e-payload@ .int dup e-a@ .e dup e-b@ .e
      1+ e-a@ .e 1 .int endof
    dup t-forall < if >r s" expr.lam" emit-binder r> else >r s" expr.forallE" emit-binder r>
    then endcase cr ;
: emit-exprs ( -- ) einv-build emap arena-used @ 0 ?do i dup emap arena@ emit-expr loop ;
: emit-all ( -- ) emit-names emit-levels emit-exprs ;

\ ---- traversals. A stack of node ids; the visit check is deferred.
arena: wstack
: push ( n -- ) wstack arena-push ;
: pop ( -- n ) wstack arena-used @ 1- dup wstack arena-used ! wstack arena@ ;
: two ( n -- ) dup e-a@ push e-b@ push ;
: kids ( n -- )
  dup e-tag@ dup t-app t-let within if drop two exit then
  dup let? if drop dup two 1+ e-a@ push exit then
  t-proj = if e-a@ push else drop then ;
: roots ( d -- )
  dup d-type@ push dup d-value@ dup none <> if push else drop then
  d-rules@ dup none <> if dup list-n@ 0 ?do i over list-item@ push loop then drop ;
defer seen?   ( n -- flag )   \ true when already visited; marks it otherwise
variable cap   variable capped   variable epoch
\ Visit everything reachable from the stack; gives the visits.
: walk ( -- visits )
  0 begin wstack arena-used @ while
    pop dup seen? if drop else kids 1+ dup cap @ > if 1 capped +! 0 wstack arena-used ! then
    then repeat ;
\ Dense visited stamps: one packed field per node, epoch-stamped.
arena: stamps
: stamps-init ( -- ) e-count stamps arena-init e-count stamps arena-used !
  stamps arena-base @ e-count u32s erase ;
: seen-dense? ( n -- flag )
  stamps arena-at dup u32@ epoch @ = if drop true else epoch @ swap u32! false then ;
\ Hashed visited set: (node+1, epoch) pairs, 2^18 pairs, linear probing.
arena: vset   18 constant vbits   1 vbits lshift 1- constant vmask   variable vprobes
: vset-init ( -- ) 1 vbits lshift 2* dup vset arena-init vset arena-used !
  vset arena-base @ 1 vbits lshift 2* u32s erase ;
: vkey@ ( slot -- u ) 2* vset arena@ ;
: vepoch@ ( slot -- u ) 2* 1+ vset arena@ ;
: vclaim ( n slot -- ) tuck 2* vset arena! epoch @ swap 2* 1+ vset arena! ;
: seen-hashed? ( n -- flag )
  1+ dup fmix vmask and begin dup vepoch@ epoch @ = while
    1 vprobes +! 2dup vkey@ = if 2drop true exit then 1+ vmask and repeat
  vclaim false ;
: seen-never? ( n -- flag ) drop false ;
\ Walk every declaration's roots; per-declaration epochs.
variable most   variable total
: walk-decls ( -- )
  0 total ! 0 most ! 0 capped ! 0 wstack arena-used !
  d-count 0 ?do i 1+ epoch ! i roots walk dup total +! most @ max most ! loop ;
: .walk ( c-addr u -- )
  type ."  visits=" total @ .n ."  max-per-decl=" most @ .n ."  capped-decls=" capped @ .n ;
: walk-dense ( -- ) stamps-init ['] seen-dense? is seen? max-n cap ! start walk-decls
  s" dense-stamps" .walk s"  " lap ;
: walk-hashed ( -- ) ['] seen-hashed? is seen? max-n cap ! 0 vprobes ! start walk-decls
  s" hashed-set" .walk ."  compared=" vprobes @ .n s"  " lap ;
: walk-tree ( limit -- ) ['] seen-never? is seen? cap ! start walk-decls
  s" no-cache" .walk ."  cap=" cap @ .n s"  " lap ;
\ Reachable nodes over all declarations at once, and the nodes reachable
\ only from theorem values (stamp 1: from types, other values and rules;
\ stamp 2: from theorem values only).
: seen-mark? ( n -- flag )
  stamps arena-at dup u32@ if drop true else epoch @ swap u32! false then ;
: non-proof-roots ( d -- )
  dup d-type@ push dup d-kind@ k-thm <> if dup d-value@ dup none <> if push else drop then then
  d-rules@ dup none <> if dup list-n@ 0 ?do i over list-item@ push loop then drop ;
: proof-roots ( d -- ) dup d-kind@ k-thm = if d-value@ push else drop then ;
: proof-only ( -- )
  ['] seen-mark? is seen? max-n cap ! stamps-init start
  1 epoch ! 0 d-count 0 ?do i non-proof-roots walk + loop
  2 epoch ! 0 d-count 0 ?do i proof-roots walk + loop
  ." reachable without theorem values=" swap .n ."  only from theorem values=" .n
  ."  of nodes=" e-count .n s"  " lap ;

\ ---- name lookups: every declaration's name, component by component
\ through the name table (no insertion), then the by-name array.
create chain 256 cells allot   variable depth#
create comp 4096 chars allot
: chain-of ( n -- ) 0 depth# ! begin dup while dup depth# @ cells chain + ! 1 depth# +!
  n-prefix@ repeat drop ;
: step ( id comp -- id' )
  dup n-tag@ name-num = if n-b@ nkey-num else n-text dup 4096 > abort" component too long"
    >r comp r@ move comp r> nkey-str then
  name-find 0= abort" name not found" ;
: resolve ( n -- id ) chain-of 0 depth# @ 0 ?do depth# @ 1- i - cells chain + @ step loop ;
: has-decl? ( d n -- flag )
  by-name arena@ begin dup while 1- 2dup = if 2drop true exit then d-next@ repeat 2drop false ;
variable found
: lookup-text ( -- )
  0 found ! start d-count 0 ?do i d-name@ dup resolve <> abort" wrong name"
  i dup d-name@ has-decl? if 1 found +! then loop
  ." name lookups by text: decls=" d-count .n ."  found=" found @ .n s"  " lap ;
: lookup-ids ( -- )
  0 found ! start d-count 0 ?do i dup d-name@ has-decl? if 1 found +! then loop
  ." name lookups by id: found=" found @ .n s"  " lap ;
