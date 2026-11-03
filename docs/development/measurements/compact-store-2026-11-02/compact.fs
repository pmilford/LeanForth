\ Prototype (ADR 0016, measurement code): the compact input tier. Names, levels,
\ level and name lists, literals, expressions and declarations in packed
\ 32-bit records, hash-consed through open-addressing tables. Not a module of src/.
\ Record layouts (q0..q3 are packed 32-bit fields, 16 bytes a record):
\   name  q0 tag 0..3 | byte length << 4   q1 prefix   q2 offset or number  q3 hash
\   level q0 tag 0..3 | param name << 4    q1 left     q2 right             q3 data
\   expr  q0 tag 0..4 | payload << 5       q1 a        q2 b                 q3 data
\ Expression data word: loose bound-variable range (bits 0-19, exact, as
\ Lean's), has level parameters (20), has free variables (21, always 0 in
\ input), approximate depth (22-31, clamped at 1023).
\ A letE takes two records: the second, tag let-body, holds the body in q1.

: quad ( i -- au ) u32s ;
: rec ( i arena -- addr ) swap 4 * swap arena-at ;

\ ---- names
0 constant name-anon  1 constant name-str  2 constant name-num
arena: names  pool: name-bytes
: nrec ( i -- addr ) names rec ;
: n-head@ ( i -- u ) nrec u32@ ;
: n-tag@ ( i -- tag ) n-head@ $F and ;
: n-len@ ( i -- u ) n-head@ 4 rshift ;
: n-prefix@ ( i -- u ) nrec 1 quad + u32@ ;
: n-b@ ( i -- u ) nrec 2 quad + u32@ ;
: n-hash@ ( i -- u ) nrec 3 quad + u32@ ;
: n-text ( i -- addr u ) dup n-b@ swap n-len@ name-bytes pool-text ;
: n-count ( -- n ) names arena-used @ 4 / ;
' n-hash@ htab: name-tab
\ The name being looked up.
begin-structure /nkey
  field: nkey-tag  field: nkey-prefix  field: nkey-addr  field: nkey-u  field: nkey-hash
end-structure
create nkey /nkey allot
: str-hash ( prefix addr u -- h ) bytes-hash swap fmix h+ 1 h+ ;
: num-hash ( prefix n -- h ) swap fmix h+ 2 h+ ;
: nkey-head= ( i -- flag ) dup n-tag@ nkey nkey-tag @ = swap n-prefix@ nkey nkey-prefix @ = and ;
: nkey-body= ( i -- flag )
  nkey nkey-tag @ name-num = if n-b@ nkey nkey-u @ =
  else n-text nkey nkey-addr @ nkey nkey-u @ compare 0= then ;
: nkey= ( i -- flag ) dup nkey-head= if nkey-body= else drop false then ;
: nkey-head ( -- head )
  nkey nkey-tag @ dup name-str = if nkey nkey-u @ 4 lshift or then ;
: name-new ( -- id )
  4 names arena-claim 4 / >r
  nkey-head r@ nrec u32!
  nkey nkey-prefix @ r@ nrec 1 quad + u32!
  nkey nkey-hash @ r@ nrec 3 quad + u32! r> ;
: name-body! ( id -- )
  nkey nkey-tag @ name-num = if nkey nkey-u @ else
  nkey nkey-addr @ nkey nkey-u @ name-bytes pool-add then swap nrec 2 quad + u32! ;
\ Find or add the name in nkey.
: name-find ( -- id true | addr false ) nkey nkey-hash @ name-tab ['] nkey= htab-find ;
: name-intern ( -- id )
  name-tab htab-ready name-find if exit then
  name-new dup name-body! tuck 1+ swap u32! name-tab htab-added ;
: nkey-str ( prefix addr u -- )
  name-str nkey nkey-tag ! nkey nkey-u ! nkey nkey-addr ! nkey nkey-prefix !
  nkey nkey-prefix @ nkey nkey-addr @ nkey nkey-u @ str-hash nkey nkey-hash ! ;
: nkey-num ( prefix n -- )
  name-num nkey nkey-tag ! 2dup num-hash nkey nkey-hash ! nkey nkey-u ! nkey nkey-prefix ! ;
: names-init ( -- )
  1 20 lshift names arena-init 1 20 lshift name-bytes pool-init 16 name-tab htab-init
  4 names arena-claim drop 0 nrec 4 quad erase ;

\ ---- levels
0 constant lv-zero  1 constant lv-succ  2 constant lv-max  3 constant lv-imax
4 constant lv-param
1 20 lshift constant lp-bit
arena: levels
: level ( i -- addr ) levels rec ;
: l-head@ ( i -- u ) level u32@ ;
: l-a@ ( i -- u ) level 1 quad + u32@ ;
: l-b@ ( i -- u ) level 2 quad + u32@ ;
: l-data@ ( i -- u ) level 3 quad + u32@ ;
: l-count ( -- n ) levels arena-used @ 4 / ;
: key3-hash ( head a b -- h ) rot fmix rot h+ swap h+ ;
: l-rehash ( i -- h ) dup l-head@ over l-a@ rot l-b@ key3-hash ;
' l-rehash htab: level-tab
create lkey 4 cells allot   \ head a b data
: lkey= ( i -- flag )
  dup l-head@ lkey @ = over l-a@ lkey cell+ @ = and swap l-b@ lkey 2 cells + @ = and ;
: level-new ( -- id )
  4 levels arena-claim 4 / 4 0 do lkey i cells + @ over level i quad + u32! loop ;
: level-intern ( head a b data -- id )
  lkey 3 cells + ! lkey 2 cells + ! lkey cell+ ! lkey ! level-tab htab-ready
  lkey @ lkey cell+ @ lkey 2 cells + @ key3-hash level-tab ['] lkey= htab-find if exit then
  level-new tuck 1+ swap u32! level-tab htab-added ;
: levels-init ( -- )
  1 16 lshift levels arena-init 12 level-tab htab-init 0 0 0 0 level-intern drop ;

\ ---- lists (of level ids or name ids): [n] [item] ...; id = quad index of n
arena: lists
create litems 1024 cells allot   variable lcount
: li! ( u -- ) lcount @ 1024 < 0= abort" list too long" litems lcount @ cells + ! 1 lcount +! ;
: list-n@ ( id -- n ) lists arena@ ;
: list-item@ ( i id -- u ) + 1+ lists arena@ ;
: litems-hash ( -- h ) lcount @ fmix lcount @ 0 ?do litems i cells + @ h+ loop ;
: list-rehash ( id -- h )
  dup list-n@ fmix swap dup list-n@ 0 ?do i over list-item@ rot swap h+ swap loop drop ;
' list-rehash htab: list-tab
: litems= ( id -- flag )
  dup list-n@ lcount @ <> if drop false exit then
  lcount @ 0 ?do i over list-item@ litems i cells + @ <> if drop false unloop exit then loop
  drop true ;
: list-new ( -- id )
  lcount @ 1+ lists arena-claim lcount @ over lists arena!
  lcount @ 0 ?do litems i cells + @ over i + 1+ lists arena! loop ;
: list-intern ( -- id )
  list-tab htab-ready litems-hash list-tab ['] litems= htab-find if exit then
  list-new tuck 1+ swap u32! list-tab htab-added ;
: lists-start ( -- ) 0 lcount ! ;
: lists-init ( -- ) 1 16 lshift lists arena-init 12 list-tab htab-init ;

\ ---- literals: records (offset, length) in lits, bytes in lit-bytes
arena: lits  pool: lit-bytes
: lit-off@ ( id -- u ) 2 * lits arena@ ;
: lit-len@ ( id -- u ) 2 * 1+ lits arena@ ;
: lit-text ( id -- addr u ) dup lit-off@ swap lit-len@ lit-bytes pool-text ;
: lit-rehash ( id -- h ) lit-text bytes-hash ;
' lit-rehash htab: lit-tab
2variable litkey
: litkey= ( id -- flag ) lit-text litkey 2@ compare 0= ;
: lit-intern ( addr u -- id )
  litkey 2! lit-tab htab-ready litkey 2@ bytes-hash lit-tab ['] litkey= htab-find
  if exit then
  litkey 2@ lit-bytes pool-add 2 lits arena-claim tuck lits arena!
  litkey 2@ nip over 1+ lits arena! 2/ tuck 1+ swap u32! lit-tab htab-added ;
: lits-init ( -- ) 1024 lits arena-init 1 20 lshift lit-bytes pool-init 10 lit-tab htab-init ;

\ ---- expressions
1 constant t-bvar  2 constant t-sort  3 constant t-const  4 constant t-app
5 constant t-lam   9 constant t-forall  13 constant t-let  14 constant t-let-nondep
15 constant t-proj  16 constant t-natlit  17 constant t-strlit  18 constant t-let-body
19 constant #tags
arena: exprs
: enode ( i -- addr ) exprs rec ;
: e-head@ ( i -- u ) enode u32@ ;
: e-tag@ ( i -- tag ) e-head@ $1F and ;
: e-payload@ ( i -- u ) e-head@ 5 rshift ;
: e-a@ ( i -- u ) enode 1 quad + u32@ ;
: e-b@ ( i -- u ) enode 2 quad + u32@ ;
: e-data@ ( i -- u ) enode 3 quad + u32@ ;
: e-count ( -- n ) exprs arena-used @ 4 / ;
: let? ( tag -- flag ) t-let t-let-nondep 1+ within ;
: e-c@ ( i -- u ) dup e-tag@ let? if 1+ e-a@ else drop 0 then ;
: key4-hash ( head a b c -- h ) >r key3-hash r> h+ ;
: e-rehash ( i -- h ) >r r@ e-head@ r@ e-a@ r@ e-b@ r> e-c@ key4-hash ;
' e-rehash htab: expr-tab
create ek 5 cells allot   \ head a b c data
: ek@ ( i -- u ) cells ek + @ ;
: ek= ( i -- flag )
  dup e-head@ 0 ek@ = 0= if drop false exit then
  dup e-a@ 1 ek@ = over e-b@ 2 ek@ = and swap e-c@ 3 ek@ = and ;
: expr-fields! ( i -- )
  0 ek@ over enode u32! 1 ek@ over enode 1 quad + u32!
  2 ek@ over enode 2 quad + u32! 4 ek@ swap enode 3 quad + u32! ;
: let-body! ( i -- )
  t-let-body over enode u32! 3 ek@ over enode 1 quad + u32!
  0 over enode 2 quad + u32! 0 swap enode 3 quad + u32! ;
: expr-new ( -- id )
  0 ek@ $1F and let? if 8 else 4 then exprs arena-claim 4 /
  dup expr-fields! 0 ek@ $1F and let? if dup 1+ let-body! then ;
variable dups   \ expressions found already present
\ The expression table's probe loop, written out (no locals, no EXECUTE).
: e-slot ( i -- addr ) expr-tab slot-at ;
: e-next ( i -- i' ) 1+ expr-tab htab-mask @ and ;
: expr-find ( h -- id true | addr false )
  expr-tab htab-looked expr-tab htab-mask @ and
  begin dup e-slot u32@ ?dup while
    1 expr-tab htab-probes +! 1- dup ek= if nip true exit then drop e-next
  repeat e-slot false ;
\ Variants for timing: 0 hash-cons (default), 1 append without a table.
variable variant  0 variant !
: ek! ( head a b c data -- ) 4 cells ek + ! 3 cells ek + ! 2 cells ek + ! ek cell+ ! ek ! ;
: expr-intern ( head a b c data -- id )
  ek! variant @ if expr-new exit then
  expr-tab htab-ready 0 ek@ 1 ek@ 2 ek@ 3 ek@ key4-hash expr-find
  if 1 dups +! exit then
  expr-new tuck 1+ swap u32! expr-tab htab-added ;
variable etab-log2  16 etab-log2 !
: exprs-init ( -- ) 1 20 lshift exprs arena-init etab-log2 @ expr-tab htab-init 0 dups ! ;

\ Data words.
1 20 lshift 1- constant range-max
lp-bit 1 21 lshift or constant flag-bits
: d-range ( d -- r ) range-max and ;
: d-depth ( d -- n ) 22 rshift ;
: d-flags ( d -- f ) flag-bits and ;
: >data ( range flags depth -- d ) 1023 min 22 lshift or or ;
: lower ( range -- range' ) 1- 0 max ;
\ Data of a node over children with data d1 and d2 (body d2 lowered when
\ binder? is true).
: data2 ( d1 d2 binder? -- d )
  >r over d-range over d-range r> if lower then max
  >r 2dup or d-flags >r d-depth swap d-depth max 1+ r> r> swap rot >data ;

\ ---- declarations: 8 quads each
1 constant k-axiom  2 constant k-def  3 constant k-thm  4 constant k-opaque
5 constant k-quot  6 constant k-induct  7 constant k-ctor  8 constant k-rec
arena: decls
: decl ( i -- addr ) 8 * decls arena-at ;
: d-count ( -- n ) decls arena-used @ 8 / ;
: d-kind@ ( i -- k ) decl u32@ ;
: d-name@ ( i -- n ) decl 1 quad + u32@ ;
: d-type@ ( i -- e ) decl 3 quad + u32@ ;
: d-value@ ( i -- e ) decl 4 quad + u32@ ;
: d-rules@ ( i -- list ) decl 6 quad + u32@ ;
: d-next@ ( i -- d+1 ) decl 7 quad + u32@ ;
u32-mask constant none
: decl-new ( kind name params type -- id )
  8 decls arena-claim 8 / >r
  r@ decl 3 quad + u32! r@ decl 2 quad + u32! r@ decl 1 quad + u32! r@ decl u32!
  none r@ decl 4 quad + u32! none r@ decl 6 quad + u32! 0 r@ decl 7 quad + u32! r> ;
: decls-init ( -- ) 1 16 lshift decls arena-init ;
\ Name id to the newest declaration of that name, + 1; 0 for none.
arena: by-name
: index-decls ( -- )
  n-count by-name arena-init n-count by-name arena-used !
  by-name arena-base @ n-count quad erase
  d-count 0 ?do i d-name@ dup by-name arena@ i decl 7 quad + u32! i 1+ swap by-name arena! loop ;

: compact-init ( -- ) names-init levels-init lists-init lits-init exprs-init decls-init ;
