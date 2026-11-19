\ Unit tests of the compact store's Lean layer (src/core/compact*.fs,
\ ADR 0016): names, levels, lists and literals, and every expression kind,
\ each built, interned to one number, read back and refused when a part
\ is wrong; the data words as Lean computes them (loose range, universe
\ parameters, free variables, depth capped at 1023); the limits at and one
\ past their bounds (a bound variable's range, a name's length and number,
\ fields beyond 32 bits); invalid handles; two tiers (a sealed input, a
\ scratch tier over it whose numbers continue and which finds the input's
\ records); marks, rollbacks and resets over all five families; and a
\ randomized model of applications built in two tiers. Loaded under HEX.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/core/compact.fs decimal

create input /tier allot   create check /tier allot   create other /tier allot
create mk /tier-mark allot   create mk2 /tier-mark allot

\ An input tier: number 0 is the anonymous name and level zero.
T{ 4 input ' tier-init rs-checked -> outcome-ok }T
T{ name-anonymous input name-tag@ level-zero input level-tag@ -> tag-name-anon tag-level-zero }T
T{ input tier-names cons-numbers input tier-levels cons-numbers input tier-exprs cons-numbers -> 1 1 0 }T

\ Names: strings and numbers, interned.
: str ( prefix c-addr u -- n ) input name-str ok? 0= abort" str" ;
name-anonymous s" Nat" str constant nat
nat s" succ" str constant nat-succ
nat s" add" str constant nat-add
T{ name-anonymous s" Nat" input name-str nat s" succ" input name-str -> nat 0 nat-succ 0 }T
T{ nat 7 input name-num nat 7 input name-num nat 8 input name-num -> 4 0 4 0 5 0 }T
T{ nat-succ input name-tag@ nat-succ input name-prefix@ nat-succ input name-text@ s" succ" compare -> tag-name-str nat 0 }T
T{ 4 input name-tag@ 4 input name-number@ 4 input name-prefix@ -> tag-name-num 7 nat }T
T{ nat-add s" succ" input name-str nat s" succ" input name-find-str -> 6 0 nat-succ true }T
T{ nat s" pred" input name-find-str nat 9 input name-find-num nat 7 input name-find-num -> false false 4 true }T
\ A prefix that is not a name; a component one past the payload limit;
\ a number beyond 32 bits.
T{ 99 s" x" input name-str 99 1 input name-num -> -1 outcome-invalid -1 outcome-invalid }T
T{ nat here payload-limit input name-str -> -1 outcome-full }T
u32-mask 0> [if]
T{ nat u32-mask input name-find-num nat u32-mask 1+ input name-num -> false -1 outcome-full }T
[then]
T{ 0 input name-valid? 6 input name-valid? 99 input name-valid? -1 input name-valid? -> true true false false }T
\ Two components of one length with the same FNV-1a hash give names with
\ the same head and stored hash: the text tells them apart.
nat s" glbvs" str constant n-co
nat s" yacxa" str constant n-li
T{ n-co n-li = n-co input name-hash@ n-li input name-hash@ = -> false true }T
T{ nat s" yacxa" input name-str nat s" glbvs" input name-find-str -> n-li 0 n-co true }T

\ Levels.
: lvl ( l outcome -- l ) ok? 0= abort" lvl" ;
name-anonymous s" u" str constant u-name
level-zero input level-succ lvl constant one
u-name input level-param lvl constant u
T{ level-zero input level-succ one u input level-max one u input level-max -> one 0 u 1+ 0 u 1+ 0 }T
T{ one u input level-imax u one input level-imax -> u 2 + 0 u 3 + 0 }T
T{ u input level-params? one input level-params? u 1+ input level-params? -> true false true }T
T{ u input level-tag@ u input level-name@ u 1+ input level-a@ u 1+ input level-b@ -> tag-level-param u-name one u }T
\ Refused: a child that is not a level, a parameter that is not a name,
\ unused fields that are not 0, a tag without a level kind, fields beyond
\ 32 bits.
T{ 99 input level-succ 99 one input level-max 99 input level-param -> -1 1 -1 1 -1 1 }T
T{ tag-level-succ one 1 input level-build tag-level-zero 1 0 input level-build -> -1 1 -1 1 }T
T{ tag-level-param u-name pack-head 0 7 input level-build 9 0 0 input level-build -> -1 1 -1 1 }T
u32-mask 0> [if]
T{ tag-level-succ u32-mask 1+ 0 input level-build -> -1 outcome-invalid }T
T{ tag-level-succ u32-mask 1+ one + 0 input level-build -> -1 outcome-invalid }T
[then]
T{ input tier-levels cons-numbers -> u 4 + }T

\ Lists of levels.
: list-of ( l1 .. ln n -- t )
  input tier-tuples tuple-start drop 0 ?do input tier-tuples tuple-add drop loop
  input tier-tuples tuple-end ok? 0= abort" list" ;
0 list-of constant no-levels
u 1 list-of constant [u]
u one 2 list-of constant [one,u]

\ Expressions: every kind, its data word, and interning.
: ex ( e outcome -- e ) ok? 0= abort" ex" ;
: range@ ( e -- n ) input expr-data@ data-range ;
: depth@ ( e -- n ) input expr-data@ data-depth ;
: params@ ( e -- flag ) input expr-data@ data-params? ;
0 input expr-bvar ex constant b0
1 input expr-bvar ex constant b1
T{ 0 input expr-bvar b0 range@ b1 range@ b0 depth@ -> b0 0 1 2 0 }T
level-zero input expr-sort ex constant prop
u input expr-sort ex constant sort-u
T{ prop params@ sort-u params@ prop input expr-a@ -> false true level-zero }T
nat-succ no-levels input expr-const ex constant c-succ
nat-add [u] input expr-const ex constant c-add-u
T{ nat-succ no-levels input expr-const c-succ params@ c-add-u params@ -> c-succ 0 false true }T
T{ c-add-u input expr-a@ c-add-u input expr-b@ c-add-u input expr-tag@ -> nat-add [u] tag-const }T
c-succ b0 input expr-app ex constant succ-b0
T{ c-succ b0 input expr-app b0 c-succ input expr-app nip -> succ-b0 0 0 }T
T{ succ-b0 range@ succ-b0 depth@ succ-b0 input expr-a@ succ-b0 input expr-b@ -> 1 1 c-succ b0 }T
\ Binders: the body's range is lowered by one; the info is in the tag.
u-name 1 lam-head prop succ-b0 input expr-make ex constant lam
u-name 3 pi-head prop b1 input expr-make ex constant pi1
T{ lam range@ lam depth@ pi1 range@ pi1 depth@ -> 0 2 1 1 }T
T{ lam input expr-tag@ pi1 input expr-tag@ lam input expr-payload@ -> tag-lam 1 + tag-pi 3 + u-name }T
\ expr-pi?: a Pi of any binder info (review s1-meta-b B4), never a lambda,
\ an application or a constant.
u-name 0 pi-head prop b1 input expr-make ex constant pi0
T{ pi0 input expr-pi? pi1 input expr-pi? lam input expr-pi? succ-b0 input expr-pi? c-succ input expr-pi?
   -> true true false false false }T
\ Telescopes: pi2 = Pi (implicit) Prop, Pi Prop, lam; a lambda's own
\ binder is no Pi, and every binder info counts.
u-name 0 pi-head prop lam input expr-make ex constant pi-lam
u-name 1 pi-head prop pi-lam input expr-make ex constant pi2
T{ pi2 input expr-pis pi-lam input expr-pis lam input expr-pis c-succ input expr-pis -> 2 1 0 0 }T
T{ pi2 input expr-pi-end pi-lam input expr-pi-end lam input expr-pi-end -> lam lam lam }T
T{ pi2 input 0 expr-pi-after pi2 input 1 expr-pi-after pi2 input 9 expr-pi-after
   -> pi2 input pi-lam input lam input }T
T{ pi2 input 0 expr-domain pi2 input 1 expr-domain pi1 input 0 expr-domain -> prop true prop true prop true }T
T{ pi2 input 2 expr-domain pi2 input 9 expr-domain lam input 0 expr-domain -> false false false }T
\ k is unsigned: a negative k is beyond every telescope.
T{ pi1 input 1 expr-domain pi1 input -1 expr-domain pi2 input -1 expr-pi-after -> false false lam input }T
T{ u-name 1 lam-head prop succ-b0 input expr-make u-name 2 lam-head prop succ-b0 input expr-make nip -> lam 0 0 }T
\ letE: a second record holds the body; the range is the body's lowered.
u-name false let-head prop b0 b1 input expr-let ex constant let1
T{ let1 input expr-body@ let1 range@ let1 depth@ let1 1+ input expr-valid? -> b1 1 1 false }T
T{ u-name false let-head prop b0 b1 input expr-let u-name true let-head prop b0 b1 input expr-let nip -> let1 0 0 }T
\ Projections and literals.
nat proj-head succ-b0 3 input expr-make ex constant proj
T{ proj range@ proj depth@ proj input expr-b@ -> 1 2 3 }T
s" 42" input tier-texts text-intern drop constant t42
t42 input expr-nat ex constant nat42
T{ t42 input expr-str ex nat42 <> t42 input expr-nat -> true nat42 0 }T
T{ nat42 input expr-a@ input tier-texts text@ s" 42" compare nat42 range@ -> 0 0 }T
\ mdata, a kind staged but marked (import/stage.fs): the wrapped
\ expression, whose data it takes one level deeper.
succ-b0 input expr-mdata ex constant md
T{ md range@ md depth@ md input expr-a@ md input expr-tag@ -> 1 2 succ-b0 tag-mdata }T
T{ succ-b0 input expr-mdata md input expr-mdata ex md depth@ 1+ swap depth@ -> md 0 3 3 }T
\ The depth is capped at 1023.
: chain ( n -- e ) b0 swap 0 ?do c-succ swap input expr-app ex loop ;
T{ 1022 chain depth@ 1023 chain depth@ 1100 chain depth@ -> 1022 1023 1023 }T
\ A bound variable's range: at Lean's bound, and one past it (full).
T{ range-max 1- input expr-bvar ex range@ range-max input expr-bvar -> range-max -1 outcome-full }T
\ The index is compared before 1+: 2^32 - 1, which a 32-bit host's u32@
\ gives as the cell -1, never wraps to a range of 0.
T{ -1 bvar-fits? u32-mask bvar-fits? range-max bvar-fits? range-max 1- bvar-fits? -> false false false true }T
T{ u32-mask input expr-bvar -> -1 outcome-full }T

\ Refusals: invalid, with nothing kept.
input tier-exprs cons-numbers constant before
T{ c-succ 99999 input expr-app let1 1+ b0 input expr-app -1 b0 input expr-app -> -1 1 -1 1 -1 1 }T
T{ tag-app 1 pack-head c-succ b0 input expr-make tag-let 0 pack-head prop b0 input expr-make -> -1 1 -1 1 }T
T{ tag-let-body 0 pack-head b0 0 input expr-make 0 0 0 input expr-make 21 0 pack-head 0 0 input expr-make -> -1 1 -1 1 -1 1 }T
T{ 99999 input expr-mdata tag-mdata 0 pack-head b0 1 input expr-make let1 1+ input expr-mdata -> -1 1 -1 1 -1 1 }T
T{ 99999 0 lam-head prop b0 input expr-make 99999 proj-head b0 0 input expr-make -> -1 1 -1 1 }T
T{ tag-app 0 pack-head prop b0 b1 input expr-let tag-bvar 0 pack-head 0 1 input expr-make -> -1 1 -1 1 }T
T{ 99 input expr-sort nat-add 2 input expr-const 99 no-levels input expr-const -> -1 1 -1 1 -1 1 }T
T{ nat-add [one,u] 1+ input expr-const 999 input expr-nat 5 input expr-fvar -> -1 1 -1 1 -1 1 }T
\ A list whose items are not levels.
99 1 list-of constant [99]
T{ nat-add [99] input expr-const -> -1 outcome-invalid }T
u32-mask 0> [if]
T{ tag-app u32-mask 1+ pack-head c-succ b0 input expr-make c-succ u32-mask 1+ b0 + input expr-app -> -1 1 -1 1 }T
[then]
T{ input tier-exprs cons-numbers -> before }T
\ Handles.
T{ b0 input expr-valid? let1 input expr-valid? let1 1+ input expr-valid? -> true true false }T
T{ before input expr-valid? -1 input expr-valid? -> false false }T
\ A constant's payload (its declaration, C4) is not part of its key.
c-succ input expr-record quad-head dup u32@ 7 5 lshift or swap u32!
T{ c-succ input expr-payload@ nat-succ no-levels input expr-const -> 7 c-succ 0 }T

\ Sealing: the input becomes read-only.
T{ input tier-seal c-succ b0 input expr-app input tier-seal -> outcome-ok -1 outcome-invalid outcome-invalid }T
T{ mk input tier-mark -> outcome-invalid }T
\ A scratch tier over it: numbers continue, the input's records are found.
other /tier erase
T{ other check tier-extend -> outcome-invalid }T
check tier-free
T{ input check tier-extend -> outcome-ok }T
T{ c-succ b0 check expr-app nat s" succ" check name-str u-name check level-param -> succ-b0 0 nat-succ 0 u 0 }T
T{ b0 c-succ check expr-app nip [u] check tier-tuples tuple-length -> 0 1 }T
input tier-exprs cons-numbers constant in-exprs
input tier-names cons-numbers constant in-names
T{ c-succ c-succ check expr-app c-succ c-succ check expr-app -> in-exprs 0 in-exprs 0 }T
T{ succ-b0 check expr-mdata -> md 0 }T
T{ nat s" zero" check name-str nat s" zero" check name-str -> in-names 0 in-names 0 }T
T{ in-names 0 lam-head prop b0 check expr-make nip in-names input name-valid? -> 0 false }T
\ A child of the scratch tier: the input's table is not probed.
: input-finds ( -- n ) check tier-exprs cons-under-finds @ ;
T{ input-finds in-exprs b0 check expr-app nip swap input-finds swap - -> 0 0 }T
T{ input-finds b0 b0 check expr-app nip swap input-finds swap - -> 0 1 }T
\ Free variables: scratch only, with their flag.
T{ 3 check expr-fvar drop 3 check expr-fvar -rot = -> 0 true }T
3 check expr-fvar drop constant fv
T{ fv check expr-data@ data-fvars? c-succ fv check expr-app drop check expr-data@ data-fvars? -> true true }T
T{ fv check expr-valid? fv input expr-valid? -> true false }T

\ Marks over all five families; a rollback checks them all first.
: numbers ( tier -- n1 .. n5 )
  >r r@ tier-names cons-numbers r@ tier-levels cons-numbers r@ tier-tuples cons-numbers
  r@ tier-texts cons-numbers r> tier-exprs cons-numbers ;
check numbers constant e0 constant x0 constant t0 constant l0 constant n0
T{ mk check tier-mark -> outcome-ok }T
: build-all ( -- )
  nat s" one" check name-str drop check level-param drop
  check tier-tuples tuple-start drop one check tier-tuples tuple-add drop check tier-tuples tuple-end 2drop
  s" 7" check tier-texts text-intern drop check expr-nat drop ;
build-all
T{ mk2 check tier-mark -> outcome-ok }T
build-all  c-succ prop check expr-app 2drop
T{ mk check tier-rollback check numbers -> outcome-ok n0 l0 t0 x0 e0 }T
T{ mk2 check tier-mark-valid? mk2 check tier-rollback mk check tier-mark-valid? -> false outcome-invalid true }T
build-all
T{ check tier-reset check tier-exprs cons-numbers check tier-names cons-numbers -> outcome-ok in-exprs in-names }T
T{ mk check tier-rollback nat s" zero" check name-str -> outcome-invalid in-names 0 }T
T{ input tier-reset -> outcome-invalid }T

\ A name looked up without adding it: its number and ok, or -1 and ok when
\ absent, or -1 and the outcome of a failed lookup.
T{ nat s" succ" check name-seek-str nat s" none" check name-seek-str -> nat-succ 0 -1 0 }T
T{ nat 7 check name-seek-num 99999 s" x" check name-seek-str nat here payload-limit check name-seek-str -> 4 0 -1 1 -1 6 }T
T{ 99999 s" x" check name-find-str nat 7 check name-find-num -> false 4 true }T

\ The sealed input is never written: lookups and builds through a scratch
\ tier leave every byte of its record and of its tables' slots as it was,
\ and are counted in the scratch tier.
lf-lib-private order+
: slots ( cons -- addr u ) cons-table dup htab-block @ swap htab-slots u32s ;
create input-copy /tier allot
create names-copy 65536 allot   create exprs-copy 65536 allot
T{ input tier-names slots nip 65536 <= input tier-exprs slots nip 65536 <= -> true true }T
input input-copy /tier move
input tier-names slots names-copy swap move  input tier-exprs slots exprs-copy swap move
: busy ( -- ) 100 0 do nat s" succ" check name-str 2drop c-succ b0 check expr-app 2drop
  b0 c-succ check expr-app 2drop nat s" absent" check name-seek-str 2drop loop ;
T{ busy input input-copy /tier tuck compare -> 0 }T
T{ input tier-names slots names-copy over compare input tier-exprs slots exprs-copy over compare -> 0 0 }T
T{ check tier-names cons-under-finds @ 0> check tier-exprs cons-under-finds @ 0> -> true true }T

\ At most two tiers: a sealed scratch tier cannot be extended (a tier3
\ tier's numbers would name records two tiers down).
create tier3 /tier allot
T{ check tier-seal check tier3 tier-extend -> outcome-ok outcome-invalid }T
tier3 tier-free check tier-free

\ A component taken from the tier's own byte slab, which grows while the
\ name is made: the text is found again, not read from the old block.
T{ input check tier-extend -> outcome-ok }T
create long-text 300 allot  long-text 300 char q fill  char x long-text 299 + c!
name-anonymous long-text 300 check name-str drop constant parent
: child ( u -- n outcome ) >r parent parent check name-text@ drop r> check name-str ;
T{ 300 child swap check name-text@ long-text 300 compare -> 0 0 }T
: children ( -- flag ) true 40 0 do 299 i - child nip ok? and loop ;
T{ children parent check name-text@ long-text 300 compare -> true 0 }T
T{ 250 child nip 250 child drop check name-text@ long-text 250 compare -> 0 0 }T
check tier-free

\ A randomized model: applications over a pool of expressions, built in
\ an input tier, then in a scratch tier over it that is reset now and
\ then; each build is compared with a list of the pairs built so far.
create pairs 3 4000 * cells allot   variable #pairs   variable #input-pairs
create pool 4000 cells allot   variable #pool   variable #input-pool
variable m-seed   variable m-bad
: m-rnd ( n -- u ) m-seed @ 1103515245 * 12345 + $7FFFFFFF and dup m-seed ! 7 rshift swap mod ;
: pair@ ( i -- f a n ) 3 * cells pairs + dup @ over cell+ @ rot 2 cells + @ ;
: pair! ( f a n -- ) #pairs @ 3 * cells pairs + tuck 2 cells + ! tuck cell+ ! ! 1 #pairs +! ;
: known ( f a -- n | -1 )
  -1 #pairs @ 0 ?do 2 pick 2 pick i pair@ >r d= if drop r> leave then r> drop loop nip nip ;
: pooled ( e -- ) #pool @ cells pool + ! 1 #pool +! ;
: pick-pool ( -- e ) #pool @ m-rnd cells pool + @ ;
\ The number app(f, a) must get: the known one, or the tier's next.
: m-expect ( f a tier -- n new? )
  >r known dup 0< if drop r> tier-exprs cons-numbers true else r> drop false then ;
\ Build app(f, a) of two random expressions of the pool in tier.
: m-build ( tier -- )
  pick-pool pick-pool rot >r 2dup r@ m-expect >r >r 2dup r> r> 2swap
  r> expr-app ok? 0= if 1 m-bad +! then rot over <> if 1 m-bad +! then
  swap if dup pooled pair! else drop 2drop then ;
: m-leaves ( tier -- ) 8 0 do i over expr-bvar drop pooled loop drop ;
: m-scratch-reset ( -- )
  check tier-reset drop #input-pairs @ #pairs ! #input-pool @ #pool ! ;
: m-run ( seed -- bad )
  m-seed ! 0 m-bad ! 0 #pairs ! 0 #pool ! 8 other tier-init drop other m-leaves
  300 0 do other m-build loop other tier-seal drop
  #pairs @ #input-pairs ! #pool @ #input-pool ! other check tier-extend drop
  3000 0 do check m-build 500 m-rnd 0= if m-scratch-reset then loop
  check tier-free other tier-free m-bad @ ;
T{ 1 m-run 2 m-run 3 m-run -> 0 0 0 }T
input tier-free
bye
