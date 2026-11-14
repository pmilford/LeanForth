\ Lean expressions in the compact store (ADR 0016 C1): 16-byte records,
\ hash-consed, so that equal terms are one number in a tier and across an
\ input tier and a scratch tier over it. Untrusted; not yet used by the
\ kernel (ADR 0016 C9 step 3).
\
\ The record (/quad):
\   quad-head  bits 0-4 the tag, bits 5-31 the payload
\   quad-a     first operand: a child expression, or a level, name, list,
\              text, index or variable number
\   quad-b     second operand
\   quad-data  bits 0-19 loose bound-variable range, bit 20 has universe
\              parameters, bit 21 has free variables, bits 22-31 depth
\              (Lean's Expr.Data without its hash and metavariable flags)
\
\   kind              tag     payload             a           b
\   bound variable    1       0                   index       0
\   Sort              2       0                   level       0
\   constant          3       0 when built *      name        list of levels
\   application       4       0                   function    argument
\   lambda            5-8     binder name         type        body
\   Pi (forallE)      9-12    binder name         domain      body
\   letE              13, 14  name                type        value
\     (14: nonDep; a second record, tag 18, holds the body in quad-a)
\   projection        15      structure name      structure   field index
\   natVal, strVal    16, 17  0                   text        0
\   free variable     19      0                   number      0
\   mdata             20      0                   expression  0
\ The binder tags are base + binder information (0 default, 1 implicit,
\ 2 strict implicit, 3 instance implicit). * A constant's payload is
\ reserved for the declaration it names, resolved when the input is
\ sealed (C4); it is not part of the key, so hashing and comparing a
\ constant ignore it. A free variable may only be built in a scratch tier.
\ An mdata record is a kind not yet supported, staged but marked
\ (src/import/stage.fs): it keeps the expression the metadata wraps, not
\ the key-value data, so it is not the term read and no check may accept
\ a term that holds one (Lean's exporter writes none unless asked to).
\
\ The data field is computed from the children when the record is built,
\ as Lean's Expr.mkData does (ADR 0016 facts L2, L3): a bound variable i
\ has range i + 1; a binder the larger of its type's range and its body's
\ range minus one (never below zero); a letE the largest of its type's,
\ value's and body's minus one; an application, projection or mdata the
\ largest of its children's; the flags are or-ed, a Sort's and a constant's
\ parameter flag come from their levels; the depth is 0 for leaves and one
\ more than the deepest child, capped at 1023. Every record is checked
\ when it is built (C8): children are expressions of the tier (never the
\ body record of a letE), names, levels, lists and texts are the tier's, a
\ constant's list holds only levels, unused fields are 0, and a bound
\ variable's range is at most 2^20 - 1 (Lean's own limit; full beyond).
\
\ Interface: the tags (tag-bvar ... tag-mdata), let-tag? binder-tag?
\ lam-head pi-head let-head proj-head expr-class expr-make expr-let
\ expr-bvar expr-sort expr-const expr-app expr-nat expr-str expr-fvar
\ expr-mdata expr-next expr-resolve!
\ expr-valid? expr-head@ expr-tag@ expr-pi? expr-payload@ expr-a@ expr-b@ expr-data@
\ expr-body@ data-range data-depth data-params? data-fvars? range-max
\ depth-max bvar-fits?. Outcomes: ok, full, invalid. State: expr-class and the check
\ table, made while loading, read-only afterwards.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/portability.fs
require ../lib/outcome.fs
require ../lib/u32.fs
require ../lib/hash32.fs
require ../lib/cons.fs
require ../lib/pools.fs
require ./compact-tier.fs
require ./compact-names.fs
require ./compact-levels.fs

1 constant tag-bvar
2 constant tag-sort
3 constant tag-const
4 constant tag-app
5 constant tag-lam
9 constant tag-pi
13 constant tag-let
14 constant tag-let-nondep
15 constant tag-proj
16 constant tag-nat
17 constant tag-str
18 constant tag-let-body
19 constant tag-fvar
20 constant tag-mdata
: binder-tag? ( tag -- flag ) tag-lam tag-let within ;
: let-tag? ( tag -- flag ) tag-let tag-proj within ;
\ Heads of binders (info 0 .. 3, unchecked), letE and projections; the
\ name must be below 2^27, or the head does not fit and is refused.
: lam-head ( name info -- head ) tag-lam + swap pack-head ;
: pi-head ( name info -- head ) tag-pi + swap pack-head ;
: let-head ( name nondep? -- head ) if tag-let-nondep else tag-let then swap pack-head ;
: proj-head ( name -- head ) tag-proj swap pack-head ;

\ The data field.
1 20 lshift 1- constant range-max
1 21 lshift constant data-fvars-bit
22 constant depth-shift
1023 constant depth-max
1 depth-shift lshift 1- constant data-low-mask
: data-range ( d -- n ) range-max and ;
: data-depth ( d -- n ) depth-shift rshift ;
: data-params? ( d -- flag ) data-params-bit and 0<> ;
: data-fvars? ( d -- flag ) data-fvars-bit and 0<> ;
: data-flags ( d -- bits ) data-params-bit data-fvars-bit or and ;
: >data ( range flags depth -- d ) depth-max min depth-shift lshift or or ;
\ The larger range, both flags and the larger depth.
: data-merge ( d1 d2 -- d )
  2dup or data-flags >r over data-range over data-range max >r
  data-depth swap data-depth max r> r> rot >data ;
: data-deeper ( d -- d' )
  dup data-depth 1+ depth-max min depth-shift lshift swap data-low-mask and or ;
\ The range of a binder's body seen from outside the binder.
: data-lower ( d -- d' ) dup data-range dup if 1- then swap range-max invert and or ;

\ Records and unchecked accessors.
/quad cons-numbers-max cons-class: expr-class
: expr-record ( e tier -- addr ) tier-exprs cons-at ;
: expr-head@ ( e tier -- head ) expr-record quad-head u32@ ;
: expr-tag@ ( e tier -- tag ) expr-head@ head-tag ;
\ Whether e is a Pi of any binder info (tags tag-pi to tag-let - 1); the
\ front end's and the command line's telescopes walk these.
: expr-pi? ( e tier -- flag ) expr-tag@ tag-pi tag-let within ;
: expr-payload@ ( e tier -- u ) expr-head@ head-payload ;
: expr-a@ ( e tier -- u ) expr-record quad-a u32@ ;
: expr-b@ ( e tier -- u ) expr-record quad-b u32@ ;
: expr-data@ ( e tier -- d ) expr-record quad-data u32@ ;
\ A letE's body, from its second record.
: expr-body@ ( e tier -- body ) expr-record /quad + quad-a u32@ ;
\ Whether e is an expression of the tier (or of the input under it).
: expr-valid? ( e tier -- flag )
  2dup tier-exprs cons-in? if expr-tag@ tag-let-body <> else 2drop false then ;

\ The class's hooks. The key is the head (a constant's without payload),
\ a, b and a letE's body; a and b are compared first, since they tell
\ most records apart.
: key-head ( head -- head' ) dup head-tag tag-const = if head-tag then ;
: record-let? ( addr -- flag ) quad-head u32@ head-tag let-tag? ;
: record-body? ( addr -- flag ) quad-head u32@ head-tag tag-let-body = ;
: body-of ( addr -- body ) /quad + quad-a u32@ ;
: expr-hash ( addr -- h )
  dup quad-head u32@ key-head hash-fmix over quad-a u32@ hash-step over quad-b u32@
  hash-step
  swap dup record-let? if body-of hash-step else drop then ;
: heads= ( addr1 addr2 -- flag )
  quad-head u32@ swap quad-head u32@ 2dup = if 2drop true else key-head swap key-head =
  then ;
: expr-key= ( addr1 addr2 -- flag )
  2dup quad-ab= 0= if 2drop false exit then 2dup heads= 0= if 2drop false exit then
  dup record-let? if body-of swap body-of = else 2drop true then ;
: expr-rehash ( n cons -- h ) cons-at expr-hash ;
: expr-same ( n key cons -- flag ) rot swap cons-at swap cons-top expr-key= ;
: expr-span ( local cons -- units ) cons-records slab-at record-let? if 2 else 1 then ;
' expr-rehash ' expr-same ' expr-span expr-class cons-hooks!

\ Checks of the candidate ( top exprs -- under? outcome ), one per tag:
\ top is the candidate's address and exprs the tier's expression set.
\ Each validates the candidate, writes its data field and says whether it
\ may be an input record (every part it refers to is one). The other
\ sets are found from the tier around exprs.
: exprs>tier ( exprs -- tier ) 0 tier-exprs - ;
: exprs>names ( exprs -- names ) exprs>tier tier-names ;
: exprs>levels ( exprs -- levels ) exprs>tier tier-levels ;
: exprs>tuples ( exprs -- tuples ) exprs>tier tier-tuples ;
: exprs>texts ( exprs -- texts ) exprs>tier tier-texts ;
\ Payload 0 and b 0: a kind that uses neither.
: bare? ( top -- flag ) dup quad-head u32@ head-payload 0= swap quad-b u32@ 0= and ;
: payload-zero? ( top -- flag ) quad-head u32@ head-payload 0= ;
: data! ( top exprs d -- top exprs ) rot tuck quad-data u32! swap ;
\ A child: an expression of the set, not a letE's body record; its data.
: expr-child ( e exprs -- d valid? )
  2dup cons-in? 0= if 2drop 0 false exit then
  cons-at dup record-body? if drop 0 false else quad-data u32@ true then ;
: child-a ( top exprs -- d valid? ) swap quad-a u32@ swap expr-child ;
: child-b ( top exprs -- d valid? ) swap quad-b u32@ swap expr-child ;
: child-body ( top exprs -- d valid? ) swap body-of swap expr-child ;
: merged ( d1 valid1? d2 valid2? -- d valid? ) rot and >r data-merge r> ;
\ An application's children; a binder's type and body seen from outside.
: child-pair ( top exprs -- d valid? ) 2dup child-a 2swap child-b merged ;
: binder-pair ( top exprs -- d valid? ) 2dup child-a 2swap child-b >r data-lower r>
  merged ;
: pair-under? ( top exprs -- flag )
  cons-first @ >r dup quad-a u32@ r@ u< swap quad-b u32@ r> u< and ;
\ The payload as a name of the tier: whether it is one, and an input one.
: payload-name ( top exprs -- name names )
  swap quad-head u32@ head-payload swap exprs>names ;
: name-checks ( top exprs -- valid? under? ) payload-name 2dup cons-in? -rot cons-under? ;

: expr-bad ( top exprs -- under? outcome ) 2drop false outcome-invalid ;
: check-app ( top exprs -- under? outcome )
  2dup child-pair >r data-deeper data! over payload-zero? r> and >r pair-under? r>
  flag>outcome ;
: check-binder ( top exprs -- under? outcome )
  2dup binder-pair >r data-deeper data! 2dup name-checks r> rot and >r >r
  pair-under? r> and r> flag>outcome ;
\ A letE's data: its type's, value's and lowered body's, one level
\ deeper; valid when all three are expressions of the set and the tag is
\ a letE's. Its parts are input records when type, value and body are.
: let-data ( top exprs -- top exprs valid? )
  2dup child-pair 2over child-body >r data-lower r> merged >r data-deeper data!
  over quad-head u32@ head-tag let-tag? r> and ;
: body-under? ( top exprs -- flag ) swap body-of swap cons-under? ;
: let-under? ( top exprs -- flag ) 2dup body-under? >r pair-under? r> and ;
: check-let ( top exprs -- under? outcome )
  let-data >r 2dup name-checks r> rot and >r >r let-under? r> and r> flag>outcome ;
: check-proj ( top exprs -- under? outcome )
  2dup child-a >r data-deeper data! 2dup name-checks r> rot and >r >r
  swap quad-a u32@ swap cons-under? r> and r> flag>outcome ;
\ A bound variable's index must be below 2^20 - 1, so that its range,
\ index + 1, is at most Lean's limit (L2); beyond it, full. The index is
\ compared before 1+, which would wrap at 2^32 - 1 on a 32-bit host.
: bvar-fits? ( index -- flag ) range-max u< ;
: check-bvar ( top exprs -- under? outcome )
  drop dup bare? 0= if drop false outcome-invalid exit then
  dup quad-a u32@ dup bvar-fits? 0= if 2drop false outcome-full exit then
  1+ swap quad-data u32! true outcome-ok ;
: check-sort ( top exprs -- under? outcome )
  exprs>levels >r dup quad-a u32@ r@ level-data >r over quad-data u32! dup bare? r> and
  swap quad-a u32@ r> cons-under? swap flag>outcome ;
\ A constant's list: a list of the tier whose n items at addr are levels,
\ their parameter bits or-ed.
: item-data ( addr levels -- d valid? ) swap u32@ swap level-data ;
: items-data ( addr n levels -- d valid? )
  0 swap 2swap u32s over + swap ?do
    i over item-data 0= if 2drop drop 0 false unloop exit then rot or swap
  1 u32s +loop drop true ;
: tuple-data ( t exprs -- d valid? )
  exprs>tier >r dup r@ tier-tuples cons-entry? 0= if r> 2drop 0 false exit then
  r@ tier-tuples cons-at dup u32@ swap 1 u32s + swap r> tier-levels items-data ;
: check-const ( top exprs -- under? outcome )
  over quad-b u32@ over tuple-data >r data! over payload-zero? r> and >r
  over quad-a u32@ over exprs>names 2dup cons-in? r> and >r cons-under? >r
  swap quad-b u32@ swap exprs>tuples cons-under? r> and r> flag>outcome ;
: check-literal ( top exprs -- under? outcome )
  exprs>texts >r dup bare? over quad-a u32@ r@ cons-in? and
  swap quad-a u32@ r> cons-under? swap flag>outcome ;
\ A free variable: only in a scratch tier, never an input record.
: check-fvar ( top exprs -- under? outcome )
  cons-under @ 0<> over bare? and data-fvars-bit rot quad-data u32! false swap
  flag>outcome ;
\ An mdata record: one child, whose data it takes one level deeper.
: check-mdata ( top exprs -- under? outcome )
  2dup child-a >r data-deeper data! over bare? r> and >r
  swap quad-a u32@ swap cons-under? r> flag>outcome ;

check-table expr-checks
' expr-bad expr-checks check-fill
' check-bvar tag-bvar expr-checks check!
' check-sort tag-sort expr-checks check!
' check-const tag-const expr-checks check!
' check-app tag-app expr-checks check!
' check-proj tag-proj expr-checks check!
' check-literal tag-nat expr-checks check!
' check-literal tag-str expr-checks check!
' check-fvar tag-fvar expr-checks check!
' check-mdata tag-mdata expr-checks check!
: binder-checks ( -- ) 8 0 do ['] check-binder tag-lam i + expr-checks check! loop ;
binder-checks

\ Find or keep the checked candidate of units records.
: expr-check ( top exprs -- under? outcome )
  over quad-head u32@ head-tag expr-checks check-run ;
: expr-keep ( units under? exprs -- e outcome )
  dup >r cons-top expr-hash swap r@ cons-find
  if nip r> drop outcome-ok else r> cons-commit then ;
: expr-finish ( units exprs -- e outcome )
  dup cons-top over expr-check dup ok? if drop swap expr-keep else fail3 then ;
\ The expression with head and operands a and b, for every kind but
\ letE: its number (an equal expression's, which may be the input
\ tier's) and ok; -1 and invalid for a bad tag, part or unused field, a
\ field beyond 32 bits or a sealed tier; -1 and full when there is no
\ room or for a bound variable beyond Lean's limit.
: expr-make ( head a b tier -- e outcome )
  tier-exprs >r 1 r@ quad-room dup ok? 0= if fail3 r> drop exit then drop
  r@ cand! 1 r> expr-finish ;
\ The letE with head (let-head), type, value and body: as expr-make.
: let-body! ( body exprs -- )
  cons-top /quad + >r tag-let-body r@ quad-head u32! r@ quad-a u32!
  0 r@ quad-b u32! 0 r> quad-data u32! ;
: expr-let ( head type value body tier -- e outcome )
  tier-exprs >r dup u32-mask u> if drop outcome-invalid fail3 r> drop exit then
  >r 2 2r@ drop quad-room dup ok? 0= if fail3 2r> 2drop exit then drop
  r> r@ let-body! r@ cand! r@ cons-top r@ check-let
  dup ok? if drop 2 swap r> expr-keep else nip r> drop no-result then ;


: expr-app ( f a tier -- e outcome ) >r tag-app -rot r> expr-make ;
: expr-bvar ( i tier -- e outcome ) >r tag-bvar swap 0 r> expr-make ;
: expr-sort ( level tier -- e outcome ) >r tag-sort swap 0 r> expr-make ;
: expr-const ( name list tier -- e outcome ) >r tag-const -rot r> expr-make ;
: expr-nat ( text tier -- e outcome ) >r tag-nat swap 0 r> expr-make ;
: expr-str ( text tier -- e outcome ) >r tag-str swap 0 r> expr-make ;
: expr-fvar ( n tier -- e outcome ) >r tag-fvar swap 0 r> expr-make ;
: expr-mdata ( e tier -- e' outcome ) >r tag-mdata swap 0 r> expr-make ;

\ Walking a tier's own expressions by number: the number after e (a letE
\ spans two). Unchecked, like the accessors.
: expr-next ( e tier -- e' ) over swap expr-record record-let? if 2 else 1 then + ;
\ Resolving a constant (C4), while its tier is still open: u, below
\ payload-limit, becomes constant e's payload, its declaration's number
\ + 1 (0: none, or several). The payload is not part of the key, so the
\ tables stay as they are. Unchecked: e is a constant of an open tier.
: expr-resolve! ( u e tier -- )
  expr-record >r tag-const swap pack-head r> quad-head u32! ;

base !   \ the BASE this file was loaded with
