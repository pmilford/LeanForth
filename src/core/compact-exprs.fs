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
\ The binder tags are base + binder information (0 default, 1 implicit,
\ 2 strict implicit, 3 instance implicit). * A constant's payload is
\ reserved for the declaration it names, resolved when the input is
\ sealed (C4); it is not part of the key, so hashing and comparing a
\ constant ignore it. A free variable may only be built in a scratch tier.
\
\ The data field is computed from the children when the record is built,
\ as Lean's Expr.mkData does (ADR 0016 facts L2, L3): a bound variable i
\ has range i + 1; a binder the larger of its type's range and its body's
\ range minus one (never below zero); a letE the largest of its type's,
\ value's and body's minus one; an application or projection the largest
\ of its children's; the flags are or-ed, a Sort's and a constant's
\ parameter flag come from their levels; the depth is 0 for leaves and one
\ more than the deepest child, capped at 1023. Every record is checked
\ when it is built (C8): children are expressions of the tier (never the
\ body record of a letE), names, levels, lists and texts are the tier's, a
\ constant's list holds only levels, unused fields are 0, and a bound
\ variable's range is at most 2^20 - 1 (Lean's own limit; full beyond).
\
\ Interface: the tags (tag-bvar ... tag-fvar), let-tag? binder-tag?
\ lam-head pi-head let-head proj-head expr-class expr-make expr-let
\ expr-bvar expr-sort expr-const expr-app expr-nat expr-str expr-fvar
\ expr-valid? expr-head@ expr-tag@ expr-payload@ expr-a@ expr-b@ expr-data@
\ expr-body@ data-range data-depth data-params? data-fvars? range-max
\ depth-max. Outcomes: ok, full, invalid. State: expr-class and the check
\ table, made while loading, read-only afterwards.

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
\ a, b and a letE's body.
: key-head ( head -- head' ) dup head-tag tag-const = if head-tag then ;
: record-let? ( addr -- flag ) quad-head u32@ head-tag let-tag? ;
: record-body? ( addr -- flag ) quad-head u32@ head-tag tag-let-body = ;
: body-of ( addr -- body ) /quad + quad-a u32@ ;
: expr-hash ( addr -- h )
  dup quad-head u32@ key-head hash-fmix over quad-a u32@ hash-step over quad-b u32@ hash-step
  swap dup record-let? if body-of hash-step else drop then ;
: expr-key= ( addr1 addr2 -- flag )
  over quad-head u32@ key-head over quad-head u32@ key-head = 0= if 2drop false exit then
  2dup quad-ab= 0= if 2drop false exit then
  dup record-let? if body-of swap body-of = else 2drop true then ;
: expr-rehash ( n cons -- h ) cons-at expr-hash ;
: expr-same ( n key cons -- flag ) rot swap cons-at swap cons-top expr-key= ;
: expr-span ( local cons -- units ) cons-records slab-at record-let? if 2 else 1 then ;
' expr-rehash ' expr-same ' expr-span expr-class cons-hooks!

\ Checks of the candidate ( exprs -- under? outcome ), one per tag, where
\ exprs is the tier's expression set: each writes the data field and says
\ whether the candidate may be an input record (every part it refers to
\ is one). The other sets are found from the tier around exprs.
: exprs>tier ( exprs -- tier ) 0 tier-exprs - ;
: exprs>names ( exprs -- names ) exprs>tier tier-names ;
: exprs>levels ( exprs -- levels ) exprs>tier tier-levels ;
: exprs>tuples ( exprs -- tuples ) exprs>tier tier-tuples ;
: exprs>texts ( exprs -- texts ) exprs>tier tier-texts ;
: cand-body ( exprs -- e ) cons-top body-of ;
: payload-zero? ( exprs -- flag ) cand-head head-payload 0= ;
: bare-b? ( exprs -- flag ) dup payload-zero? swap cand-b 0= and ;
: payload-name ( exprs -- name names ) dup cand-head head-payload swap exprs>names ;
: payload-name? ( exprs -- flag ) payload-name cons-in? ;
: payload-under? ( exprs -- flag ) payload-name cons-under? ;
: a-under? ( exprs -- flag ) dup cand-a swap cons-under? ;
: b-under? ( exprs -- flag ) dup cand-b swap cons-under? ;
: ab-under? ( exprs -- flag ) dup a-under? swap b-under? and ;
\ A child: an expression of the set, not a letE's body record; its data.
: expr-child ( e exprs -- d valid? )
  2dup cons-in? 0= if 2drop 0 false exit then
  cons-at dup record-body? if drop 0 false else quad-data u32@ true then ;
: data-into ( d exprs -- ) dup cand-data rot data-merge swap cand-data! ;
: child-into ( e exprs -- valid? ) tuck expr-child >r swap data-into r> ;
: lowered-into ( e exprs -- valid? ) tuck expr-child >r data-lower swap data-into r> ;
: a-into ( exprs -- valid? ) dup cand-a swap child-into ;
: b-into ( exprs -- valid? ) dup cand-b swap child-into ;
: deeper! ( exprs -- ) dup cand-data data-deeper swap cand-data! ;
: valid>outcome ( under? valid? -- under? outcome ) flag>outcome ;

: expr-bad ( exprs -- under? outcome ) drop false outcome-invalid ;
: check-app ( exprs -- under? outcome )
  dup payload-zero? >r dup a-into r> and >r dup b-into r> and >r
  dup deeper! ab-under? r> valid>outcome ;
: check-binder ( exprs -- under? outcome )
  dup payload-name? >r dup a-into r> and >r dup dup cand-b swap lowered-into r> and >r
  dup deeper! dup ab-under? swap payload-under? and r> valid>outcome ;
: check-let ( exprs -- under? outcome )
  dup cand-head head-tag let-tag? >r dup payload-name? r> and >r dup a-into r> and >r
  dup b-into r> and >r dup dup cand-body swap lowered-into r> and >r dup deeper!
  dup ab-under? over dup cand-body swap cons-under? and swap payload-under? and r> valid>outcome ;
: check-proj ( exprs -- under? outcome )
  dup payload-name? >r dup a-into r> and >r dup deeper!
  dup a-under? swap payload-under? and r> valid>outcome ;
\ A bound variable's range beyond 2^20 - 1 is full (Lean's limit, L2).
: check-bvar ( exprs -- under? outcome )
  dup bare-b? 0= if drop false outcome-invalid exit then
  dup cand-a 1+ dup range-max u> if 2drop false outcome-full exit then
  swap cand-data! true outcome-ok ;
\ A level operand: its data (the parameter bit).
: cand-level ( exprs -- d valid? )
  dup cand-a swap exprs>levels 2dup cons-in? if cons-at quad-data u32@ true else 2drop 0 false then ;
: check-sort ( exprs -- under? outcome )
  dup cand-level >r over cand-data! dup bare-b? r> and
  over cand-a rot exprs>levels cons-under? swap valid>outcome ;
\ A constant's list: a list of the tier whose items are levels, their
\ parameter bits or-ed into the data field.
: item-into ( l exprs -- valid? )
  tuck exprs>levels 2dup cons-in? if cons-at quad-data u32@ swap data-into true
  else 2drop drop false then ;
: items-into ( addr n exprs -- valid? )
  swap 0 ?do over i u32s + u32@ over item-into 0= if 2drop false unloop exit then loop 2drop true ;
: tuple-into ( exprs -- valid? )
  dup cand-b over exprs>tuples 2dup cons-entry? 0= if 2drop drop false exit then
  cons-at dup u32@ swap 1 u32s + swap rot items-into ;
: check-const ( exprs -- under? outcome )
  dup payload-zero? >r dup cand-a over exprs>names cons-in? r> and >r dup tuple-into r> and >r
  dup cand-a over exprs>names cons-under? over cand-b rot exprs>tuples cons-under? and
  r> valid>outcome ;
: check-literal ( exprs -- under? outcome )
  dup bare-b? >r dup cand-a over exprs>texts cons-in? r> and >r
  dup cand-a swap exprs>texts cons-under? r> valid>outcome ;
: check-fvar ( exprs -- under? outcome )
  data-fvars-bit over cand-data! dup bare-b? swap cons-under @ 0<> and false swap valid>outcome ;

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
: binder-checks ( -- ) 8 0 do ['] check-binder tag-lam i + expr-checks check! loop ;
binder-checks

\ Find or keep the checked candidate of units records.
: expr-keep ( units under? exprs -- e )
  dup >r cons-top expr-hash swap r@ cons-find if nip r> drop else r> cons-commit then ;
: expr-finish ( units exprs -- e outcome )
  dup dup cand-head head-tag expr-checks check-run
  dup ok? if drop swap expr-keep outcome-ok else fail3 then ;
\ The expression with head and operands a and b, for every kind but
\ letE: its number (an equal expression's, which may be the input
\ tier's) and ok; -1 and invalid for a bad tag, part or unused field, a
\ field beyond 32 bits or a sealed tier; -1 and full when there is no
\ room or for a bound variable beyond Lean's limit.
: expr-make ( head a b tier -- e outcome )
  tier-exprs >r fields-fit? 0= if outcome-invalid fail3 r> drop exit then
  1 0 r@ cons-room dup ok? 0= if fail3 r> drop exit then drop
  r@ cand! 1 r> expr-finish ;
\ The letE with head (let-head), type, value and body: as expr-make.
: let-body! ( body exprs -- )
  cons-top /quad + >r tag-let-body r@ quad-head u32! r@ quad-a u32!
  0 r@ quad-b u32! 0 r> quad-data u32! ;
: expr-let ( head type value body tier -- e outcome )
  tier-exprs >r dup u32-mask u> if drop outcome-invalid fail3 r> drop exit then
  2 0 r@ cons-room dup ok? 0= if nip fail3 r> drop exit then drop
  r@ let-body! fields-fit? 0= if outcome-invalid fail3 r> drop exit then
  r@ cand! r@ check-let dup ok? if drop 2 swap r> expr-keep outcome-ok
  else nip r> drop no-result then ;

: expr-app ( f a tier -- e outcome ) >r tag-app -rot r> expr-make ;
: expr-bvar ( i tier -- e outcome ) >r tag-bvar swap 0 r> expr-make ;
: expr-sort ( level tier -- e outcome ) >r tag-sort swap 0 r> expr-make ;
: expr-const ( name list tier -- e outcome ) >r tag-const -rot r> expr-make ;
: expr-nat ( text tier -- e outcome ) >r tag-nat swap 0 r> expr-make ;
: expr-str ( text tier -- e outcome ) >r tag-str swap 0 r> expr-make ;
: expr-fvar ( n tier -- e outcome ) >r tag-fvar swap 0 r> expr-make ;
