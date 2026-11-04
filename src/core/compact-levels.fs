\ Lean universe levels in the compact store (ADR 0016 C1): zero, successor,
\ max, imax and parameters, interned, so that equal levels are one number
\ in a tier and across an input tier and a scratch tier over it.
\ Untrusted; not yet used by the kernel.
\
\ A level record is a /quad: the head holds the tag and, for a parameter,
\ its name as the payload; quad-a and quad-b the children (succ uses
\ quad-a; both 0 where unused); quad-data the "has universe parameters"
\ bit, computed from the children when the level is built, never taken
\ from the input. Number 0 of an input tier is zero (compact.fs makes it
\ first). Every record is checked when it is built (ADR 0016 C8): children
\ are levels of the tier, a parameter's name is a name of the tier, unused
\ fields are 0.
\
\ Interface: tag-level-zero tag-level-succ tag-level-max tag-level-imax
\ tag-level-param level-zero level-class level-build level-succ level-max
\ level-imax level-param level-valid? level-tag@ level-a@ level-b@
\ level-name@ level-params?. Outcomes: ok, full, invalid. State:
\ level-class and the check table, made while loading, read-only after.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/portability.fs
require ../lib/outcome.fs
require ../lib/u32.fs
require ../lib/hash32.fs
require ../lib/cons.fs
require ./compact-tier.fs
require ./compact-names.fs

0 constant tag-level-zero
1 constant tag-level-succ
2 constant tag-level-max
3 constant tag-level-imax
4 constant tag-level-param
0 constant level-zero

/quad cons-numbers-max cons-class: level-class

: level-record ( l tier -- addr ) tier-levels cons-at ;
\ Unchecked accessors: give them valid levels.
: level-tag@ ( l tier -- tag ) level-record quad-head u32@ head-tag ;
: level-a@ ( l tier -- l' ) level-record quad-a u32@ ;
: level-b@ ( l tier -- l' ) level-record quad-b u32@ ;
: level-name@ ( l tier -- name ) level-record quad-head u32@ head-payload ;
: level-data@ ( l tier -- d ) level-record quad-data u32@ ;
: level-params? ( l tier -- flag ) level-data@ data-params-bit and 0<> ;
\ Whether l is a level of the tier (or of the input tier under it).
: level-valid? ( l tier -- flag ) tier-levels cons-in? ;

\ The class's hooks: equal when head and children are; the data field
\ follows from them.
: quad-hash ( addr -- h )
  dup quad-head u32@ hash-fmix over quad-a u32@ hash-step swap quad-b u32@ hash-step ;
: quad-key= ( addr1 addr2 -- flag )
  over quad-head u32@ over quad-head u32@ = >r quad-ab= r> and ;
: level-rehash ( n cons -- h ) cons-at quad-hash ;
: level-same ( n key cons -- flag ) rot swap cons-at swap cons-top quad-key= ;
: level-span ( local cons -- units ) 2drop 1 ;
' level-rehash ' level-same ' level-span level-class cons-hooks!

\ Checks of the candidate, one per tag ( levels -- under? valid? ), where
\ levels is the tier's level set: each writes the data field and says
\ whether the candidate may be an input record (every part it refers to
\ is one).
: level-in? ( l levels -- flag ) cons-in? ;
: cand-payload ( cons -- u ) cand-head head-payload ;
: cand-a-level ( levels -- d valid? )
  dup cand-a over level-in? if dup cand-a swap cons-at quad-data u32@ true else drop 0 false then ;
: cand-b-level ( levels -- d valid? )
  dup cand-b over level-in? if dup cand-b swap cons-at quad-data u32@ true else drop 0 false then ;
: cand-a-under? ( cons -- flag ) dup cand-a swap cons-under? ;
: cand-b-under? ( cons -- flag ) dup cand-b swap cons-under? ;
: cand-bare? ( cons -- flag ) dup cand-payload 0= over cand-a 0= and swap cand-b 0= and ;
: check-zero ( levels -- under? valid? ) cand-bare? true swap ;
: check-succ ( levels -- under? valid? )
  dup cand-payload 0= over cand-b 0= and >r dup cand-a-level r> and
  >r over cand-data! cand-a-under? r> ;
: check-two ( levels -- under? valid? )
  dup cand-payload 0= >r dup cand-a-level r> and >r over cand-b-level r> and
  >r or over cand-data! dup cand-a-under? swap cand-b-under? and r> ;
\ A parameter: the payload is a name of the tier holding this level set,
\ which sits tier-levels after the tier's start.
: levels>tier ( levels -- tier ) 0 tier-levels - ;
: check-param ( levels -- under? valid? )
  data-params-bit over cand-data! dup cand-payload over levels>tier tier-names
  2dup cons-in? >r cons-under? swap dup cand-a 0= swap cand-b 0= and r> and ;
: level-bad ( levels -- under? valid? ) drop false false ;

\ The check of each tag; a tag without one is invalid.
check-table level-checks
' level-bad level-checks check-fill
' check-zero tag-level-zero level-checks check!
' check-succ tag-level-succ level-checks check!
' check-two tag-level-max level-checks check!
' check-two tag-level-imax level-checks check!
' check-param tag-level-param level-checks check!

\ Find or keep the checked candidate.
: level-keep ( under? levels -- l outcome )
  dup >r cons-top quad-hash swap r@ cons-find
  if r> drop outcome-ok else 1 swap r> cons-commit then ;
: check-level ( levels -- under? valid? ) dup cand-head head-tag level-checks check-run ;
\ The level with head and children a and b: its number (an equal level's,
\ which may be the input tier's) and ok; -1 and invalid when a part is not
\ a level or name of the tier, a field that should be 0 is not or does
\ not fit 32 bits, or the tier is sealed; -1 and full when there is no
\ room.
: level-build ( head a b tier -- l outcome )
  tier-levels >r fields-fit? 0= if outcome-invalid fail3 r> drop exit then
  1 0 r@ cons-room dup ok? 0= if fail3 r> drop exit then drop
  r@ cand! r@ check-level if r> level-keep else drop r> drop outcome-invalid no-result then ;
: level-succ ( l tier -- l' outcome ) >r tag-level-succ swap 0 r> level-build ;
: level-max ( l1 l2 tier -- l outcome ) >r tag-level-max -rot r> level-build ;
: level-imax ( l1 l2 tier -- l outcome ) >r tag-level-imax -rot r> level-build ;
: level-param ( name tier -- l outcome ) >r tag-level-param swap pack-head 0 0 r> level-build ;

base !   \ the BASE this file was loaded with
