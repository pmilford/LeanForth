\ Lean names in the compact store (ADR 0016 C2): hierarchical names whose
\ components are strings or natural numbers, interned, so that equal names
\ are one number in a tier and across an input tier and a scratch tier
\ over it. Untrusted; not yet used by the kernel.
\
\ A name record is a /quad: the head holds the tag (anonymous, string or
\ number) and, for a string, its length in bytes as the payload; quad-a
\ the prefix name; quad-b the offset of the string in the tier's byte slab,
\ or the number; quad-data a stored 32-bit hash of tag, prefix and
\ component (recomputing it would read the bytes). Number 0 of an input
\ tier is the anonymous name (compact.fs makes it first).
\
\ Limits, each full when reached: 2^27 names in the input and a scratch
\ tier together (a name is the payload of a binder head, C1), string
\ components under 2^27 bytes, numeric components up to 2^32-1 (Mathlib's
\ largest fits; a larger one is reported full, not cut). Outcomes: ok,
\ full, invalid for a prefix that is not a name or a sealed tier.
\ name-seek-str and name-seek-num look a name up without adding it (-1
\ when it is absent; name-find-str and name-find-num are the older forms,
\ which cannot tell an absent name from a failed lookup); like every word
\ that builds, they need an open tier, so look names up in a sealed input
\ tier through a scratch tier over it. A component's text may lie
\ anywhere, even in the tier's own byte slab, which moves when it grows:
\ it is kept as an offset meanwhile (cons-key!, lib/cons.fs).
\
\ Interface: tag-name-anon tag-name-str tag-name-num name-anonymous
\ name-class name-str name-num name-seek-str name-seek-num name-find-str
\ name-find-num name-valid?
\ name-tag@ name-prefix@ name-number@ name-text@ name-hash@ name-anon-make
\ name-own? name-up name-depth name-copy.
\ State: name-class, made while loading and read-only afterwards.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/portability.fs
require ../lib/outcome.fs
require ../lib/u32.fs
require ../lib/hash32.fs
require ../lib/cons.fs
require ./compact-tier.fs

0 constant tag-name-anon
1 constant tag-name-str
2 constant tag-name-num
0 constant name-anonymous

/quad payload-limit cons-class: name-class

: name-record ( n tier -- addr ) tier-names cons-at ;
\ Unchecked accessors: give them valid names.
: name-tag@ ( n tier -- tag ) name-record quad-head u32@ head-tag ;
: name-prefix@ ( n tier -- prefix ) name-record quad-a u32@ ;
: name-number@ ( n tier -- u ) name-record quad-b u32@ ;
: name-hash@ ( n tier -- h ) name-record quad-data u32@ ;
: name-text-of ( n cons -- addr u )
  2dup cons-at dup quad-b u32@ swap quad-head u32@ head-payload >r -rot cons-text-at r> ;
: name-text@ ( n tier -- addr u ) tier-names name-text-of ;
\ Whether n is a name of the tier (or of the input tier under it).
: name-valid? ( n tier -- flag ) tier-names cons-in? ;

\ The class's hooks. Two names are equal when tag, length, prefix and
\ hash agree and then the strings, or the numbers, do.
: name-rehash ( n cons -- h ) cons-at quad-data u32@ ;
\ The stored hash first: it tells almost every other name apart.
: name-fixed= ( record candidate -- flag )
  over quad-data u32@ over quad-data u32@ <> if 2drop false exit then
  over quad-head u32@ over quad-head u32@ = >r quad-a u32@ swap quad-a u32@ = r> and ;
: name-same ( n key cons -- flag )
  >r over r@ cons-at over cons-top name-fixed= 0= if r> drop 2drop false exit then
  over r@ cons-at quad-head u32@ head-tag tag-name-str =
  if cons-key 2@ rot r> name-text-of compare 0=
  else cons-top quad-b u32@ swap r> cons-at quad-b u32@ = then ;
: name-span ( local cons -- units ) 2drop 1 ;
' name-rehash ' name-same ' name-span name-class cons-hooks!


\ Building the candidate.
: name-cand ( tier -- addr ) tier-names cons-top ;
\ Room for a candidate with bytes of text, its prefix checked.
: name-room ( prefix bytes tier -- outcome )
  rot over name-valid? 0= if 2drop outcome-invalid exit then 1 -rot tier-names cons-room ;
: name-head! ( prefix head tier -- ) name-cand tuck quad-head u32! quad-a u32! ;
: name-x! ( x tier -- ) name-cand quad-b u32! ;
\ The candidate's hash: its tag, its prefix and x, the component's hash or
\ number.
: name-hash! ( x tier -- )
  name-cand >r r@ quad-head u32@ head-tag hash-fmix r@ quad-a u32@ hash-step
  swap hash-step r> quad-data u32! ;
: name-under? ( tier -- flag ) dup name-cand quad-a u32@ swap tier-names cons-under? ;
: name-lookup ( tier -- n true | i false )
  dup name-cand quad-data u32@ over name-under? rot tier-names cons-find ;
: name-keep ( i tier -- n outcome ) 1 -rot tier-names cons-commit ;
: name-intern ( tier -- n outcome )
  dup name-lookup if nip outcome-ok else swap name-keep then ;
\ A string component: the record is kept first (at the limit it is full),
\ then its text, whose offset goes into the record.
: str-text! ( n tier -- n )
  tier-names >r r@ cons-key 2@ r@ cons-text, over r> cons-at quad-b u32! ;
: str-keep ( i tier -- n outcome )
  tuck name-keep dup ok? if drop swap str-text! outcome-ok else rot drop then ;
: str-intern ( tier -- n outcome )
  dup name-lookup if nip outcome-ok else swap str-keep then ;

\ A string component. Its text goes into the set's key first (cons-key!),
\ so that a text from the tier's own byte slab, which may move while room
\ is made, is found again (cons-room-key); then the head and the hash.
: str-room ( prefix tier -- prefix outcome )
  2dup name-valid? 0= if drop outcome-invalid exit then 1 swap tier-names cons-room-key ;
: str-head! ( prefix tier -- )
  >r tag-name-str r@ tier-names cons-key @ pack-head r> name-head! ;
: str-hash! ( tier -- ) dup tier-names cons-key 2@ hash-bytes swap name-hash! ;
: str-setup ( prefix addr u tier -- outcome )
  >r dup payload-limit u< 0= if 2drop drop r> drop outcome-full exit then
  r@ tier-names cons-key! r@ str-room dup ok? 0= if nip r> drop exit then drop
  r@ str-head! r> str-hash! outcome-ok ;
\ A numeric component: room, head, the number and hash.
: num-setup ( prefix u tier -- outcome )
  over u32-mask u> if drop 2drop outcome-full exit then
  >r over 0 r@ name-room dup ok? 0= if nip nip r> drop exit then drop
  swap tag-name-num r@ name-head! dup r@ name-x! r> name-hash! outcome-ok ;

\ The name prefix.addr-u, or prefix.u: its number (an equal name's, which
\ may be the input tier's) and ok; or -1 and full or invalid.
: name-str ( prefix addr u tier -- n outcome )
  dup >r str-setup dup ok? if drop r> str-intern else r> drop no-result then ;
: name-num ( prefix u tier -- n outcome )
  dup >r num-setup dup ok? if drop r> name-intern else r> drop no-result then ;
\ The same names looked up without adding them: the number and ok; -1
\ and ok when the name is absent; -1 and full or invalid when the lookup
\ fails, as name-str and name-num would.
: name-seek ( tier -- n outcome ) name-lookup 0= if drop -1 then outcome-ok ;
: name-seek-str ( prefix addr u tier -- n outcome )
  dup >r str-setup dup ok? if drop r> name-seek else r> drop no-result then ;
: name-seek-num ( prefix u tier -- n outcome )
  dup >r num-setup dup ok? if drop r> name-seek else r> drop no-result then ;
\ The older forms: the number and true, or false, both when the name is
\ absent and when the lookup fails (name-seek-str tells them apart).
: seek>find ( n outcome -- n true | false ) ok? over 0< 0= and dup 0= if nip then ;
: name-find-str ( prefix addr u tier -- n true | false ) name-seek-str seek>find ;
: name-find-num ( prefix u tier -- n true | false ) name-seek-num seek>find ;


\ Copying a name between two scratch tiers over one input tier (ADR 0020
\ D5; plan step SN5): name-own? whether n is the tier's own (beyond its
\ input); name-up n's ancestor k prefixes up; name-depth how many of n's
\ ancestors, n included, are the tier's own; name-copy makes name n of
\ tier from in tier to, one component at a time from its nearest ancestor
\ in the input down: (n' ok), or (-1 full) or (-1 invalid) as name-str and
\ name-num give them. A name of the input is itself in both.
: name-own? ( n tier -- flag ) tier-names cons-under? 0= ;
: name-up ( n k tier -- n' ) swap 0 ?do tuck name-prefix@ swap loop drop ;
: name-depth ( n tier -- d )
  0 >r begin 2dup name-own? while tuck name-prefix@ swap r> 1+ >r repeat 2drop r> ;
: name-graft ( prefix' n from to -- n' outcome )
  >r 2dup name-tag@ tag-name-str =
  if name-text@ r> name-str else name-number@ r> name-num then ;
: name-lower ( n from to root k -- n from to root' outcome )
  >r 3 pick r> 4 pick name-up 3 pick 3 pick name-graft ;
: name-copy ( n from to -- n' outcome )
  2 pick 2 pick name-depth >r 2 pick r@ 3 pick name-up r>
  begin dup while
    1- dup >r name-lower ok-then? 0= if r> drop >r 2drop drop r> no-result exit then r>
  repeat drop >r 2drop drop r> outcome-ok ;

\ The anonymous name, made first in an input tier (compact.fs).
: name-anon-make ( tier -- n outcome )
  >r 1 0 r@ tier-names cons-room dup ok? 0= if r> drop no-result exit then drop
  0 0 r@ name-head! 0 r@ name-x! 0 r@ name-hash! r> name-intern ;

base !   \ the BASE this file was loaded with
