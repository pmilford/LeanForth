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
\ name-find-str and name-find-num look a name up without adding it; like
\ every word that builds, they need an open tier, so look names up in a
\ sealed input tier through a scratch tier over it. The text given to
\ name-str or name-find-str must not lie in the same tier's byte slab,
\ which may move while the word makes room (an input tier's text, given
\ to a scratch tier over it, is fine: a sealed tier never moves).
\
\ Interface: tag-name-anon tag-name-str tag-name-num name-anonymous
\ name-class name-str name-num name-find-str name-find-num name-valid?
\ name-tag@ name-prefix@ name-number@ name-text@ name-hash@ name-anon-make.
\ State: name-class, made while loading and read-only afterwards.

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
: quad-same? ( addr1 addr2 field-xt -- flag ) tuck execute u32@ >r execute u32@ r> = ;
: name-fixed= ( record candidate -- flag )
  2dup ['] quad-head quad-same? >r 2dup ['] quad-a quad-same? >r
  ['] quad-data quad-same? r> r> and and ;
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
: name-keep ( i tier -- n ) 1 -rot tier-names cons-commit ;
: name-intern ( tier -- n outcome ) dup name-lookup if nip else swap name-keep then outcome-ok ;
: str-keep ( i tier -- n )
  dup tier-names dup cons-key 2@ rot cons-text, over name-x! name-keep ;
: str-intern ( tier -- n outcome ) dup name-lookup if nip else swap str-keep then outcome-ok ;
: name-find ( tier -- n true | false ) name-lookup dup 0= if nip then ;

\ A string component: the text in the key, room for it, head and hash.
: str-setup ( prefix addr u tier -- outcome )
  >r 2dup r@ tier-names cons-key 2! nip
  dup payload-limit u< 0= if 2drop r> drop outcome-full exit then
  2dup r@ name-room dup ok? 0= if nip nip r> drop exit then drop
  tag-name-str swap pack-head r@ name-head! r@ tier-names cons-key 2@ hash-bytes r> name-hash!
  outcome-ok ;
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
\ The same names looked up without adding them: the number and true, or
\ false when the name is absent or the lookup fails.
: name-find-str ( prefix addr u tier -- n true | false )
  dup >r str-setup ok? if r> name-find else r> drop false then ;
: name-find-num ( prefix u tier -- n true | false )
  dup >r num-setup ok? if r> name-find else r> drop false then ;

\ The anonymous name, made first in an input tier (compact.fs).
: name-anon-make ( tier -- n outcome )
  >r 1 0 r@ tier-names cons-room dup ok? 0= if r> drop no-result exit then drop
  0 0 r@ name-head! 0 r@ name-x! 0 r@ name-hash! r> name-intern ;
