\ The compact store's tiers (ADR 0016 C1-C3): Lean's names, universe
\ levels, universe-argument and parameter lists, literals and expressions,
\ each a hash-consed set (lib/cons.fs), grouped into one tier record.
\ Untrusted; not yet used by the kernel (ADR 0016 C9 step 3 moves the
\ term, level and name stores onto it). Lean-specific: the families and
\ their records are Lean's; the machinery under them is the general
\ library (lib/slab.fs, htab.fs, cons.fs, pools.fs).
\
\ An *input tier* holds everything decoded from an export. It is filled
\ once by one task, then sealed (tier-seal): read-only from then on, so
\ every worker reads it without locks (ADR 0009 decision 3, ADR 0012 E1).
\ It has no marks. A *scratch tier* (tier-extend) extends a sealed input
\ tier for the terms one check builds: its numbers continue after the
\ input's, family by family, and finding a record looks in the input's
\ tables first when every part it refers to is an input record, so a term
\ rebuilt by a check gets the input's number. A scratch tier has LIFO
\ marks (tier-mark, tier-rollback) and is emptied after each check
\ (tier-reset); handles into it never leave the check (ADR 0016 C3).
\
\ The 16-byte record (C1): four packed 32-bit fields, read and written only
\ through u32@ and u32! (lib/u32.fs: Gforth's l@ and l!, or the Forth-2012
\ fallback), named by the fields of /quad. The first field of names,
\ levels and expressions is a head: bits 0-4 a tag, bits 5-31 a payload
\ of 27 bits.
\
\ Interface: /quad quad-head quad-a quad-b quad-data pack-head head-tag
\ head-payload payload-limit /tier tier-names tier-levels tier-tuples
\ tier-texts tier-exprs tier-extend tier-seal /tier-mark tier-mark
\ tier-mark-valid? tier-rollback tier-reset tier-free tier-allocated
\ tier-used. tier-init, which needs every family, is in compact.fs.
\ State: none of its own; every word takes a tier record, which owns its
\ heap memory until tier-free. A tier must not be a checker-context member
\ yet: members may not own heap memory (lib/context.fs).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/portability.fs
require ../lib/outcome.fs
require ../lib/u32.fs
require ../lib/slab.fs
require ../lib/htab.fs
require ../lib/cons.fs

\ The 16-byte record.
begin-structure /quad
  1 u32s +field quad-head    \ tag and payload
  1 u32s +field quad-a       \ first operand
  1 u32s +field quad-b       \ second operand
  1 u32s +field quad-data    \ facts about the record, or a stored hash
end-structure

\ Whether two records' a and b fields are equal.
: quad-ab= ( addr1 addr2 -- flag )
  over quad-a u32@ over quad-a u32@ = >r quad-b u32@ swap quad-b u32@ = r> and ;

\ Heads: a tag of 5 bits and a payload of 27 bits.
31 constant head-tag-mask
1 27 lshift constant payload-limit
: pack-head ( tag payload -- head ) 5 lshift or ;
: head-tag ( head -- tag ) head-tag-mask and ;
: head-payload ( head -- payload ) 5 rshift ;
\ A head is at most 32 bits; a larger one has a payload beyond 27 bits.
: head-fits? ( head -- flag ) u32-mask u> 0= ;

\ The "has universe parameters" bit of a level's and an expression's
\ data field (Lean's hasLevelParam, ADR 0016 C1).
1 20 lshift constant data-params-bit

\ The candidate record of a family, at its set's free end, and its fields.
: cand-head ( cons -- u ) cons-top quad-head u32@ ;
: cand-a ( cons -- u ) cons-top quad-a u32@ ;
: cand-b ( cons -- u ) cons-top quad-b u32@ ;
: cand-data! ( u cons -- ) cons-top quad-data u32! ;
: cand-data ( cons -- u ) cons-top quad-data u32@ ;
\ Unchecked, after cons-room: write a candidate's first three fields; its
\ data field is 0.
: cand! ( head a b cons -- )
  cons-top >r r@ quad-b u32! r@ quad-a u32! r@ quad-head u32! 0 r> quad-data u32! ;
\ Whether number n is below the set's first own number: an under record.
: cons-under? ( n cons -- flag ) cons-first @ u< ;
\ Whether n is a number of the set or its under set.
: cons-in? ( n cons -- flag ) cons-numbers u< ;
\ Whether three fields fit 32 bits each (cand! would cut them otherwise).
: fields-fit? ( x y z -- x y z flag ) dup 2over rot or or u32-mask u> 0= ;
\ A builder's failure with its three fields: -1 in the result's place.
: fail3 ( x y z outcome -- -1 outcome ) nip nip nip no-result ;

\ Tables of one check per tag: check-table makes one, check-fill sets
\ every entry, check! one; check-run runs the check of tag on the
\ arguments below it.
: check-table ( "name" -- ) create head-tag-mask 1+ cells allot ;
: check-fill ( xt table -- ) head-tag-mask 1+ 0 do 2dup i cells + ! loop 2drop ;
: check! ( xt tag table -- ) swap cells + ! ;
: check-run ( i*x tag table -- j*x ) swap cells + @ execute ;

begin-structure /tier
  /cons +field tier-names
  /cons +field tier-levels
  /cons +field tier-tuples    \ universe-argument and parameter lists
  /cons +field tier-texts     \ the bytes of natVal and strVal literals
  /cons +field tier-exprs
end-structure

\ The five families, for the words that treat them alike.
5 constant tier-families
create tier-family-xts ' tier-names , ' tier-levels , ' tier-tuples , ' tier-texts ,
  ' tier-exprs ,
: tier-family ( i tier -- cons ) swap cells tier-family-xts + @ execute ;

\ A scratch tier's tables start at 2^10 slots and grow.
10 constant tier-scratch-log2

\ Make a scratch tier over a sealed input tier: ok, invalid when the input
\ is not sealed, or full. Stops at the first failure; tier-free then frees
\ what was made. The record must not hold memory: tier-free first.
: tier-extend-family ( input tier i -- outcome )
  tuck swap tier-family >r swap tier-family tier-scratch-log2 swap r> cons-extend ;
: tier-extend ( input tier -- outcome )
  dup /tier erase tier-families 0 do
    2dup i tier-extend-family dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;

\ Seal an input tier: every family read-only. ok, or invalid for a tier
\ that is not open (sealed already, or a family missing).
: tier-seal ( tier -- outcome )
  tier-families 0 do
    i over tier-family cons-seal dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
: tier-free ( tier -- )
  tier-families 0 do i over tier-family cons-free loop drop ;

\ Marks: one per family. A mark is valid when every family's part is; a
\ rollback checks all five before it changes anything.
begin-structure /tier-mark
  tier-families /cons-mark * +field tier-mark-parts
end-structure
: tier-mark-part ( i mark -- part ) tier-mark-parts swap /cons-mark * + ;
: tier-pair ( mark tier i -- part cons ) tuck swap tier-family >r swap tier-mark-part r> ;
\ Mark a scratch tier (or an input tier still being filled): ok; or, with
\ a mark every rollback refuses, invalid or full.
: tier-mark ( mark tier -- outcome )
  tier-families 0 do
    2dup i tier-pair cons-mark dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
: tier-mark-valid? ( mark tier -- flag )
  tier-families 0 do 2dup i tier-pair cons-mark-valid? 0= if 2drop false unloop exit then
  loop 2drop true ;
\ Give back every record made since the mark: ok, or invalid with nothing
\ changed.
: tier-rollback ( mark tier -- outcome )
  2dup tier-mark-valid? 0= if 2drop outcome-invalid exit then
  tier-families 0 do 2dup i tier-pair cons-rollback drop loop 2drop outcome-ok ;
\ Empty a scratch tier after a check, whatever its outcome: ok, or invalid
\ for a sealed tier.
: tier-reset ( tier -- outcome )
  outcome-ok tier-families 0 do
    over i swap tier-family cons-reset ok? 0= if drop outcome-invalid then
  loop nip ;

\ Address units allocated, and in use, by a tier's slabs and tables.
: cons-allocated ( cons -- u )
  dup cons-records slab-bytes over cons-bytes slab-bytes + swap cons-table htab-slots u32s + ;
: slab-used-bytes ( slab -- u ) dup slab-count swap slab-unit * ;
: cons-used ( cons -- u )
  dup cons-records slab-used-bytes over cons-bytes slab-used-bytes +
  swap cons-table htab-slots u32s + ;
: tier-allocated ( tier -- u )
  0 swap tier-families 0 do i over tier-family cons-allocated rot + swap loop drop ;
: tier-used ( tier -- u )
  0 swap tier-families 0 do i over tier-family cons-used rot + swap loop drop ;

base !   \ the BASE this file was loaded with
