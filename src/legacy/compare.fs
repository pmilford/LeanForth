\ Untrusted conversion experiment over the bounded mutable term prototype.
\ It does not establish well-typedness, issue theorem handles or authorize
\ proofs. Inputs must not be mutated concurrently; all scratch state is global.
\ Equality here is only a candidate for review, not a trusted kernel judgment.
include beta.fs

0 constant lf-compare-equal
1 constant lf-compare-invalid
2 constant lf-compare-exhausted
3 constant lf-compare-unknown
6 constant lf-compare-frame-cells
create lf-compare-frames lf-term-capacity lf-compare-frame-cells * cells allot
create lf-syntax-frames lf-term-capacity lf-compare-frame-cells * cells allot
variable lf-compare-level
variable lf-syntax-level
variable lf-compare-fuel
variable lf-compare-start

\ Locate the active comparison or exact-syntax frame.
: lf-compare-frame ( level -- addr )
  lf-compare-frame-cells * cells lf-compare-frames + ;
: lf-syntax-frame ( level -- addr )
  lf-compare-frame-cells * cells lf-syntax-frames + ;
: lf-compare-current ( -- addr ) lf-compare-level @ 1- lf-compare-frame ;
: lf-syntax-current ( -- addr ) lf-syntax-level @ 1- lf-syntax-frame ;

\ Read or write a field in the active frame of the corresponding traversal.
: lf-compare@ ( offset -- value ) cells lf-compare-current + @ ;
: lf-compare! ( value offset -- ) cells lf-compare-current + ! ;
: lf-syntax@ ( offset -- value ) cells lf-syntax-current + @ ;
: lf-syntax! ( value offset -- ) cells lf-syntax-current + ! ;

\ Pop a traversal frame while preserving its status.
: lf-compare-leave ( status -- status ) -1 lf-compare-level +! ;
: lf-syntax-leave ( status -- status ) -1 lf-syntax-level +! ;

\ Compare stored syntax without reducing either term. Both operands must have
\ been structurally validated by the caller. Differences are unknown, not a
\ proof of inequality. Every visited pair consumes a shared fuel unit.
: lf-syntax-walk ( left right -- status )
  lf-compare-fuel @ 0= lf-syntax-level @ lf-term-capacity >= or if
    2drop lf-compare-exhausted exit
  then
  -1 lf-compare-fuel +!
  lf-syntax-level @ lf-syntax-frame >r r@ cell+ ! r> !
  1 lf-syntax-level +!
  0 lf-syntax@ lf-term-read 0= if lf-compare-invalid lf-syntax-leave exit then
  3 lf-syntax! 2 lf-syntax! 4 lf-syntax!
  1 lf-syntax@ lf-term-read 0= if lf-compare-invalid lf-syntax-leave exit then
  5 lf-syntax! swap 4 lf-syntax@ <> if
    drop lf-compare-unknown lf-syntax-leave exit
  then
  4 lf-syntax@ lf-tag-sort = 4 lf-syntax@ lf-tag-bvar = or if
    2 lf-syntax@ = 3 lf-syntax@ 5 lf-syntax@ = and if
      lf-compare-equal else lf-compare-unknown then lf-syntax-leave exit
  then
  4 lf-syntax@ lf-tag-app = 4 lf-syntax@ lf-tag-lam = or
  4 lf-syntax@ lf-tag-pi = or 0= if
    drop lf-compare-invalid lf-syntax-leave exit
  then
  2 lf-syntax@ swap recurse
  ?dup if lf-syntax-leave exit then
  3 lf-syntax@ 5 lf-syntax@ recurse lf-syntax-leave ;

\ Reduce a node with the shared comparison budget and retain remaining fuel.
: lf-compare-whnf ( node -- result status )
  lf-compare-fuel @ lf-beta-whnf lf-beta-fuel @ lf-compare-fuel ! ;

\ Compare after weak-head beta reduction. Binder domains must match exactly
\ in stored syntax before comparing bodies, as in the conservative ADR.
\ This procedure assumes no typing evidence and must remain outside the kernel.
: lf-compare-walk ( left right -- status )
  lf-compare-fuel @ 0= lf-compare-level @ lf-term-capacity >= or if
    2drop lf-compare-exhausted exit
  then
  -1 lf-compare-fuel +!
  lf-compare-level @ lf-compare-frame >r r@ cell+ ! r> !
  1 lf-compare-level +!
  0 lf-compare@ lf-compare-whnf
  dup if nip lf-compare-leave exit then drop 0 lf-compare!
  1 lf-compare@ lf-compare-whnf
  dup if nip lf-compare-leave exit then drop 1 lf-compare!
  0 lf-compare@ lf-term-read 0= if lf-compare-invalid lf-compare-leave exit then
  3 lf-compare! 2 lf-compare! 4 lf-compare!
  1 lf-compare@ lf-term-read 0= if lf-compare-invalid lf-compare-leave exit then
  5 lf-compare! swap 4 lf-compare@ <> if
    drop lf-compare-unknown lf-compare-leave exit
  then
  4 lf-compare@ lf-tag-sort = 4 lf-compare@ lf-tag-bvar = or if
    2 lf-compare@ = 3 lf-compare@ 5 lf-compare@ = and if
      lf-compare-equal else lf-compare-unknown then lf-compare-leave exit
  then
  4 lf-compare@ lf-tag-app = if
    2 lf-compare@ swap recurse
    ?dup if lf-compare-leave exit then
  else
    4 lf-compare@ lf-tag-lam = 4 lf-compare@ lf-tag-pi = or 0= if
      drop lf-compare-invalid lf-compare-leave exit
    then
    2 lf-compare@ swap lf-syntax-walk
    ?dup if lf-compare-leave exit then
  then
  3 lf-compare@ 5 lf-compare@ recurse lf-compare-leave ;

\ Compare two roots with a finite budget. Temporary allocations are discarded
\ even on success. Equal is an experimental result, never theorem validity.
: lf-compare ( left right fuel -- status )
  dup 0< if drop 2drop lf-compare-invalid exit then lf-compare-fuel !
  lf-term-count-valid? 0= if 2drop lf-compare-invalid exit then
  over lf-term-valid? over lf-term-valid? and 0= if
    2drop lf-compare-invalid exit
  then
  lf-term-count @ lf-compare-start !
  0 lf-compare-level ! 0 lf-syntax-level !
  lf-compare-walk
  lf-compare-start @ lf-term-count ! ;
