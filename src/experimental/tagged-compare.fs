\ Untrusted syntactic comparison of generation-tagged symbolic terms.
\ Load terms, levels, level-scope, tagged-sort-boundary, symbolic-session and
\ generation-handles first. Global scratch: non-reentrant; no concurrent
\ arena mutation or raw writes during a call. No typing, beta reduction,
\ universe equivalence, or theorem validity is established.
0 constant lf-tcompare-equal
1 constant lf-tcompare-invalid
2 constant lf-tcompare-exhausted
3 constant lf-tcompare-unknown
6 constant lf-tcompare-frame-cells
create lf-tcompare-frames lf-term-capacity lf-tcompare-frame-cells * cells allot
variable lf-tcompare-depth
variable lf-tcompare-fuel
variable lf-tcompare-left
variable lf-tcompare-lid
variable lf-tcompare-right
variable lf-tcompare-rid
: lf-tcompare-frame ( depth -- addr ) lf-tcompare-frame-cells * cells lf-tcompare-frames + ;
: lf-tcompare@ ( field -- x ) cells lf-tcompare-depth @ 1- lf-tcompare-frame + @ ;
: lf-tcompare! ( x field -- ) cells lf-tcompare-depth @ 1- lf-tcompare-frame + ! ;
: lf-tcompare-leave ( status -- status ) -1 lf-tcompare-depth +! ;
\ Inputs have already been fully audited. Each pair consumes fuel and a
\ bounded frame; unequal syntax yields unknown, never a disequality claim.
: lf-tcompare-walk ( left right -- status )
  lf-tcompare-fuel @ 0= lf-tcompare-depth @ lf-term-capacity >= or if
    2drop lf-tcompare-exhausted exit then
  -1 lf-tcompare-fuel +!
  lf-tcompare-depth @ lf-tcompare-frame >r r@ cell+ ! r> !
  1 lf-tcompare-depth +!
  0 lf-tcompare@ lf-term-read 0= if lf-tcompare-invalid lf-tcompare-leave exit then
  3 lf-tcompare! 2 lf-tcompare! 4 lf-tcompare!
  1 lf-tcompare@ lf-term-read 0= if lf-tcompare-invalid lf-tcompare-leave exit then
  5 lf-tcompare! swap 4 lf-tcompare@ <> if
    drop lf-tcompare-unknown lf-tcompare-leave exit then
  4 lf-tcompare@ lf-tag-symbolic-sort = 4 lf-tcompare@ lf-tag-bvar = or if
    2 lf-tcompare@ = 3 lf-tcompare@ 5 lf-tcompare@ = and if
      lf-tcompare-equal else lf-tcompare-unknown then lf-tcompare-leave exit then
  4 lf-tcompare@ lf-tag-app = 4 lf-tcompare@ lf-tag-lam = or
  4 lf-tcompare@ lf-tag-pi = or 0= if
    drop lf-tcompare-invalid lf-tcompare-leave exit then
  2 lf-tcompare@ swap recurse ?dup if lf-tcompare-leave exit then
  3 lf-tcompare@ 5 lf-tcompare@ recurse lf-tcompare-leave ;
\ ( left-index left-id right-index right-id fuel -- status )
\ Both complete graphs are checked even for identical handles or root tags;
\ validation and comparison share fuel. Invalid fuel/handles/graphs fail closed;
\ resource exhaustion is distinct from unknown. Failed validation sets the
\ remaining fuel to zero conservatively. Sort equality requires the
\ identical live level index, not structural or semantic level equivalence.
: lf-tagged-compare ( left lid right rid fuel -- status )
  dup 0< if drop 2drop 2drop lf-tcompare-invalid exit then
  lf-tcompare-fuel ! lf-tcompare-rid ! lf-tcompare-right !
  lf-tcompare-lid ! lf-tcompare-left !
  lf-tcompare-left @ lf-tcompare-lid @ lf-tcompare-fuel @ lf-hterm-check
  ?dup if 0 lf-tcompare-fuel ! exit then lf-href-fuel @ lf-tcompare-fuel !
  lf-tcompare-right @ lf-tcompare-rid @ lf-tcompare-fuel @ lf-hterm-check
  ?dup if 0 lf-tcompare-fuel ! exit then lf-href-fuel @ lf-tcompare-fuel !
  0 lf-tcompare-depth ! lf-tcompare-left @ lf-tcompare-right @ lf-tcompare-walk ;
