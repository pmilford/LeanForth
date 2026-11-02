\ Untrusted mixed-term syntax comparison. Load constant-term-boundary.fs and
\ its dependencies first. Global scratch is non-reentrant; exclude arena,
\ context and name mutation during a call. Not a typing or proof judgment.
\ Equal opaque level parameter IDs are assumed to denote the same Lean name.
0 constant lf-mcompare-equal
1 constant lf-mcompare-invalid
2 constant lf-mcompare-exhausted
3 constant lf-mcompare-unknown
variable lf-mcompare-fuel
variable lf-mcompare-left
variable lf-mcompare-lid
variable lf-mcompare-right
variable lf-mcompare-rid
variable lf-mcompare-na
variable lf-mcompare-nb
variable lf-mcompare-ca
variable lf-mcompare-cb
variable lf-mcompare-count

: lf-mcompare-spend ( -- flag )
  lf-mcompare-fuel @ 0= if false exit then -1 lf-mcompare-fuel +! true ;
\ Both names have passed the complete name-table audit. Compare components,
\ including bytes, even if their indices coincide. One unit per component;
\ byte comparisons are bounded by the name arena capacity.
: lf-mcompare-names ( a b -- status )
  lf-mcompare-nb ! lf-mcompare-na !
  begin
    lf-mcompare-spend 0= if lf-mcompare-exhausted exit then
    lf-mcompare-na @ 0 lf-name-field lf-mcompare-nb @ 0 lf-name-field <> if
      lf-mcompare-unknown exit then
    lf-mcompare-na @ 0= lf-mcompare-nb @ 0= and if lf-mcompare-equal exit then
    lf-mcompare-na @ 0 lf-name-field lf-name-tag-num = if
      lf-mcompare-na @ 2 lf-name-field lf-mcompare-nb @ 2 lf-name-field <> if
        lf-mcompare-unknown exit then
    else
      lf-mcompare-na @ 2 lf-name-field lf-name-bytes +
      lf-mcompare-na @ 3 lf-name-field
      lf-mcompare-nb @ 2 lf-name-field lf-name-bytes +
      lf-mcompare-nb @ 3 lf-name-field compare if lf-mcompare-unknown exit then
    then
    lf-mcompare-na @ 1 lf-name-field lf-mcompare-na !
    lf-mcompare-nb @ 1 lf-name-field lf-mcompare-nb !
  again ;

6 constant lf-mcompare-frame-cells
create lf-mcompare-level-frames lf-level-capacity lf-mcompare-frame-cells * cells allot
variable lf-mcompare-level-depth
: lf-mcompare-level@ ( field -- x ) cells lf-mcompare-level-depth @ 1- lf-mcompare-frame-cells * cells lf-mcompare-level-frames + + @ ;
: lf-mcompare-level! ( x field -- ) cells lf-mcompare-level-depth @ 1- lf-mcompare-frame-cells * cells lf-mcompare-level-frames + + ! ;
: lf-mcompare-level-leave ( status -- status ) -1 lf-mcompare-level-depth +! ;
\ Compare audited level syntax in order, without normalization.
: lf-mcompare-level ( a b -- status )
  lf-mcompare-level-depth @ lf-level-capacity >= lf-mcompare-spend 0= or if
    2drop lf-mcompare-exhausted exit then
  1 lf-mcompare-level-depth +!
  lf-level-read 0= if drop lf-mcompare-invalid lf-mcompare-level-leave exit then
  5 lf-mcompare-level! 4 lf-mcompare-level! 3 lf-mcompare-level!
  lf-level-read 0= if lf-mcompare-invalid lf-mcompare-level-leave exit then
  2 lf-mcompare-level! 1 lf-mcompare-level! 0 lf-mcompare-level!
  0 lf-mcompare-level@ 3 lf-mcompare-level@ <> if lf-mcompare-unknown lf-mcompare-level-leave exit then
  0 lf-mcompare-level@ lf-level-tag-zero = if lf-mcompare-equal lf-mcompare-level-leave exit then
  0 lf-mcompare-level@ lf-level-tag-param = if
    1 lf-mcompare-level@ 4 lf-mcompare-level@ = if lf-mcompare-equal else lf-mcompare-unknown then
    lf-mcompare-level-leave exit then
  1 lf-mcompare-level@ 4 lf-mcompare-level@ recurse ?dup if lf-mcompare-level-leave exit then
  0 lf-mcompare-level@ lf-level-tag-succ = if lf-mcompare-equal lf-mcompare-level-leave exit then
  2 lf-mcompare-level@ 5 lf-mcompare-level@ recurse lf-mcompare-level-leave ;

\ Reference slots were audited; compare name and each ordered level tree.
: lf-mcompare-constants ( a b -- status )
  lf-cref-slot lf-mcompare-cb ! lf-cref-slot lf-mcompare-ca !
  lf-mcompare-ca @ 3 cells + @ lf-mcompare-cb @ 3 cells + @ <> if lf-mcompare-unknown exit then
  lf-mcompare-ca @ cell+ @ lf-mcompare-cb @ cell+ @ lf-mcompare-names ?dup if exit then
  lf-mcompare-ca @ 3 cells + @ lf-mcompare-count !
  lf-mcompare-count @ 0 ?do
    lf-mcompare-ca @ i lf-cref-arg @ lf-mcompare-cb @ i lf-cref-arg @
    0 lf-mcompare-level-depth ! lf-mcompare-level ?dup if unloop exit then
  loop lf-mcompare-equal ;

create lf-mcompare-frames lf-term-capacity lf-mcompare-frame-cells * cells allot
variable lf-mcompare-depth
: lf-mcompare@ ( field -- x ) cells lf-mcompare-depth @ 1- lf-mcompare-frame-cells * cells lf-mcompare-frames + + @ ;
: lf-mcompare! ( x field -- ) cells lf-mcompare-depth @ 1- lf-mcompare-frame-cells * cells lf-mcompare-frames + + ! ;
: lf-mcompare-leave ( status -- status ) -1 lf-mcompare-depth +! ;
: lf-mcompare-walk ( a b -- status )
  lf-mcompare-depth @ lf-term-capacity >= lf-mcompare-spend 0= or if
    2drop lf-mcompare-exhausted exit then
  1 lf-mcompare-depth +!
  lf-term-read 0= if drop lf-mcompare-invalid lf-mcompare-leave exit then
  5 lf-mcompare! 4 lf-mcompare! 3 lf-mcompare!
  lf-term-read 0= if lf-mcompare-invalid lf-mcompare-leave exit then
  2 lf-mcompare! 1 lf-mcompare! 0 lf-mcompare!
  0 lf-mcompare@ 3 lf-mcompare@ <> if lf-mcompare-unknown lf-mcompare-leave exit then
  0 lf-mcompare@ lf-tag-constant = if
    1 lf-mcompare@ 4 lf-mcompare@ lf-mcompare-constants lf-mcompare-leave exit then
  0 lf-mcompare@ lf-tag-bvar = if
    1 lf-mcompare@ 4 lf-mcompare@ = if lf-mcompare-equal else lf-mcompare-unknown then
    lf-mcompare-leave exit then
  0 lf-mcompare@ lf-tag-symbolic-sort = if
    1 lf-mcompare@ 4 lf-mcompare@ 0 lf-mcompare-level-depth !
    lf-mcompare-level lf-mcompare-leave exit then
  1 lf-mcompare@ 4 lf-mcompare@ recurse ?dup if lf-mcompare-leave exit then
  2 lf-mcompare@ 5 lf-mcompare@ recurse lf-mcompare-leave ;

\ ( left identity right identity fuel -- status ) Both complete structural
\ audits precede comparison and share its fuel. Scope of term binders, typing,
\ declaration lookup and Lean string encoding are not checked. Failed audits
\ zero remaining fuel. Exhaustion can prevent discovery of a later invalidity.
: lf-mcompare-audit-status ( status -- status )
  case
    lf-repr-ok of lf-mcompare-equal endof
    lf-repr-invalid of lf-mcompare-invalid endof
    lf-repr-exhausted of lf-mcompare-exhausted endof
    drop lf-mcompare-invalid 0
  endcase ;
: lf-mixed-compare ( left lid right rid fuel -- status )
  dup 0< if drop 2drop 2drop 0 lf-mcompare-fuel ! lf-mcompare-invalid exit then
  lf-mcompare-fuel ! lf-mcompare-rid ! lf-mcompare-right ! lf-mcompare-lid ! lf-mcompare-left !
  lf-mcompare-left @ lf-mcompare-lid @ lf-mcompare-fuel @ lf-cterm-check lf-mcompare-audit-status
  ?dup if 0 lf-mcompare-fuel ! exit then lf-cterm-fuel @ lf-mcompare-fuel !
  lf-mcompare-right @ lf-mcompare-rid @ lf-mcompare-fuel @ lf-cterm-check lf-mcompare-audit-status
  ?dup if 0 lf-mcompare-fuel ! exit then lf-cterm-fuel @ lf-mcompare-fuel !
  0 lf-mcompare-depth ! lf-mcompare-left @ lf-mcompare-right @ lf-mcompare-walk ;
