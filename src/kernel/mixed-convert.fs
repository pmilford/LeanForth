\ Untrusted conservative beta conversion for mixed terms. Load mixed-beta,
\ mixed-compare, level-value and level-compare and their dependencies first. This is not a trusted kernel or proof checker.
\ Both inputs are audited; beta normalization and comparison share fuel. Sorts
\ use a conservative symbolic level comparator. Other differences are unknown.
\ Global mutable state is non-reentrant; no raw or concurrent mutation is safe.
\ The audit checks universe parameter scope, not term binder scope or typing;
\ callers must establish those independently before using a conversion result.

0 constant lf-mconvert-equal
1 constant lf-mconvert-invalid
2 constant lf-mconvert-exhausted
3 constant lf-mconvert-unknown
6 constant lf-mconvert-frame-cells
create lf-mconvert-frames lf-term-capacity lf-mconvert-frame-cells * cells allot
variable lf-mconvert-depth
variable lf-mconvert-fuel
variable lf-mconvert-level-start
variable lf-mconvert-start
variable lf-mconvert-left
variable lf-mconvert-lid
variable lf-mconvert-right
variable lf-mconvert-rid

\ Access the current bounded comparison frame and preserve its result on exit.
: lf-mconvert-frame ( depth -- addr )
  lf-mconvert-frame-cells * cells lf-mconvert-frames + ;
: lf-mconvert@ ( field -- x ) cells lf-mconvert-depth @ 1- lf-mconvert-frame + @ ;
: lf-mconvert! ( x field -- ) cells lf-mconvert-depth @ 1- lf-mconvert-frame + ! ;
: lf-mconvert-leave ( status -- status ) -1 lf-mconvert-depth +! ;

\ Translate dependency statuses explicitly so changes cannot create equality.
: lf-mconvert-beta-status ( status -- status )
  case
    lf-mbeta-ok of lf-mconvert-equal endof
    lf-mbeta-invalid of lf-mconvert-invalid endof
    lf-mbeta-exhausted of lf-mconvert-exhausted endof
    drop lf-mconvert-invalid 0
  endcase ;
: lf-mconvert-compare-status ( status -- status )
  case
    lf-mcompare-equal of lf-mconvert-equal endof
    lf-mcompare-invalid of lf-mconvert-invalid endof
    lf-mcompare-exhausted of lf-mconvert-exhausted endof
    lf-mcompare-unknown of lf-mconvert-unknown endof
    drop lf-mconvert-invalid 0
  endcase ;

\ Reduce one audited node with the same budget. Its handle identity is checked
\ before use; failure never authorizes equality.
: lf-mconvert-whnf ( node -- node status )
  dup lf-term-identity 0= if drop -1 lf-mconvert-invalid exit then
  lf-mconvert-fuel @ lf-mixed-beta
  lf-mbeta-fuel @ lf-mconvert-fuel ! swap drop lf-mconvert-beta-status ;

\ Map the conservative level result explicitly; unexpected statuses fail
\ closed. Both reachable level graphs are checked under the current context.
: lf-mconvert-levels ( left right -- status )
  lf-mconvert-fuel @ lf-level-compare
  lf-lcmp-fuel @ lf-mconvert-fuel !
  case
    lf-lcmp-equal of lf-mconvert-equal endof
    lf-lcmp-invalid of lf-mconvert-invalid endof
    lf-lcmp-exhausted of lf-mconvert-exhausted endof
    lf-lcmp-unknown of lf-mconvert-unknown endof
    drop lf-mconvert-invalid 0
  endcase ;

\ Names and reference slots were audited before allocation. Compare each
\ ordered universe argument with the same conservative level relation.
variable lf-mconvert-ca
variable lf-mconvert-cb
: lf-mconvert-constants ( a b -- status )
  lf-cref-slot lf-mconvert-cb ! lf-cref-slot lf-mconvert-ca !
  lf-mconvert-ca @ 3 cells + @ lf-mconvert-cb @ 3 cells + @ <> if
    lf-mconvert-unknown exit then
  lf-mconvert-fuel @ lf-mcompare-fuel !
  lf-mconvert-ca @ cell+ @ lf-mconvert-cb @ cell+ @ lf-mcompare-names
  lf-mcompare-fuel @ lf-mconvert-fuel ! lf-mconvert-compare-status ?dup if exit then
  lf-mconvert-ca @ 3 cells + @ 0 ?do
    lf-mconvert-ca @ i lf-cref-arg @ lf-mconvert-cb @ i lf-cref-arg @
    lf-mconvert-levels ?dup if unloop exit then
  loop lf-mconvert-equal ;

\ Compare reduced heads recursively. Constructors not known here are invalid;
\ distinct valid syntax is unknown, not a proof of inequality. Both operands
\ have already passed the full public audit, including discarded arguments.
: lf-mconvert-walk ( left right -- status )
  lf-mconvert-fuel @ 0= lf-mconvert-depth @ lf-term-capacity >= or if
    2drop lf-mconvert-exhausted exit then
  -1 lf-mconvert-fuel +!
  lf-mconvert-depth @ lf-mconvert-frame >r r@ cell+ ! r> !
  1 lf-mconvert-depth +!
  0 lf-mconvert@ lf-mconvert-whnf
  dup if nip lf-mconvert-leave exit then drop 0 lf-mconvert!
  1 lf-mconvert@ lf-mconvert-whnf
  dup if nip lf-mconvert-leave exit then drop 1 lf-mconvert!
  0 lf-mconvert@ lf-term-read 0= if lf-mconvert-invalid lf-mconvert-leave exit then
  3 lf-mconvert! 2 lf-mconvert! 4 lf-mconvert!
  1 lf-mconvert@ lf-term-read 0= if lf-mconvert-invalid lf-mconvert-leave exit then
  5 lf-mconvert! swap 4 lf-mconvert@ <> if
    drop lf-mconvert-unknown lf-mconvert-leave exit then
  4 lf-mconvert@ lf-tag-symbolic-sort = if
    3 lf-mconvert@ 5 lf-mconvert@ <> if
      drop lf-mconvert-invalid lf-mconvert-leave exit then
    2 lf-mconvert@ swap lf-mconvert-levels lf-mconvert-leave exit
  then
  4 lf-mconvert@ lf-tag-constant = if
    2 lf-mconvert@ swap lf-mconvert-constants lf-mconvert-leave exit
  then
  4 lf-mconvert@ lf-tag-bvar = if
    2 lf-mconvert@ = 3 lf-mconvert@ 5 lf-mconvert@ = and if
      lf-mconvert-equal else lf-mconvert-unknown then lf-mconvert-leave exit then
  4 lf-mconvert@ lf-tag-app = 4 lf-mconvert@ lf-tag-lam = or
  4 lf-mconvert@ lf-tag-pi = or 0= if
    drop lf-mconvert-invalid lf-mconvert-leave exit then
  2 lf-mconvert@ swap recurse ?dup if lf-mconvert-leave exit then
  3 lf-mconvert@ 5 lf-mconvert@ recurse lf-mconvert-leave ;

\ ( left left-id right right-id fuel -- status )
\ Validate both complete graphs, then compare; restore all temporary term
\ allocations on every result. Failed preflight conservatively leaves zero fuel.
: lf-mixed-convert ( left lid right rid fuel -- status )
  dup 0< if drop 2drop 2drop 0 lf-mconvert-fuel ! lf-mconvert-invalid exit then
  lf-mconvert-fuel ! lf-mconvert-rid ! lf-mconvert-right !
  lf-mconvert-lid ! lf-mconvert-left !
  lf-mconvert-left @ lf-mconvert-lid @ lf-mconvert-fuel @ lf-cterm-check lf-mcompare-audit-status lf-mconvert-compare-status
  ?dup if 0 lf-mconvert-fuel ! exit then lf-cterm-fuel @ lf-mconvert-fuel !
  lf-mconvert-right @ lf-mconvert-rid @ lf-mconvert-fuel @ lf-cterm-check lf-mcompare-audit-status lf-mconvert-compare-status
  ?dup if 0 lf-mconvert-fuel ! exit then lf-cterm-fuel @ lf-mconvert-fuel !
  lf-term-count @ lf-mconvert-start ! lf-level-count @ lf-mconvert-level-start !
  0 lf-mconvert-depth !
  lf-mconvert-left @ lf-mconvert-right @ lf-mconvert-walk
  lf-mconvert-start @ lf-term-count ! lf-mconvert-level-start @ lf-level-count ! ;
