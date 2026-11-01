\ Untrusted conservative beta conversion for tagged terms. Load the tagged
\ handle, beta, level-value and level-compare modules first. This is not a trusted kernel or proof checker.
\ Both inputs are audited; beta normalization and comparison share fuel. Sorts
\ use a conservative symbolic level comparator. Other differences are unknown.
\ Global mutable state is non-reentrant; no raw or concurrent mutation is safe.
\ The audit checks universe parameter scope, not term binder scope or typing;
\ callers must establish those independently before using a conversion result.

0 constant lf-tconvert-equal
1 constant lf-tconvert-invalid
2 constant lf-tconvert-exhausted
3 constant lf-tconvert-unknown
6 constant lf-tconvert-frame-cells
create lf-tconvert-frames lf-term-capacity lf-tconvert-frame-cells * cells allot
variable lf-tconvert-depth
variable lf-tconvert-fuel
variable lf-tconvert-start
variable lf-tconvert-left
variable lf-tconvert-lid
variable lf-tconvert-right
variable lf-tconvert-rid

\ Access the current bounded comparison frame and preserve its result on exit.
: lf-tconvert-frame ( depth -- addr )
  lf-tconvert-frame-cells * cells lf-tconvert-frames + ;
: lf-tconvert@ ( field -- x ) cells lf-tconvert-depth @ 1- lf-tconvert-frame + @ ;
: lf-tconvert! ( x field -- ) cells lf-tconvert-depth @ 1- lf-tconvert-frame + ! ;
: lf-tconvert-leave ( status -- status ) -1 lf-tconvert-depth +! ;

\ Reduce one audited node with the same budget. Its handle identity is checked
\ before use; failure never authorizes equality.
: lf-tconvert-whnf ( node -- node status )
  dup lf-term-identity 0= if drop -1 lf-tconvert-invalid exit then
  lf-tconvert-fuel @ lf-tagged-beta
  lf-tbeta-fuel @ lf-tconvert-fuel ! swap drop ;

\ Map the conservative level result explicitly; unexpected statuses fail
\ closed. Both reachable level graphs are checked under the current context.
: lf-tconvert-levels ( left right -- status )
  lf-tconvert-fuel @ lf-level-compare
  lf-lcmp-fuel @ lf-tconvert-fuel !
  case
    lf-lcmp-equal of lf-tconvert-equal endof
    lf-lcmp-invalid of lf-tconvert-invalid endof
    lf-lcmp-exhausted of lf-tconvert-exhausted endof
    lf-lcmp-unknown of lf-tconvert-unknown endof
    drop lf-tconvert-invalid 0
  endcase ;

\ Compare reduced heads recursively. Constructors not known here are invalid;
\ distinct valid syntax is unknown, not a proof of inequality. Both operands
\ have already passed the full public audit, including discarded arguments.
: lf-tconvert-walk ( left right -- status )
  lf-tconvert-fuel @ 0= lf-tconvert-depth @ lf-term-capacity >= or if
    2drop lf-tconvert-exhausted exit then
  -1 lf-tconvert-fuel +!
  lf-tconvert-depth @ lf-tconvert-frame >r r@ cell+ ! r> !
  1 lf-tconvert-depth +!
  0 lf-tconvert@ lf-tconvert-whnf
  dup if nip lf-tconvert-leave exit then drop 0 lf-tconvert!
  1 lf-tconvert@ lf-tconvert-whnf
  dup if nip lf-tconvert-leave exit then drop 1 lf-tconvert!
  0 lf-tconvert@ lf-term-read 0= if lf-tconvert-invalid lf-tconvert-leave exit then
  3 lf-tconvert! 2 lf-tconvert! 4 lf-tconvert!
  1 lf-tconvert@ lf-term-read 0= if lf-tconvert-invalid lf-tconvert-leave exit then
  5 lf-tconvert! swap 4 lf-tconvert@ <> if
    drop lf-tconvert-unknown lf-tconvert-leave exit then
  4 lf-tconvert@ lf-tag-symbolic-sort = if
    3 lf-tconvert@ 5 lf-tconvert@ <> if
      drop lf-tconvert-invalid lf-tconvert-leave exit then
    2 lf-tconvert@ swap lf-tconvert-levels lf-tconvert-leave exit
  then
  4 lf-tconvert@ lf-tag-bvar = if
    2 lf-tconvert@ = 3 lf-tconvert@ 5 lf-tconvert@ = and if
      lf-tconvert-equal else lf-tconvert-unknown then lf-tconvert-leave exit then
  4 lf-tconvert@ lf-tag-app = 4 lf-tconvert@ lf-tag-lam = or
  4 lf-tconvert@ lf-tag-pi = or 0= if
    drop lf-tconvert-invalid lf-tconvert-leave exit then
  2 lf-tconvert@ swap recurse ?dup if lf-tconvert-leave exit then
  3 lf-tconvert@ 5 lf-tconvert@ recurse lf-tconvert-leave ;

\ ( left left-id right right-id fuel -- status )
\ Validate both complete graphs, then compare; restore all temporary term
\ allocations on every result. Failed preflight conservatively leaves zero fuel.
: lf-tagged-convert ( left lid right rid fuel -- status )
  dup 0< if drop 2drop 2drop 0 lf-tconvert-fuel ! lf-tconvert-invalid exit then
  lf-tconvert-fuel ! lf-tconvert-rid ! lf-tconvert-right !
  lf-tconvert-lid ! lf-tconvert-left !
  lf-tconvert-left @ lf-tconvert-lid @ lf-tconvert-fuel @ lf-hterm-check
  ?dup if 0 lf-tconvert-fuel ! exit then lf-href-fuel @ lf-tconvert-fuel !
  lf-tconvert-right @ lf-tconvert-rid @ lf-tconvert-fuel @ lf-hterm-check
  ?dup if 0 lf-tconvert-fuel ! exit then lf-href-fuel @ lf-tconvert-fuel !
  lf-term-count @ lf-tconvert-start ! 0 lf-tconvert-depth !
  lf-tconvert-left @ lf-tconvert-right @ lf-tconvert-walk
  lf-tconvert-start @ lf-term-count ! ;
