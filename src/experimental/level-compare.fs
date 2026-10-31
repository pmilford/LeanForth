\ Untrusted conservative equality experiment for Lean-style level graphs.
\ Equal is only an experimental diagnostic, never a theorem or type judgment.
\ It assumes a single immutable-during-call arena and context, and that equal
\ opaque parameter IDs denote the same Lean name. Global state is non-reentrant.
\ The caller must include levels.fs, level-scope.fs and level-value.fs first.

0 constant lf-lcmp-equal
1 constant lf-lcmp-invalid
2 constant lf-lcmp-exhausted
3 constant lf-lcmp-unknown
6 constant lf-lcmp-frame-cells
create lf-lcmp-frames lf-level-capacity lf-lcmp-frame-cells * cells allot
variable lf-lcmp-depth
variable lf-lcmp-fuel
variable lf-lcmp-left
variable lf-lcmp-right
variable lf-lcmp-concrete
variable lf-lcmp-shrink-tag
variable lf-lcmp-shrink-first
variable lf-lcmp-shrink-second

\ Address the active comparison frame; callers must hold an active frame.
: lf-lcmp-frame ( -- addr )
  lf-lcmp-depth @ 1- lf-lcmp-frame-cells * cells lf-lcmp-frames + ;
\ Read and write fields in the active comparison frame.
: lf-lcmp@ ( offset -- value ) cells lf-lcmp-frame + @ ;
: lf-lcmp! ( value offset -- ) cells lf-lcmp-frame + ! ;
\ Pop a frame while preserving the comparison status.
: lf-lcmp-leave ( status -- status ) -1 lf-lcmp-depth +! ;

\ Explicitly translate helper statuses; unexpected values fail closed.
: lf-lcmp-scope-status ( status -- status )
  case
    lf-lscope-ok of lf-lcmp-equal endof
    lf-lscope-invalid of lf-lcmp-invalid endof
    lf-lscope-exhausted of lf-lcmp-exhausted endof
    drop lf-lcmp-invalid 0
  endcase ;
: lf-lcmp-value-status ( status -- status )
  case
    lf-lvalue-ok of lf-lcmp-equal endof
    lf-lvalue-invalid of lf-lcmp-invalid endof
    lf-lvalue-exhausted of lf-lcmp-exhausted endof
    lf-lvalue-unknown of lf-lcmp-unknown endof
    drop lf-lcmp-invalid 0
  endcase ;

\ Reduce only literal-zero level identities. Both inputs were completely
\ scope-checked first; each rewrite points to an earlier node and costs fuel.
\ This is not general Lean universe normalization.
: lf-lcmp-shrink ( node -- node status )
  begin
    lf-lcmp-fuel @ 0= if drop -1 lf-lcmp-exhausted exit then
    -1 lf-lcmp-fuel +!
    dup lf-level-read 0= if drop -1 lf-lcmp-invalid exit then
    lf-lcmp-shrink-second ! lf-lcmp-shrink-first ! lf-lcmp-shrink-tag !
    lf-lcmp-shrink-tag @ lf-level-tag-max = if
      lf-lcmp-shrink-first @ 0= if
        drop lf-lcmp-shrink-second @
      else lf-lcmp-shrink-second @ 0= if
        drop lf-lcmp-shrink-first @
      else lf-lcmp-equal exit then then
    else lf-lcmp-shrink-tag @ lf-level-tag-imax =
         lf-lcmp-shrink-second @ 0= and if
      drop 0
    else lf-lcmp-equal exit then then
  again ;

\ Compare syntax after both roots have passed scope validation. Work and
\ recursion are bounded; any unmatched constructor or ID is unknown.
: lf-lcmp-walk ( left right -- status )
  lf-lcmp-fuel @ 0= lf-lcmp-depth @ lf-level-capacity >= or if
    2drop lf-lcmp-exhausted exit
  then
  -1 lf-lcmp-fuel +! 1 lf-lcmp-depth +!
  lf-lcmp-shrink dup if nip nip lf-lcmp-leave exit then drop
  swap lf-lcmp-shrink dup if nip nip lf-lcmp-leave exit then drop swap
  lf-level-read 0= if drop lf-lcmp-invalid lf-lcmp-leave exit then
  5 lf-lcmp! 4 lf-lcmp! 3 lf-lcmp!
  lf-level-read 0= if lf-lcmp-invalid lf-lcmp-leave exit then
  2 lf-lcmp! 1 lf-lcmp! 0 lf-lcmp!
  0 lf-lcmp@ 3 lf-lcmp@ <> if lf-lcmp-unknown lf-lcmp-leave exit then
  0 lf-lcmp@ lf-level-tag-zero = if lf-lcmp-equal lf-lcmp-leave exit then
  0 lf-lcmp@ lf-level-tag-param = if
    1 lf-lcmp@ 4 lf-lcmp@ = if lf-lcmp-equal else lf-lcmp-unknown then
    lf-lcmp-leave exit
  then
  1 lf-lcmp@ 4 lf-lcmp@ recurse ?dup if lf-lcmp-leave exit then
  0 lf-lcmp@ lf-level-tag-succ = if lf-lcmp-equal lf-lcmp-leave exit then
  2 lf-lcmp@ 5 lf-lcmp@ recurse lf-lcmp-leave ;

\ If syntax did not match, independently evaluate both unassigned concrete
\ graphs. Unequal or symbolic values are unknown, never an inequality verdict.
: lf-lcmp-concrete-fallback ( -- status )
  lf-lcmp-left @ lf-lcmp-fuel @ lf-level-value lf-lcmp-value-status
  ?dup if nip 0 lf-lcmp-fuel ! exit then lf-lcmp-concrete !
  lf-lvalue-fuel @ lf-lcmp-fuel !
  lf-lcmp-right @ lf-lcmp-fuel @ lf-level-value lf-lcmp-value-status
  ?dup if nip 0 lf-lcmp-fuel ! exit then
  lf-lvalue-fuel @ lf-lcmp-fuel !
  lf-lcmp-concrete @ = if lf-lcmp-equal else lf-lcmp-unknown then ;

\ Compare two roots against one explicit parameter context. Scope checks run
\ before any equality shortcut and share fuel with comparison and evaluation.
\ Only one status is returned; this word cannot register a declaration.
: lf-level-compare ( left right fuel -- status )
  dup 0< if drop 2drop 0 lf-lcmp-fuel ! lf-lcmp-invalid exit then lf-lcmp-fuel !
  lf-lcmp-right ! lf-lcmp-left !
  lf-lcmp-left @ lf-lcmp-fuel @ lf-lscope-check lf-lcmp-scope-status
  ?dup if 0 lf-lcmp-fuel ! exit then lf-lscope-fuel @ lf-lcmp-fuel !
  lf-lcmp-right @ lf-lcmp-fuel @ lf-lscope-check lf-lcmp-scope-status
  ?dup if 0 lf-lcmp-fuel ! exit then lf-lscope-fuel @ lf-lcmp-fuel !
  0 lf-lcmp-depth ! lf-lcmp-left @ lf-lcmp-right @ lf-lcmp-walk
  dup lf-lcmp-unknown = if drop lf-lcmp-concrete-fallback
  else dup if 0 lf-lcmp-fuel ! then then ;
