\ UNSAFE DRAFT: concrete and symbolic Sort encodings are not isolated.
\ Excluded from the standard test suite. Do not use with concrete inference.
\ Untrusted symbolic-universe inference experiment; not a trusted kernel.
\ Success returns a mutable term index, not a theorem or proof certificate.
\ This prototype has not received the review required for a trusted kernel.
\ Every Sort payload is interpreted as an index into the separate level DAG,
\ not as the concrete level used by infer.fs. Never mix the two encodings.
\ Global mutable arenas, context identity, host cells and bounded recursion
\ are assumptions; callers must prevent concurrent mutation and stale IDs.
include compare.fs
include scope.fs
include levels.fs
include level-scope.fs

0 constant lf-sinfer-ok
1 constant lf-sinfer-invalid
2 constant lf-sinfer-exhausted
3 constant lf-sinfer-unknown
6 constant lf-sinfer-frame-cells
create lf-sinfer-frames lf-term-capacity lf-sinfer-frame-cells * cells allot
create lf-sinfer-context lf-term-capacity cells allot
variable lf-sinfer-level
variable lf-sinfer-depth
variable lf-sinfer-fuel
variable lf-sinfer-start
variable lf-sinfer-level-start

\ Locate an inference frame; callers must supply an in-range frame index.
: lf-sinfer-frame ( level -- addr )
  lf-sinfer-frame-cells * cells lf-sinfer-frames + ;
\ Return the currently active frame, which must already exist.
: lf-sinfer-current ( -- addr ) lf-sinfer-level @ 1- lf-sinfer-frame ;
\ Read or write a numbered field of the active inference frame.
: lf-sinfer@ ( offset -- value ) cells lf-sinfer-current + @ ;
: lf-sinfer! ( value offset -- ) cells lf-sinfer-current + ! ;
\ Pop the active frame without consuming its result or status.
: lf-sinfer-leave ( result status -- result status ) -1 lf-sinfer-level +! ;

\ Extend the local context with a domain represented in the previous context.
: lf-sinfer-push ( domain -- flag )
  lf-sinfer-depth @ lf-term-capacity >= if drop false exit then
  lf-sinfer-depth @ cells lf-sinfer-context + !
  1 lf-sinfer-depth +! true ;
\ Remove an existing context entry after finishing its binder body.
: lf-sinfer-pop ( -- ) -1 lf-sinfer-depth +! ;

\ Run a supporting experimental operation with the remaining shared budget.
: lf-sinfer-whnf ( node -- result status )
  lf-sinfer-fuel @ lf-beta-whnf lf-beta-fuel @ lf-sinfer-fuel ! ;
: lf-sinfer-shift ( node amount -- result status )
  0 swap lf-sinfer-fuel @ lf-shift lf-shift-fuel @ lf-sinfer-fuel ! ;
: lf-sinfer-inst ( body argument -- result status )
  lf-sinfer-fuel @ lf-instantiate lf-inst-fuel @ lf-sinfer-fuel ! ;
: lf-sinfer-compare ( left right -- status )
  lf-sinfer-fuel @ lf-compare lf-compare-fuel @ lf-sinfer-fuel ! ;

\ Reduce an inferred type and extract its symbolic level index, or return an
\ explicit failure. Non-sort results remain unknown, not a theorem judgment.
: lf-sinfer-sortlevel ( node -- level status )
  lf-sinfer-whnf dup if exit then drop
  lf-term-read 0= if -1 lf-sinfer-invalid exit then
  drop swap lf-tag-sort <> if drop -1 lf-sinfer-unknown exit then
  lf-sinfer-ok ;

\ Construct the concrete-zero case of imax directly. Inputs originate from
\ checked level graphs; this never discards an unchecked parameter branch.
: lf-sinfer-imax ( domain-level body-level -- level status )
  dup 0= if 2drop 0 lf-sinfer-ok exit then
  lf-level-imax lf-shift-allocated ;

\ Map structural level statuses without relying on numeric coincidence.
: lf-sinfer-level-status ( status -- status )
  case
    lf-lscope-ok of lf-sinfer-ok endof
    lf-lscope-invalid of lf-sinfer-invalid endof
    lf-lscope-exhausted of lf-sinfer-exhausted endof
    drop lf-sinfer-invalid 0
  endcase ;

\ Conservatively validate every Sort payload in the original term arena,
\ including unused nodes. This is bounded but may reject an otherwise usable
\ root because unrelated data is invalid. Every level visit consumes fuel.
: lf-sinfer-levels-preflight ( -- status )
  lf-level-count-valid? lf-lscope-context-valid? and 0= if lf-sinfer-invalid exit then
  lf-term-count @ 0 ?do
    i lf-term-read 0= if lf-sinfer-invalid unloop exit then
    drop swap lf-tag-sort = if
      lf-sinfer-fuel @ lf-lscope-check lf-sinfer-level-status
      dup if unloop exit then drop
      lf-lscope-fuel @ lf-sinfer-fuel !
    else drop then
  loop lf-sinfer-ok ;

\ Infer one original input node in the current context. Results are appended
\ to the arena and may include original nodes. Every inference visit consumes
\ fuel; called operations consume the same budget and may also exhaust memory.
: lf-sinfer-walk ( node -- type status )
  lf-sinfer-fuel @ 0= lf-sinfer-level @ lf-term-capacity >= or if
    drop -1 lf-sinfer-exhausted exit
  then
  -1 lf-sinfer-fuel +!
  lf-sinfer-level @ lf-sinfer-frame ! 1 lf-sinfer-level +!
  0 lf-sinfer@ dup 0< swap lf-sinfer-start @ >= or if
    -1 lf-sinfer-invalid lf-sinfer-leave exit
  then
  0 lf-sinfer@ lf-term-read 0= if -1 lf-sinfer-invalid lf-sinfer-leave exit then
  3 lf-sinfer! 2 lf-sinfer! 1 lf-sinfer!
  1 lf-sinfer@ lf-tag-sort = if
    2 lf-sinfer@ lf-level-succ lf-shift-allocated
    dup if lf-sinfer-leave exit then drop
    lf-term-sort lf-shift-allocated lf-sinfer-leave exit
  then
  1 lf-sinfer@ lf-tag-bvar = if
    2 lf-sinfer@ lf-sinfer-depth @ >= if
      -1 lf-sinfer-invalid lf-sinfer-leave exit
    then
    lf-sinfer-depth @ 1- 2 lf-sinfer@ - cells lf-sinfer-context + @
    2 lf-sinfer@ 1+ lf-sinfer-shift lf-sinfer-leave exit
  then
  1 lf-sinfer@ lf-tag-lam = 1 lf-sinfer@ lf-tag-pi = or if
    2 lf-sinfer@ recurse dup if lf-sinfer-leave exit then drop
    lf-sinfer-sortlevel dup if lf-sinfer-leave exit then drop 4 lf-sinfer!
    2 lf-sinfer@ lf-sinfer-push 0= if
      -1 lf-sinfer-exhausted lf-sinfer-leave exit
    then
    3 lf-sinfer@ recurse lf-sinfer-pop
    dup if lf-sinfer-leave exit then drop
    1 lf-sinfer@ lf-tag-lam = if
      2 lf-sinfer@ swap lf-term-pi lf-shift-allocated lf-sinfer-leave exit
    then
    lf-sinfer-sortlevel dup if lf-sinfer-leave exit then drop
    4 lf-sinfer@ swap lf-sinfer-imax
    dup if lf-sinfer-leave exit then drop
    lf-term-sort lf-shift-allocated lf-sinfer-leave exit
  then
  1 lf-sinfer@ lf-tag-app = if
    2 lf-sinfer@ recurse dup if lf-sinfer-leave exit then drop
    lf-sinfer-whnf dup if lf-sinfer-leave exit then drop
    lf-term-read 0= if -1 lf-sinfer-invalid lf-sinfer-leave exit then
    5 lf-sinfer! 4 lf-sinfer!
    lf-tag-pi <> if -1 lf-sinfer-unknown lf-sinfer-leave exit then
    3 lf-sinfer@ recurse dup if lf-sinfer-leave exit then drop
    4 lf-sinfer@ lf-sinfer-compare
    ?dup if -1 swap lf-sinfer-leave exit then
    5 lf-sinfer@ 3 lf-sinfer@ lf-sinfer-inst lf-sinfer-leave exit
  then
  -1 lf-sinfer-invalid lf-sinfer-leave ;

\ Infer a closed root with a finite visit budget. Structural validation is
\ performed first, including a complete scope traversal. On any failure the
\ counts for both arenas are restored. Success returns mutable data only and
\ cannot authorize a LeanForth theorem. Temporary allocations persist on success.
: lf-sinfer ( root fuel -- type status )
  dup 0< if 2drop -1 lf-sinfer-invalid exit then lf-sinfer-fuel !
  lf-term-count-valid? 0= if drop -1 lf-sinfer-invalid exit then
  dup lf-term-valid? 0= if drop -1 lf-sinfer-invalid exit then
  dup lf-sinfer-fuel @ lf-scope-check lf-scope-fuel @ lf-sinfer-fuel !
  ?dup if nip -1 swap exit then
  lf-sinfer-levels-preflight ?dup if nip -1 swap exit then
  lf-term-count @ lf-sinfer-start !
  lf-level-count @ lf-sinfer-level-start !
  dup 0 0 lf-sinfer-fuel @ lf-shift
  lf-shift-fuel @ lf-sinfer-fuel !
  dup if nip nip -1 swap exit then 2drop
  lf-sinfer-start @ lf-term-count !
  0 lf-sinfer-level ! 0 lf-sinfer-depth !
  lf-sinfer-walk
  dup if
    lf-sinfer-start @ lf-term-count !
    lf-sinfer-level-start @ lf-level-count !
  then ;
