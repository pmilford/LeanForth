\ Untrusted type-inference experiment for a narrow concrete-universe fragment.
\ Success returns a mutable term index, not a theorem or proof certificate.
\ This prototype has not received the review required for a trusted kernel.
\ Its global mutable state, host cells and bounded host recursion are assumed;
\ callers must prevent concurrent mutation and discard handles after reset.
include compare.fs
include scope.fs

0 constant lf-infer-ok
1 constant lf-infer-invalid
2 constant lf-infer-exhausted
3 constant lf-infer-unknown
6 constant lf-infer-frame-cells
create lf-infer-frames lf-term-capacity lf-infer-frame-cells * cells allot
create lf-infer-context lf-term-capacity cells allot
variable lf-infer-level
variable lf-infer-depth
variable lf-infer-fuel
variable lf-infer-start

\ Locate an inference frame; callers must supply an in-range frame index.
: lf-infer-frame ( level -- addr )
  lf-infer-frame-cells * cells lf-infer-frames + ;
\ Return the currently active frame, which must already exist.
: lf-infer-current ( -- addr ) lf-infer-level @ 1- lf-infer-frame ;
\ Read or write a numbered field of the active inference frame.
: lf-infer@ ( offset -- value ) cells lf-infer-current + @ ;
: lf-infer! ( value offset -- ) cells lf-infer-current + ! ;
\ Pop the active frame without consuming its result or status.
: lf-infer-leave ( result status -- result status ) -1 lf-infer-level +! ;

\ Extend the local context with a domain represented in the previous context.
: lf-infer-push ( domain -- flag )
  lf-infer-depth @ lf-term-capacity >= if drop false exit then
  lf-infer-depth @ cells lf-infer-context + !
  1 lf-infer-depth +! true ;
\ Remove an existing context entry after finishing its binder body.
: lf-infer-pop ( -- ) -1 lf-infer-depth +! ;

\ Run a supporting experimental operation with the remaining shared budget.
: lf-infer-whnf ( node -- result status )
  lf-infer-fuel @ lf-beta-whnf lf-beta-fuel @ lf-infer-fuel ! ;
: lf-infer-shift ( node amount -- result status )
  0 swap lf-infer-fuel @ lf-shift lf-shift-fuel @ lf-infer-fuel ! ;
: lf-infer-inst ( body argument -- result status )
  lf-infer-fuel @ lf-instantiate lf-inst-fuel @ lf-infer-fuel ! ;
: lf-infer-compare ( left right -- status )
  lf-infer-fuel @ lf-compare lf-compare-fuel @ lf-infer-fuel ! ;

\ Reduce an inferred type and extract its concrete sort level, or return an
\ explicit failure. Non-sort results remain unknown, not a theorem judgment.
: lf-infer-sortlevel ( node -- level status )
  lf-infer-whnf dup if exit then drop
  lf-term-read 0= if -1 lf-infer-invalid exit then
  drop swap lf-tag-sort <> if drop -1 lf-infer-unknown exit then
  lf-infer-ok ;

\ Infer one original input node in the current context. Results are appended
\ to the arena and may include original nodes. Every inference visit consumes
\ fuel; called operations consume the same budget and may also exhaust memory.
: lf-infer-walk ( node -- type status )
  lf-infer-fuel @ 0= lf-infer-level @ lf-term-capacity >= or if
    drop -1 lf-infer-exhausted exit
  then
  -1 lf-infer-fuel +!
  lf-infer-level @ lf-infer-frame ! 1 lf-infer-level +!
  0 lf-infer@ dup 0< swap lf-infer-start @ >= or if
    -1 lf-infer-invalid lf-infer-leave exit
  then
  0 lf-infer@ lf-term-read 0= if -1 lf-infer-invalid lf-infer-leave exit then
  3 lf-infer! 2 lf-infer! 1 lf-infer!
  1 lf-infer@ lf-tag-sort = if
    2 lf-infer@ lf-shift-cell-max = if
      -1 lf-infer-exhausted lf-infer-leave exit
    then
    2 lf-infer@ 1+ lf-term-sort lf-shift-allocated lf-infer-leave exit
  then
  1 lf-infer@ lf-tag-bvar = if
    2 lf-infer@ lf-infer-depth @ >= if
      -1 lf-infer-invalid lf-infer-leave exit
    then
    lf-infer-depth @ 1- 2 lf-infer@ - cells lf-infer-context + @
    2 lf-infer@ 1+ lf-infer-shift lf-infer-leave exit
  then
  1 lf-infer@ lf-tag-lam = 1 lf-infer@ lf-tag-pi = or if
    2 lf-infer@ recurse dup if lf-infer-leave exit then drop
    lf-infer-sortlevel dup if lf-infer-leave exit then drop 4 lf-infer!
    2 lf-infer@ lf-infer-push 0= if
      -1 lf-infer-exhausted lf-infer-leave exit
    then
    3 lf-infer@ recurse lf-infer-pop
    dup if lf-infer-leave exit then drop
    1 lf-infer@ lf-tag-lam = if
      2 lf-infer@ swap lf-term-pi lf-shift-allocated lf-infer-leave exit
    then
    lf-infer-sortlevel dup if lf-infer-leave exit then drop
    dup 0= if drop 0 else 4 lf-infer@ max then
    lf-term-sort lf-shift-allocated lf-infer-leave exit
  then
  1 lf-infer@ lf-tag-app = if
    2 lf-infer@ recurse dup if lf-infer-leave exit then drop
    lf-infer-whnf dup if lf-infer-leave exit then drop
    lf-term-read 0= if -1 lf-infer-invalid lf-infer-leave exit then
    5 lf-infer! 4 lf-infer!
    lf-tag-pi <> if -1 lf-infer-unknown lf-infer-leave exit then
    3 lf-infer@ recurse dup if lf-infer-leave exit then drop
    4 lf-infer@ lf-infer-compare
    ?dup if -1 swap lf-infer-leave exit then
    5 lf-infer@ 3 lf-infer@ lf-infer-inst lf-infer-leave exit
  then
  -1 lf-infer-invalid lf-infer-leave ;

\ Infer a closed root with a finite visit budget. Structural validation is
\ performed first, including a complete scope traversal. On any failure the
\ allocation count is restored. Success is
\ an experimental inference result and cannot authorize a LeanForth theorem.
: lf-infer ( root fuel -- type status )
  dup 0< if 2drop -1 lf-infer-invalid exit then lf-infer-fuel !
  lf-term-count-valid? 0= if drop -1 lf-infer-invalid exit then
  dup lf-term-valid? 0= if drop -1 lf-infer-invalid exit then
  dup lf-infer-fuel @ lf-scope-check lf-scope-fuel @ lf-infer-fuel !
  ?dup if nip -1 swap exit then
  lf-term-count @ lf-infer-start !
  dup 0 0 lf-infer-fuel @ lf-shift
  lf-shift-fuel @ lf-infer-fuel !
  dup if nip nip -1 swap exit then 2drop
  lf-infer-start @ lf-term-count !
  0 lf-infer-level ! 0 lf-infer-depth !
  lf-infer-walk
  dup if lf-infer-start @ lf-term-count ! then ;
