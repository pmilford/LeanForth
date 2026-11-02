\ Untrusted, single-threaded diagnostic; load the dependencies used by
\ constant-application-oracle.fs first. No proof or declaration is checked or
\ registered. A result is conditional on the unchecked candidate signature.
\ No mutation, reset, reentrancy or access to scratch is permitted during a call.
\ Handles/tokens are forgeable session-local diagnostics, not capabilities.

0 constant lf-caprobe-ok
1 constant lf-caprobe-invalid
2 constant lf-caprobe-exhausted
3 constant lf-caprobe-unknown
\ Independent fixed visit budgets: each preflight, candidate boundary, each
\ signature lookup/substitution, candidate scope, beta, inference, conversion and instantiation
\ receives 10000; each dependency defines its own internal sharing of that fuel.
10000 constant lf-caprobe-budget
variable lf-caprobe-token
variable lf-caprobe-root
variable lf-caprobe-root-id
variable lf-caprobe-arg
variable lf-caprobe-arg-id
variable lf-caprobe-terms
variable lf-caprobe-levels
variable lf-caprobe-domain
variable lf-caprobe-body

\ Closed-scope traversal of an already audited ordinary symbolic graph. Work
\ items carry binder depth because a shared node may occur under different
\ binders. Every visit costs fuel; capacity or fuel failure is exhaustion.
create lf-caprobe-scope-work lf-term-capacity 2 * cells allot
variable lf-caprobe-scope-pending
variable lf-caprobe-scope-fuel
variable lf-caprobe-scope-node
variable lf-caprobe-scope-depth
variable lf-caprobe-scope-first
variable lf-caprobe-scope-second
variable lf-caprobe-scope-tag
: lf-caprobe-scope-push ( node depth -- flag )
  lf-caprobe-scope-pending @ lf-term-capacity >= if 2drop false exit then
  lf-caprobe-scope-pending @ 2 * cells lf-caprobe-scope-work + >r
  r@ cell+ ! r> ! 1 lf-caprobe-scope-pending +! true ;
: lf-caprobe-scope-visit ( -- status )
  lf-caprobe-scope-node @ lf-term-read 0= if lf-caprobe-invalid exit then
  lf-caprobe-scope-second ! lf-caprobe-scope-first ! lf-caprobe-scope-tag !
  lf-caprobe-scope-tag @ lf-tag-symbolic-sort = if lf-caprobe-ok exit then
  lf-caprobe-scope-tag @ lf-tag-bvar = if
    lf-caprobe-scope-first @ 0<
    lf-caprobe-scope-first @ lf-caprobe-scope-depth @ >= or if
      lf-caprobe-invalid else lf-caprobe-ok then exit
  then
  lf-caprobe-scope-tag @ lf-tag-app = lf-caprobe-scope-tag @ lf-tag-lam = or
  lf-caprobe-scope-tag @ lf-tag-pi = or 0= if lf-caprobe-invalid exit then
  lf-caprobe-scope-first @ lf-caprobe-scope-depth @ lf-caprobe-scope-push 0= if
    lf-caprobe-exhausted exit then
  lf-caprobe-scope-second @ lf-caprobe-scope-depth @
  lf-caprobe-scope-tag @ lf-tag-app <> if 1+ then
  lf-caprobe-scope-push 0= if lf-caprobe-exhausted exit then
  lf-caprobe-ok ;
\ The graph must first pass lf-hterm-check; no allocations occur here.
: lf-caprobe-closed ( root fuel -- status )
  dup 0< if 2drop lf-caprobe-invalid exit then lf-caprobe-scope-fuel !
  0 lf-caprobe-scope-pending ! 0 lf-caprobe-scope-push 0= if
    lf-caprobe-exhausted exit then
  begin lf-caprobe-scope-pending @ 0> while
    lf-caprobe-scope-fuel @ 0= if lf-caprobe-exhausted exit then
    -1 lf-caprobe-scope-fuel +! -1 lf-caprobe-scope-pending +!
    lf-caprobe-scope-pending @ 2 * cells lf-caprobe-scope-work +
    dup @ lf-caprobe-scope-node ! cell+ @ lf-caprobe-scope-depth !
    lf-caprobe-scope-visit ?dup if exit then
  repeat lf-caprobe-ok ;

: lf-caprobe-repr-status ( status -- status )
  case
    lf-repr-ok of lf-caprobe-ok endof
    lf-repr-invalid of lf-caprobe-invalid endof
    lf-repr-exhausted of lf-caprobe-exhausted endof
    drop lf-caprobe-invalid 0
  endcase ;
: lf-caprobe-candidate-status ( status -- status )
  case
    lf-rspec-ok of lf-caprobe-ok endof
    lf-rspec-invalid of lf-caprobe-invalid endof
    lf-rspec-exhausted of lf-caprobe-exhausted endof
    lf-rspec-unknown of lf-caprobe-unknown endof
    drop lf-caprobe-invalid 0
  endcase ;
: lf-caprobe-infer-status ( status -- status )
  case
    lf-tinfer-ok of lf-caprobe-ok endof
    lf-tinfer-invalid of lf-caprobe-invalid endof
    lf-tinfer-exhausted of lf-caprobe-exhausted endof
    lf-tinfer-unknown of lf-caprobe-unknown endof
    drop lf-caprobe-invalid 0
  endcase ;
: lf-caprobe-convert-status ( status -- status )
  case
    lf-tconvert-equal of lf-caprobe-ok endof
    lf-tconvert-invalid of lf-caprobe-invalid endof
    lf-tconvert-exhausted of lf-caprobe-exhausted endof
    lf-tconvert-unknown of lf-caprobe-unknown endof
    drop lf-caprobe-invalid 0
  endcase ;
: lf-caprobe-beta-status ( status -- status )
  case
    lf-tbeta-ok of lf-caprobe-ok endof
    lf-tbeta-invalid of lf-caprobe-invalid endof
    lf-tbeta-exhausted of lf-caprobe-exhausted endof
    drop lf-caprobe-invalid 0
  endcase ;
: lf-caprobe-inst-status ( status -- status )
  case
    lf-tinst-ok of lf-caprobe-ok endof
    lf-tinst-invalid of lf-caprobe-invalid endof
    lf-tinst-exhausted of lf-caprobe-exhausted endof
    drop lf-caprobe-invalid 0
  endcase ;

\ Internal worker: returns ( term identity ok | status ). Ordinary argument
\ audit excludes constants anywhere in its graph; inference enforces closure.
: lf-caprobe-work ( -- term identity 0 | status )
  lf-caprobe-root @ lf-caprobe-root-id @ lf-caprobe-budget lf-cterm-check
  lf-caprobe-repr-status ?dup if exit then
  lf-caprobe-arg @ lf-caprobe-arg-id @ lf-caprobe-budget lf-hterm-check
  lf-caprobe-repr-status ?dup if exit then
  lf-caprobe-token @ lf-caprobe-root @ lf-caprobe-root-id @
  lf-caprobe-budget lf-caprobe-budget lf-cttype-probe
  lf-caprobe-candidate-status ?dup if exit then
  2dup lf-caprobe-budget lf-hterm-check lf-caprobe-repr-status
  ?dup if >r 2drop r> exit then
  over lf-caprobe-budget lf-caprobe-closed
  ?dup if >r 2drop r> exit then
  lf-caprobe-budget lf-tagged-beta lf-caprobe-beta-status
  ?dup if >r 2drop r> exit then
  drop lf-term-read 0= if lf-caprobe-invalid exit then
  lf-caprobe-body ! lf-caprobe-domain !
  lf-tag-pi <> if lf-caprobe-unknown exit then
  lf-caprobe-arg @ lf-caprobe-arg-id @ lf-caprobe-budget lf-tinfer
  lf-caprobe-infer-status ?dup if >r 2drop r> exit then
  lf-caprobe-domain @ dup lf-term-identity 0= if
    drop 2drop lf-caprobe-invalid exit
  then
  lf-caprobe-budget lf-tagged-convert lf-caprobe-convert-status
  ?dup if exit then
  lf-caprobe-body @ dup lf-term-identity 0= if
    drop lf-caprobe-invalid exit
  then
  lf-caprobe-arg @ lf-caprobe-arg-id @ lf-caprobe-budget lf-tagged-instantiate
  lf-caprobe-inst-status ?dup if >r 2drop r> exit then
  lf-caprobe-ok ;

\ ( token constant constant-id argument argument-id -- result id status )
\ Arguments containing constants anywhere are invalid, even when otherwise
\ structurally valid. Candidate signatures must be closed; this is not typing.
\ Failure returns -1 0 and invalid, exhausted, or unknown. Snapshot both
\ arenas before any operation can allocate. Every failure restores counts,
\ never serials; success retains allocations including intermediate nodes.
: lf-constant-application-probe ( token root root-id arg arg-id -- result id status )
  lf-caprobe-arg-id ! lf-caprobe-arg ! lf-caprobe-root-id !
  lf-caprobe-root ! lf-caprobe-token !
  lf-term-count @ lf-caprobe-terms ! lf-level-count @ lf-caprobe-levels !
  lf-caprobe-work dup if
    lf-caprobe-terms @ lf-term-count ! lf-caprobe-levels @ lf-level-count !
    -1 0 rot
  then ;
