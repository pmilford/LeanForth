\ Untrusted, bounded diagnostic for a constant with ordinary closed arguments.
\ Load constant-application-probe.fs and its dependencies first. A successful
\ result is conditional on an unchecked candidate signature: it is not a
\ declaration, typing judgment, proof or theorem. Global state is single-
\ threaded and non-reentrant; callers must prevent mutation during a call.
\ The caller-owned array contains count (term-index, identity) cell pairs;
\ it must be readable, aligned and disjoint from all arenas and scratch.
\ Nested constants in arguments and candidate types are unsupported and may
\ report invalid, even when the corresponding Lean expression is valid.

8 constant lf-spine-capacity
variable lf-spine-token
variable lf-spine-root
variable lf-spine-root-id
variable lf-spine-array
variable lf-spine-count
variable lf-spine-terms
variable lf-spine-levels
variable lf-spine-type
variable lf-spine-type-id
variable lf-spine-domain
variable lf-spine-body
variable lf-spine-arg
variable lf-spine-arg-id

\ Fetch a caller-supplied pair. The position and readable storage are checked
\ or guaranteed by the calling contract before this helper is used.
: lf-spine-argument ( position -- index identity )
  2 * cells lf-spine-array @ + dup @ swap cell+ @ ;

\ Audit every argument before any operation allocates, so a bad later handle
\ cannot become live because earlier work happened to allocate its slot.
: lf-spine-audit ( -- status )
  lf-spine-count @ 0 ?do
    i lf-spine-argument lf-caprobe-budget lf-hterm-check
    lf-caprobe-repr-status ?dup if unloop exit then
    i lf-spine-argument drop lf-caprobe-budget lf-caprobe-closed
    ?dup if unloop exit then
  loop lf-caprobe-ok ;

\ Instantiate the current Pi with one already-audited closed argument.
\ Each dependency gets its own fixed bounded budget, as in the single-arg
\ probe. Unsupported conversion returns unknown rather than success.
: lf-spine-step ( position -- status )
  lf-spine-argument lf-spine-arg-id ! lf-spine-arg !
  lf-spine-type @ lf-spine-type-id @ lf-caprobe-budget lf-tagged-beta
  lf-caprobe-beta-status ?dup if >r 2drop r> exit then
  drop lf-term-read 0= if lf-caprobe-invalid exit then
  lf-spine-body ! lf-spine-domain !
  lf-tag-pi <> if lf-caprobe-unknown exit then
  lf-spine-arg @ lf-spine-arg-id @ lf-caprobe-budget lf-tinfer
  lf-caprobe-infer-status ?dup if >r 2drop r> exit then
  lf-spine-domain @ dup lf-term-identity 0= if
    drop 2drop lf-caprobe-invalid exit
  then
  lf-caprobe-budget lf-tagged-convert lf-caprobe-convert-status ?dup if exit then
  lf-spine-body @ dup lf-term-identity 0= if drop lf-caprobe-invalid exit then
  lf-spine-arg @ lf-spine-arg-id @ lf-caprobe-budget lf-tagged-instantiate
  lf-caprobe-inst-status ?dup if >r 2drop r> exit then
  lf-spine-type-id ! lf-spine-type ! lf-caprobe-ok ;

\ Obtain and audit the specialized candidate before processing arguments.
: lf-spine-work ( -- term identity 0 | status )
  lf-spine-audit ?dup if exit then
  lf-spine-token @ lf-spine-root @ lf-spine-root-id @
  lf-caprobe-budget lf-caprobe-budget lf-cttype-probe
  lf-caprobe-candidate-status ?dup if exit then
  2dup lf-caprobe-budget lf-hterm-check lf-caprobe-repr-status
  ?dup if >r 2drop r> exit then
  over lf-caprobe-budget lf-caprobe-closed ?dup if >r 2drop r> exit then
  lf-spine-type-id ! lf-spine-type !
  lf-spine-count @ 0 ?do i lf-spine-step ?dup if unloop exit then loop
  lf-spine-type @ lf-spine-type-id @ lf-caprobe-ok ;

\ ( token root root-id array count -- result identity status )
\ Up to eight arguments are supported; zero leaves the candidate unchanged.
\ On any failure return -1 0 status and restore both arena counts; identity
\ serials and scratch are not restored. Success retains intermediate nodes.
: lf-constant-spine-probe ( token root root-id array count -- result id status )
  dup 0< over lf-spine-capacity > or if
    drop 2drop 2drop -1 0 lf-caprobe-invalid exit
  then
  lf-spine-count ! lf-spine-array ! lf-spine-root-id ! lf-spine-root ! lf-spine-token !
  lf-term-count @ lf-spine-terms ! lf-level-count @ lf-spine-levels !
  lf-spine-work dup if
    lf-spine-terms @ lf-term-count ! lf-spine-levels @ lf-level-count ! -1 0 rot
  then ;
