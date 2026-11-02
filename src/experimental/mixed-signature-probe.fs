\ Untrusted candidate signatures for mixed constant-bearing syntax.
\ Load mixed-level-substitute.fs and its dependencies first. No declaration,
\ binder scope, type, proof, dependency or theorem is checked or registered.
\ Candidates and all nested constant signatures are unchecked assumptions.
\ Single-threaded and non-reentrant: exclude resets, raw writes, callbacks and
\ concurrent calls. Caller arrays must be aligned, readable and disjoint from
\ arenas, contexts, index and all scratch. Handles/tokens are forgeable and
\ instance-local, not capabilities or serialized identities. Bare name IDs
\ belong to the captured name generation; callers must not reuse stale IDs.
\ Source and actual parameters must be in the same live session context.
\ A cref reset does not invalidate the index token; each use rechecks the
\ reachable references and their allocation identities. No cache is provided.

32 constant lf-msp-capacity
0 constant lf-msp-ok
1 constant lf-msp-invalid
2 constant lf-msp-exhausted
3 constant lf-msp-unknown
create lf-msp-names lf-msp-capacity cells allot
create lf-msp-roots lf-msp-capacity cells allot
create lf-msp-ids lf-msp-capacity cells allot
create lf-msp-arities lf-msp-capacity cells allot
create lf-msp-formals lf-msp-capacity lf-level-capacity * cells allot
create lf-msp-zero lf-level-capacity 2 * cells allot
variable lf-msp-count variable lf-msp-active variable lf-msp-generation
variable lf-msp-name-generation variable lf-msp-term-generation
variable lf-msp-level-generation variable lf-msp-context-generation
variable lf-msp-name variable lf-msp-root variable lf-msp-id
variable lf-msp-array variable lf-msp-arity variable lf-msp-fuel
variable lf-msp-position-value
variable lf-msp-terms variable lf-msp-levels variable lf-msp-crefs
0 lf-msp-active ! 0 lf-msp-count ! 0 lf-msp-generation !

\ Clear and start a new lifetime; every attempt consumes a generation. On
\ saturation begin fails permanently. Failure leaves the index inactive.
: lf-msp-begin ( -- flag )
  0 lf-msp-active ! 0 lf-msp-count !
  lf-msp-generation @ dup 0< if drop false exit then
  dup -1 1 rshift = if drop -1 lf-msp-generation ! false exit then
  1+ lf-msp-generation !
  lf-name-storage-valid? lf-ssession-current? and lf-cref-state-valid? and
  0= if false exit then
  lf-name-generation @ lf-msp-name-generation !
  lf-term-generation @ lf-msp-term-generation !
  lf-level-generation @ lf-msp-level-generation !
  lf-lscope-generation @ lf-msp-context-generation !
  true dup lf-msp-active ! ;

: lf-msp-current? ( token -- flag )
  lf-msp-active @ 0= if drop false exit then
  lf-msp-generation @ <> if false exit then
  lf-msp-count @ dup 0< 0= swap lf-msp-capacity <= and
  lf-name-storage-valid? and lf-ssession-current? and lf-cref-state-valid? and
  lf-name-generation @ lf-msp-name-generation @ = and
  lf-term-generation @ lf-msp-term-generation @ = and
  lf-level-generation @ lf-msp-level-generation @ = and
  lf-lscope-generation @ lf-msp-context-generation @ = and ;
\ Token denotes lifetime, not content revision; insertions do not change it.
: lf-msp-token ( -- token true | false )
  lf-msp-generation @ dup lf-msp-current? if true else drop false then ;
: lf-msp-position ( name -- position | -1 )
  lf-msp-count @ 0 ?do
    dup i cells lf-msp-names + @ = if drop i unloop exit then
  loop drop -1 ;
: lf-msp-formals-at ( position -- addr )
  lf-level-capacity * cells lf-msp-formals + ;
: lf-msp-status ( status -- status )
  case lf-mlsubst-ok of lf-msp-ok endof
    lf-mlsubst-invalid of lf-msp-invalid endof
    lf-mlsubst-exhausted of lf-msp-exhausted endof
    drop lf-msp-invalid 0 endcase ;
: lf-msp-save ( -- )
  lf-term-count @ lf-msp-terms ! lf-level-count @ lf-msp-levels !
  lf-cref-count @ lf-msp-crefs ! ;
: lf-msp-restore ( -- )
  lf-msp-terms @ lf-term-count ! lf-msp-levels @ lf-level-count !
  lf-msp-crefs @ lf-cref-count ! ;

\ Coverage uses one complete mixed substitution with zero actuals. Even on
\ success all temporary allocations are discarded, never their serials.
\ This can exhaust arena space or identity serials for an otherwise valid list.
: lf-msp-coverage ( -- status )
  lf-msp-save
  0 lf-level-identity 0= if lf-msp-invalid exit then
  lf-msp-arity @ 0 ?do
    dup i 2 * cells lf-msp-zero + cell+ !
    0 i 2 * cells lf-msp-zero + !
  loop drop
  lf-msp-root @ lf-msp-id @ lf-msp-array @ lf-msp-zero
  lf-msp-arity @ lf-msp-fuel @ lf-mixed-level-substitute lf-msp-status
  ?dup 0= if 2drop lf-msp-ok then
  lf-msp-restore ;

\ ( token name root identity formals count fuel -- status )
\ Copy ordered distinct formal IDs only after coverage succeeds. The single
\ coverage fuel is shared by the mixed substitution's full audit and build;
\ bounded index/list scans and identity checks are additional unmetered work.
\ Every failure leaves index contents and all three arena counts unchanged.
: lf-msp-put ( token name root identity formals count fuel -- status )
  lf-msp-fuel ! lf-msp-arity ! lf-msp-array ! lf-msp-id !
  lf-msp-root ! lf-msp-name !
  lf-msp-current? 0= if lf-msp-invalid exit then
  lf-msp-fuel @ 0< lf-msp-arity @ 0< or
  lf-msp-arity @ lf-level-capacity > or if lf-msp-invalid exit then
  lf-msp-name @ dup 0<= swap lf-name-valid? 0= or if lf-msp-invalid exit then
  lf-msp-name @ lf-msp-position 0>= if lf-msp-invalid exit then
  lf-msp-count @ lf-msp-capacity >= if lf-msp-exhausted exit then
  lf-msp-coverage ?dup if exit then
  lf-msp-name @ lf-msp-count @ cells lf-msp-names + !
  lf-msp-root @ lf-msp-count @ cells lf-msp-roots + !
  lf-msp-id @ lf-msp-count @ cells lf-msp-ids + !
  lf-msp-arity @ lf-msp-count @ cells lf-msp-arities + !
  lf-msp-array @ lf-msp-count @ lf-msp-formals-at
  lf-msp-arity @ cells move
  1 lf-msp-count +! lf-msp-ok ;

\ ( token name actual-pairs count fuel -- root identity 0 | status )
\ Exact arity includes unused formals. One shared substitution budget covers
\ the full audit and build; index scans and identity checks are unmetered.
\ Failure rolls back all arena counts, not allocation serials or scratch.
\ Returned syntax is conditional on unchecked metadata and is never a theorem.
: lf-msp-specialize ( token name actual-pairs count fuel -- root identity 0 | status )
  lf-msp-fuel ! lf-msp-arity ! lf-msp-array ! lf-msp-name !
  lf-msp-current? 0= if lf-msp-invalid exit then
  lf-msp-fuel @ 0< lf-msp-arity @ 0< or
  lf-msp-arity @ lf-level-capacity > or if lf-msp-invalid exit then
  lf-msp-name @ dup 0<= swap lf-name-valid? 0= or if lf-msp-invalid exit then
  lf-msp-name @ lf-msp-position dup 0< if drop lf-msp-unknown exit then
  lf-msp-position-value !
  lf-msp-arity @ lf-msp-position-value @ cells lf-msp-arities + @ <>
  if lf-msp-invalid exit then
  lf-msp-position-value @ cells lf-msp-roots + @
  lf-msp-position-value @ cells lf-msp-ids + @
  lf-msp-position-value @ lf-msp-formals-at lf-msp-array @
  lf-msp-arity @ lf-msp-fuel @ lf-mixed-level-substitute lf-msp-status ;
