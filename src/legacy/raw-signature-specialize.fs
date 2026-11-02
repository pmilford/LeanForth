\ Untrusted, session-local candidate signature metadata and specialization.
\ Load raw-declaration-index.fs and term-level-substitute.fs and dependencies.
\ This does not check or accept a declaration, type, theorem, or proof.
\ Non-reentrant; callers must not mutate arenas, index, metadata or input
\ arrays during calls. Arrays must be aligned, accessible and disjoint from
\ all arenas and scratch. Tokens are forgeable and local to this loaded image.
\ The index validates source terms in the same session caller context used
\ for actuals; source formal parameters must therefore also be in that context.
\ A metadata table cannot be restarted within one index lifetime. A new index
\ lifetime permits begin to discard old metadata; old tokens then fail.

0 constant lf-rspec-ok
1 constant lf-rspec-invalid
2 constant lf-rspec-exhausted
3 constant lf-rspec-unknown
create lf-rspec-names lf-rawdecl-capacity cells allot
create lf-rspec-types lf-rawdecl-capacity cells allot
create lf-rspec-ids lf-rawdecl-capacity cells allot
create lf-rspec-arities lf-rawdecl-capacity cells allot
create lf-rspec-formals lf-rawdecl-capacity lf-level-capacity * cells allot
variable lf-rspec-count
variable lf-rspec-token
variable lf-rspec-active
variable lf-rspec-name
variable lf-rspec-type
variable lf-rspec-id
variable lf-rspec-array
variable lf-rspec-arity
variable lf-rspec-fuel
variable lf-rspec-position-value
variable lf-rspec-terms-before
variable lf-rspec-levels-before
create lf-rspec-zero-actuals lf-level-capacity 2 * cells allot
0 lf-rspec-active ! 0 lf-rspec-count !

\ Bind an empty table to a new index lifetime. A repeated begin in the same
\ lifetime fails without changing metadata; stale/invalid indexes fail closed.
: lf-rspec-begin ( -- flag )
  lf-rawdecl-token 0= if false exit then
  lf-rspec-active @ if
    dup lf-rspec-token @ = if drop false exit then
  then
  lf-rspec-token ! 0 lf-rspec-count ! true dup lf-rspec-active ! ;

: lf-rspec-current? ( token -- flag )
  lf-rspec-active @ 0= if drop false exit then
  lf-rspec-count @ dup 0< swap lf-rawdecl-capacity > or if drop false exit then
  lf-rspec-token @ <> if false exit then
  lf-rawdecl-token 0= if false exit then lf-rspec-token @ = ;
: lf-rspec-position ( name -- position | -1 )
  lf-rspec-count @ 0 ?do
    dup i cells lf-rspec-names + @ = if drop i unloop exit then
  loop drop -1 ;
: lf-rspec-formals-at ( position -- addr )
  lf-level-capacity * cells lf-rspec-formals + ;
: lf-rspec-decl-status ( status -- status )
  case
    lf-rawdecl-ok of lf-rspec-ok endof
    lf-rawdecl-invalid of lf-rspec-invalid endof
    lf-rawdecl-exhausted of lf-rspec-exhausted endof
    lf-rawdecl-unknown of lf-rspec-unknown endof
    drop lf-rspec-invalid 0
  endcase ;
: lf-rspec-subst-status ( status -- status )
  case
    lf-tlsubst-ok of lf-rspec-ok endof
    lf-tlsubst-invalid of lf-rspec-invalid endof
    lf-tlsubst-exhausted of lf-rspec-exhausted endof
    drop lf-rspec-invalid 0
  endcase ;
\ The bounded list is copied in order only after all validation succeeds.
: lf-rspec-formals-valid? ( -- flag )
  lf-rspec-arity @ 0 ?do
    i cells lf-rspec-array @ + @ 0<= if false unloop exit then
    i 0 ?do
      i cells lf-rspec-array @ + @ j cells lf-rspec-array @ + @ = if
        false unloop unloop exit
      then
    loop
  loop true ;

\ Validate coverage by substituting the session's level zero for every formal.
\ This performs full substitution work, including allocation and fuel charges;
\ counts are restored on every result, while consumed identity serials and
\ scratch remain changed. Arena/serial exhaustion can reject an otherwise
\ adequate list. This is coverage, not proof or type validation.
: lf-rspec-coverage ( -- status )
  lf-term-count @ lf-rspec-terms-before !
  lf-level-count @ lf-rspec-levels-before !
  0 lf-level-identity 0= if lf-rspec-invalid exit then
  lf-rspec-arity @ 0 ?do
    dup i 2 * cells lf-rspec-zero-actuals + cell+ !
    0 i 2 * cells lf-rspec-zero-actuals + !
  loop drop
  lf-rspec-type @ lf-rspec-id @ lf-rspec-array @ lf-rspec-zero-actuals
  lf-rspec-arity @ lf-rspec-fuel @ lf-tlsubst lf-rspec-subst-status
  ?dup 0= if 2drop lf-rspec-ok then
  lf-rspec-terms-before @ lf-term-count !
  lf-rspec-levels-before @ lf-level-count ! ;

\ Attach formal IDs to an existing candidate, matching its exact term handle.
\ ( token name term id formals count fuel -- status )
\ A duplicate name, bad list, stale token or mismatched term is invalid.
\ Lookup and coverage each receive the supplied fuel independently. Coverage
\ may allocate temporarily; it always restores arena counts, not serials.
: lf-rspec-put ( token name term id formals count fuel -- status )
  lf-rspec-fuel ! lf-rspec-arity ! lf-rspec-array ! lf-rspec-id !
  lf-rspec-type ! lf-rspec-name !
  lf-rspec-current? 0= if lf-rspec-invalid exit then
  lf-rspec-fuel @ 0< lf-rspec-arity @ 0< or
  lf-rspec-arity @ lf-level-capacity > or if lf-rspec-invalid exit then
  lf-rspec-name @ lf-rspec-position 0>= if lf-rspec-invalid exit then
  lf-rspec-count @ lf-rawdecl-capacity >= if lf-rspec-exhausted exit then
  lf-rspec-formals-valid? 0= if lf-rspec-invalid exit then
  lf-rspec-name @ lf-rspec-fuel @ lf-rawdecl-find lf-rspec-decl-status
  ?dup if >r 2drop r> exit then
  lf-rspec-id @ <> swap lf-rspec-type @ <> or if lf-rspec-invalid exit then
  lf-rspec-coverage ?dup if exit then
  lf-rspec-name @ lf-rspec-count @ cells lf-rspec-names + !
  lf-rspec-type @ lf-rspec-count @ cells lf-rspec-types + !
  lf-rspec-id @ lf-rspec-count @ cells lf-rspec-ids + !
  lf-rspec-arity @ lf-rspec-count @ cells lf-rspec-arities + !
  lf-rspec-array @ lf-rspec-count @ lf-rspec-formals-at
  lf-rspec-arity @ cells move
  1 lf-rspec-count +! lf-rspec-ok ;

\ ( token name actual-handles count fuel -- result id 0 | status )
\ Exact arity is required, including unused formals. Each actual is an
\ (index, identity) pair in caller scope. Lookup and substitution each receive
\ the supplied fuel independently. Substitution rolls back allocation counts
\ on failure; identity serials and scratch are not rolled back.
: lf-rspec-specialize ( token name actual-handles count fuel -- result id 0 | status )
  lf-rspec-fuel ! lf-rspec-arity ! lf-rspec-array ! lf-rspec-name !
  lf-rspec-current? 0= if lf-rspec-invalid exit then
  lf-rspec-fuel @ 0< lf-rspec-arity @ 0< or
  lf-rspec-arity @ lf-level-capacity > or if lf-rspec-invalid exit then
  lf-rspec-name @ lf-rspec-position dup 0< if drop lf-rspec-unknown exit then
  lf-rspec-position-value !
  lf-rspec-arity @ lf-rspec-position-value @ cells lf-rspec-arities + @ <>
  if lf-rspec-invalid exit then
  lf-rspec-name @ lf-rspec-fuel @ lf-rawdecl-find lf-rspec-decl-status
  ?dup if >r 2drop r> exit then
  lf-rspec-position-value @ cells lf-rspec-ids + @ <>
  swap lf-rspec-position-value @ cells lf-rspec-types + @ <> or
  if lf-rspec-invalid exit then
  lf-rspec-position-value @ cells lf-rspec-types + @
  lf-rspec-position-value @ cells lf-rspec-ids + @
  lf-rspec-position-value @ lf-rspec-formals-at lf-rspec-array @
  lf-rspec-arity @ lf-rspec-fuel @ lf-tlsubst lf-rspec-subst-status ;
