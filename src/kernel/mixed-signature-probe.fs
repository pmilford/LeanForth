\ Untrusted candidate signatures for mixed constant-bearing syntax.
\ Load mixed-level-substitute.fs and its dependencies first. No declaration,
\ binder scope, type, proof, dependency or theorem is checked or registered.
\ Candidates and all nested constant signatures are unchecked assumptions.
\ Caller arrays must be aligned, readable and disjoint from arenas,
\ contexts, the index and all scratch. Handles/tokens are forgeable and
\ instance-local, not capabilities or serialized identities. Bare name IDs
\ belong to the captured name generation; callers must not reuse stale IDs.
\ Source and actual parameters must be in the same live session context.
\ A cref reset does not invalidate the index token; each use rechecks the
\ reachable references and their allocation identities. No cache is provided.
\ State: the index record lf-msp-index (lifetime, captured generations and
\ the candidate arrays) and the request record lf-msp-request (one put or
\ specialize call's arguments and the zero actuals used by coverage).
\ Single-threaded and not re-entrant: exclude resets, raw writes, callbacks
\ and concurrent calls.

32 constant lf-msp-capacity
outcome-ok constant lf-msp-ok
outcome-invalid constant lf-msp-invalid
outcome-exhausted constant lf-msp-exhausted
outcome-unknown constant lf-msp-unknown

\ The index: parallel arrays of candidate records, because callers and tests
\ address them as cell arrays (lf-msp-names, ...) and copy their prefixes.
begin-structure /lf-msi
  field: lf-msi-count                 \ records in use, 0..capacity
  field: lf-msi-active                \ true while a lifetime is open
  field: lf-msi-generation            \ lifetime counter; negative once spent
  2 cells +field lf-msi-store-gens    \ name and term generations at begin
  2 cells +field lf-msi-scope-gens    \ level and context generations at begin
  lf-msp-capacity cells +field lf-msi-names
  lf-msp-capacity cells +field lf-msi-roots
  lf-msp-capacity cells +field lf-msi-ids
  lf-msp-capacity cells +field lf-msi-arities
  lf-msp-capacity lf-level-capacity * cells +field lf-msi-formals
end-structure

\ One request. Put fills name, root, id, formals, arity and fuel; specialize
\ fills name, actuals, arity and fuel, then root, id and formals from the
\ matching record. Coverage points actuals at the zero pairs.
begin-structure /lf-msr
  field: lf-msr-name
  field: lf-msr-root
  field: lf-msr-id
  field: lf-msr-formals               \ address of arity formal IDs
  field: lf-msr-actuals               \ address of arity (index identity) pairs
  field: lf-msr-arity
  field: lf-msr-fuel
  lf-level-capacity 2* cells +field lf-msr-zeros
end-structure

create lf-msp-index /lf-msi allot
lf-msp-index /lf-msi erase
create lf-msp-request /lf-msr allot
lf-msp-request /lf-msr erase

\ The index fields under their established names (tests and stream fixtures
\ read the arrays and the count).
: lf-msp-count ( -- addr ) lf-msp-index lf-msi-count ;
: lf-msp-active ( -- addr ) lf-msp-index lf-msi-active ;
: lf-msp-generation ( -- addr ) lf-msp-index lf-msi-generation ;
: lf-msp-names ( -- addr ) lf-msp-index lf-msi-names ;
: lf-msp-roots ( -- addr ) lf-msp-index lf-msi-roots ;
: lf-msp-ids ( -- addr ) lf-msp-index lf-msi-ids ;
: lf-msp-arities ( -- addr ) lf-msp-index lf-msi-arities ;
: lf-msp-formals ( -- addr ) lf-msp-index lf-msi-formals ;
: lf-msp-formals-at ( position -- addr ) lf-level-capacity * cells lf-msp-formals + ;
\ Unchecked: one field of the record at a position below the count.
: lf-msp-name@ ( position -- name ) cells lf-msp-names + @ ;
: lf-msp-root@ ( position -- root ) cells lf-msp-roots + @ ;
: lf-msp-id@ ( position -- identity ) cells lf-msp-ids + @ ;
: lf-msp-arity@ ( position -- arity ) cells lf-msp-arities + @ ;

\ The generations of the name, term and level stores and of the level
\ context, captured when a lifetime begins; a change to any of them ends it.
: lf-msp-store-gens ( -- name term ) lf-name-generation @ lf-term-generation @ ;
: lf-msp-scope-gens ( -- level context ) lf-level-generation @ lf-lscope-generation @ ;
: lf-msp-capture ( -- )
  lf-msp-store-gens lf-msp-index lf-msi-store-gens 2!
  lf-msp-scope-gens lf-msp-index lf-msi-scope-gens 2! ;
: lf-msp-pair= ( x1 x2 addr -- flag ) 2@ rot = -rot = and ;
: lf-msp-unchanged? ( -- flag )
  lf-msp-store-gens lf-msp-index lf-msi-store-gens lf-msp-pair=
  lf-msp-scope-gens lf-msp-index lf-msi-scope-gens lf-msp-pair= and ;
: lf-msp-sources? ( -- flag )
  lf-name-storage-valid? lf-ssession-current? and lf-cref-state-valid? and ;

\ Clear and start a new lifetime; every attempt consumes a generation. On
\ saturation begin fails permanently. Failure leaves the index inactive.
: lf-msp-renew ( -- flag ) lf-msp-generation dup @ epoch+ dup rot ! 0< 0= ;
: lf-msp-begin ( -- flag )
  false lf-msp-active ! 0 lf-msp-count !
  lf-msp-renew lf-msp-sources? and dup if lf-msp-capture dup lf-msp-active ! then ;

\ A token is current while its lifetime is open, the count is in range and
\ the stores, session and context it captured are unchanged.
: lf-msp-live? ( -- flag )
  lf-msp-count @ lf-msp-capacity upto? lf-msp-sources? and lf-msp-unchanged? and ;
: lf-msp-current? ( token -- flag )
  lf-msp-active @ if lf-msp-generation @ = lf-msp-live? and else drop false then ;
\ Token denotes lifetime, not content revision; insertions do not change it.
: lf-msp-token ( -- token true | false )
  lf-msp-generation @ dup lf-msp-current? if true else drop false then ;

\ Searching. lf-msp-cell-index is generic: the first of n cells at addr
\ equal to x. The caller has validated n.
: lf-msp-cell-index ( x addr n -- i | -1 )
  0 ?do 2dup i cells + @ = if 2drop i unloop exit then loop 2drop -1 ;
: lf-msp-find ( name n -- position | -1 ) lf-msp-names swap lf-msp-cell-index ;
: lf-msp-position ( name -- position | -1 ) lf-msp-count @ lf-msp-find ;

\ A request is well formed when its token is current, its fuel is
\ nonnegative, its arity is 0..lf-level-capacity and its name is a positive,
\ live name ID. Only then may the index be searched.
: lf-msp-name? ( name -- flag ) dup 0> swap lf-name-valid? and ;
: lf-msr-sizes? ( req -- flag )
  dup lf-msr-fuel @ 0< 0= swap lf-msr-arity @ lf-level-capacity upto? and ;
: lf-msp-well-formed? ( token req -- flag )
  dup lf-msr-sizes? swap lf-msr-name @ lf-msp-name? and swap lf-msp-current? and ;
: lf-msr-budget! ( count fuel req -- ) tuck lf-msr-fuel ! lf-msr-arity ! ;
: lf-msr-source! ( root identity req -- ) tuck lf-msr-id ! lf-msr-root ! ;

\ Substitute the request's actuals for its formals in its root.
\ lf-mixed-level-substitute reports only ok, invalid or exhausted.
: lf-msr-substitute ( req -- root identity 0 | status )
  >r r@ lf-msr-root @ r@ lf-msr-id @ r@ lf-msr-formals @ r@ lf-msr-actuals @
  r@ lf-msr-arity @ r> lf-msr-fuel @ lf-mixed-level-substitute outcome-sane ;

\ Coverage uses one complete mixed substitution with every actual the zero
\ level, which fails unless every source parameter is a formal. Even on
\ success all temporary allocations are discarded, never their serials.
\ This can exhaust arena space or identity serials for an otherwise valid list.
: lf-msp-marks ( -- terms levels crefs )
  lf-term-count @ lf-level-count @ lf-cref-count @ ;
: lf-msp-rewind ( terms levels crefs -- )
  lf-cref-count ! lf-level-count ! lf-term-count ! ;
: lf-msp-zeros ( identity req -- )
  dup lf-msr-zeros swap lf-msr-arity @ 0 ?do 2dup i 2* cells + 0 swap 2! loop 2drop ;
: lf-msp-discard ( root identity 0 | status -- status ) dup ok? if nip nip then ;
: lf-msp-cover ( req -- status )
  dup lf-msr-zeros over lf-msr-actuals ! lf-msr-substitute lf-msp-discard ;
: lf-msp-zero-actuals ( req -- status )
  0 lf-level-identity if over lf-msp-zeros lf-msp-cover else drop-invalid then ;
: lf-msp-coverage ( req -- status )
  lf-msp-marks 2>r >r lf-msp-zero-actuals r> 2r> lf-msp-rewind ;

\ Insertion: a well-formed request for a new name, room in the index, then
\ coverage; only then are the record and its formal IDs copied in.
: lf-msp-new? ( token req -- flag )
  tuck lf-msp-well-formed? if lf-msr-name @ lf-msp-position 0< else drop false then ;
: lf-msp-room ( -- outcome )
  lf-msp-count @ lf-msp-capacity < if outcome-ok else outcome-exhausted then ;
: lf-msp-addable ( token req -- status )
  lf-msp-new? if lf-msp-room else outcome-invalid then ;
: lf-msp-next ( array -- addr ) lf-msp-count @ cells + ;
: lf-msp-copy ( req -- )
  dup lf-msr-formals @ lf-msp-count @ lf-msp-formals-at rot lf-msr-arity @ cells move ;
: lf-msp-record! ( req -- )
  dup lf-msr-name @ lf-msp-names lf-msp-next !
  dup lf-msr-root @ lf-msp-roots lf-msp-next !
  dup lf-msr-id @ lf-msp-ids lf-msp-next !
  lf-msr-arity @ lf-msp-arities lf-msp-next ! ;
: lf-msp-append ( req -- ) dup lf-msp-record! lf-msp-copy 1 lf-msp-count +! ;
: lf-msp-insert ( req -- status )
  dup lf-msp-coverage ok-then? if lf-msp-append outcome-ok then ;
: lf-msp-add ( token req -- status ) tuck lf-msp-addable ok-then? if lf-msp-insert then ;

\ Copy ordered distinct formal IDs only after coverage succeeds. The single
\ coverage fuel is shared by the mixed substitution's full audit and build;
\ bounded index/list scans and identity checks are additional unmetered work.
\ Every failure leaves index contents and all three arena counts unchanged.
: lf-msp-put ( token name root identity formals count fuel -- status )
  lf-msp-request >r r@ lf-msr-budget! r@ lf-msr-formals ! r@ lf-msr-source!
  r@ lf-msr-name ! r> lf-msp-add ;

\ Lookup: a name with no candidate is unknown; a candidate whose arity
\ differs from the request is invalid.
: lf-msp-arity= ( req position -- flag ) lf-msp-arity@ swap lf-msr-arity @ = ;
: lf-msp-entry! ( position req -- )
  over lf-msp-root@ over lf-msr-root ! over lf-msp-id@ over lf-msr-id !
  swap lf-msp-formals-at swap lf-msr-formals ! ;
: lf-msp-select ( req -- status )
  dup lf-msr-name @ lf-msp-position dup 0< if 2drop outcome-unknown exit then
  2dup lf-msp-arity= if swap lf-msp-entry! outcome-ok else 2drop outcome-invalid then ;
: lf-msp-found ( req -- root identity 0 | status )
  dup lf-msp-select ok-then? if lf-msr-substitute then ;
: lf-msp-lookup ( token req -- root identity 0 | status )
  tuck lf-msp-well-formed? if lf-msp-found else drop-invalid then ;

\ Exact arity includes unused formals. One shared substitution budget covers
\ the full audit and build; index scans and identity checks are unmetered.
\ Failure rolls back all arena counts, not allocation serials or scratch.
\ Returned syntax is conditional on unchecked metadata and is never a theorem.
: lf-msp-specialize ( token name actual-pairs count fuel -- root identity 0 | status )
  lf-msp-request >r r@ lf-msr-budget! r@ lf-msr-actuals ! r@ lf-msr-name !
  r> lf-msp-lookup ;
