\ Untrusted candidate signatures for mixed constant-bearing syntax. No
\ declaration, binder scope, type, proof, dependency or theorem is checked
\ or registered. Candidates and all nested constant signatures are unchecked
\ assumptions. Caller arrays must be aligned, readable and disjoint from
\ arenas, contexts, the index and all scratch. Handles/tokens are forgeable
\ and instance-local, not capabilities or serialized identities. Bare name
\ IDs belong to the captured name generation; callers must not reuse stale
\ IDs. Source and actual parameters must be in the same live session
\ context. A cref reset does not invalidate the index token; each use
\ rechecks the reachable references and their allocation identities. No
\ cache is provided.
\ State: the index record lf-msp-index (lifetime, count and captured
\ generations), its candidate arrays and formal pool (context slabs, which
\ grow: no fixed number of candidates since plan task 6.2.0), and the
\ request record lf-msp-request (one put or specialize call's arguments
\ and the zero actuals used by coverage), and coverage's scratch mark
\ lf-msp-mark, all members of the checker context (lib/context.fs): the
\ index refers to its own context's stores. Single-threaded within one
\ context: exclude resets, raw writes, callbacks and concurrent calls.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/diagnostics.fs
require ../core/level-scope.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/scratch-marks.fs
require ../core/symbolic-session.fs
require ../core/terms.fs
require ./mixed-level-substitute.fs

\ The index: parallel arrays of candidate records, because callers and tests
\ address them as cell arrays (lf-msp-names, ...) and copy their prefixes.
\ Each array is a growable slab (plan task 6.2.0), all held to the same
\ room before a record is added; an address is valid until the next put.
begin-structure /lf-sigs
  field: lf-sigs-count                 \ records in use, 0..the arrays' room
  field: lf-sigs-active                \ true while a lifetime is open
  field: lf-sigs-generation            \ lifetime counter; negative once spent
  2 cells +field lf-sigs-store-gens    \ name and term generations at begin
  2 cells +field lf-sigs-scope-gens    \ level and context generations at begin
end-structure
1 cells context-slab: lf-sigs-names
1 cells context-slab: lf-sigs-roots
1 cells context-slab: lf-sigs-ids
1 cells context-slab: lf-sigs-arities
1 cells context-slab: lf-sigs-offsets   \ where each record's formals begin
\ Every record's formal IDs, one after another, and the zero actuals of
\ coverage: growable arrays with no fixed limit on an arity (plan task
\ 6.2.0); one the heap cannot grow is full.
1 cells context-slab: lf-msp-formal-pool
2 cells context-slab: lf-msp-zero-pairs

\ One request. Put fills name, root, id, formals, arity and fuel; specialize
\ fills name, actuals, arity and fuel, then root, id and formals from the
\ matching record. Coverage points actuals at the zero pairs.
begin-structure /lf-sigreq
  field: lf-sigreq-name
  field: lf-sigreq-root
  field: lf-sigreq-id
  field: lf-sigreq-formals            \ address of arity formal IDs
  field: lf-sigreq-actuals            \ address of arity (index identity) pairs
  field: lf-sigreq-arity
  field: lf-sigreq-fuel
end-structure

/lf-sigs context-record: lf-msp-index
/lf-sigreq context-record: lf-msp-request
/lf-scratch context-record: lf-msp-mark   \ the stores before coverage

\ Failures are recorded as diagnostics at the module's one site, whose
\ name gives the prefix of its public words: a full index (lf-msp-put) and
\ a missing candidate (lf-msp-specialize) differ by their codes.
: lf-msp-site ( -- site ) c" mixed-signature-probe lf-msp" ;

\ The index fields under their established names (tests and stream fixtures
\ read the arrays and the count).
: lf-msp-count ( -- addr ) lf-msp-index lf-sigs-count ;
: lf-msp-active ( -- addr ) lf-msp-index lf-sigs-active ;
: lf-msp-generation ( -- addr ) lf-msp-index lf-sigs-generation ;
: lf-msp-names ( -- addr ) lf-sigs-names slab-base ;
: lf-msp-roots ( -- addr ) lf-sigs-roots slab-base ;
: lf-msp-ids ( -- addr ) lf-sigs-ids slab-base ;
: lf-msp-arities ( -- addr ) lf-sigs-arities slab-base ;
: lf-msp-formals ( -- addr ) 0 lf-msp-formal-pool slab-at ;
: lf-msp-offsets ( -- addr ) lf-sigs-offsets slab-base ;
\ The five arrays, and the records every one has room for.
create lf-msp-arrays
  ' lf-sigs-names , ' lf-sigs-roots , ' lf-sigs-ids , ' lf-sigs-arities , ' lf-sigs-offsets ,
here lf-msp-arrays - 1 cells / constant lf-msp-arrays#
: lf-msp-array ( i -- slab ) cells lf-msp-arrays + @ execute ;
: lf-msp-room@ ( -- n ) max-n lf-msp-arrays# 0 do i lf-msp-array slab-capacity min loop ;
: lf-msp-offset@ ( position -- u ) cells lf-msp-offsets + @ ;
: lf-msp-formals-at ( position -- addr ) lf-msp-offset@ lf-msp-formal-pool slab-at ;
\ Unchecked: one field of the record at a position below the count.
: lf-msp-name@ ( position -- name ) cells lf-msp-names + @ ;
: lf-msp-root@ ( position -- root ) cells lf-msp-roots + @ ;
: lf-msp-id@ ( position -- identity ) cells lf-msp-ids + @ ;
: lf-msp-arity@ ( position -- arity ) cells lf-msp-arities + @ ;
\ The pool cells the first n records use: where record n's formals go.
: lf-msp-formal-cells ( n -- u )
  ?dup if 1- dup lf-msp-offset@ swap lf-msp-arity@ + else 0 then ;

\ The generations of the name, term and level stores and of the level
\ context, captured when a lifetime begins; a change to any of them ends it.
: lf-msp-store-gens ( -- name term ) lf-name-generation @ lf-term-generation @ ;
: lf-msp-scope-gens ( -- level context ) lf-level-generation @ lf-lscope-generation @ ;
: lf-msp-capture ( -- )
  lf-msp-store-gens lf-msp-index lf-sigs-store-gens 2!
  lf-msp-scope-gens lf-msp-index lf-sigs-scope-gens 2! ;
: lf-msp-pair= ( x1 x2 addr -- flag ) 2@ rot = -rot = and ;
: lf-msp-unchanged? ( -- flag )
  lf-msp-store-gens lf-msp-index lf-sigs-store-gens lf-msp-pair=
  lf-msp-scope-gens lf-msp-index lf-sigs-scope-gens lf-msp-pair= and ;
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
  lf-msp-count @ lf-msp-room@ upto? lf-msp-sources? and lf-msp-unchanged? and ;
: lf-msp-current? ( token -- flag )
  lf-msp-active @ if lf-msp-generation @ = lf-msp-live? and else drop false then ;
\ Token denotes lifetime, not content revision; insertions do not change it.
: lf-msp-token ( -- token true | false )
  lf-msp-generation @ dup lf-msp-current? if true else drop false then ;

\ Searching. lf-msp-cell-index is generic: the first of n cells at addr
\ equal to x. The caller has validated n.
: lf-msp-cell-index ( x addr n -- i | -1 ) cells-index 0= if -1 then ;
: lf-msp-find ( name n -- position | -1 ) lf-msp-names swap lf-msp-cell-index ;
: lf-msp-position ( name -- position | -1 ) lf-msp-count @ lf-msp-find ;

\ A request is well formed when its token is current, its fuel is
\ nonnegative, its arity is nonnegative and its name is a positive, live
\ name ID. Only then may the index be searched.
: lf-msp-name? ( name -- flag ) dup 0> swap lf-name-valid? and ;
: lf-msp-sizes? ( req -- flag )
  dup lf-sigreq-fuel @ 0< 0= swap lf-sigreq-arity @ 0< 0= and ;
: lf-msp-well-formed? ( token req -- flag )
  dup lf-msp-sizes? swap lf-sigreq-name @ lf-msp-name? and swap lf-msp-current? and ;
: lf-msp-budget! ( count fuel req -- ) tuck lf-sigreq-fuel ! lf-sigreq-arity ! ;
: lf-msp-source! ( root identity req -- ) tuck lf-sigreq-id ! lf-sigreq-root ! ;

\ Substitute the request's actuals for its formals in its root.
\ lf-mixed-level-substitute reports only ok, invalid, exhausted or full.
: lf-msp-substitute ( req -- root identity 0 | status )
  >r r@ lf-sigreq-root @ r@ lf-sigreq-id @ r@ lf-sigreq-formals @ r@ lf-sigreq-actuals @
  r@ lf-sigreq-arity @ r> lf-sigreq-fuel @ lf-mixed-level-substitute outcome-sane ;

\ Coverage uses one complete mixed substitution with every actual the zero
\ level, which fails unless every source parameter is a formal. Even on
\ success all temporary allocations are discarded, never their serials:
\ the stores go back to a scratch mark (core/scratch-marks.fs). This can
\ fill arena space or spend identity serials (full) for an otherwise
\ valid list. LIFO: the mark is taken before the substitution and given
\ back after it, whose own mark is younger and given back first; coverage
\ never runs inside another. A mark that cannot be taken is invalid,
\ nothing run; a refused rollback makes the outcome invalid.
: lf-msp-zeros-at ( -- addr ) 0 lf-msp-zero-pairs slab-at ;
: lf-msp-zeros ( identity req -- )
  lf-msp-zeros-at swap lf-sigreq-arity @
  0 ?do 2dup i 2* cells + 0 swap 2! loop 2drop ;
: lf-msp-discard ( root identity 0 | status -- status ) dup ok? if nip nip then ;
: lf-msp-cover ( req -- status )
  lf-msp-zeros-at over lf-sigreq-actuals ! lf-msp-substitute lf-msp-discard ;
: lf-msp-zero-room ( req -- outcome ) lf-sigreq-arity @ lf-msp-zero-pairs slab-hold ;
: lf-msp-zero-actuals ( req -- status )
  dup lf-msp-zero-room ok-then? 0= if nip exit then
  0 lf-level-identity if over lf-msp-zeros lf-msp-cover else drop-invalid then ;
: lf-msp-coverage ( req -- status )
  lf-msp-mark lf-scratch-mark ok-then? 0= if exit then
  lf-msp-zero-actuals lf-msp-mark lf-scratch-rollback lf-scratch-settled ;

\ Insertion: a well-formed request for a new name, room in the index, then
\ coverage; only then are the record and its formal IDs copied in. An index
\ the heap cannot grow is full.
: lf-msp-new? ( token req -- flag )
  tuck lf-msp-well-formed? if lf-sigreq-name @ lf-msp-position 0< else drop false then ;
: lf-msp-full ( -- outcome )
  lf-msp-count @ lf-msp-room@ lf-msp-site lf-diag-signatures-full lf-diag-note
  outcome-full ;
: lf-msp-hold? ( n -- flag )
  true lf-msp-arrays# 0 do over i lf-msp-array slab-hold ok? and loop nip ;
: lf-msp-room ( -- outcome )
  lf-msp-count @ 1+ lf-msp-hold? if outcome-ok else lf-msp-full then ;
: lf-msp-pool-room ( req -- outcome )
  lf-msp-count @ lf-msp-formal-cells swap lf-sigreq-arity @ + lf-msp-formal-pool slab-hold ;
: lf-msp-addable ( token req -- status )
  tuck lf-msp-new? 0= if drop outcome-invalid exit then
  lf-msp-room dup ok? if drop lf-msp-pool-room else nip then ;
: lf-msp-next ( array -- addr ) lf-msp-count @ cells + ;
: lf-msp-copy ( req -- )
  lf-msp-count @ dup lf-msp-formal-cells tuck swap cells lf-msp-offsets + !
  lf-msp-formal-pool slab-at swap dup lf-sigreq-formals @ swap lf-sigreq-arity @
  >r swap r> cells move ;
: lf-msp-record! ( req -- )
  dup lf-sigreq-name @ lf-msp-names lf-msp-next !
  dup lf-sigreq-root @ lf-msp-roots lf-msp-next !
  dup lf-sigreq-id @ lf-msp-ids lf-msp-next !
  lf-sigreq-arity @ lf-msp-arities lf-msp-next ! ;
: lf-msp-append ( req -- ) dup lf-msp-record! lf-msp-copy 1 lf-msp-count +! ;
: lf-msp-insert ( req -- status )
  dup lf-msp-coverage ok-then? if lf-msp-append outcome-ok then ;
: lf-msp-add ( token req -- status ) tuck lf-msp-addable ok-then? if lf-msp-insert then ;

\ Copy ordered distinct formal IDs only after coverage succeeds. The single
\ coverage fuel is shared by the mixed substitution's full audit and build;
\ bounded index/list scans and identity checks are additional unmetered work.
\ Every failure leaves index contents and all three arena counts unchanged.
: lf-msp-put ( token name root identity formals count fuel -- status )
  lf-msp-request >r r@ lf-msp-budget! r@ lf-sigreq-formals ! r@ lf-msp-source!
  r@ lf-sigreq-name ! r> lf-msp-add ;

\ Lookup: a name with no candidate is unknown, recorded as no signature; a
\ candidate whose arity differs from the request is invalid.
: lf-msp-arity= ( req position -- flag ) lf-msp-arity@ swap lf-sigreq-arity @ = ;
: lf-msp-entry! ( position req -- )
  over lf-msp-root@ over lf-sigreq-root ! over lf-msp-id@ over lf-sigreq-id !
  swap lf-msp-formals-at swap lf-sigreq-formals ! ;
: lf-msp-missing ( req position -- status )
  drop lf-sigreq-name @ 0 lf-msp-site lf-diag-no-signature lf-diag-note outcome-unknown ;
: lf-msp-select ( req -- status )
  dup lf-sigreq-name @ lf-msp-position dup 0< if lf-msp-missing exit then
  2dup lf-msp-arity= if swap lf-msp-entry! outcome-ok else 2drop outcome-invalid then ;
: lf-msp-found ( req -- root identity 0 | status )
  dup lf-msp-select ok-then? if lf-msp-substitute then ;
: lf-msp-lookup ( token req -- root identity 0 | status )
  tuck lf-msp-well-formed? if lf-msp-found else drop-invalid then ;

\ Exact arity includes unused formals. One shared substitution budget covers
\ the full audit and build; index scans and identity checks are unmetered.
\ Failure rolls back all arena counts, not allocation serials or scratch.
\ Returned syntax is conditional on unchecked metadata and is never a theorem.
\ The status is ok, invalid, exhausted, full, or unknown for a name with no
\ candidate. lf-msp-specialize-fuel also gives the fuel left on success, for
\ mixed-infer to continue with.
: lf-msp-specialize-fuel
  ( token name actual-pairs count fuel -- root identity fuel' 0 | status )
  lf-msp-request >r r@ lf-msp-budget! r@ lf-sigreq-actuals ! r@ lf-sigreq-name !
  r> lf-msp-lookup lf-mls-left ;
: lf-msp-specialize ( token name actual-pairs count fuel -- root identity 0 | status )
  lf-msp-specialize-fuel dup ok? if nip then ;
