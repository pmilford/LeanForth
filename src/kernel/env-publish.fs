\ The single publisher of the checked environment (ADR 0012, E4, E6, E7)
\ and the serial driver of phase 2.
\
\ lf-env-hand-over takes the candidate a check left in the current
\ context and fills its slot. It is the publisher's only entry, and it
\ refuses inside a job (G-P1: one writer, outside every job). For an ok
\ outcome it first re-checks the candidate's cheap invariants against the
\ environment (E4 step 1, as amended 2026-11-02): every slot below it with
\ the same name is final and rejected (N2, K5, G-P5); its dependencies are
\ ascending, distinct, below it, final and accepted; its axiom set is the
\ union of theirs and within the allowlist, its provenance the union of
\ theirs and "checked" in a final run; its kind is a definition or
\ theorem, safe, with a value and distinct universe parameters. A failure
\ is a fault in LeanForth and makes the outcome invalid. Then it appends
\ the dependencies to the pool (full, with nothing appended or written,
\ when there is no room) and copies the input declaration into the slot,
\ so the record points at the very input terms that were checked. Any
\ other outcome is written alone. Last, it marks the slot final: the
\ single point at which a result becomes visible. Only an ok check
\ followed by these steps makes a slot final with outcome ok, and nothing
\ changes a final slot.
\
\ The hand-over marks the pool, then publishes under CATCH: a THROW before
\ the final mark leaves the slot not final and cleared and the pool
\ rolled back. That, a pool that cannot be marked, a candidate with no
\ slot to publish and a publication that ends without a final slot are
\ faults: invalid, after which the run stops.
\
\ lf-env-step checks one declaration: it begins the check, runs it,
\ makes sure the snapshot is still of that declaration, hands the
\ candidate over, and rolls the scratch above the input marks back,
\ whatever the outcome. A THROW in the check makes the declaration
\ invalid and spends the context (G-P6, lf-env-thrown): lf-env-begin
\ refuses a spent context, which must be replaced. lf-env-run, the
\ phase-2 scheduler, checks every declaration in input order, in the
\ current context until a check throws, then in a new context from a
\ maker the caller gives, which must hold the same input (in v0 the input
\ is per context, src/core/input.fs; the environment's fingerprint
\ refuses any other). It frees each context it made once that is spent or
\ the run ends, and returns to the caller's context, which it never
\ frees. In a parallel run the scheduler waits for a job, selects its
\ context, calls lf-env-thrown when the job's ior is not 0, then
\ lf-env-hand-over, and replaces the context when lf-env-spent? holds; the
\ pool's lock in job-submit orders each publication before every check
\ handed out afterwards (G-P2). Publication must not pause or print.
\
\ Failures are explained in the context's diagnostic: a failed re-check
\ (lf-diag-recheck, with the part that failed, or 6 for a check that
\ moved its snapshot), no room in the pool (lf-diag-pool-full) and a
\ THROW in a check or in the publisher (lf-diag-publisher-fault, with the
\ THROW code).
\
\ [kernel] code: experimental, not through the review gate.
\ State: none of its own. It writes environments (environment.fs), whose
\ header holds the publisher's pool mark, reads the candidate in the
\ current context and writes that context's worker record. A test that
\ defines lf-env-fault-hooks before loading this file also gets the
\ fault-injection hook lf-env-before-final (a DEFER, shared).

require ../lib/lib.fs
require ../core/diagnostics.fs
require ../core/terms.fs
require ../core/input.fs
require ./environment.fs

\ Fault injection, for tests only (ADR 0012 test row 6): runs after a
\ slot's outcome and record are written and before it is marked final.
\ Compiled as a DEFER only when a test defines lf-env-fault-hooks first;
\ otherwise an empty word that nothing can change.
[defined] lf-env-fault-hooks [if]
: lf-env-no-fault ( -- ) ;
defer lf-env-before-final
' lf-env-no-fault is lf-env-before-final
[else]
: lf-env-before-final ( -- ) ;
[then]

\ The slot this context's candidate is for: (slot true) when its snapshot
\ is a check of the valid current environment and the slot is not final.
: lf-env-target ( -- slot true | false )
  lf-env-checking 0= if false exit then swap lf-env-slot dup lf-slot-open? ?keep ;

\ E4 step 1. The dependencies: a count in range, each readable and
\ accepted in the snapshot (so below the declaration and final), each
\ above the one before.
: lf-dep@ ( k -- d ) lf-cand-dep @ ;
: lf-recheck-order? ( k -- flag )
  dup 0= if drop true exit then dup 1- lf-dep@ swap lf-dep@ < ;
: lf-recheck-dep? ( k -- flag )
  dup lf-dep@ lf-env-accepted nip ok? swap lf-recheck-order? and ;
: lf-recheck-deps? ( -- flag )
  lf-cand-count? 0= if false exit then
  true lf-cand-count@ 0 ?do i lf-recheck-dep? and loop ;
\ The union of a slot field over the dependencies, read from the slots.
\ Unchecked: the dependencies passed lf-recheck-deps?.
: lf-dep-slot ( k -- slot ) lf-dep@ lf-env lf-env-slot ;
: lf-deps-union ( field -- bits )
  0 lf-cand-count@ 0 ?do over i lf-dep-slot swap execute @ or loop nip ;
: lf-allowed? ( bits -- flag ) lf-env lf-envh-allowed @ invert and 0= ;
: lf-recheck-axioms? ( -- flag )
  ['] lf-slot-axioms lf-deps-union
  dup lf-env-cand lf-cand-axioms @ = swap lf-allowed? and ;
: lf-final-run? ( -- flag ) lf-env lf-envh-mode @ lf-mode-final = ;
: lf-provenance-ok? ( bits -- flag ) lf-provenance-checked = lf-final-run? 0= or ;
: lf-recheck-provenance? ( -- flag )
  ['] lf-slot-provenance lf-deps-union
  dup lf-env-cand lf-cand-provenance @ = swap lf-provenance-ok? and ;
\ N2 and K5 (as amended): every slot below the declaration with its name
\ is final (G-P5) and rejected. One that is open, accepted, undecided or
\ unsupported is a conflict: lf-env-own-name would not have said ok. The
\ name store is audited first, as the scan and the parameters need it.
: lf-slot-conflict? ( slot -- flag )
  dup lf-slot-open? swap lf-slot-outcome@ outcome-rejected <> or ;
: lf-own-matches ( test -- n ) lf-env-limit dup lf-input-name -rot lf-env-matches ;
: lf-recheck-name? ( -- flag )
  lf-name-storage-valid? if ['] lf-slot-conflict? lf-own-matches 0= else false then ;
\ Kind and safety in scope (ADR 0011), a value, distinct parameters (L3).
: lf-scope-kind? ( kind -- flag ) dup lf-kind-definition = swap lf-kind-theorem = or ;
: lf-recheck-kind? ( decl -- flag )
  dup lf-idecl-kind @ lf-scope-kind? over lf-idecl-safety @ lf-safety-safe = and
  swap lf-idecl-value @ lf-term-valid? and ;
: lf-recheck-decl? ( -- flag )
  lf-env-limit lf-input-decl dup lf-recheck-kind?
  swap lf-idecl-params@ lf-params-distinct? and ;
\ The re-checks ( -- flag ), in order, each relying on the ones before:
\ part 1 the dependencies, 2 the axiom set, 3 the provenance, 4 the name
\ (N2, K5, G-P5; or a corrupted name store), 5 the kind, safety, value or
\ parameters. Part 6 is lf-env-step's: a check that moved its snapshot.
5 constant lf-rechecks#
6 constant lf-recheck-moved
create lf-rechecks
  ' lf-recheck-deps? , ' lf-recheck-axioms? , ' lf-recheck-provenance? ,
  ' lf-recheck-name? , ' lf-recheck-decl? ,
: lf-recheck@ ( k -- xt ) cells lf-rechecks + @ ;
\ The first re-check that fails, (part true), or false when all pass.
: lf-recheck ( -- part true | false )
  lf-rechecks# 0 ?do i lf-recheck@ execute 0= if i 1+ true unloop exit then loop false ;
: lf-recheck-failed ( part -- outcome )
  lf-env-limit swap c" env-publish lf-env-hand-over" lf-diag-recheck lf-diag-note
  outcome-invalid ;
\ The outcome to record: the check's; ok only when the re-check passes.
: lf-cand-outcome@ ( -- outcome ) lf-env-cand lf-cand-outcome @ outcome-sane ;
: lf-env-verdict ( -- outcome )
  lf-cand-outcome@ dup ok? 0= if exit then
  drop lf-recheck if lf-recheck-failed else outcome-ok then ;

\ E4 step 2 for an ok outcome. The pool has room for n more when both its
\ records and its identities suffice; a refusal after that check is a
\ fault and throws.
: lf-pool-free ( store -- u ) dup store-capacity @ swap store-count @ - ;
: lf-pool-ids ( store -- u ) max-n swap store-serial @ - ;
: lf-pool-room? ( n store -- flag )
  2dup lf-pool-free upto? -rot lf-pool-ids upto? and ;
: lf-pool-put ( d store -- )
  dup store-new 0= abort" lf-env: pool refused" swap store-slot ! ;
: lf-pool-append ( store -- )
  lf-cand-count@ 0 ?do i lf-dep@ over lf-pool-put loop drop ;
\ Append the candidate's dependencies: (first ok), or (-1 full) with
\ nothing appended.
: lf-pool-take ( store -- first outcome )
  dup store-count @ swap lf-pool-append outcome-ok ;
: lf-pool-full ( store -- -1 outcome )
  dup store-count @ lf-cand-count@ + swap store-capacity @ c" env-publish lf-env-append"
  lf-diag-pool-full lf-diag-note -1 outcome-full ;
: lf-env-append ( -- first outcome )
  lf-env lf-env-pool lf-cand-count@ over lf-pool-room?
  if lf-pool-take else lf-pool-full then ;
: lf-slot-input! ( slot -- )
  lf-env-limit lf-input-decl swap lf-slot-decl /lf-idecl move ;
: lf-slot-sets! ( slot -- )
  lf-env-cand lf-cand-axioms @ over lf-slot-axioms !
  lf-env-cand lf-cand-provenance @ swap lf-slot-provenance ! ;
: lf-slot-deps! ( first slot -- )
  tuck lf-slot-deps ! lf-cand-count@ swap lf-slot-count ! ;
: lf-slot-fill ( first slot -- ) tuck lf-slot-deps! dup lf-slot-input! lf-slot-sets! ;
\ The record of an accepted declaration: (slot ok), or (slot full) with
\ nothing appended or written.
: lf-env-record ( slot -- slot outcome )
  lf-env-append dup ok? 0= if nip exit then drop over lf-slot-fill outcome-ok ;
\ E4 step 3: the outcome, the fault-injection point, then, last, the mark.
: lf-env-final ( slot outcome -- outcome )
  2dup swap lf-slot-outcome ! lf-env-before-final lf-state-final rot lf-slot-state ! ;
\ Publish the candidate in this context into its slot: the outcome
\ recorded. Internal: only lf-env-hand-over calls it, outside jobs, under
\ CATCH, with the slot its target.
: lf-env-write ( slot -- outcome )
  lf-env-verdict dup ok? if drop lf-env-record then lf-env-final ;

\ After a THROW in the publisher: the diagnostic, the pool back to its
\ mark and the slot cleared while it is not final. The hand-over is a
\ fault either way, so a refused rollback, which leaves pool entries that
\ no slot points to, needs no status of its own.
: lf-env-pub-mark ( -- mark store ) lf-env lf-envh-pub-mark lf-env lf-env-pool ;
: lf-env-unpublish ( slot ior -- )
  lf-env-limit swap c" env-publish lf-env-hand-over" lf-diag-publisher-fault lf-diag-note
  lf-env-pub-mark store-rollback drop dup lf-slot-open? if /lf-slot erase else drop then ;
\ Mark the pool, then write the slot under CATCH: (outcome false) once the
\ slot is final; (invalid true) when the pool cannot be marked (nothing
\ written), after a THROW (undone as above), or when the slot is still
\ not final. CATCH may leave its argument cell undefined, so a copy of
\ the slot stays below it.
: lf-env-guarded ( slot -- outcome fault? )
  lf-env-pub-mark store-mark ok? 0= if drop outcome-invalid true exit then
  dup ['] lf-env-write catch ?dup if nip lf-env-unpublish outcome-invalid true exit then
  swap lf-slot-open? ;
\ Publish the candidate in this context (E4): (outcome false) once its
\ slot is final; (invalid true), with nothing written, inside a job
\ (G-P1), or when the candidate has no slot to publish (no check's
\ snapshot of the valid current environment, or its slot already final),
\ and as lf-env-guarded says.
: lf-env-hand-over ( -- outcome fault? )
  lf-env-in-job? if outcome-invalid true exit then
  lf-env-target if lf-env-guarded else outcome-invalid true then ;

\ A check in this context threw ior (G-P6): the declaration is invalid,
\ recorded as an internal fault, and the context is spent. lf-env-step
\ calls it; a parallel scheduler calls it for a job whose ior is not 0,
\ before handing the candidate over.
: lf-env-thrown ( ior -- )
  lf-env-limit swap c" env-publish lf-env-step" lf-diag-publisher-fault lf-diag-note
  outcome-invalid lf-env-finish lf-env-spend ;
: lf-env-run-check ( xt -- ) catch ?dup if lf-env-thrown then ;
\ Whether this context's snapshot is still a check of declaration i; a
\ check that began another one is a fault, and nothing is published.
: lf-env-still? ( i -- flag ) lf-env-checking if nip = else drop false then ;
: lf-env-moved ( i -- outcome true )
  lf-recheck-moved c" env-publish lf-env-step" lf-diag-recheck lf-diag-note
  outcome-invalid true ;
: lf-env-hand-over-at ( i -- outcome fault? )
  dup lf-env-still? if drop lf-env-hand-over else lf-env-moved then ;
\ Check declaration i in this context with xt ( -- ), which ends with
\ lf-env-finish; a THROW in it makes the declaration invalid and spends
\ the context. Then, while the snapshot is still of declaration i, hand
\ the candidate over, and roll the scratch back to the input marks. Gives
\ the outcome published and whether the run must stop: a refused start
\ (inside a job, in a spent context, ...), a moved snapshot, a fault in
\ the publisher or a failed rollback.
: lf-env-step ( xt i -- outcome fault? )
  lf-env-in-job? if 2drop outcome-invalid true exit then
  dup lf-env-begin ok? 0= if 2drop outcome-invalid true exit then
  swap lf-env-run-check lf-env-hand-over-at lf-input-rollback ok? 0= or ;

\ The serial run's contexts (G-P6). After a check threw, the run goes on
\ in a new context from maker ( -- context ior ), which must make an
\ idle context holding the same input and leave the current one
\ selected. A maker that throws, fails, or gives the current or the main
\ context stops the run. A context the run made is freed once it is
\ spent and when the run ends.
: lf-env-made? ( -- flag ) lf-env-worker lf-worker-made @ ;
: lf-env-leave ( -- ior ) lf-env-made? if lf-context @ context-free else 0 then ;
: lf-env-make ( maker -- context ior )
  lf-context @ >r catch ?dup if 0 swap then r> lf-context ! ;
: lf-env-fresh? ( context -- flag ) dup context-main <> swap lf-context @ <> and ;
: lf-env-adopt ( context -- ) context-use true lf-env-worker lf-worker-made ! ;
\ Replace the current, spent context: true, or false when the run must stop.
: lf-env-renew ( maker -- flag )
  lf-env-make if drop false exit then dup lf-env-fresh? 0= if drop false exit then
  lf-env-leave swap lf-env-adopt 0= ;
\ Step i, then a new context if the check threw: whether to stop.
: lf-env-next ( check maker i -- check maker fault? )
  >r over r> lf-env-step nip dup if exit then
  drop lf-env-spent? if dup lf-env-renew 0= else false then ;
: lf-env-steps ( check maker n -- outcome )
  0 ?do i lf-env-next if 2drop unloop outcome-invalid exit then loop 2drop outcome-ok ;
\ Back in the caller's context, freeing the run's own: invalid if FREE
\ fails.
: lf-env-home ( outcome home -- outcome )
  >r lf-env-leave if drop outcome-invalid then r> context-use ;
\ The serial publisher of phase 2: every input declaration in input
\ order, checked with check ( -- ), new contexts from maker. ok when every
\ slot is final; invalid when the run stopped on a fault, with the slots
\ before it published and the others not final, inside a job, without a
\ valid current environment, or when no new context could be made after
\ a THROW. The caller's context is current again afterwards.
: lf-env-run ( check maker -- outcome )
  lf-env-in-job? if 2drop outcome-invalid exit then
  lf-env-current 0= if 2drop outcome-invalid exit then
  lf-env-length lf-context @ >r lf-env-steps r> lf-env-home ;
