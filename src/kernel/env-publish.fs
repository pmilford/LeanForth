\ The single publisher of the checked environment (ADR 0012, E4, E6, E7)
\ and the serial driver of phase 2.
\
\ lf-env-publish takes the candidate a check left in the current context
\ and fills its slot. For an ok outcome it first re-checks the candidate's
\ cheap invariants against the environment (E4 step 1): every slot below
\ it with the same name is final and none is accepted (N2, G-P5); its
\ dependencies are ascending,
\ distinct, below it, final and accepted; its axiom set is the union of
\ theirs and within the allowlist, its provenance the union of theirs and
\ "checked" in a final run; its kind is a definition or theorem, safe,
\ with a value and distinct universe parameters. A failure is a fault in
\ LeanForth and makes the outcome invalid. Then it appends the
\ dependencies to the pool (full, with nothing appended or written, when
\ there is no room) and copies the input declaration into the slot, so the
\ record points at the very input terms that were checked. Any other
\ outcome is written alone. Last, it marks the slot final: the single
\ point at which a result becomes visible. Only an ok check followed by
\ these steps makes a slot final with outcome ok, and nothing changes a
\ final slot.
\
\ lf-env-hand-over publishes under CATCH: a THROW before the final mark
\ leaves the slot not final and cleared and the pool rolled back, and
\ reports invalid and a fault, after which the run stops. lf-env-step
\ checks one declaration and lf-env-run all of them in input order, the
\ phase-2 scheduler; after each check the scratch above the input marks
\ is rolled back, whatever the outcome. In a parallel run the scheduler
\ waits for a job, selects its context and calls lf-env-hand-over; the
\ pool's lock in job-submit orders each publication before every check
\ handed out afterwards (G-P2). Publication must not pause or print.
\
\ Failures are explained in the context's diagnostic: a failed re-check
\ (lf-diag-recheck, with the part that failed), no room in the pool
\ (lf-diag-pool-full) and a THROW in a check or in the publisher
\ (lf-diag-publisher-fault, with the THROW code). The serial driver runs
\ in one context, which must hold the input (src/core/input.fs).
\
\ [kernel] code: experimental, not through the review gate.
\ State: the publisher's pool mark lf-pub-mark and the fault-injection
\ hook lf-env-before-final (shared, outside every context; used only by
\ the publishing task); it writes environments (environment.fs) and reads
\ the candidate in the current context.

require ../lib/lib.fs
require ../core/diagnostics.fs
require ../core/terms.fs
require ../core/input.fs
require ./environment.fs

\ Fault injection for tests (ADR 0012 test row 6): runs after a slot's
\ outcome and record are written and before it is marked final. Does
\ nothing unless a test sets it with IS, never while jobs run.
: lf-env-no-fault ( -- ) ;
defer lf-env-before-final
' lf-env-no-fault is lf-env-before-final

create lf-pub-mark /store-mark allot
lf-pub-mark /store-mark erase

\ The slot this context's candidate is for: (slot true) when its snapshot
\ is a check of the valid current environment and the slot is not final.
: lf-env-target ( -- slot true | false )
  lf-env-checking 0= if false exit then swap lf-env-slot dup lf-slot-final?
  if drop false else true then ;

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
\ N2: every slot below the declaration with its name is final (G-P5),
\ and none of them is accepted.
: lf-own-matches ( test -- n ) lf-env-limit dup lf-input-name -rot lf-env-matches ;
: lf-recheck-name? ( -- flag )
  ['] lf-slot-open? lf-own-matches ['] lf-slot-accepted? lf-own-matches or 0= ;
\ Kind and safety in scope (ADR 0011), a value, distinct parameters (L3).
: lf-scope-kind? ( kind -- flag ) dup lf-kind-definition = swap lf-kind-theorem = or ;
: lf-recheck-kind? ( decl -- flag )
  dup lf-idecl-kind @ lf-scope-kind? over lf-idecl-safety @ lf-safety-safe = and
  swap lf-idecl-value @ lf-term-valid? and ;
: lf-recheck-decl? ( -- flag )
  lf-env-limit lf-input-decl dup lf-recheck-kind?
  swap lf-idecl-params@ lf-params-distinct? and ;
\ The first re-check that fails: 1 the dependencies, 2 the axiom set,
\ 3 the provenance, 4 the name (N2), 5 the kind, safety, value or
\ parameters; 0 when all pass.
: lf-recheck ( -- part )
  lf-name-storage-valid? lf-recheck-deps? and 0= if 1 exit then
  lf-recheck-axioms? 0= if 2 exit then lf-recheck-provenance? 0= if 3 exit then
  lf-recheck-name? 0= if 4 exit then lf-recheck-decl? 0= if 5 exit then 0 ;
: lf-recheck-failed ( part -- outcome )
  lf-env-limit swap c" env-publish lf-env-publish" lf-diag-recheck lf-diag-note
  outcome-invalid ;
\ The outcome to record: the check's; ok only when the re-check passes.
: lf-cand-outcome@ ( -- outcome ) lf-env-cand lf-cand-outcome @ outcome-sane ;
: lf-env-verdict ( -- outcome )
  lf-cand-outcome@ dup ok? 0= if exit then
  drop lf-recheck ?dup if lf-recheck-failed else outcome-ok then ;

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

\ Publish the candidate in this context: the outcome recorded in its
\ slot; invalid, with nothing written, when there is no slot to publish
\ (no valid snapshot of a check of the current environment, or a slot
\ already final).
: lf-env-publish ( -- outcome )
  lf-env-target 0= if outcome-invalid exit then
  lf-env-verdict dup ok? if drop lf-env-record then lf-env-final ;

\ Publish under CATCH: (outcome false) once the slot is final; after a
\ THROW, the pool rolled back to its mark, the slot cleared while it is
\ not final, and (invalid true): a fault, after which the run stops. A
\ publication that ends without making the slot final is a fault too.
: lf-env-unpublish ( ior -- )
  lf-env-limit swap c" env-publish lf-env-hand-over" lf-diag-publisher-fault lf-diag-note
  lf-pub-mark lf-env lf-env-pool store-rollback drop
  lf-env-target if /lf-slot erase then ;
: lf-env-published? ( -- flag )
  lf-env-limit lf-env-final-at if drop true else false then ;
: lf-env-guarded ( env -- outcome fault? )
  lf-pub-mark swap lf-env-pool store-mark drop
  ['] lf-env-publish catch ?dup if lf-env-unpublish outcome-invalid true exit then
  lf-env-published? 0= ;
: lf-env-hand-over ( -- outcome fault? )
  lf-env-current if lf-env-guarded else outcome-invalid true then ;

\ Check declaration i in this context with xt ( -- ), which ends with
\ lf-env-finish; a THROW in it makes the declaration invalid (G-P6). Then
\ hand the candidate over and roll the scratch back to the input marks.
\ Gives the outcome published and whether the run must stop: a refused
\ start, a fault in the publisher or a failed rollback.
: lf-env-thrown ( ior -- )
  lf-env-limit swap c" env-publish lf-env-step" lf-diag-publisher-fault lf-diag-note
  outcome-invalid lf-env-finish ;
: lf-env-run-check ( xt -- ) catch ?dup if lf-env-thrown then ;
: lf-env-step ( xt i -- outcome fault? )
  lf-env-begin ok? 0= if drop outcome-invalid true exit then
  lf-env-run-check lf-env-hand-over lf-input-rollback ok? 0= or ;
\ The serial publisher of phase 2: every input declaration in input
\ order. ok when every slot is final; invalid when the run stopped on a
\ fault, with the slots before it published and the others not final, or
\ without a valid current environment.
: lf-env-steps ( xt n -- outcome )
  0 ?do dup i lf-env-step nip if drop unloop outcome-invalid exit then loop
  drop outcome-ok ;
: lf-env-run ( xt -- outcome )
  lf-env-current if lf-env-length lf-env-steps else drop outcome-invalid then ;
