\ The single publisher of the checked environment (ADR 0012, E4, E6, E7)
\ and the serial driver of phase 2.
\
\ lf-env-hand-over takes the candidate a check left in the current
\ context and fills its slot. It is the publisher's only entry, and it
\ refuses inside a job or a check (G-P1: one writer, outside every job
\ and check). For an ok outcome it first re-checks the candidate's cheap
\ invariants against the environment (E4 step 1, as amended 2026-11-02):
\ every slot below it with the same name is final and rejected (N2, K5,
\ G-P5); its dependencies are ascending, distinct, below it, final and
\ accepted; its axiom set is the union of theirs and within the
\ allowlist, its provenance the union of theirs and "checked" in a final
\ run; its kind is a definition or theorem, safe, with a value and
\ distinct universe parameters. A failure is a fault in LeanForth and
\ makes the outcome invalid. Then it appends the dependencies to the pool
\ (full, with nothing appended or written, when there is no room) and
\ copies the input declaration into the slot, so the record points at
\ the very input terms that were checked. Any other outcome is written
\ alone. Last, it marks the slot final: the single point at which a
\ result becomes visible. Only an ok check followed by these steps makes
\ a slot final with outcome ok, and nothing changes a final slot.
\
\ The hand-over marks the pool, then publishes under CATCH: a THROW before
\ the final mark leaves the slot not final and cleared (outcome invalid)
\ and the pool rolled back (a slot already final is left as it is, with
\ its dependencies; undoing one aborts). That, a pool that cannot be
\ marked, a candidate with no slot to publish and a publication that ends
\ without a final slot are faults: invalid, after which the run stops.
\ Every internal word here that writes the environment, and every word
\ that ends or undoes a publication, first calls lf-env-may-write
\ (environment.fs), which throws lf-env-refused inside a job or a check.
\
\ lf-env-step checks one declaration: it begins the check, runs it,
\ makes sure the snapshot is still of that declaration, hands the
\ candidate over, and rolls the scratch above the input marks back,
\ whatever the outcome. The check runs as task.fs runs a job's word: with
\ the owner token lib/context.fs's context-check-owner, so that every
\ guard that refuses a job refuses it too (G-P1: it can neither publish
\ nor make, choose or free environments, nor make, select, free, claim or
\ release contexts); with the task's context and token restored
\ afterwards; and above a copy of the declaration's number, its stack
\ depth and that copy checked when it returns (lib/context.fs's
\ call-balanced: a change throws lf-env-unbalanced, the code of task.fs's
\ task-unbalanced).
\ A THROW in the check makes the declaration invalid and spends the
\ context (G-P6, lf-env-thrown): lf-env-begin refuses a spent context,
\ which must be replaced.
\
\ lf-env-run, the phase-2 scheduler, checks every declaration in input
\ order, in the current context until a check throws, then in a new
\ context from a maker the caller gives. The maker must make an idle
\ context holding the same input, loaded the same way: in v0 the input is
\ per context (src/core/input.fs), and the environment's fingerprint
\ covers the input stores' identities and generations, so it records how
\ the input was loaded and not only what it holds (a context that loaded
\ it twice is continued only by one that did the same). The run adopts a
\ context only when it is a context (an address that cannot be read is
\ not, where the host turns the memory fault into a THROW, as Gforth
\ does), idle, neither the main nor the current one, and not spent, and
\ only from a maker that left the current environment as it was; it
\ frees each context it made once that is spent or the run ends, never
\ one a maker gave that it refused, and returns to the caller's context,
\ which it never frees. A maker that leaves anything but its two cells
\ counts as one that threw; after the maker, as after a check, the run
\ restores the current context and owner token. The check and the maker
\ wait on the return stack while the other runs, out of reach of a word
\ with a wrong stack effect, which can change only cells of the run's
\ caller. A context in which a check threw stays spent: the main context,
\ which cannot be freed, then serves no further check for the rest of the
\ program. The run answers ok only when, at its end, the environment it
\ started in is still current and every slot is final.
\
\ In a parallel run the scheduler waits for a job, selects its context
\ and calls lf-env-hand-over-job with the job's ior and declaration: it
\ records a THROW (G-P6), makes sure the snapshot is still of that
\ declaration and hands the candidate over. The scheduler replaces the
\ context when lf-env-spent? holds; the pool's lock in job-submit orders
\ each publication before every check handed out afterwards (G-P2).
\ Publication must not pause or print.
\
\ Threat model. The check is kernel code under review (check-declaration,
\ plan task 2.2.3; the tests' synthetic check until then): it is not
\ trusted to be correct, and the guards here are defence in depth against
\ its bugs, not a defence against a hostile check. The maker and the
\ scheduler (whatever calls lf-env-run, lf-env-step, lf-env-hand-over-job
\ and the maker) are trusted harness code, relied on to use these words
\ as documented. The maker keeps its caller's token: the check owner
\ token would refuse the context-new and context-use it needs. Even so,
\ the environment fails closed on the misuse it can detect cheaply, and
\ only on that (docs/programming/CHECKED_ENVIRONMENT.md has the list):
\ - a check that throws, or changes the stack depth or the cell below
\   it: its declaration is invalid and its context spent;
\ - a check that calls a word that publishes, steps, runs, makes, chooses
\   or frees an environment, makes, selects, frees, claims or releases a
\   context, or submits or waits for a job: refused, nothing changed. The
\   word gives invalid, false (context-claim) or task-refused, and the
\   check carries on; or it aborts, as every internal word that writes
\   shared state does (lf-env-refused, before writing), which is a THROW
\   in the check unless the check catches it;
\ - a check that leaves another snapshot (begins another declaration,
\   takes a view): a fault, nothing published; one that claims ok where
\   the re-check fails: invalid; one that leaves another context or token
\   selected: both restored;
\ - a serial run that would end with a slot not final, or with another
\   environment current: invalid;
\ - a maker that throws, fails, leaves anything but two cells, gives
\   anything but a fresh context, or leaves another environment current:
\   the run stops, invalid; one that leaves another context or token
\   selected: both restored;
\ - a hand-over inside a job or a check, without a check's snapshot, for
\   a final slot or a moved snapshot: a fault, nothing published.
\ Not detected: a check, maker or scheduler that writes memory outside
\ what these words let it (the slots, pool and header of an environment,
\ lf-envs, other contexts' records) beyond what the end of a serial run
\ sees, also through library words on an environment's addresses (such
\ as store-rollback on its pool and lf-env-pub-mark, which can let a
\ later publication overwrite an accepted slot's dependencies: no guard
\ sees a library word), unbalances the return stack, or changes cells
\ below its frame; a check that stores into its task's owner token,
\ lf-owner, which every G-P1 guard reads (0 switches them all off until
\ the check returns; the token is then restored); a maker that gives a
\ context it did not make (the run adopts and frees it), keeps one the
\ run refused (the run says only invalid), or frees a context the run
\ uses, its caller's or the current one (the run then reads or selects
\ freed memory, which is undefined); a scheduler that publishes while
\ checks run without G-P2's ordering, frees an environment in use, or
\ never rolls the scratch back.
\
\ Failures are explained in the context's diagnostic: a failed re-check
\ (lf-diag-recheck, with the part that failed, or lf-recheck-moved for a
\ check that moved its snapshot), no room in the pool (lf-diag-pool-full)
\ and a THROW in a check or in the publisher (lf-diag-publisher-fault,
\ with the THROW code; 0 for a publication that ended without a final
\ slot).
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
\ parameters. The part after the last, lf-recheck-moved, is lf-env-step's:
\ a check that moved its snapshot.
create lf-rechecks
  ' lf-recheck-deps? , ' lf-recheck-axioms? , ' lf-recheck-provenance? ,
  ' lf-recheck-name? , ' lf-recheck-decl? ,
here lf-rechecks - 1 cells / constant lf-rechecks#
lf-rechecks# 1+ constant lf-recheck-moved
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
  lf-env-may-write dup store-new 0= abort" lf-env: pool refused" swap store-slot ! ;
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
  lf-env-may-write lf-env-limit lf-input-decl swap lf-slot-decl /lf-idecl move ;
: lf-slot-sets! ( slot -- )
  lf-env-may-write lf-env-cand lf-cand-axioms @ over lf-slot-axioms !
  lf-env-cand lf-cand-provenance @ swap lf-slot-provenance ! ;
: lf-slot-deps! ( first slot -- )
  lf-env-may-write tuck lf-slot-deps ! lf-cand-count@ swap lf-slot-count ! ;
: lf-slot-fill ( first slot -- ) tuck lf-slot-deps! dup lf-slot-input! lf-slot-sets! ;
\ The record of an accepted declaration: (slot ok), or (slot full) with
\ nothing appended or written.
: lf-env-record ( slot -- slot outcome )
  lf-env-append dup ok? 0= if nip exit then drop over lf-slot-fill outcome-ok ;
\ E4 step 3: the outcome, the fault-injection point, then, last, the mark.
: lf-env-final ( slot outcome -- outcome )
  lf-env-may-write 2dup swap lf-slot-outcome ! lf-env-before-final
  lf-state-final rot lf-slot-state ! ;
\ Publish the candidate in this context into its slot: the outcome
\ recorded. Internal: only lf-env-hand-over calls it, outside jobs, under
\ CATCH, with the slot its target.
: lf-env-write ( slot -- outcome )
  lf-env-may-write lf-env-verdict dup ok? if drop lf-env-record then lf-env-final ;

\ After a THROW in the publisher: the diagnostic and, while the slot is
\ not final, the pool back to its mark and the slot cleared: not final,
\ its outcome invalid, every other field zero. A slot that became final
\ (only an asynchronous THROW, such as an interrupt, can arrive after the
\ final mark) keeps its record and dependencies. The hand-over is a fault
\ either way, so a refused rollback, which leaves pool entries that no
\ slot points to, needs no status of its own.
: lf-env-pub-mark ( -- mark store ) lf-env lf-envh-pub-mark lf-env lf-env-pool ;
: lf-env-pub-fault ( ior -- )
  lf-env-limit swap c" env-publish lf-env-hand-over"
  lf-diag-publisher-fault lf-diag-note ;
\ Undo the publication into an open slot. A final slot never changes:
\ undoing one aborts (its callers test first, so only a fault gets here).
: lf-env-undo ( slot -- )
  lf-env-may-write dup lf-slot-open? 0= abort" lf-env: undo of a final slot"
  lf-env-pub-mark store-rollback drop dup /lf-slot erase lf-slot-invalid! ;
: lf-env-unpublish ( slot ior -- )
  lf-env-may-write lf-env-pub-fault dup lf-slot-open? if lf-env-undo else drop then ;
\ The end of a publication that did not throw: (outcome false) when the
\ slot is final; else a fault, recorded with code 0 and undone as after a
\ THROW: (invalid true), whatever outcome was written.
: lf-env-unfinished ( outcome slot -- invalid true )
  lf-env-may-write 0 lf-env-pub-fault lf-env-undo drop outcome-invalid true ;
: lf-env-ended ( outcome slot -- outcome fault? )
  lf-env-may-write dup lf-slot-open? if lf-env-unfinished else drop false then ;
\ Mark the pool, then write the slot under CATCH: (outcome false) once the
\ slot is final; (invalid true) when the pool cannot be marked (nothing
\ written), after a THROW (undone as above), or when the slot is still
\ not final. CATCH may leave its argument cell undefined, so a copy of
\ the slot stays below it.
: lf-env-marked? ( -- flag ) lf-env-may-write lf-env-pub-mark store-mark ok? ;
: lf-env-guarded ( slot -- outcome fault? )
  lf-env-may-write lf-env-marked? 0= if drop outcome-invalid true exit then
  dup ['] lf-env-write catch ?dup if nip lf-env-unpublish outcome-invalid true exit then
  swap lf-env-ended ;
\ Publish the candidate in this context (E4): (outcome false) once its
\ slot is final; (invalid true), with nothing written, inside a job or a
\ check (G-P1), or when the candidate has no slot to publish (no check's
\ snapshot of the valid current environment, or its slot already final),
\ and as lf-env-guarded says.
: lf-env-hand-over ( -- outcome fault? )
  context-in-job? if outcome-invalid true exit then
  lf-env-target if lf-env-guarded else outcome-invalid true then ;

\ A check in this context threw ior (G-P6): the declaration is invalid,
\ recorded as an internal fault, and the context is spent. lf-env-step
\ and lf-env-hand-over-job call it.
: lf-env-thrown ( ior -- )
  lf-env-limit swap c" env-publish lf-env-step" lf-diag-publisher-fault lf-diag-note
  outcome-invalid lf-env-finish lf-env-spend ;
\ Whether this context's snapshot is still a check of declaration i; a
\ check that began another one is a fault, and nothing is published.
: lf-env-still? ( i -- flag ) lf-env-checking if nip = else drop false then ;
: lf-env-moved ( i -- outcome true )
  lf-recheck-moved c" env-publish lf-env-step" lf-diag-recheck lf-diag-note
  outcome-invalid true ;
: lf-env-hand-over-at ( i -- outcome fault? )
  dup lf-env-still? if drop lf-env-hand-over else lf-env-moved then ;
\ The parallel scheduler's entry, after the job that checked declaration
\ i in this context ended with ior: a THROW is recorded (G-P6), then the
\ candidate handed over while the snapshot is still of declaration i. The
\ outcome published and whether the run must stop, as lf-env-step gives
\ them, except that the scheduler rolls the scratch back itself. Inside a
\ job or a check (G-P1) it is refused first, (invalid true), with nothing
\ changed: no THROW recorded, the context not spent.
: lf-env-hand-over-job ( ior i -- outcome fault? )
  context-in-job? if 2drop outcome-invalid true exit then
  swap ?dup if lf-env-thrown then lf-env-hand-over-at ;

\ Running a check (G-P1, G-P6), as task.fs's job-run and job-call run a
\ job's word. The check's word xt ( -- ) runs above x, the declaration's
\ number, with lib/context.fs's call-balanced: x and the stack depth must
\ be unchanged when it returns, else it throws context-unbalanced (here
\ also named lf-env-unbalanced), task.fs's code for task-unbalanced.
\ It runs under CATCH (which leaves its two argument cells undefined
\ after a THROW) with the token context-check-owner, the task's context
\ and token restored afterwards: 0, or the THROW code.
context-unbalanced constant lf-env-unbalanced
: lf-env-caught ( x xt -- ior ) ['] call-balanced catch dup if nip nip then ;
: lf-env-as-check ( x xt -- ior )
  lf-context @ lf-owner @ 2>r context-check-owner lf-owner ! lf-env-caught
  2r> lf-owner ! lf-context ! ;
: lf-env-run-check ( i xt -- ) lf-env-as-check ?dup if lf-env-thrown then ;
: lf-env-checked ( xt i -- outcome fault? )
  dup >r swap lf-env-run-check r> lf-env-hand-over-at ;
\ Check declaration i in this context with xt ( -- ), which ends with
\ lf-env-finish; a THROW in it, or a changed stack, makes the declaration
\ invalid and spends the context. Then, while the snapshot is still of
\ declaration i, hand the candidate over, and roll the scratch back to the
\ input marks. Gives the outcome published and whether the run must stop:
\ a refused start (inside a job or a check, in a spent context, ...), a
\ moved snapshot, a fault in the publisher or a failed rollback.
: lf-env-step ( xt i -- outcome fault? )
  context-in-job? if 2drop outcome-invalid true exit then
  dup lf-env-begin ok? 0= if 2drop outcome-invalid true exit then
  lf-env-checked lf-input-rollback ok? 0= or ;

\ The serial run's contexts (G-P6). After a check threw, the run goes on
\ in a new context from maker ( -- context ior ), which must make an
\ idle context holding the same input and leave the current one
\ selected. A maker that throws or fails stops the run, and so does one
\ that gives anything but a context that is idle, neither the main nor
\ the current one, and not spent: refusing spent contexts protects the
\ caller's, which the run leaves only after a check threw in it. Nothing
\ is freed before the new context passes, and a context that does not
\ pass is left to the caller. A context the run made is freed once it is
\ spent and when the run ends.
: lf-env-made? ( -- flag ) lf-env-worker lf-worker-made @ ;
: lf-env-leave ( -- ior ) lf-env-made? if lf-context @ context-free else 0 then ;
\ The maker runs under CATCH, the current context and the owner token
\ restored afterwards, its stack depth checked as a check's is: one that
\ leaves anything but two cells counts as one that threw.
: lf-env-two ( maker -- context ior )
  depth >r execute depth r> 1+ = ?call-balanced ;
: lf-env-make ( maker -- context ior )
  lf-owner @ >r ['] lf-env-two context-catch r> lf-owner ! ?dup if nip 0 swap then ;
: lf-env-spent-in? ( context -- flag )
  lf-context @ swap lf-context ! lf-env-spent? swap lf-context ! ;
: lf-env-other? ( context -- flag )
  dup context-idle? over context-main <> and swap lf-context @ <> and ;
: lf-env-usable? ( context -- flag )
  dup lf-env-other? if lf-env-spent-in? 0= else drop false then ;
: lf-env-fresh? ( context -- flag ) dup context? if lf-env-usable? else drop false then ;
\ The same under CATCH, the current context restored: an address that
\ cannot be read is not a context to adopt, where the host turns the
\ memory fault into a THROW (-9 on Gforth); Forth-2012 leaves reading
\ such an address undefined.
: lf-env-fresh-caught? ( context -- flag )
  ['] lf-env-fresh? context-catch if drop false then ;
\ The context maker gave, when it may be adopted: (context true), else
\ false, with nothing freed.
: lf-env-given ( maker -- context true | false )
  lf-env-make if drop false else dup lf-env-fresh-caught? ?keep then ;
: lf-env-adopt ( context -- ) context-use true lf-env-worker lf-worker-made ! ;
\ Adopt a fresh context from maker, freeing the spent one if the run made
\ it: true, or false when the run must stop.
: lf-env-renewed ( maker -- flag )
  lf-env-given if lf-env-leave swap lf-env-adopt 0= else false then ;
\ Replace the current, spent context: true, or false when the run must
\ stop, also when the maker left another environment current (compared
\ by identity, which never repeats); the context it gave, if adopted, is
\ then freed when the run ends.
: lf-env-renew ( maker -- flag ) lf-env-id >r lf-env-renewed r> lf-env-id = and ;
\ Step i with check, then, if it threw, replace the context with one from
\ maker: whether the run must stop. Meanwhile check and maker wait on the
\ return stack, out of reach of either.
: lf-env-replace ( maker -- fault? )
  lf-env-spent? if lf-env-renew 0= else drop false then ;
: lf-env-try ( i check maker -- fault? )
  >r swap lf-env-step nip r> swap if drop true else lf-env-replace then ;
: lf-env-next ( check maker i -- check maker fault? )
  -rot 2dup 2>r lf-env-try 2r> rot ;
: lf-env-steps ( check maker n -- outcome )
  0 ?do i lf-env-next if 2drop unloop outcome-invalid exit then loop 2drop outcome-ok ;
\ Back in the caller's context, freeing the run's own: invalid if FREE
\ fails.
: lf-env-home ( outcome home -- outcome )
  >r lf-env-leave if drop outcome-invalid then r> context-use ;
\ The run's last word: ok stands only when the environment it started
\ in, by identity, is still current and live, and every slot is final.
: lf-slots-final? ( env -- flag )
  true over lf-env-length 0 ?do over i swap lf-env-slot lf-slot-final? and loop nip ;
: lf-env-finished? ( identity -- flag )
  lf-env-id = lf-env lf-env-live? and if lf-env lf-slots-final? else false then ;
: lf-env-confirm ( outcome identity -- outcome )
  lf-env-finished? 0= if drop outcome-invalid then ;
: lf-env-all ( check maker env -- outcome )
  lf-env-length lf-context @ >r lf-env-steps r> lf-env-home ;
\ The serial publisher of phase 2: every input declaration in input
\ order, checked with check ( -- ), new contexts from maker. ok when
\ every slot of the environment it started in is final and that is
\ still the current one; invalid when the run stopped on a fault, with
\ the slots before it published and the others not final, inside a job
\ or a check, without a valid current environment, when no new context
\ could be adopted after a THROW, or when a maker left another
\ environment current. The caller's context is current again afterwards.
: lf-env-run ( check maker -- outcome )
  context-in-job? if 2drop outcome-invalid exit then
  lf-env-current 0= if 2drop outcome-invalid exit then
  dup lf-envh-identity @ >r lf-env-all r> lf-env-confirm ;
