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
\ accepted; its axiom set is the union of theirs with, for an axiom, its
\ own bit (core/axiom-allowlist.fs), its provenance the union of theirs and
\ "checked" in a final run; its kind is a definition, theorem or opaque
\ declaration with a value, or an axiom or quotient record without one,
\ safe, with distinct universe parameters. A failure is a fault in LeanForth and
\ makes the outcome invalid. Then it appends the dependencies to the pool
\ (full, with nothing appended or written, when there is no room: the
\ pool grew before the hand-over marked it, so only when the heap
\ refused, or the pool's identities are spent) and copies the input
\ declaration into the slot, so the record points at the very input
\ terms that were checked. Any other outcome is written
\ alone. For every outcome it also stores the candidate's lookups
\ (environment.fs, "Lookups"; plan step SN3), sealed at the hand-over (their
\ names beyond the input made the environment's own, step SN5), in the
\ lookup pool, grown, marked
\ and rolled back with the dependency pool; a list that lost an entry
\ makes the outcome full. A candidate the snapshot's loader filled
\ (lf-env-saved!) is re-checked as any other and its slots marked saved.
\ Last, it marks the slot final: the single point at which a
\ result becomes visible. Only an ok check followed by these steps makes
\ a slot final with outcome ok, and nothing changes a final slot.
\
\ The hand-over grows the pool when the candidate's dependencies need it
\ (environment.fs, "The pool"; plan task 6.2.0), marks the pool, then
\ publishes under CATCH: a THROW before
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
\ [kernel] code: not through the review gate (AGENTS.md).
\ State: none of its own. It writes environments (environment.fs), whose
\ header holds the publisher's pool mark, reads the candidate in the
\ current context and writes that context's worker record. A test that
\ defines lf-env-fault-hooks before loading this file also gets the
\ fault-injection hook lf-env-before-final (a DEFER, shared).

require ../lib/lib.fs
require ../core/derivation-log.fs
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

\ Block publication (ADR 0015 B5; plan task 5.2.1a): a candidate's span
\ (environment.fs) covers its declaration's slot and the next span-1, an
\ inductive block's members, all written with the one outcome, record
\ and dependencies, and marked final together, last. Slot k of the span.
: lf-slot+ ( slot k -- slot' ) /lf-slot * + ;
: lf-span-open? ( slot -- flag )
  false lf-cand-span@ 0 ?do over i lf-slot+ lf-slot-open? or loop nip ;
: lf-span-all-open? ( slot -- flag )
  true lf-cand-span@ 0 ?do over i lf-slot+ lf-slot-open? and loop nip ;
\ The first slot this context's candidate is for: (slot true) when its
\ snapshot is a check of the valid current environment and every slot of
\ its span is in range and not final.
: lf-env-span-fits? ( env i -- flag ) lf-cand-span@ + swap lf-env-length upto? ;
: lf-env-target ( -- slot true | false )
  lf-env-checking 0= if false exit then 2dup lf-env-span-fits? 0= if 2drop false exit then
  swap lf-env-slot dup lf-span-all-open? ?keep ;

\ E4 step 1. The dependencies: a count in range, each readable and
\ accepted in the snapshot (so below the declaration and final), each
\ above the one before.
: lf-dep@ ( k -- d ) lf-cand-dep @ ;
: lf-recheck-order? ( k -- flag )
  dup 0= if drop true exit then dup 1- lf-dep@ swap lf-dep@ < ;
: lf-recheck-dep? ( k -- flag )
  dup lf-dep@ lf-env-usable nip ok? swap lf-recheck-order? and ;
: lf-recheck-deps? ( -- flag )
  lf-cand-count? 0= if false exit then
  true lf-cand-count@ 0 ?do i lf-recheck-dep? and loop ;
\ The union of a slot field over the dependencies, read from the slots.
\ Unchecked: the dependencies passed lf-recheck-deps?.
: lf-dep-slot ( k -- slot ) lf-dep@ lf-env lf-env-slot ;
: lf-deps-union ( field -- bits )
  0 lf-cand-count@ 0 ?do over i lf-dep-slot swap execute @ or loop nip ;
\ The axiom set: the union of the dependencies' and, for an axiom, its
\ own bit, computed again (environment.fs lf-own-axiom). Any bit may be
\ set: an axiom outside the allowlist is accepted as Lean accepts it and
\ marked NOT PROVED where results are reported (owner decision 4 as
\ amended).
: lf-recheck-own ( -- bits )
  lf-env-limit lf-input-decl lf-own-axiom ok? 0= if drop -1 then ;
: lf-recheck-axioms? ( -- flag )
  ['] lf-slot-axioms lf-deps-union lf-recheck-own or lf-env-cand lf-cand-axioms @ = ;
: lf-final-run? ( -- flag ) lf-env lf-envh-mode @ lf-mode-final = ;
: lf-provenance-ok? ( bits -- flag ) lf-provenance-checked = lf-final-run? 0= or ;
\ A candidate the snapshot's loader filled (lf-env-saved!) adds saved.
: lf-cand-own ( -- bits ) lf-env-cand lf-cand-saved @ 0<> lf-provenance-saved and ;
: lf-recheck-provenance? ( -- flag )
  ['] lf-slot-provenance lf-deps-union lf-cand-own or
  dup lf-env-cand lf-cand-provenance @ = swap lf-provenance-ok? and ;
\ N2 and K5 (as amended): every slot below the declaration with its name
\ is final (G-P5) and rejected, not skipped. One that is open, accepted,
\ added, skipped, undecided or unsupported is a conflict: lf-env-own-name
\ would not have said ok. The
\ name store is audited first, as the scan and the parameters need it.
: lf-slot-conflict? ( slot -- flag )
  dup lf-slot-open? over lf-slot-added? or over lf-slot-skipped? or
  swap lf-slot-outcome@ outcome-rejected <> or ;
\ For a span, every member's name, each below the first member.
: lf-own-matches ( test k -- n )
  lf-env-limit + lf-input-name swap lf-env-limit lf-env-matches ;
\ A name Lean's generated recursor of an earlier type holds (environment.fs,
\ lf-env-reserving) is a conflict too, unless nothing holds it; and so is
\ one of the four quotient names that an earlier quotient record holds
\ (lf-env-quot-holding), for any declaration but a quotient record
\ (quot.fs checks those as add_quot does).
: lf-own-quot ( d -- n )
  dup lf-input-decl lf-idecl-kind @ lf-kind-quotient = if drop 0 exit then
  lf-input-name lf-env-limit lf-env-quot-holding nip outcome-rejected <> 1 and ;
: lf-own-held ( k -- n )
  lf-env-limit + dup lf-input-name lf-env-limit lf-env-reserving nip
  outcome-rejected <> 1 and swap lf-own-quot + ;
: lf-span-conflicts ( -- n )
  0 lf-cand-span@ 0 ?do ['] lf-slot-conflict? i lf-own-matches + i lf-own-held + loop ;
: lf-recheck-name? ( -- flag )
  lf-name-storage-valid? if lf-span-conflicts 0= else false then ;
\ Kind and safety in scope (ADR 0011), a value exactly for the kinds that
\ have one (environment.fs lf-kind-valued?), distinct parameters (L3).
: lf-recheck-value? ( decl -- flag )
  dup lf-idecl-value @ swap lf-idecl-kind @ lf-kind-valued?
  if lf-term-root? else -1 = then ;
: lf-recheck-kind? ( decl -- flag )
  dup lf-idecl-kind @ dup lf-kind-valued? swap lf-kind-bare? or
  over lf-idecl-safety @ lf-safety-safe = and swap lf-recheck-value? and ;
\ A block's member (ADR 0015): an inductive type, constructor or recursor,
\ safe, without a value, in the same block as the first member, which the
\ block's header names, and the span exactly the header's members.
: lf-block-kind? ( kind -- flag ) lf-kind-inductive lf-kind-recursor between? ;
: lf-recheck-member? ( decl -- flag )
  dup lf-idecl-kind @ lf-block-kind? over lf-idecl-safety @ lf-safety-safe = and
  over lf-idecl-value @ -1 = and
  swap lf-idecl-block @ lf-env-limit lf-input-decl lf-idecl-block @ = and ;
: lf-header-fits? ( decl -- flag )
  lf-idecl-header ?dup 0= if false exit then
  dup lf-hdr-first lf-more-field lf-env-limit = swap
  dup lf-hdr-types lf-more-field over lf-hdr-ctors lf-more-field +
  swap lf-hdr-recs lf-more-field + lf-cand-span@ = and ;
: lf-recheck-members? ( -- flag )
  lf-env-limit lf-input-decl lf-header-fits? 0= if false exit then
  true lf-cand-span@ 0 ?do lf-env-limit i + lf-input-decl lf-recheck-member? and loop ;
: lf-recheck-one? ( decl -- flag ) lf-recheck-kind? lf-cand-span@ 1 = and ;
\ A block rejected only by B3 (lf-env-added!) publishes its type's and
\ constructors' slots with the type's universe parameters, as Lean's
\ kernel declares them (its file records may differ: B3 field 1); only
\ the type's are re-checked then. A quotient record's never are: add_quot
\ never reads the record (quot.cpp 47-104), so its check takes no L3 step
\ either (check-declaration.fs; review rvAX M1).
: lf-cand-added? ( -- flag ) lf-env-cand lf-cand-added @ 0<> ;
: lf-member-kind ( k -- kind ) lf-env-limit + lf-input-decl lf-idecl-kind @ ;
: lf-member-checked? ( k -- flag )
  dup lf-member-kind lf-kind-quotient = if drop false exit then
  lf-cand-added? if lf-member-kind lf-kind-inductive = else drop true then ;
: lf-recheck-params? ( -- flag )
  true lf-cand-span@ 0 ?do i lf-member-checked? if
    lf-env-limit i + lf-input-decl lf-idecl-params@ lf-params-distinct? and then
  loop ;
\ Only a block's check says it was rejected by B3 alone (lf-env-added!;
\ review rvSN3 m4).
: lf-recheck-lone? ( decl -- flag ) lf-recheck-one? lf-cand-added? 0= and ;
: lf-recheck-decl? ( -- flag )
  lf-env-limit lf-input-decl dup lf-idecl-block @
  if drop lf-recheck-members? else lf-recheck-lone? then lf-recheck-params? and ;
\ The re-checks ( -- flag ), in order, each relying on the ones before:
\ part 1 the dependencies, 2 the axiom set, 3 the provenance, 4 the name
\ (N2, K5, G-P5; or a corrupted name store), 5 the kind, safety, value or
\ parameters. The part after the last, lf-recheck-moved, is lf-env-step's:
\ a check that moved its snapshot; the next, lf-recheck-skipped, a skipped
\ claim on a safe declaration (lf-recheck-skip below).
create lf-rechecks
  ' lf-recheck-deps? , ' lf-recheck-axioms? , ' lf-recheck-provenance? ,
  ' lf-recheck-name? , ' lf-recheck-decl? ,
here lf-rechecks - 1 cells / constant lf-rechecks#
lf-rechecks# 1+ constant lf-recheck-moved
lf-recheck-moved 1+ constant lf-recheck-skipped
lf-recheck-skipped 1+ constant lf-recheck-early
: lf-recheck@ ( k -- xt ) cells lf-rechecks + @ ;
\ The first re-check that fails, (part true), or false when all pass.
: lf-recheck ( -- part true | false )
  lf-rechecks# 0 ?do i lf-recheck@ execute 0= if i 1+ true unloop exit then loop false ;
: lf-recheck-failed ( part -- outcome )
  lf-env-limit swap c" env-publish lf-env-hand-over" lf-diag-recheck lf-diag-note
  outcome-invalid ;
\ The outcome to record: the check's; ok only when the re-check passes.
: lf-cand-outcome@ ( -- outcome ) lf-env-cand lf-cand-outcome @ outcome-sane ;
\ A block rejected only by B3 is recorded too (ADR 0015 decision 11: its
\ type and constructors are usable), so it is re-checked as an accepted
\ one; one that fails the re-check is invalid and not added.
: lf-env-recorded? ( outcome -- flag )
  dup ok? swap outcome-rejected = lf-cand-added? and or ;
\ A skipped claim (lf-env-skipped!) is marked only on a rejected outcome,
\ and stands only when the input marks every member of the span unsafe
\ or partial; any other is a fault (part lf-recheck-skipped): invalid,
\ nothing marked.
: lf-cand-skipped? ( outcome -- flag )
  outcome-rejected = lf-env-cand lf-cand-skipped @ 0<> and ;
: lf-member-safe? ( k -- flag )
  lf-env-limit + lf-input-decl lf-idecl-safety @ lf-safety-safe = ;
: lf-span-unsafe? ( -- flag ) true lf-cand-span@ 0 ?do i lf-member-safe? 0= and loop ;
: lf-recheck-skip ( outcome -- outcome )
  dup lf-cand-skipped? lf-span-unsafe? 0= and 0= if exit then
  drop lf-recheck-skipped lf-recheck-failed false lf-env-skipped! ;
\ A claim to record that passed the re-checks, from a check that found a
\ slot below it not final (environment.fs, lf-env-early?: it began too
\ early, G-P5), is a fault too (part lf-recheck-early): invalid, nothing
\ added. The parallel scheduler never hands such a check over; a serial
\ run never makes one.
: lf-recheck-in-time ( outcome -- outcome )
  lf-env-early? 0= if exit then
  drop lf-recheck-early lf-recheck-failed false lf-env-added! ;
\ A check whose lookup list lost an entry (no heap; environment.fs,
\ "Lookups") is full whatever it found: a snapshot must never store an
\ incomplete list.
: lf-cand-lost? ( -- flag ) lf-env-cand lf-cand-lost @ 0<> ;
: lf-looks-lost ( -- outcome )
  lf-env-limit lf-cand-looked@ c" env-publish lf-env-hand-over" lf-diag-lookups-full
  lf-diag-note outcome-full ;
: lf-env-verdict ( -- outcome )
  lf-cand-lost? if lf-looks-lost exit then
  lf-cand-outcome@ lf-recheck-skip dup lf-env-recorded? 0= if exit then
  lf-recheck if nip lf-recheck-failed false lf-env-added! exit then lf-recheck-in-time ;

\ E4 step 2 for an ok outcome. The pool has room for n more when both its
\ records and its identities suffice; a refusal after that check is a
\ fault and throws.
: lf-pool-free ( store -- u ) dup store-capacity @ swap store-count @ - ;
: lf-pool-ids ( store -- u ) max-n swap store-serial @ - ;
: lf-pool-room? ( n store -- flag )
  2dup lf-pool-free upto? -rot lf-pool-ids upto? and ;
\ Growing the pool (environment.fs, "The pool"), before the hand-over
\ marks it: a new block with room for the n more, at least twice the
\ old room and 16, the store copied in (records, identities and
\ counters), the old block linked from it, and then, last, the new one
\ current. A heap that refuses leaves the pool as it was, and the
\ append then finds it full. Only a candidate with a sound count asks,
\ only of a sound pool whose records are too few and identities enough
\ (growing would not give it more identities).
: lf-pool-wanted ( n store -- room )
  tuck store-count @ + swap store-capacity @ 2* max 16 max ;
\ Move n cells from old's area to new's, xt ( store -- addr ) finding
\ the area; copy a header field of old's into new's.
: lf-pool-area ( old new n xt -- old new )
  swap >r >r over r@ execute over r> execute r> cells move ;
: lf-pool-field ( old new xt -- old new ) >r over r@ execute @ over r> execute ! ;
: lf-pool-copy ( old new -- )
  over store-count @ dup >r ['] store-identities lf-pool-area r> ['] store-records lf-pool-area
  ['] store-serial lf-pool-field ['] store-generation lf-pool-field
  ['] store-count lf-pool-field 2drop ;
\ The two pools (environment.fs): the dependencies' and the lookups',
\ each named by its header field ( env -- addr ), grown the same way.
: lf-pool-install ( block field -- )
  lf-env-may-write lf-env swap execute dup @ rot tuck ! swap ! ;
: lf-pool-grow ( n store field -- )
  lf-env-may-write >r tuck lf-pool-wanted lf-pool-block ok? 0= if r> drop 2drop exit then
  tuck cell+ lf-pool-copy r> lf-pool-install ;
: lf-pool-short? ( n store -- flag )
  2dup lf-pool-free upto? 0= -rot lf-pool-ids upto? and ;
\ Grow the pool of field for n more records when it is sound and short.
: lf-pool-sized ( n field -- )
  >r lf-env r@ execute @ cell+ dup store-count-valid? 0= if 2drop r> drop exit then
  2dup lf-pool-short? if r> lf-pool-grow else 2drop r> drop then ;
: lf-pool-ready ( -- )
  lf-cand-count? 0= if exit then lf-cand-count@ ['] lf-envh-pool lf-pool-sized
  lf-cand-looked@ 2* ['] lf-envh-looks lf-pool-sized ;
: lf-pool-put ( d store -- )
  lf-env-may-write dup store-new 0= abort" lf-env: pool refused" swap store-slot ! ;
: lf-pool-append ( store -- )
  lf-cand-count@ 0 ?do i lf-dep@ over lf-pool-put loop drop ;
\ Append the candidate's dependencies: (first ok), or (-1 full) with
\ nothing appended.
: lf-pool-take ( store -- first outcome )
  dup store-count @ swap lf-pool-append outcome-ok ;
: lf-pool-full ( n store -- -1 outcome )
  dup store-count @ rot + swap store-capacity @ c" env-publish lf-env-append"
  lf-diag-pool-full lf-diag-note -1 outcome-full ;
: lf-env-append ( -- first outcome )
  lf-env lf-env-pool lf-cand-count@ over lf-pool-room?
  if lf-pool-take else lf-cand-count@ swap lf-pool-full then ;
\ The candidate's lookups into the lookup pool, key then answer:
\ (first ok), or (-1 full) with nothing appended.
: lf-pool-pair ( answer key store -- store ) tuck lf-pool-put tuck lf-pool-put ;
: lf-looks-put ( store -- )
  lf-cand-looked@ 0 ?do i lf-look-at 2@ rot lf-pool-pair loop drop ;
: lf-looks-room? ( -- flag ) lf-cand-looked@ 2* lf-env lf-env-looks lf-pool-room? ;
: lf-looks-full ( -- -1 outcome ) lf-cand-looked@ 2* lf-env lf-env-looks lf-pool-full ;
: lf-looks-append ( -- first outcome )
  lf-looks-room? 0= if lf-looks-full exit then
  lf-env lf-env-looks dup store-count @ swap lf-looks-put outcome-ok ;
\ Slot k of the span gets declaration limit+k, copied whole.
: lf-slot-input! ( k slot -- )
  lf-env-may-write swap lf-env-limit + lf-input-decl swap lf-slot-decl /lf-idecl move ;
: lf-slot-recipe! ( slot -- ) lf-env-cand lf-cand-recipe @ swap lf-slot-recipe ! ;
: lf-slot-sets! ( slot -- )
  lf-env-may-write lf-env-cand lf-cand-axioms @ over lf-slot-axioms !
  dup lf-slot-recipe!
  lf-env-cand lf-cand-warnings @ over lf-slot-warnings !
  lf-env-cand lf-cand-provenance @ swap lf-slot-provenance ! ;
: lf-slot-deps! ( first slot -- )
  lf-env-may-write tuck lf-slot-deps ! lf-cand-count@ swap lf-slot-count ! ;
\ Member k's shape, which the block's check computed (lf-env-shape!).
: lf-slot-shape! ( k slot -- )
  lf-env-may-write swap lf-cand-shape@ swap lf-slot-shape ! ;
: lf-slot-fill ( first k slot -- )
  2dup lf-slot-shape! rot over lf-slot-deps! tuck lf-slot-input! lf-slot-sets! ;
: lf-span-fill ( first slot -- )
  lf-env-may-write lf-cand-span@ 0 ?do 2dup i swap i lf-slot+ lf-slot-fill loop 2drop ;
\ Every slot of the span gets the one list of lookups from first.
: lf-slot-looks! ( first slot -- )
  lf-env-may-write tuck lf-slot-looks ! lf-cand-looked@ swap lf-slot-looked ! ;
: lf-span-looks ( first slot -- ) lf-cand-span@ 0 ?do 2dup i lf-slot+ lf-slot-looks! loop
  2drop ;
\ The record of an accepted declaration, or of every member of an
\ accepted block, sharing one list of dependencies and one of lookups:
\ (slot ok), or (slot full) with nothing appended or written.
: lf-env-record ( slot -- slot outcome )
  lf-looks-room? 0= if lf-looks-full nip exit then
  lf-env-append dup ok? 0= if nip exit then drop over lf-span-fill
  lf-looks-append drop over lf-span-looks outcome-ok ;
\ Any other outcome keeps the lookups alone (a later import replays them,
\ ADR 0020 D5): (slot outcome), or (slot full) with nothing appended.
: lf-env-looked ( slot outcome -- slot outcome' )
  lf-cand-looked@ 0= if exit then
  >r lf-looks-append ok? if over lf-span-looks r> else drop r> drop outcome-full then ;
\ E4 step 3: the outcome of every slot of the span, the fault-injection
\ point, then, last, the marks.
: lf-span-outcome! ( slot outcome -- )
  lf-env-may-write lf-cand-span@ 0 ?do 2dup swap i lf-slot+ lf-slot-outcome ! loop 2drop ;
\ A block rejected only by B3 (lf-env-added!): member k's name is taken
\ when it is the type or a constructor, which Lean's kernel added; the
\ file's recursor is not (Lean's T.rec, which its type holds, may differ
\ from it, or have another name).
: lf-member-added? ( k -- flag ) lf-member-kind lf-kind-recursor <> lf-cand-added? and ;
\ A constructor's slot takes the type's universe parameters (slot 0 of
\ the span is the type's).
: lf-slot-type-params! ( type-slot slot -- )
  swap lf-slot-decl swap lf-slot-decl
  over lf-idecl-param-at @ over lf-idecl-param-at !
  swap lf-idecl-arity @ swap lf-idecl-arity ! ;
: lf-member-added! ( slot k -- )
  2dup lf-slot+ over lf-member-added? over lf-slot-added !
  swap lf-member-kind lf-kind-constructor = lf-cand-added? and
  if lf-slot-type-params! else 2drop then ;
\ xt ( slot i -- ) for each member i of the candidate's span.
: lf-span-each ( slot xt -- )
  lf-env-may-write lf-cand-span@ 0 ?do 2dup i swap execute loop 2drop ;
: lf-span-added! ( slot -- ) ['] lf-member-added! lf-span-each ;
\ Slot k of the span: its place in it, then, last, final.
: lf-slot-final! ( slot k -- )
  tuck lf-slot+ tuck lf-slot-member ! lf-state-final swap lf-slot-state ! ;
: lf-span-final! ( slot -- ) ['] lf-slot-final! lf-span-each ;
\ A skipped declaration (lf-cand-skipped?): each slot of the span marked;
\ any other's marks cleared.
: lf-span-skipped! ( slot outcome -- )
  lf-env-may-write lf-cand-skipped? swap
  lf-cand-span@ 0 ?do 2dup i lf-slot+ lf-slot-skipped ! loop 2drop ;
\ A candidate of the snapshot's loader (lf-env-saved!): each slot of the
\ span marked saved.
: lf-span-saved! ( slot -- )
  lf-env-may-write lf-env-cand lf-cand-saved @ 0<>
  lf-cand-span@ 0 ?do over i lf-slot+ over swap lf-slot-saved ! loop 2drop ;
: lf-env-final ( slot outcome -- outcome )
  lf-env-may-write 2dup lf-span-outcome! 2dup lf-span-skipped! over lf-span-added!
  over lf-span-saved! lf-env-before-final swap lf-span-final! ;
\ Publish the candidate in this context into its slot: the outcome
\ recorded. Internal: only lf-env-hand-over calls it, outside jobs, under
\ CATCH, with the slot its target.
: lf-env-recorded ( slot outcome -- slot outcome' )
  >r lf-env-record dup ok? if drop r> else r> drop then ;
: lf-env-write ( slot -- outcome )
  lf-env-may-write lf-env-verdict dup lf-env-recorded?
  if lf-env-recorded else lf-env-looked then lf-env-final ;

\ After a THROW in the publisher: the diagnostic and, while the slot is
\ not final, the pool back to its mark and the slot cleared: not final,
\ its outcome invalid, every other field zero. A slot that became final
\ (only an asynchronous THROW, such as an interrupt, can arrive after the
\ final mark) keeps its record and dependencies. The hand-over is a fault
\ either way, so a refused rollback, which leaves pool entries that no
\ slot points to, needs no status of its own.
: lf-env-pub-mark ( -- mark store ) lf-env lf-envh-pub-mark lf-env lf-env-pool ;
: lf-env-look-mark ( -- mark store ) lf-env lf-envh-look-mark lf-env lf-env-looks ;
: lf-env-pub-fault ( ior -- )
  lf-env-limit swap c" env-publish lf-env-hand-over"
  lf-diag-publisher-fault lf-diag-note ;
\ Undo the publication into the span's open slots. A final slot never
\ changes: undoing a span with none open aborts (its callers test first,
\ so only a fault gets here). The pool goes back to its mark only when no
\ slot of the span became final, as a final one keeps its dependencies.
: lf-slot-clear ( slot -- ) lf-env-may-write dup /lf-slot erase lf-slot-invalid! ;
: lf-pools-back ( -- )
  lf-env-pub-mark store-rollback drop lf-env-look-mark store-rollback drop ;
: lf-span-clear ( slot -- )
  lf-env-may-write lf-cand-span@ 0 ?do
    dup i lf-slot+ dup lf-slot-open? if lf-slot-clear else drop then
  loop drop ;
: lf-env-undo ( slot -- )
  lf-env-may-write dup lf-span-open? 0= abort" lf-env: undo of a final slot"
  dup lf-span-all-open? if lf-pools-back then lf-span-clear ;
: lf-env-unpublish ( slot ior -- )
  lf-env-may-write lf-env-pub-fault dup lf-span-open? if lf-env-undo else drop then ;
\ The end of a publication that did not throw: (outcome false) when every
\ slot of the span is final; else a fault, recorded with code 0 and
\ undone as after a THROW: (invalid true), whatever outcome was written.
: lf-env-unfinished ( outcome slot -- invalid true )
  lf-env-may-write 0 lf-env-pub-fault lf-env-undo drop outcome-invalid true ;
: lf-env-ended ( outcome slot -- outcome fault? )
  lf-env-may-write dup lf-span-open? if lf-env-unfinished else drop false then ;
\ Grow the pool for the candidate when it must, mark it, then write the
\ slot under CATCH: (outcome false) once the slot is final; (invalid
\ true) when the pool cannot be marked (nothing written), after a THROW
\ (undone as above), or when the slot is still not final. CATCH may leave
\ its argument cell undefined, so a copy of the slot stays below it.
: lf-env-marked? ( -- flag )
  lf-env-may-write lf-env-pub-mark store-mark ok? lf-env-look-mark store-mark ok? and ;
: lf-env-guarded ( slot -- outcome fault? )
  lf-env-may-write lf-pool-ready lf-env-marked? 0= if drop outcome-invalid true exit then
  dup ['] lf-env-write catch ?dup if nip lf-env-unpublish outcome-invalid true exit then
  swap lf-env-ended ;
\ Publish the candidate in this context (E4): (outcome false) once its
\ slot is final; (invalid true), with nothing written, inside a job or a
\ check (G-P1), or when the candidate has no slot to publish (no check's
\ snapshot of the valid current environment, or its slot already final),
\ and as lf-env-guarded says. It drops the stamp first (environment.fs,
\ lf-env-held?), so every publication runs the full lf-env-current.
: lf-env-hand-over ( -- outcome fault? )
  lf-env-unhold context-in-job? if outcome-invalid true exit then
  lf-env-target if lf-env-seal lf-env-guarded else outcome-invalid true then ;

\ A check in this context threw ior (G-P6): the declaration is invalid,
\ recorded as an internal fault, and the context is spent. lf-env-step
\ and lf-env-hand-over-job call it.
: lf-env-thrown ( ior -- )
  lf-env-limit swap c" env-publish lf-env-step" lf-diag-publisher-fault lf-diag-note
  outcome-invalid lf-env-finish lf-env-spend ;
\ Whether this context's snapshot is still a check of declaration i; a
\ check that began another one is a fault, and nothing is published.
\ lf-env-hand-over-at drops the stamp first: the full check runs here too.
: lf-env-still? ( i -- flag ) lf-env-checking if nip = else drop false then ;
: lf-env-moved ( i -- outcome true )
  lf-recheck-moved c" env-publish lf-env-step" lf-diag-recheck lf-diag-note
  outcome-invalid true ;
: lf-env-hand-over-at ( i -- outcome fault? )
  lf-env-unhold dup lf-env-still? if drop lf-env-hand-over else lf-env-moved then ;
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
\ The derivation log's publish step (ADR 0013): the slot, its number of
\ dependencies and the outcome published; the log then stops recording.
: lf-env-logged-publish ( outcome fault? -- outcome fault? )
  over >r lf-env-limit lf-cand-count@ r> lf-log-publish ;
: lf-env-step ( xt i -- outcome fault? )
  context-in-job? if 2drop outcome-invalid true exit then
  dup lf-env-begin ok? 0= if 2drop outcome-invalid true exit then
  lf-env-checked lf-env-logged-publish lf-input-rollback ok? 0= or ;

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
\ A block's member after its first, whose slot is final, was published
\ with the first (ADR 0015 B5): it is not checked again. Any other final
\ slot is still a fault when the run reaches it.
: lf-env-trailing? ( i -- flag )
  dup lf-input-decl lf-idecl-header ?dup 0= if drop false exit then
  lf-hdr-first lf-more-field <> ;
: lf-env-published? ( i -- flag )
  dup lf-env-trailing? swap lf-env lf-env-slot lf-slot-final? and ;
: lf-env-next ( check maker i -- check maker fault? )
  dup lf-env-published? if drop false exit then
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
