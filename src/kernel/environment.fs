\ The checked environment v0 (ADR 0012; plan task 2.2.2): LeanForth's
\ library of accepted declarations. An environment has one slot per input
\ declaration (src/core/input.fs): slot i for declaration i, so slot
\ numbers never depend on timing. Only the publisher (env-publish.fs)
\ writes a slot, once, after its declaration's check has ended: first the
\ outcome and, for an accepted declaration, its record (E2), then, last,
\ the state that makes it final. Until then the slot's outcome is invalid,
\ never ok. A final slot never changes, and only a final slot is ever read.
\
\ Identity (E3). Each environment gets a number from a serial that only
\ grows and never repeats; once it is spent no environment can be made.
\ An environment is never reset or rolled back: starting over means a new
\ one. It is bound to the fingerprint of the input it was made over: it is
\ valid only in a context whose input is intact and has that fingerprint,
\ so a context holding no input, or another one, fails closed (see
\ input.fs on why the input is per context in v0, and on the
\ fingerprint's limits). Environments are made, chosen and freed only
\ outside jobs (G-P1): inside one, lf-env-new, lf-env-use and lf-env-free
\ refuse with invalid. "Inside a job" includes a check that the serial
\ driver runs (env-publish.fs), which holds lib/context.fs's
\ context-check-owner token. Until a word list hides the internal words
\ (plan task 1.1.7), every internal word that writes shared state, here
\ and in env-publish.fs, first calls lf-env-may-write, which throws
\ lf-env-refused inside a job; the job's CATCH, or the serial driver's,
\ then makes the declaration invalid and spends the context (G-P6).
\
\ Checks (E4, E5, E7). The check of declaration i runs in its own context
\ (ADR 0009) and records there its snapshot, (identity, i), with
\ lf-env-begin; it may read slot d only when d < i and slot d is final.
\ It builds its candidate in the context: the accepted declarations it
\ uses (lf-env-resolve, lf-env-depend), ascending and distinct, with the
\ union of their axiom sets and provenance, and ends with lf-env-finish.
\ lf-env-lookup scans the earlier declarations of a name: the accepted one
\ gives it; else an undecided one (unknown, exhausted, full, invalid)
\ gives unknown, and else an unsupported one unsupported (K5; unknown
\ first when there are both, ADR 0012 E5 as amended); else rejected (N1:
\ unknown, forward and self references). A same-named earlier slot that
\ is not final means the check started too early: invalid. In a parallel
\ run a scheduler starts a check only when lf-env-ready? holds for every
\ name it uses and its own (G-P5). A context in which a check threw is
\ spent (G-P6, env-publish.fs): lf-env-begin refuses it, for good.
\
\ Handles (E3): (identity, d) of an accepted slot. In a snapshot
\ (identity', i) one is valid only when identity = identity', d < i and
\ slot d is final and accepted; every other handle is invalid. In a
\ parallel run a check must use handles only for slots its readiness made
\ final; phase 2 checks find constants by name and use none. Results
\ (lf-env-outcome, lf-env-axioms, lf-env-handle) are read within the
\ snapshot too, so a check never reads a later slot (G-P4); after a run,
\ lf-env-view gives a snapshot of every slot.
\
\ Outcomes (E9) are ADR 0008's. Every refusal is invalid; a candidate with
\ no room for another dependency is full. Nothing here ever makes a failed
\ check read as accepted. Failures are explained in the context's
\ diagnostic (core/diagnostics.fs) with the codes below, catalogued in
\ docs/programming/DIAGNOSTICS.md; recording never changes an outcome.
\ lf-env-begin clears the diagnostic.
\
\ [kernel] code: experimental, not through the review gate, not
\ independently audited. Phase-2 limits: lf-input-capacity slots,
\ lf-env-dep-capacity dependencies per check, lf-env-pool-max in a pool.
\ State: the shared record lf-envs (the identity serial and the current
\ environment; changed only while no job runs), each environment's
\ ALLOCATEd record (shared, outside every context: written only by the
\ publisher, which keeps its pool mark in the header, read by every
\ check), and two context records, one per context (ADR 0009): the
\ candidate lf-env-cand and the worker record lf-env-worker. An
\ environment must be freed only when no task uses it. The layout is
\ host-specific and never serialized.

require ../lib/lib.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../core/terms.fs
require ../core/input.fs

16 constant lf-env-dep-capacity     \ dependencies one check may record
65536 constant lf-env-pool-max      \ most dependencies one environment holds
1 constant lf-state-final           \ the state of a published slot
0 constant lf-mode-final            \ run modes (E8); phase 2 makes only final
1 constant lf-mode-development
0 constant lf-provenance-checked    \ checked in this run
1 constant lf-provenance-saved      \ from saved results, not re-checked here

\ The environment's diagnostic codes (15, 16, 25-29, 35, 41, 50-54) are
\ defined with the others in core/diagnostics.fs, whose catalogue names
\ them; DIAGNOSTICS.md documents them.

begin-structure /lf-envs
  field: lf-envs-serial     \ last identity issued; max-n once spent
  field: lf-envs-current    \ the current environment, or 0
end-structure
create lf-envs /lf-envs allot
lf-envs /lf-envs erase

\ An environment: this header, the slots, then the dependency pool, a
\ store of one cell per dependency.
begin-structure /lf-env
  field: lf-envh-identity   \ never repeats; 0 once freed
  field: lf-envh-input      \ the input's fingerprint when made
  field: lf-envh-length     \ number of slots: the input's declarations
  field: lf-envh-allowed    \ axiom bits the allowlist permits; none in version 0
                            \ (a test may set one on a synthetic environment)
  field: lf-envh-version    \ allowlist version
  field: lf-envh-mode       \ run mode
  /store-mark +field lf-envh-pub-mark   \ the publisher's pool mark while it publishes
end-structure

\ A slot (E2). Only the state and outcome mean anything for a declaration
\ that was not accepted; the other fields stay zero.
begin-structure /lf-slot
  field: lf-slot-state      \ lf-state-final once published, else not final
  field: lf-slot-outcome    \ the declaration's outcome (ADR 0008)
  /lf-idecl +field lf-slot-decl   \ the input declaration, copied whole
  field: lf-slot-deps       \ index of its first dependency in the pool
  field: lf-slot-count      \ its number of dependencies
  field: lf-slot-axioms     \ its transitive axiom set (E6)
  field: lf-slot-provenance \ lf-provenance-...
end-structure

\ A check's snapshot and candidate, in its context.
begin-structure /lf-cand
  field: lf-cand-identity   \ snapshot: the environment's identity; 0 for none
  field: lf-cand-decl       \ snapshot: the declaration checked; for a view, the length
  field: lf-cand-outcome    \ invalid until lf-env-finish
  field: lf-cand-axioms     \ union of the dependencies' axiom sets
  field: lf-cand-provenance \ union of their provenance
  field: lf-cand-count      \ dependencies recorded
  field: lf-cand-span       \ slots the outcome is for, from the checked one on:
                            \ an inductive block's members (ADR 0015 B5); 0 is 1
  lf-env-dep-capacity cells +field lf-cand-deps   \ their slots, ascending
end-structure
/lf-cand context-record: lf-env-cand
\ The candidate's span: how many slots, from the declaration checked on,
\ its outcome and record are for. A block's check sets it to the block's
\ members (kernel/check-block.fs); every other check leaves it 1.
: lf-cand-span@ ( -- n ) lf-env-cand lf-cand-span @ 1 max ;
: lf-env-span! ( n -- ) lf-env-cand lf-cand-span ! ;

\ A context as a worker (G-P6). Zero in a new context; never cleared.
begin-structure /lf-worker
  field: lf-worker-spent    \ true once a check in this context threw
  field: lf-worker-made     \ true when lf-env-run made this context
end-structure
/lf-worker context-record: lf-env-worker

\ Keep x with a true flag, drop it with a false one.
: ?keep ( x flag -- x true | false ) dup 0= if nip then ;
\ The THROW code of an internal word that would write shared state inside
\ a job or a check (G-P1); outside Forth-2012's reserved range and
\ task.fs's codes (-4096 to -4101).
-4110 constant lf-env-refused
: lf-env-may-write ( -- ) context-in-job? if lf-env-refused throw then ;

\ Layout. Unchecked: d is below the length.
: lf-env ( -- env ) lf-envs lf-envs-current @ ;
: lf-env-length ( env -- n ) lf-envh-length @ ;
: lf-env-slot ( d env -- slot ) /lf-env + swap /lf-slot * + ;
: lf-env-pool ( env -- store ) dup lf-env-length swap lf-env-slot ;
: lf-env-bytes ( slots deps -- u ) 1 cells store-size swap /lf-slot * + /lf-env + ;
: lf-env-in? ( d env -- flag ) lf-env-length 0 swap within ;

\ Sanity checks; like context?, they cannot recognise every stale
\ address. A live environment has an issued identity, a length within the
\ input's capacity and a sound pool.
: lf-env-serial ( -- addr ) lf-envs lf-envs-serial ;
: lf-env-sane? ( env -- flag )
  dup lf-envh-identity @ 1 lf-env-serial @ between?
  swap lf-env-length lf-input-capacity upto? and ;
: lf-env-live? ( env -- flag )
  ?dup 0= if false exit then
  dup lf-env-sane? if lf-env-pool store-count-valid? else drop false then ;
: lf-env-input? ( env -- flag )
  lf-envh-input @ lf-input-fingerprint = lf-input-intact? and ;
: lf-env-valid? ( env -- flag ) dup lf-env-live? if lf-env-input? else drop false then ;
\ The current environment, when it is live and this context's input is
\ intact and the one it was made over.
: lf-env-current ( -- env true | false ) lf-env dup lf-env-valid? ?keep ;

\ Making, freeing and choosing environments, only outside jobs (G-P1).
\ lf-env-new gives a new environment over this context's intact input,
\ with room for deps dependencies and the empty allowlist of version 0, in
\ final mode: (env ok); (0 invalid) inside a job, for an input that is not
\ intact or deps outside 0..lf-env-pool-max; (0 full) when the identities
\ are spent or memory cannot be allocated.
: lf-env-fields ( env -- env )
  lf-env-may-write lf-input-count over lf-envh-length !
  lf-input-fingerprint over lf-envh-input ! lf-mode-final over lf-envh-mode ! ;
: lf-env-identity+ ( env -- env )
  lf-env-may-write 1 lf-env-serial +! lf-env-serial @ over lf-envh-identity ! ;
\ Every slot starts not final with outcome invalid, never ok, though
\ nothing reads a slot before it is final. lf-env-unpublished writes only
\ through lf-slot-invalid!, which refuses inside a job.
: lf-slot-invalid! ( slot -- ) lf-env-may-write outcome-invalid swap lf-slot-outcome ! ;
: lf-env-unpublished ( env -- env )
  dup lf-env-length 0 ?do i over lf-env-slot lf-slot-invalid! loop ;
\ Format the pool as a store of deps one-cell entries: whether store-init
\ accepts that shape.
: lf-env-pool-init ( deps env -- flag ) lf-env-pool >r 1 cells 0 r> store-init ;
\ Format the slots and the pool and give the environment its identity:
\ (env ok); or (0 invalid), the memory freed, for a pool shape
\ store-init refuses.
: lf-env-made ( deps env -- env outcome )
  lf-env-may-write lf-env-fields lf-env-unpublished tuck lf-env-pool-init
  if lf-env-identity+ outcome-ok else free drop 0 outcome-invalid then ;
: lf-env-deps? ( deps -- flag ) 0 lf-env-pool-max between? ;
: lf-env-new-ok? ( deps -- flag )
  lf-env-deps? lf-input-intact? and context-in-job? 0= and ;
: lf-env-new ( deps -- env outcome )
  dup lf-env-new-ok? 0= if drop 0 outcome-invalid exit then
  lf-env-serial @ max-n = if drop 0 outcome-full exit then
  lf-input-count over lf-env-bytes allocate0 if 2drop 0 outcome-full exit then
  lf-env-made ;
\ Free a live environment: ok, or invalid when it is not live or inside
\ a job (nothing is freed) or FREE fails. Its identity is cleared first
\ and it stops being current.
: lf-env-choosable? ( env -- flag ) lf-env-live? context-in-job? 0= and ;
: lf-env-forget ( env -- env )
  lf-env-may-write dup lf-env = if 0 lf-envs lf-envs-current ! then
  0 over lf-envh-identity ! ;
: lf-env-free ( env -- outcome )
  dup lf-env-choosable? 0= if drop outcome-invalid exit then
  lf-env-forget free 0= flag>outcome ;
\ Make a live environment current: ok, or invalid with nothing changed
\ when it is not live or inside a job.
: lf-env-use ( env -- outcome )
  dup lf-env-choosable? 0= if drop outcome-invalid exit then
  lf-envs lf-envs-current ! outcome-ok ;

\ Slots.
: lf-slot-final? ( slot -- flag ) lf-slot-state @ lf-state-final = ;
: lf-slot-outcome@ ( slot -- outcome ) lf-slot-outcome @ outcome-sane ;
: lf-slot-accepted? ( slot -- flag ) dup lf-slot-final? swap lf-slot-outcome@ ok? and ;
: lf-slot-open? ( slot -- flag ) lf-slot-final? 0= ;
: lf-slot-unsupported? ( slot -- flag ) lf-slot-outcome@ outcome-unsupported = ;
\ Undecided (K5): unknown, exhausted, full or invalid.
: lf-slot-undecided? ( slot -- flag )
  lf-slot-outcome@ dup ok? over outcome-rejected = or swap outcome-unsupported = or 0= ;
: lf-final-slot ( slot -- slot true | false ) dup lf-slot-final? ?keep ;

\ Snapshots. lf-env-snapshot gives the current environment and this
\ context's snapshot of it, (env i true), when the snapshot is of that
\ environment; lf-env-checking the same for a check, not a view. A
\ failure records lf-diag-no-snapshot.
: lf-env-mine? ( env -- flag ) lf-envh-identity @ lf-env-cand lf-cand-identity @ = ;
: lf-env-limit ( -- i ) lf-env-cand lf-cand-decl @ ;
: lf-env-id ( -- identity ) lf-env ?dup if lf-envh-identity @ else 0 then ;
: lf-env-unseen ( -- false )
  lf-env-cand lf-cand-identity @ lf-env-id c" environment lf-env-snapshot"
  lf-diag-no-snapshot lf-diag-note false ;
: lf-env-keep ( env i flag -- env i true | false ) ?keep ?keep ;
: lf-env-ours ( -- env true | false )
  lf-env-current 0= if false exit then dup lf-env-mine? ?keep ;
: lf-env-snapshot ( -- env i true | false )
  lf-env-ours 0= if lf-env-unseen exit then
  lf-env-limit 2dup swap lf-env-length upto? lf-env-keep
  dup 0= if drop lf-env-unseen then ;
: lf-env-checking ( -- env i true | false )
  lf-env-snapshot 0= if false exit then 2dup swap lf-env-length < lf-env-keep ;
: lf-env-clear ( -- )
  lf-env-cand /lf-cand erase outcome-invalid lf-env-cand lf-cand-outcome ! ;
: lf-env-snap! ( i env -- )
  lf-envh-identity @ lf-env-cand lf-cand-identity ! lf-env-cand lf-cand-decl ! ;
: lf-env-open? ( i env -- flag )
  2dup lf-env-in? if lf-env-slot lf-slot-open? else 2drop false then ;
: lf-env-bad-start ( i -- outcome )
  0 c" environment lf-env-begin" lf-diag-bad-argument lf-diag-note outcome-invalid ;
\ A context in which a check threw is spent (G-P6): it must be freed and
\ replaced, never used for another check.
: lf-env-spent? ( -- flag ) lf-env-worker lf-worker-spent @ ;
: lf-env-spend ( -- ) true lf-env-worker lf-worker-spent ! ;
: lf-env-spent ( i -- outcome )
  0 c" environment lf-env-begin" lf-diag-publisher-fault lf-diag-note outcome-invalid ;
: lf-env-start ( i -- outcome )
  lf-env-current 0= if lf-env-unseen 2drop outcome-invalid exit then
  2dup lf-env-open? if lf-env-snap! outcome-ok else drop lf-env-bad-start then ;
\ Start the check of declaration i in this context: ok, recording its
\ snapshot; invalid, with no snapshot, in a spent context, without a
\ valid current environment or when slot i is out of range or already
\ final. The diagnostic is cleared, and the candidate starts empty, its
\ outcome invalid until lf-env-finish.
: lf-env-begin ( i -- outcome )
  dup lf-log-begin
  lf-diag-clear lf-env-clear lf-env-spent? if lf-env-spent else lf-env-start then ;
\ A snapshot of every slot, for queries once a run has ended: ok, or
\ invalid without a valid current environment. It is not a check.
: lf-env-view ( -- outcome )
  lf-env-clear lf-env-current 0= if outcome-invalid exit then
  dup lf-env-length swap lf-env-snap! outcome-ok ;
\ End the check with its outcome.
: lf-env-finish ( outcome -- ) outcome-sane lf-env-cand lf-cand-outcome ! ;

\ Reading slots in the snapshot. lf-env-readable gives slot d when the
\ snapshot may read it (d below its declaration, slot d final);
\ lf-env-accepted gives (slot ok) when slot d is also accepted, else
\ (0 invalid), recording lf-diag-env-handle.
: lf-env-below? ( d env i -- d env flag ) >r over 0 r> within ;
: lf-env-readable ( d -- slot true | false )
  lf-env-snapshot 0= if drop false exit then
  lf-env-below? if lf-env-slot lf-final-slot else 2drop false then ;
: lf-env-refuse ( d -- 0 outcome )
  lf-env-cand lf-cand-identity @ swap c" environment lf-env-accepted"
  lf-diag-env-handle lf-diag-note 0 outcome-invalid ;
: lf-env-accepted ( d -- slot outcome )
  dup lf-env-readable 0= if lf-env-refuse exit then
  dup lf-slot-accepted? if nip outcome-ok else drop lf-env-refuse then ;

\ Handles. lf-env-handle gives a handle to slot d of the current
\ environment, (identity d ok), when this context's snapshot may read it
\ and it is accepted, else (0 -1 invalid). lf-env-handle? checks a handle
\ in this context's snapshot: ok, or invalid recording lf-diag-env-handle.
: lf-env-handle ( d -- identity d outcome )
  dup lf-env-readable if lf-slot-accepted? else false then
  if lf-env lf-envh-identity @ swap outcome-ok else drop 0 -1 outcome-invalid then ;
: lf-env-foreign ( identity d -- outcome )
  c" environment lf-env-handle?" lf-diag-env-handle lf-diag-note outcome-invalid ;
: lf-env-handle? ( identity d -- outcome )
  over lf-env-cand lf-cand-identity @ <> if lf-env-foreign exit then
  nip lf-env-accepted nip ;

\ Scans of the declarations before limit. A match is a declaration whose
\ input name equals name and whose slot passes test ( slot -- flag ).
\ Unchecked: the names are valid in an audited name store, and limit is
\ between 0 and the current environment's length.
: lf-env-match? ( name test d -- flag )
  >r over r@ lf-input-name lf-name-same?
  if r> lf-env lf-env-slot swap execute nip else r> drop 2drop false then ;
: lf-env-scan-first ( name test limit -- d|-1 )
  0 ?do 2dup i lf-env-match? if 2drop i unloop exit then loop 2drop -1 ;
: lf-env-scan-matches ( name test limit -- n )
  >r 0 -rot r> 0 ?do 2dup i lf-env-match? >r rot r> - -rot loop 2drop ;
\ With an indexed input (names interned in a shared input tier,
\ core/input.fs), the declarations named name are its chain, newest
\ first (ADR 0016 C4): the same answers in time proportional to the
\ chain. Each declaration of the chain below limit passing test counts;
\ the first is the last one met.
: lf-env-passes? ( test d -- flag ) lf-env lf-env-slot swap execute ;
: lf-env-chain-step ( test limit d -- test limit d flag )
  2dup > if 2 pick over lf-env-passes? else false then ;
: lf-env-chain-first ( name test limit -- d|-1 )
  -1 >r rot lf-input-newest begin dup 0< 0= while
    lf-env-chain-step if r> drop dup >r then lf-input-before
  repeat drop 2drop r> ;
: lf-env-chain-matches ( name test limit -- n )
  0 >r rot lf-input-newest begin dup 0< 0= while
    lf-env-chain-step if r> 1+ >r then lf-input-before
  repeat drop 2drop r> ;
: lf-env-first ( name test limit -- d|-1 )
  lf-input-indexed? if lf-env-chain-first else lf-env-scan-first then ;
: lf-env-matches ( name test limit -- n )
  lf-input-indexed? if lf-env-chain-matches else lf-env-scan-matches then ;
: lf-env-any? ( name limit test -- flag ) swap lf-env-first 0< 0= ;

\ Finding a constant (E5) once every same-named slot below limit is final.
\ With none accepted, K5 (unknown first, ADR 0012 E5 as amended): the
\ first undecided slot makes the user unknown, else the first unsupported
\ one unsupported, each recording that slot; else N1 rejects. A slot not
\ final records lf-diag-too-early.
: lf-env-k5-unknown ( d -- outcome )
  dup lf-env lf-env-slot lf-slot-outcome@ c" environment lf-env-lookup"
  lf-diag-dependency-undecided lf-diag-note outcome-unknown ;
: lf-env-k5-unsupported ( d -- outcome )
  0 c" environment lf-env-lookup" lf-diag-dependency-unsupported lf-diag-note
  outcome-unsupported ;
: lf-env-unsupported ( name limit -- outcome )
  ['] lf-slot-unsupported? swap lf-env-first
  dup 0< if drop outcome-rejected else lf-env-k5-unsupported then ;
: lf-env-undecided ( name limit -- outcome )
  2dup ['] lf-slot-undecided? swap lf-env-first
  dup 0< if drop lf-env-unsupported else nip nip lf-env-k5-unknown then ;
: lf-env-decide ( name limit -- d outcome )
  2dup ['] lf-slot-accepted? swap lf-env-matches case
    0 of lf-env-undecided no-result endof
    1 of ['] lf-slot-accepted? swap lf-env-first outcome-ok endof
    >r 2drop -1 outcome-invalid r> endcase ;
: lf-env-early ( name limit -- d outcome )
  tuck ['] lf-slot-open? swap lf-env-first swap c" environment lf-env-lookup"
  lf-diag-too-early lf-diag-note -1 outcome-invalid ;
: lf-env-find ( name limit -- d outcome )
  2dup ['] lf-slot-open? lf-env-any? if lf-env-early else lf-env-decide then ;
: lf-env-name-ok? ( name -- flag ) lf-name-valid? lf-name-storage-valid? and ;
: lf-env-bad-name ( name -- d outcome )
  0 c" environment lf-env-lookup" lf-diag-bad-argument lf-diag-note -1 outcome-invalid ;
: lf-env-n1 ( name limit outcome -- outcome )
  dup outcome-rejected = if >r c" environment lf-env-lookup" lf-diag-unknown-constant
  lf-diag-note r> else nip nip then ;
\ Find the constant named name for the check in this context: (d ok) for
\ the accepted earlier declaration of that name; (-1 rejected) when none
\ was accepted, undecided or unsupported (N1); (-1 unknown) when one was
\ undecided, else (-1 unsupported) when one was unsupported (K5, unknown
\ first); (-1 invalid)
\ without a valid snapshot or name, when a same-named earlier slot is not
\ final (started too early), or when two were accepted.
: lf-env-lookup-pass ( name -- d outcome )
  lf-env-snapshot 0= if drop -1 outcome-invalid exit then nip
  over lf-env-name-ok? 0= if drop lf-env-bad-name exit then
  2dup lf-env-find dup ok? if 2swap 2drop exit then nip lf-env-n1 no-result ;
\ The derivation log (ADR 0013): with it on, a lookup is one resolve step
\ of the name, its result the slot found.
: lf-env-lookup-logged ( name -- d outcome )
  dup lf-log-none lf-rule-resolve lf-log-open lf-env-lookup-pass lf-log-close ;
: lf-env-lookup ( name -- d outcome )
  lf-log? if lf-env-lookup-logged else lf-env-lookup-pass then ;
\ N2 for the declaration being checked, by the same lookup on its own
\ name: ok when no earlier one of that name was accepted (none, or all
\ rejected); rejected when one was; unknown or unsupported when one was
\ undecided or unsupported (K5, unknown first); invalid as for
\ lf-env-lookup.
: lf-env-declared ( d -- outcome )
  lf-env-limit lf-input-name swap c" environment lf-env-own-name"
  lf-diag-already-declared lf-diag-note outcome-rejected ;
\ N2 from the lookup's (d outcome): accepted is a conflict, rejected none;
\ any other outcome stands.
: lf-env-n2 ( d outcome -- outcome )
  dup outcome-rejected = if 2drop outcome-ok exit then
  dup ok? if drop lf-env-declared else nip then ;
: lf-env-own-name-pass ( -- outcome )
  lf-env-checking 0= if outcome-invalid exit then nip
  lf-name-storage-valid? 0= if drop outcome-invalid exit then
  dup lf-input-name swap lf-env-find lf-env-n2 ;
\ The derivation log (ADR 0013) records N2 as a fresh-name step, L1 as a
\ universe-arity step, L2 as a universe-parameter step and L3 as a
\ distinct-parameters step; a and b as the catalogue gives them (the
\ declaration as its number, a name as its ID).
: lf-env-logged ( a b rule xt -- outcome ) >r lf-log-open r> execute lf-log-decided ;
: lf-env-own-name ( -- outcome )
  lf-log? 0= if lf-env-own-name-pass exit then
  lf-env-limit lf-log-none lf-rule-fresh-name ['] lf-env-own-name-pass lf-env-logged ;
\ G-P5, for a scheduler outside any check: whether every declaration
\ before i named name has a final slot in the current environment. False
\ inside a job or a check (the scheduler alone asks), without a valid
\ current environment, for i out of range or an invalid name.
: lf-env-ready-args? ( name i -- flag )
  lf-env-current 0= if 2drop false exit then
  lf-env-length upto? swap lf-env-name-ok? and context-in-job? 0= and ;
: lf-env-ready? ( name i -- flag )
  2dup lf-env-ready-args? if ['] lf-slot-open? lf-env-any? 0= else 2drop false then ;

\ The candidate's dependencies, kept ascending and distinct. The count is
\ checked before the list is read.
: lf-cand-count@ ( -- n ) lf-env-cand lf-cand-count @ ;
: lf-cand-count? ( -- flag ) lf-cand-count@ lf-env-dep-capacity upto? ;
: lf-cand-dep ( k -- addr ) cells lf-env-cand lf-cand-deps + ;
: lf-cand-has? ( d -- flag )
  false lf-cand-count@ 0 ?do over i lf-cand-dep @ = or loop nip ;
\ Where d goes: the first position holding a larger slot, or the end.
: lf-cand-place ( d -- k )
  lf-cand-count@ 0 ?do dup i lf-cand-dep @ < if drop i unloop exit then loop
  drop lf-cand-count@ ;
: lf-cand-open ( k -- ) dup lf-cand-dep dup cell+ rot lf-cand-count@ swap - cells move ;
: lf-cand-insert ( d -- )
  dup lf-cand-place dup lf-cand-open lf-cand-dep ! 1 lf-env-cand lf-cand-count +! ;
: lf-or! ( bits addr -- ) tuck @ or swap ! ;
: lf-cand-union ( slot -- )
  dup lf-slot-axioms @ lf-env-cand lf-cand-axioms lf-or!
  lf-slot-provenance @ lf-env-cand lf-cand-provenance lf-or! ;
: lf-cand-full ( d slot -- outcome )
  2drop lf-cand-count@ lf-env-dep-capacity c" environment lf-env-depend"
  lf-diag-deps-full lf-diag-note outcome-full ;
: lf-cand-add ( d slot -- outcome )
  over lf-cand-has? if 2drop outcome-ok exit then
  lf-cand-count@ lf-env-dep-capacity = if lf-cand-full exit then
  lf-cand-union lf-cand-insert outcome-ok ;
\ Record that the check in this context uses slot d (E4, E6): ok, adding
\ d to its dependencies and the slot's axiom set and provenance to its
\ own; full when d is new and lf-env-dep-capacity are recorded already;
\ invalid when slot d is not readable and accepted in the snapshot or the
\ candidate is corrupted.
: lf-env-depend ( d -- outcome )
  lf-cand-count? 0= if drop outcome-invalid exit then
  dup lf-env-accepted ok? if lf-cand-add else 2drop outcome-invalid then ;
\ Look name up and record it as a dependency: (d ok), or (-1 outcome).
: lf-env-resolve ( name -- d outcome )
  lf-env-lookup dup ok? 0= if exit then
  drop dup lf-env-depend dup ok? if exit then nip no-result ;

\ Universe parameters (E2; ADR 0011 rules L1–L3). Names compare
\ structurally. Unchecked: the names are valid in an audited name store.
: lf-params-has? ( name params n -- flag )
  0 ?do 2dup i lf-param@ lf-name-same? if 2drop true unloop exit then loop
  2drop false ;
: lf-param-repeated? ( params k -- flag ) 2dup lf-param@ -rot lf-params-has? ;
: lf-params-distinct? ( params n -- flag )
  1 max 1 ?do dup i lf-param-repeated? if drop false unloop exit then loop drop true ;
\ The parameters of accepted slot d, readable in this context's snapshot:
\ (params n ok), else (0 0 invalid). The address is the slot's own.
: lf-env-params ( d -- params n outcome )
  lf-env-accepted ok? if lf-slot-decl lf-idecl-params@ outcome-ok exit then
  drop 0 0 outcome-invalid ;
\ L1: a reference to slot d supplies n universe levels: ok when n is
\ d's number of parameters, else rejected; invalid as lf-env-params.
: lf-env-arity-rejected ( n arity -- outcome )
  c" environment lf-env-arity?" lf-diag-level-count lf-diag-note outcome-rejected ;
: lf-env-arity-pass ( n d -- outcome )
  lf-env-params ok? 0= if 2drop drop outcome-invalid exit then
  nip 2dup = if 2drop outcome-ok else lf-env-arity-rejected then ;
: lf-env-arity? ( n d -- outcome )
  lf-log? 0= if lf-env-arity-pass exit then
  2dup lf-rule-universe-arity ['] lf-env-arity-pass lf-env-logged ;
\ L2: whether name is a universe parameter of the declaration being
\ checked: ok or rejected; invalid without a check's snapshot or for an
\ invalid name.
: lf-env-undeclared ( name -- outcome )
  0 c" environment lf-env-param?" lf-diag-undeclared-param lf-diag-note
  outcome-rejected ;
: lf-env-param-pass ( name -- outcome )
  lf-env-checking 0= if drop outcome-invalid exit then nip
  over lf-env-name-ok? 0= if 2drop outcome-invalid exit then
  over swap lf-input-params lf-params-has?
  if drop outcome-ok else lf-env-undeclared then ;
: lf-env-param? ( name -- outcome )
  lf-log? 0= if lf-env-param-pass exit then
  dup lf-log-none lf-rule-universe-parameter ['] lf-env-param-pass lf-env-logged ;
\ L3: the declaration being checked lists no parameter twice: ok or
\ rejected; invalid without a check's snapshot.
: lf-env-repeated ( i -- outcome )
  0 c" environment lf-env-own-params" lf-diag-duplicate-param lf-diag-note
  outcome-rejected ;
: lf-env-own-params-pass ( -- outcome )
  lf-env-checking 0= if outcome-invalid exit then nip
  lf-name-storage-valid? 0= if drop outcome-invalid exit then
  dup lf-input-params lf-params-distinct? if drop outcome-ok else lf-env-repeated then ;
: lf-env-own-params ( -- outcome )
  lf-log? 0= if lf-env-own-params-pass exit then
  lf-env-limit lf-log-none lf-rule-distinct-parameters ['] lf-env-own-params-pass
  lf-env-logged ;

\ Results, read within this context's snapshot (G-P4; after a run, take
\ one with lf-env-view). The outcome of declaration d when the snapshot
\ may read its slot (below its declaration, final), else invalid; the
\ axiom set of an accepted one, (bits ok), else (0 invalid). Accepted
\ results print "accepted — experimental, not independently audited;
\ axioms: none" (ADR 0011).
: lf-env-outcome ( d -- outcome )
  lf-env-readable if lf-slot-outcome@ else outcome-invalid then ;
: lf-env-axioms ( d -- bits outcome )
  lf-env-readable 0= if 0 outcome-invalid exit then
  dup lf-slot-accepted? if lf-slot-axioms @ outcome-ok else drop 0 outcome-invalid then ;
