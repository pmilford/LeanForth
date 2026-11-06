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
\ independently audited. Limits: lf-input-capacity slots; a check's
\ dependencies and an environment's pool have no fixed limit (plan task
\ 6.2.0): both grow with the heap, and one the heap cannot grow is full.
\ State: the shared record lf-envs (the identity serial and the current
\ environment; changed only while no job runs), each environment's
\ ALLOCATEd record and its pool's blocks (shared, outside every context:
\ written only by the publisher, which keeps its pool mark in the
\ header, read by every check), two context records, one per context
\ (ADR 0009): the candidate lf-env-cand and the worker record
\ lf-env-worker, and the candidate's list of dependencies, the context
\ slab lf-cand-deps. An environment must be freed only when no task uses
\ it. The layout is host-specific and never serialized.

require ../lib/lib.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../core/terms.fs
require ../core/input.fs
require ./axiom-allowlist.fs

65536 constant lf-env-pool-start    \ the pool room `check` starts with; it grows
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

\ An environment: this header, then the slots. Its dependency pool, a
\ store of one cell per dependency, is a heap block of its own (see
\ "The pool" below).
begin-structure /lf-env
  field: lf-envh-identity   \ never repeats; 0 once freed
  field: lf-envh-input      \ the input's fingerprint when made
  field: lf-envh-length     \ number of slots: the input's declarations
  field: lf-envh-allowed    \ axiom bits that count as proved (axiom-allowlist.fs;
                            \ a test may set others on a synthetic environment)
  field: lf-envh-version    \ allowlist version
  field: lf-envh-mode       \ run mode
  field: lf-envh-pool       \ the pool's current block
  /store-mark +field lf-envh-pub-mark   \ the publisher's pool mark while it publishes
end-structure

\ A slot (E2). Only the state and outcome mean anything for a declaration
\ that was not accepted, except the members of a block rejected only by
\ B3, whose slots are written as an accepted block's (lf-slot-added); the
\ other fields stay zero.
begin-structure /lf-slot
  field: lf-slot-state      \ lf-state-final once published, else not final
  field: lf-slot-outcome    \ the declaration's outcome (ADR 0008)
  /lf-idecl +field lf-slot-decl   \ the input declaration, copied whole
  field: lf-slot-deps       \ index of its first dependency in the pool
  field: lf-slot-count      \ its number of dependencies
  field: lf-slot-axioms     \ its transitive axiom set (E6)
  field: lf-slot-provenance \ lf-provenance-...
  field: lf-slot-warnings   \ an accepted inductive block's warnings (ADR 0015
                            \ B4, check-block.fs), on each member; else 0
  field: lf-slot-added      \ true on the type and constructors of a block
                            \ rejected only by B3: Lean's kernel added them
  field: lf-slot-recipe     \ a block's generated recursor: lf-recipe-... bits
end-structure
\ The recipe bits (ADR 0015 decision 12): the recursor LeanForth generated
\ for the block can be built again from its input (generated-recursor.fs);
\ it eliminates into every universe (its motive universe its first
\ universe parameter).
\ The kinds a declaration's own check covers (check-declaration.fs): with
\ a value (definition, theorem, opaque) or without (axiom, quotient).
: lf-kind-valued? ( kind -- flag )
  dup lf-kind-definition = over lf-kind-theorem = or swap lf-kind-opaque = or ;
: lf-kind-bare? ( kind -- flag ) dup lf-kind-axiom = swap lf-kind-quotient = or ;
1 constant lf-recipe-raw
2 constant lf-recipe-large

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
  field: lf-cand-warnings   \ a block's B4 warning bits, published with it
  field: lf-cand-added      \ a block rejected only by B3 (lf-env-added!)
  field: lf-cand-recipe     \ its generated recursor's recipe (lf-env-recipe!)
end-structure
/lf-cand context-record: lf-env-cand
\ The dependencies' slots, ascending: a growable array, as long as the
\ check needs (plan task 6.2.0).
1 cells context-slab: lf-cand-deps
\ The candidate's span: how many slots, from the declaration checked on,
\ its outcome and record are for. A block's check sets it to the block's
\ members (kernel/check-block.fs); every other check leaves it 1.
: lf-cand-span@ ( -- n ) lf-env-cand lf-cand-span @ 1 max ;
: lf-env-span! ( n -- ) lf-env-cand lf-cand-span ! ;
\ A block's check also sets its warnings (ADR 0015 B4, owner answer Q2:
\ fields Lean's replay ignores that differ from what LeanForth computed,
\ and a recursor the file leaves out); an accepted block's slots keep
\ them (lf-env-warnings).
: lf-env-warnings! ( bits -- ) lf-env-cand lf-cand-warnings ! ;
\ A block rejected only by B3, replay's comparison after its addDecl
\ (ADR 0015 decision 11; review rvI21 R2-1): Lean's kernel has already
\ added the type, its constructors and the recursor it generated, so
\ their names are taken although the file's records are refused. The
\ check says so with true; the publisher marks the type's and
\ constructors' slots (lf-slot-added?), and the name checks below read
\ them.
: lf-env-added! ( flag -- ) lf-env-cand lf-cand-added ! ;
\ A block's check sets the recipe of the recursor it generated
\ (lf-recipe-... bits); the publisher keeps it on the block's slots, where
\ a later lookup of T.rec that no slot holds finds it (ADR 0015 decision
\ 12).
: lf-env-recipe! ( bits -- ) lf-env-cand lf-cand-recipe ! ;

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
: lf-env-bytes ( slots -- u ) /lf-slot * /lf-env + ;
: lf-env-in? ( d env -- flag ) lf-env-length 0 swap within ;

\ The pool (E2; plan task 6.2.0): a heap block holding a link cell, then
\ a store of one-cell records, room of them. Only the publisher writes
\ it (env-publish.fs). When a publication needs more room than the pool
\ has, the publisher, before it marks the pool, makes a block with room
\ for at least twice as many, copies the store into it, links the old
\ block from the new one and then, in one cell, makes the new one
\ current; the old blocks are freed with the environment. So a check in a
\ job that reads the pool's header while the publisher grows it
\ (lf-env-live?) reads a whole, sealed store: the current one or an
\ older one, which no longer changes. Unchecked: a live environment.
: lf-env-pool ( env -- store ) lf-envh-pool @ cell+ ;
\ Whether a pool of room records is a sound store shape, with a cell to
\ spare for the link.
: lf-pool-plan? ( room -- flag ) dup 0< 0= swap 1+ 1 cells 0 store-plan? and ;
: lf-pool-size ( room -- u ) 1 cells store-size cell+ ;
\ A new pool block of room records, its link 0: (block ok); (0 invalid)
\ for an unsound room, (0 full) when the heap has no room.
: lf-pool-block ( room -- block outcome )
  dup lf-pool-plan? 0= if drop 0 outcome-invalid exit then
  dup lf-pool-size allocate if 2drop 0 outcome-full exit then
  0 over ! tuck cell+ >r 1 cells 0 r> store-init drop outcome-ok ;
\ Free a block and every older one it links.
: lf-pool-release ( block -- ) begin ?dup while dup @ swap free drop repeat ;

\ Sanity checks; like context?, they cannot recognise every stale
\ address. A live environment has an issued identity, a length within the
\ input's capacity and a sound pool.
: lf-env-serial ( -- addr ) lf-envs lf-envs-serial ;
: lf-env-sane? ( env -- flag )
  dup lf-envh-identity @ 1 lf-env-serial @ between?
  swap lf-env-length lf-input-capacity upto? and ;
: lf-env-pooled? ( env -- flag )
  lf-envh-pool @ ?dup if cell+ store-count-valid? else false then ;
: lf-env-live? ( env -- flag )
  ?dup 0= if false exit then
  dup lf-env-sane? if lf-env-pooled? else drop false then ;
: lf-env-input? ( env -- flag )
  lf-envh-input @ lf-input-fingerprint = lf-input-intact? and ;
: lf-env-valid? ( env -- flag ) dup lf-env-live? if lf-env-input? else drop false then ;
\ The current environment, when it is live and this context's input is
\ intact and the one it was made over.
: lf-env-current ( -- env true | false ) lf-env dup lf-env-valid? ?keep ;

\ Making, freeing and choosing environments, only outside jobs (G-P1).
\ lf-env-new gives a new environment over this context's intact input,
\ its pool starting with room for deps dependencies (it grows), and the
\ axiom allowlist (lf-env-allowlist), in final mode: (env ok); (0 invalid)
\ inside a job, for an input that is not intact or a negative deps or
\ one too large for a store (lf-pool-plan?); (0 full) when the
\ identities are spent or memory cannot be allocated.
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
\ Give the environment a pool of deps records: (env ok); or (0 invalid)
\ for an unsound deps, (0 full) when the heap has no room, the
\ environment's memory freed.
: lf-env-pooled ( deps env -- env outcome )
  swap lf-pool-block dup ok? if drop over lf-envh-pool ! outcome-ok exit then
  >r drop free drop 0 r> ;
\ The axiom allowlist (axiom-allowlist.fs): its version, and the bits
\ that count as proved.
: lf-env-allowlist ( env -- env )
  lf-allowlist-bits over lf-envh-allowed ! lf-allowlist-version over lf-envh-version ! ;
\ Format the slots, make the pool and give the environment its
\ identity: (env ok), or as lf-env-pooled.
: lf-env-made ( deps env -- env outcome )
  lf-env-may-write lf-env-fields lf-env-allowlist lf-env-unpublished lf-env-pooled
  dup ok? if drop lf-env-identity+ outcome-ok then ;
: lf-env-new-ok? ( deps -- flag )
  lf-pool-plan? lf-input-intact? and context-in-job? 0= and ;
: lf-env-new ( deps -- env outcome )
  dup lf-env-new-ok? 0= if drop 0 outcome-invalid exit then
  lf-env-serial @ max-n = if drop 0 outcome-full exit then
  lf-input-count lf-env-bytes allocate0 if 2drop 0 outcome-full exit then
  lf-env-made ;
\ Free a live environment and its pool's blocks: ok, or invalid when it
\ is not live or inside a job (nothing is freed) or FREE fails on its
\ record. Its identity is cleared first and it stops being current.
: lf-env-choosable? ( env -- flag ) lf-env-live? context-in-job? 0= and ;
: lf-env-forget ( env -- env )
  lf-env-may-write dup lf-env = if 0 lf-envs lf-envs-current ! then
  0 over lf-envh-identity ! ;
: lf-env-free ( env -- outcome )
  dup lf-env-choosable? 0= if drop outcome-invalid exit then
  lf-env-forget dup lf-envh-pool @ lf-pool-release free 0= flag>outcome ;
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
\ A rejected slot whose name Lean's kernel holds (lf-env-added!).
: lf-slot-added? ( slot -- flag )
  dup lf-slot-final? over lf-slot-outcome@ outcome-rejected = and
  swap lf-slot-added @ 0<> and ;
\ A slot later declarations may use: accepted, or added by Lean's kernel
\ (its own verdict stays rejected; ADR 0015 decision 11).
\ An added slot is usable once the publisher wrote its record (its
\ declaration's name is never anonymous).
: lf-slot-recorded? ( slot -- flag ) lf-slot-decl lf-idecl-name @ 0<> ;
: lf-slot-usable? ( slot -- flag )
  dup lf-slot-accepted? if drop true exit then
  dup lf-slot-added? swap lf-slot-recorded? and ;

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
\ The same for a slot later declarations may use (lf-slot-usable?):
\ lookups, dependencies and the publisher's re-check read slots so.
: lf-env-usable ( d -- slot outcome )
  dup lf-env-readable 0= if lf-env-refuse exit then
  dup lf-slot-usable? if nip outcome-ok else drop lf-env-refuse then ;

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
\ A recursor Lean's kernel generated that no slot holds and that cannot
\ be built again (its type left no recipe; ADR 0015 decision 12):
\ unknown, the name and the type's slot recorded.
: lf-env-generated ( name d -- outcome )
  c" environment lf-env-lookup" lf-diag-generated-recursor lf-diag-note outcome-unknown ;
: lf-env-undecided ( name limit -- outcome )
  2dup ['] lf-slot-undecided? swap lf-env-first
  dup 0< if drop lf-env-unsupported else nip nip lf-env-k5-unknown then ;
: lf-env-decide ( name limit -- d outcome )
  2dup ['] lf-slot-usable? swap lf-env-matches case
    0 of lf-env-undecided no-result endof
    1 of ['] lf-slot-usable? swap lf-env-first outcome-ok endof
    >r 2drop -1 outcome-invalid r> endcase ;
: lf-env-early ( name limit -- d outcome )
  tuck ['] lf-slot-open? swap lf-env-first swap c" environment lf-env-lookup"
  lf-diag-too-early lf-diag-note -1 outcome-invalid ;
: lf-env-find ( name limit -- d outcome )
  2dup ['] lf-slot-open? lf-env-any? if lf-env-early else lf-env-decide then ;
: lf-env-name-ok? ( name -- flag ) lf-name-valid? lf-name-storage-valid? and ;
: lf-env-bad-name ( name -- d outcome )
  0 c" environment lf-env-lookup" lf-diag-bad-argument lf-diag-note -1 outcome-invalid ;

\ Lean's generated recursors (ADR 0015, decision 9; review rvI21 B2).
\ Lean's add_inductive adds the recursor T.rec it generates to its
\ environment whatever the file holds, so a file that leaves T.rec out
\ (B4) still has T.rec declared once T is accepted. LeanForth cannot
\ publish a declaration the file does not hold: a slot is an input
\ declaration (one per input record, fixed when the environment is
\ made), and the generated terms are a check's scratch, rolled back
\ after it. So it reserves the name: a name P.rec is held by the
\ inductive types named P below limit -- declared when one is accepted,
\ K5 when one is undecided or unsupported, too early when one is not
\ final -- (d class), d that type's slot, class ok, unknown, unsupported
\ or invalid; (-1 rejected) when nothing holds it. No diagnostic.
\ P.rec_<digits>, the auxiliary recursors Lean generates for a nested
\ block (named after its first type), is held the same way except by an
\ accepted type: LeanForth accepts no nested block yet (plan task 5.2.2
\ must hold these names for the nested blocks it accepts).
: lf-env-number-rest ( c-addr u -- u' ) 0 0 2swap >number >r 2drop drop r> ;
: lf-env-digits? ( c-addr u -- flag )
  dup 0> >r base @ >r decimal lf-env-number-rest r> base ! 0= r> and ;
: lf-env-aux-rec? ( c-addr u -- flag )
  2dup 4 min s" rec_" compare if 2drop false else 4 /string lf-env-digits? then ;
\ The kind of name's last part: lf-rec-main (rec), lf-rec-aux
\ (rec_<digits>), 0 any other.
1 constant lf-rec-main
2 constant lf-rec-aux
: lf-env-rec-kind ( name -- kind )
  dup lf-name-tag@ lf-name-tag-str <> if drop 0 exit then
  lf-name-text 2dup s" rec" compare 0=
  if 2drop lf-rec-main else lf-env-aux-rec? lf-rec-aux and then ;
: lf-slot-index ( slot -- d ) 0 lf-env lf-env-slot - /lf-slot / ;
: lf-slot-type? ( slot -- flag )
  lf-slot-index lf-input-decl lf-idecl-kind @ lf-kind-inductive = ;
: lf-slot-type-open? ( slot -- flag ) dup lf-slot-open? swap lf-slot-type? and ;
: lf-slot-type-accepted? ( slot -- flag ) dup lf-slot-accepted? swap lf-slot-type? and ;
: lf-slot-type-undecided? ( slot -- flag )
  dup lf-slot-final? over lf-slot-undecided? and swap lf-slot-type? and ;
: lf-slot-type-unsupported? ( slot -- flag )
  dup lf-slot-final? over lf-slot-unsupported? and swap lf-slot-type? and ;
: lf-slot-type-added? ( slot -- flag ) dup lf-slot-added? swap lf-slot-type? and ;
\ The tests, in order, each with the class it gives: an entry is a test
\ ( slot -- flag ) and its class. A type rejected only by B3 holds T.rec
\ as an accepted one does: Lean's kernel generated it (R2-1).
create lf-env-holders
  ' lf-slot-type-open? , outcome-invalid ,  ' lf-slot-type-accepted? , outcome-ok ,
  ' lf-slot-type-added? , outcome-ok ,  ' lf-slot-type-undecided? , outcome-unknown ,
  ' lf-slot-type-unsupported? , outcome-unsupported ,
here lf-env-holders - 2 cells / constant lf-env-holders#
: lf-env-held ( prefix limit entry -- d class true | false )
  dup cell+ @ >r @ swap lf-env-first dup 0< if drop r> drop false else r> true then ;
: lf-env-holding ( prefix limit -- d class )
  lf-env-holders lf-env-holders# 2* cells bounds ?do
    2dup i lf-env-held if 2swap 2drop unloop exit then
  2 cells +loop 2drop -1 outcome-rejected ;
: lf-env-aux-held ( d class -- d class ) dup ok? if 2drop -1 outcome-rejected then ;
\ The name of the types that may hold name, 0 when no type can.
: lf-env-type-name ( name -- prefix|0 )
  dup lf-env-rec-kind if lf-name-prefix@ else drop 0 then ;
: lf-env-reserving ( name limit -- d class )
  over lf-env-rec-kind >r swap lf-env-type-name ?dup 0=
  if r> 2drop -1 outcome-rejected exit then
  swap lf-env-holding r> lf-rec-aux = if lf-env-aux-held then ;
\ Whether a type that may hold name below i is not final (the scheduler's
\ readiness, lf-env-ready?).
: lf-env-held-open? ( name i -- flag )
  swap lf-env-type-name ?dup 0= if drop false exit then
  swap ['] lf-slot-type-open? lf-env-any? ;

\ N1 for a lookup that found no declaration of name below limit: rejected
\ (an unknown constant); unknown when an accepted type reserves the name
\ (Lean's kernel holds its recursor, no slot does); K5 or invalid as
\ the type that reserves it says.
: lf-env-unknown-constant ( name limit -- outcome )
  c" environment lf-env-lookup" lf-diag-unknown-constant lf-diag-note outcome-rejected ;
\ A lookup that found Lean's generated recursor of the block whose type
\ is slot d, which no slot holds: (-1 ok) -- no slot is the constant,
\ so no caller can read T's slot as T.rec's (review rvI21 R4-5) -- with
\ d given by lf-env-genrec-of until the next lookup; the caller builds
\ the recursor again from the recipe on slot d (env-signature.fs,
\ generated-recursor.fs). Without a recipe (a type whose telescope only
\ whnf shows), unknown.
1 cells context-record: lf-env-gen-state
: lf-env-genrec-of ( -- d|-1 ) lf-env-gen-state @ 1- ;
: lf-env-rebuildable? ( d -- flag )
  lf-env lf-env-slot lf-slot-recipe @ lf-recipe-raw and 0<> ;
: lf-env-genrec ( name d -- -1 outcome )
  dup lf-env-rebuildable? if nip 1+ lf-env-gen-state ! -1 outcome-ok exit then
  lf-env-generated no-result ;
: lf-env-absent-early ( name limit d -- outcome )
  rot drop swap c" environment lf-env-lookup" lf-diag-too-early lf-diag-note
  outcome-invalid ;
: lf-env-absent-as ( name limit d class -- -1 outcome )
  case outcome-rejected of drop lf-env-unknown-constant no-result endof
    outcome-ok of nip lf-env-genrec endof
    outcome-unknown of nip nip lf-env-k5-unknown no-result endof
    outcome-unsupported of nip nip lf-env-k5-unsupported no-result endof
    >r lf-env-absent-early no-result r> endcase ;
: lf-env-n1 ( name limit outcome -- -1 outcome )
  dup outcome-rejected = 0= if nip nip no-result exit then
  drop 2dup lf-env-reserving lf-env-absent-as ;
\ Find the constant named name for the check in this context: (d ok) for
\ the usable earlier declaration of that name (accepted, or added with a
\ block rejected only by B3); (-1 ok) for the recursor Lean's kernel
\ generated for an earlier type that holds the name and no slot holds,
\ the type's slot then lf-env-genrec-of (ADR 0015 decision 12); (-1
\ rejected) when none was usable, undecided or unsupported (N1) and no
\ earlier type holds the name; (-1 unknown) when one was undecided, or a
\ holder type left no recipe, else (-1 unsupported) when one was
\ unsupported (K5, unknown first); (-1 invalid) without a valid snapshot
\ or name, when a same-named earlier slot or a holder type is not final
\ (started too early), or when two were usable.
: lf-env-lookup-pass ( name -- d outcome )
  0 lf-env-gen-state !
  lf-env-snapshot 0= if drop -1 outcome-invalid exit then nip
  over lf-env-name-ok? 0= if drop lf-env-bad-name exit then
  2dup lf-env-find dup ok? if 2swap 2drop exit then nip lf-env-n1 ;
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
\ N2 against Lean's generated recursors, from lf-env-reserving's (d
\ class): an accepted type holding the name declares it; K5 and too early
\ as for the name's own slots.
: lf-env-held-early ( d -- outcome )
  lf-env-limit c" environment lf-env-own-name" lf-diag-too-early lf-diag-note
  outcome-invalid ;
: lf-env-n2-held ( d class -- outcome )
  case outcome-ok of lf-env-declared endof  outcome-rejected of drop outcome-ok endof
    outcome-unknown of lf-env-k5-unknown endof
    outcome-unsupported of lf-env-k5-unsupported endof
    >r lf-env-held-early r> endcase ;
\ N2 for name below limit: no usable declaration of it (the slots of that
\ name: accepted, or added by Lean's kernel with a block rejected only by
\ B3, R2-1), and no accepted or added type T with name T.rec (Lean's
\ generated recursor, review rvI21 B2). ok, rejected, unknown,
\ unsupported or invalid, as lf-env-n2 and lf-env-n2-held say.
: lf-env-fresh ( name limit -- outcome )
  2dup lf-env-find lf-env-n2 dup ok? 0= if nip nip exit then drop
  lf-env-reserving lf-env-n2-held ;
: lf-env-own-name-pass ( -- outcome )
  lf-env-checking 0= if outcome-invalid exit then nip
  lf-name-storage-valid? 0= if drop outcome-invalid exit then
  dup lf-input-name swap lf-env-fresh ;
\ The derivation log (ADR 0013) records N2 as a fresh-name step, L1 as a
\ universe-arity step, L2 as a universe-parameter step and L3 as a
\ distinct-parameters step; a and b as the catalogue gives them (the
\ declaration as its number, a name as its ID).
: lf-env-logged ( a b rule xt -- outcome ) >r lf-log-open r> execute lf-log-decided ;
: lf-env-own-name ( -- outcome )
  lf-log? 0= if lf-env-own-name-pass exit then
  lf-env-limit lf-log-none lf-rule-fresh-name ['] lf-env-own-name-pass lf-env-logged ;
\ G-P5, for a scheduler outside any check: whether every declaration
\ before i named name has a final slot in the current environment, and,
\ for a name a generated recursor may hold (lf-env-reserving), every type
\ before i that may hold it. False inside a job or a check (the scheduler
\ alone asks), without a valid current environment, for i out of range or
\ an invalid name.
: lf-env-ready-args? ( name i -- flag )
  lf-env-current 0= if 2drop false exit then
  lf-env-length upto? swap lf-env-name-ok? and context-in-job? 0= and ;
: lf-env-ready? ( name i -- flag )
  2dup lf-env-ready-args? 0= if 2drop false exit then
  2dup ['] lf-slot-open? lf-env-any? >r lf-env-held-open? r> or 0= ;

\ The candidate's dependencies, kept ascending and distinct, in the
\ context's slab lf-cand-deps. The count is checked against the slab's
\ room before the list is read; an address is valid until it grows.
: lf-cand-count@ ( -- n ) lf-env-cand lf-cand-count @ ;
: lf-cand-count? ( -- flag ) lf-cand-count@ lf-cand-deps slab-capacity upto? ;
: lf-cand-dep ( k -- addr ) cells lf-cand-deps slab-base + ;
\ Where d goes: the first position whose slot is not below d, or the
\ count; by halving the range lo..hi in which it lies.
: lf-cand-halve ( d lo hi -- d lo' hi' )
  2dup + 2/ dup >r lf-cand-dep @ 3 pick < if nip r> 1+ swap else drop r> then ;
: lf-cand-place ( d -- k )
  0 lf-cand-count@ begin 2dup < while lf-cand-halve repeat drop nip ;
: lf-cand-has? ( d -- flag )
  dup lf-cand-place dup lf-cand-count@ < if lf-cand-dep @ = else 2drop false then ;
: lf-cand-open ( k -- ) dup lf-cand-dep dup cell+ rot lf-cand-count@ swap - cells move ;
: lf-cand-insert ( d -- )
  dup lf-cand-place dup lf-cand-open lf-cand-dep ! 1 lf-env-cand lf-cand-count +! ;
: lf-or! ( bits addr -- ) tuck @ or swap ! ;
\ An axiom's own bit (axiom-allowlist.fs), joined to the candidate's set
\ by its check (check-declaration.fs).
: lf-env-axiom! ( bits -- ) lf-env-cand lf-cand-axioms lf-or! ;
: lf-cand-union ( slot -- )
  dup lf-slot-axioms @ lf-env-cand lf-cand-axioms lf-or!
  lf-slot-provenance @ lf-env-cand lf-cand-provenance lf-or! ;
: lf-cand-room? ( -- flag ) lf-cand-count@ 1+ lf-cand-deps slab-hold ok? ;
: lf-cand-full ( d slot -- outcome )
  2drop lf-cand-count@ lf-cand-deps slab-capacity c" environment lf-env-depend"
  lf-diag-deps-full lf-diag-note outcome-full ;
: lf-cand-add ( d slot -- outcome )
  over lf-cand-has? if 2drop outcome-ok exit then
  lf-cand-room? 0= if lf-cand-full exit then
  lf-cand-union lf-cand-insert outcome-ok ;
\ Record that the check in this context uses slot d (E4, E6): ok, adding
\ d to its dependencies and the slot's axiom set and provenance to its
\ own; full when d is new and the heap cannot grow the list for it;
\ invalid when slot d is not readable and accepted in the snapshot or the
\ candidate is corrupted.
: lf-env-depend ( d -- outcome )
  lf-cand-count? 0= if drop outcome-invalid exit then
  dup lf-env-usable ok? if lf-cand-add else 2drop outcome-invalid then ;
\ Look name up and record it as a dependency: (d ok); (-1 ok) for a
\ generated recursor, its type's slot (lf-env-genrec-of) recorded; or
\ (-1 outcome).
: lf-env-resolve-generated ( -1 -- -1 outcome ) lf-env-genrec-of lf-env-depend ;
: lf-env-resolve ( name -- d outcome )
  lf-env-lookup dup ok? 0= if exit then drop
  dup 0< if lf-env-resolve-generated exit then
  dup lf-env-depend dup ok? if exit then nip no-result ;

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
  lf-env-usable ok? if lf-slot-decl lf-idecl-params@ outcome-ok exit then
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
\ The warnings of an accepted declaration, (bits ok): an inductive block
\ member's B4 bits (check-block.fs lf-warn-...), 0 for any other; else
\ (0 invalid).
: lf-env-warnings ( d -- bits outcome )
  lf-env-readable 0= if 0 outcome-invalid exit then
  dup lf-slot-accepted? if lf-slot-warnings @ outcome-ok
  else drop 0 outcome-invalid then ;

\ Axioms (plan task 5.3.1; owner decision 4 as amended). The bits of an
\ axiom set that do not count as proved: an accepted declaration with any
\ is NOT PROVED (Lean's verdict, marked).
: lf-env-unproved ( bits -- bits' ) lf-env lf-envh-allowed @ invert and ;
\ A declaration's own axiom bit: an axiom's (axiom-allowlist.fs, whose
\ comparison is bounded by its texts, so its fuel is not limited here), 0
\ for any other kind; ok, or the comparison's failure.
: lf-own-axiom ( decl -- bit outcome )
  dup lf-idecl-kind @ lf-kind-axiom = 0= if drop 0 outcome-ok exit then
  max-n lf-stmt-fuel ! lf-axiom-bit ;
\ The axioms declaration d depends on (plan task 5.3.2 in part: the set
\ Lean's #print axioms lists): every accepted axiom among d and the
\ declarations it uses, directly or not, given to xt ( d' -- ) in
\ ascending order, within this context's snapshot. A dependency is always
\ an earlier slot, so one pass from d down marks them all (no recursion),
\ one byte per slot in a heap block freed before the word returns. ok;
\ full when the heap has no room; invalid when slot d is not readable and
\ accepted.
: lf-dep-at ( k slot -- d ) lf-slot-deps @ + lf-env lf-env-pool store-slot @ ;
: lf-marks-of ( marks slot -- )
  dup lf-slot-count @ 0 ?do 2dup i swap lf-dep-at + true swap c! loop 2drop ;
: lf-marked? ( marks d -- flag ) + c@ 0<> ;
: lf-mark-down ( marks d -- )
  0 swap do dup i lf-marked? if dup i lf-env lf-env-slot lf-marks-of then -1 +loop drop ;
: lf-axiom-slot? ( d -- flag )
  lf-env lf-env-slot dup lf-slot-accepted? swap lf-slot-decl lf-idecl-kind @ lf-kind-axiom = and ;
: lf-marks-give ( marks d xt -- )
  swap 1+ 0 ?do over i lf-marked? if i lf-axiom-slot? if i over execute then then loop 2drop ;
: lf-marks-new ( d -- marks outcome )
  1+ dup allocate if 2drop 0 outcome-full exit then tuck swap erase outcome-ok ;
: lf-marks-run ( d xt marks -- )
  dup >r dup 3 pick + true swap c! dup 3 pick lf-mark-down -rot lf-marks-give
  r> free drop ;
: lf-env-axiom-deps ( d xt -- outcome )
  over lf-env-accepted nip ok? 0= if 2drop outcome-invalid exit then
  over lf-marks-new ok-then? 0= if nip nip exit then lf-marks-run outcome-ok ;
