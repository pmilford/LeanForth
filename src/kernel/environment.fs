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
\ Lookups (ADR 0020 D1, D5, I2; plan task 6.2.5, step SN3). A check
\ records in its candidate every name query it makes of the environment,
\ deciding or aside, with its answer: lf-env-lookup-pass, the N2 queries
\ (lf-env-fresh, lf-env-fresh-generated, lf-env-unheld, lf-env-skip's),
\ lf-env-find, lf-env-first and lf-env-quot-held, each a kind (lf-look-...).
\ The list is sorted by key (name number * 16 + kind) and distinct; the
\ publisher stores it with the slot for every outcome (env-publish.fs),
\ names a check made beyond its input collapsed into one key that a later
\ import can never match. Nothing reads the list back into a check: the
\ verdicts do not change, except that a check whose list the heap cannot
\ hold is published full. A test build (lf-env-i2-checks defined before
\ loading) counts every slot a check reads through lf-env-readable that
\ no recorded query answered (lf-i2-misses).
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
\ lf-env-worker, and the candidate's lists of dependencies and lookups and
\ its block's shapes, the context slabs lf-cand-deps, lf-cand-looks and
\ lf-cand-shapes; for the
\ reports, the axiom sets each slot rests on, kept per context
\ (lf-axd-state and the slabs lf-axd-rows, -row-of, -number and -axioms;
\ lf-env-axiom-deps), and lf-env-gen-state; in a test build lf-i2-misses.
\ An environment must be freed only when no task uses it. The layout is
\ host-specific and never written to a file as it is (a snapshot,
\ env-snapshot.fs, writes chosen fields in a fixed byte order).

require ../lib/lib.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../core/terms.fs
require ../core/input.fs
require ../core/axiom-allowlist.fs

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
  field: lf-envh-allowed    \ axiom bits that count as proved (core/axiom-allowlist.fs;
                            \ a test may set others on a synthetic environment)
  field: lf-envh-version    \ allowlist version
  field: lf-envh-mode       \ run mode
  field: lf-envh-pool       \ the pool's current block
  /store-mark +field lf-envh-pub-mark   \ the publisher's pool mark while it publishes
  field: lf-envh-looks      \ the lookup pool's current block ("Lookups")
  /store-mark +field lf-envh-look-mark  \ and the publisher's mark of it
end-structure

\ A slot (E2). Only the state and outcome mean anything for a declaration
\ that was not accepted, except the members of a block rejected only by
\ B3, whose slots are written as an accepted block's (lf-slot-added), and
\ the skipped mark of a rejected one (lf-slot-skipped); the other fields
\ stay zero.
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
  field: lf-slot-shape      \ an accepted inductive type's computed shape
                            \ (lf-shape-...); else 0
  field: lf-slot-skipped    \ true on a rejected declaration Lean's replay
                            \ skips, unchecked (lf-env-skipped!); else 0
  field: lf-slot-looks      \ index in the pool of its first lookup (two cells each)
  field: lf-slot-looked     \ its number of lookups, on every slot published
  field: lf-slot-saved      \ true: published from a snapshot, not checked here
  field: lf-slot-member     \ its place in the span it was published with (0: first)
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
\ A nested block's recipe (plan task 5.2.5b) is its number of auxiliary
\ types shifted by lf-recipe-aux-shift, without lf-recipe-raw: its
\ recursors are not built again (unknown), and its first type holds the
\ names T.rec_1 .. T.rec_n.
8 constant lf-recipe-aux-shift
\ The shape of an inductive type as LeanForth's block check computed it
\ (ADR 0015 section 8, owner answer Q2: its own values, never the file's,
\ which Lean's replay ignores): Lean's numIndices and is_rec, and a bit
\ saying it was computed; 0, no shape, on any other slot.
1 constant lf-shape-known
2 constant lf-shape-rec
: lf-shape ( nindices rec -- shape ) lf-shape-rec and swap 4 * or lf-shape-known or ;
: lf-shape-indices ( shape -- n ) 4 / ;
: lf-shape-rec? ( shape -- flag ) lf-shape-rec and 0<> ;

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
  field: lf-cand-shaped     \ members with a shape in lf-cand-shapes, from 0
  field: lf-cand-skipped    \ a declaration Lean's replay skips (lf-env-skipped!)
  field: lf-cand-early      \ true once the check found a slot below it not final
  field: lf-cand-looked     \ lookups recorded
  field: lf-cand-sealed     \ true once handed over or a view: nothing more recorded
  field: lf-cand-lost       \ true when a lookup found no room: published full
  field: lf-cand-saved      \ true: the snapshot's loader fills it (lf-env-saved!)
end-structure
/lf-cand context-record: lf-env-cand
\ The dependencies' slots, ascending: a growable array, as long as the
\ check needs (plan task 6.2.0).
1 cells context-slab: lf-cand-deps
\ The lookups, (key, answer) pairs ascending by key ("Lookups" below).
2 cells context-slab: lf-cand-looks
\ The shapes of a block's types (lf-env-shape!), by member: a growable
\ array, as long as the block has types.
1 cells context-slab: lf-cand-shapes
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
\ A declaration Lean's replay skips unchecked, an unsafe constant or a
\ partial definition (Lean/Replay.lean 180-183; plan task 5.2.7): its
\ check says so with true and ends rejected; the publisher marks its
\ slots (lf-slot-skipped?). No later declaration can use it (N1: Lean's
\ unknown constant), its name stays taken (N2: lean4export's parser
\ refuses a name given twice, Parse.lean 78-80), and reports call it
\ skipped (lf-env-skipped?), with Lean's exit status 0.
: lf-env-skipped! ( flag -- ) lf-env-cand lf-cand-skipped ! ;
\ A block's check sets the recipe of the recursor it generated
\ (lf-recipe-... bits); the publisher keeps it on the block's slots, where
\ a later lookup of T.rec that no slot holds finds it (ADR 0015 decision
\ 12).
: lf-env-recipe! ( bits -- ) lf-env-cand lf-cand-recipe ! ;
\ A block's check sets the shape it computed for member k, a type of the
\ block (lf-shape): ok, or full when the array cannot grow. The publisher
\ keeps it on the member's slot (lf-env-shape); a member without one
\ gets 0.
: lf-cand-shaped@ ( -- n ) lf-env-cand lf-cand-shaped @ ;
: lf-env-shape! ( shape k -- outcome )
  dup 1+ lf-cand-shapes slab-hold ok-then? 0= if nip exit then
  dup 1+ lf-cand-shaped@ max lf-env-cand lf-cand-shaped !
  lf-cand-shapes slab-at ! outcome-ok ;
: lf-cand-shape@ ( k -- shape )
  dup lf-cand-shaped@ < if lf-cand-shapes slab-at @ else drop 0 then ;

\ The candidate's lookups (see "Lookups" in the header). A key is a name
\ number times 16 plus the query's kind; an answer the slot it gave + 1 (0
\ for none) times 16, plus 8 for Lean's generated recursor (its holder's
\ slot), plus the outcome. Both fit 32 bits: names and declarations are
\ below 2^27 (ADR 0016 C1, C2). Keys compare unsigned.
16 constant lf-look-kinds
0 constant lf-look-find         \ lf-env-lookup-pass
1 constant lf-look-fresh        \ lf-env-fresh: N2 of a declaration's own name
2 constant lf-look-generated    \ lf-env-fresh-generated: N2 of a generated name
3 constant lf-look-unheld       \ lf-env-unheld (the quotient's names)
4 constant lf-look-seek         \ lf-env-find
5 constant lf-look-type         \ lf-env-first for an inductive type (lf-slot-type?)
6 constant lf-look-any          \ lf-env-first for any slot (lf-slot-any)
7 constant lf-look-other        \ lf-env-first with a test of another module
8 constant lf-look-quot         \ lf-env-quot-held, under the anonymous name
8 constant lf-look-holder       \ an answer's bit: the generated recursor's holder
u32-mask constant lf-look-outside   \ the key of names beyond the input (published)
: lf-look-key ( name kind -- key ) swap lf-look-kinds * + ;
: lf-look-answer ( d outcome -- answer ) swap 1+ lf-look-kinds * + ;
\ The slot an answer gives + 1, 0 for none.
: lf-look-slot+1 ( answer -- n ) 4 rshift ;
: lf-cand-looked@ ( -- n ) lf-env-cand lf-cand-looked @ ;
: lf-look-at ( k -- addr ) lf-cand-looks slab-at ;
\ Recording is on in a check's candidate until the publisher seals it.
: lf-look-on? ( -- flag )
  lf-env-cand dup lf-cand-identity @ 0<> swap lf-cand-sealed @ 0= and ;
\ Where key goes: the first entry whose key is not below it, by halving.
: lf-look-halve ( key lo hi -- key lo' hi' )
  2dup + 2/ dup >r lf-look-at @ 3 pick u< if nip r> 1+ swap else drop r> then ;
: lf-look-place ( key -- key k )
  0 lf-cand-looked@ begin 2dup < while lf-look-halve repeat drop ;
: lf-look-has? ( key k -- flag )
  dup lf-cand-looked@ < if lf-look-at @ = else 2drop false then ;
: lf-look-open ( k -- )
  dup lf-look-at dup 2 cells + rot lf-cand-looked@ swap - 2* cells move ;
: lf-look-insert ( answer key k -- )
  dup lf-look-open lf-look-at 2! 1 lf-env-cand lf-cand-looked +! ;
: lf-look-room? ( -- flag ) lf-cand-looked@ 1+ lf-cand-looks slab-hold ok? ;
: lf-look-lost ( answer key -- ) 2drop true lf-env-cand lf-cand-lost ! ;
\ Record key with its answer, once: a check's queries of one key answer
\ alike, as every slot below it is final while it runs (G-P5).
: lf-look-add ( answer key -- )
  lf-look-place 2dup lf-look-has? if drop 2drop exit then
  lf-look-room? if lf-look-insert else drop lf-look-lost then ;
: lf-env-noted ( answer key -- ) lf-look-on? if lf-look-add else 2drop then ;
\ Record the answer (d outcome) of the query of kind about name.
: lf-look-noted ( d outcome name kind -- d outcome )
  lf-look-key >r 2dup lf-look-answer r> lf-env-noted ;
\ The publisher's seal (env-publish.fs): recording ends, and the keys of
\ names a check made beyond its input tier (core/names.fs; their numbers
\ mean nothing outside its context), the last of the list, become the one
\ key lf-look-outside. Without a view every name is the input's.
: lf-look-input# ( -- n ) lf-name-view lf-nview-input @ tier-names cons-numbers ;
: lf-look-outside! ( k -- )
  dup lf-env-cand lf-cand-looked ! 0 lf-look-outside rot lf-look-at 2!
  1 lf-env-cand lf-cand-looked +! ;
: lf-look-collapse ( -- )
  lf-name-viewed? 0= if exit then
  lf-look-input# lf-look-kinds * lf-look-place nip
  dup lf-cand-looked@ < if lf-look-outside! else drop then ;
: lf-env-seal ( -- ) lf-look-on? if lf-look-collapse then true lf-env-cand lf-cand-sealed ! ;
\ The snapshot's loader (env-snapshot.fs) gives a candidate a saved
\ lookup with lf-env-look!.
: lf-env-look! ( answer key -- ) lf-look-add ;
\ I2 in a test build: a slot read in a check must be one a recorded
\ query answered.
[defined] lf-env-i2-checks [if]
variable lf-i2-misses  0 lf-i2-misses !
: lf-look-gave? ( d -- flag )
  1+ false lf-cand-looked@ 0 ?do over i lf-look-at cell+ @ lf-look-slot+1 = or loop nip ;
: lf-env-i2 ( d -- d )
  lf-look-on? if dup lf-look-gave? 0= if 1 lf-i2-misses +! then then ;
[else]
: lf-env-i2 ( d -- d ) ;
[then]

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
\ The lookup pool ("Lookups") is a second pool, kept the same way: each
\ lookup two records, its key, then its answer.
: lf-env-looks ( env -- store ) lf-envh-looks @ cell+ ;
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
: lf-pool-sound? ( block|0 -- flag ) ?dup if cell+ store-count-valid? else false then ;
: lf-env-pooled? ( env -- flag )
  dup lf-envh-pool @ lf-pool-sound? swap lf-envh-looks @ lf-pool-sound? and ;
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
\ Give the environment its two pools of deps records each: (env ok); or
\ (0 invalid) for an unsound deps, (0 full) when the heap has no room,
\ the environment's memory freed.
: lf-env-block ( room env field -- env outcome )
  >r swap lf-pool-block dup ok? if drop over r> execute ! outcome-ok else nip r> drop then ;
: lf-env-scrap ( env outcome -- 0 outcome ) >r free drop 0 r> ;
: lf-env-unpool ( env outcome -- 0 outcome ) over lf-envh-pool @ lf-pool-release lf-env-scrap ;
: lf-env-pooled ( deps env -- env outcome )
  over over ['] lf-envh-pool lf-env-block dup ok? 0= if >r nip nip r> lf-env-scrap exit then
  2drop ['] lf-envh-looks lf-env-block dup ok? 0= if lf-env-unpool then ;
\ The axiom allowlist (core/axiom-allowlist.fs): its version, and the bits
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
  lf-env-forget dup lf-envh-pool @ lf-pool-release dup lf-envh-looks @ lf-pool-release
  free 0= flag>outcome ;
\ Make a live environment current: ok, or invalid with nothing changed
\ when it is not live or inside a job.
: lf-env-use ( env -- outcome )
  dup lf-env-choosable? 0= if drop outcome-invalid exit then
  lf-envs lf-envs-current ! outcome-ok ;

\ Slots. G-P5's witness (plan task 7.3.1): a slot of the current
\ environment below the declaration of this context's snapshot that is
\ found not final, by whatever word asks (a lookup's scan, a read, the
\ holders of a generated recursor), is noted in the candidate,
\ lf-cand-early, which only lf-env-clear clears. It means the check began
\ before a slot it reads was final: the parallel scheduler
\ (env-schedule.fs) never hands such a candidate over but checks the
\ declaration again once every slot below it is final, and the publisher
\ refuses one that claims ok (env-publish.fs, lf-recheck-early). In a
\ serial run every slot below the declaration is final when its check
\ begins, so nothing is ever noted. (A view, whose limit is the length,
\ may note one too; nothing publishes a view.)
: lf-slot-number ( slot -- d ) lf-env /lf-env + - /lf-slot / ;
: lf-slot-below? ( slot -- flag )
  lf-env if lf-slot-number 0 lf-env-cand lf-cand-decl @ within else drop false then ;
: lf-slot-early ( slot -- ) lf-slot-below? if true lf-env-cand lf-cand-early ! then ;
: lf-env-early? ( -- flag ) lf-env-cand lf-cand-early @ 0<> ;
: lf-slot-final? ( slot -- flag )
  dup lf-slot-state @ lf-state-final = dup if nip exit then swap lf-slot-early ;
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
\ A rejected slot of a declaration Lean's replay skips (lf-env-skipped!).
: lf-slot-skipped? ( slot -- flag )
  dup lf-slot-final? over lf-slot-outcome@ outcome-rejected = and
  swap lf-slot-skipped @ 0<> and ;
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
  lf-env-clear true lf-env-cand lf-cand-sealed ! lf-env-current 0= if outcome-invalid exit then
  dup lf-env-length swap lf-env-snap! outcome-ok ;
\ End the check with its outcome.
: lf-env-finish ( outcome -- ) outcome-sane lf-env-cand lf-cand-outcome ! ;

\ Reading slots in the snapshot. lf-env-readable gives slot d when the
\ snapshot may read it (d below its declaration, slot d final);
\ lf-env-accepted gives (slot ok) when slot d is also accepted, else
\ (0 invalid), recording lf-diag-env-handle.
: lf-env-below? ( d env i -- d env flag ) >r over 0 r> within ;
: lf-env-readable ( d -- slot true | false )
  lf-env-i2 lf-env-snapshot 0= if drop false exit then
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
: lf-env-earliest ( name test limit -- d|-1 )
  lf-input-indexed? if lf-env-chain-first else lf-env-scan-first then ;
: lf-env-matches ( name test limit -- n )
  lf-input-indexed? if lf-env-chain-matches else lf-env-scan-matches then ;
: lf-env-any? ( name limit test -- flag ) swap lf-env-earliest 0< 0= ;

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
  ['] lf-slot-unsupported? swap lf-env-earliest
  dup 0< if drop outcome-rejected else lf-env-k5-unsupported then ;
\ A recursor Lean's kernel generated that no slot holds and that cannot
\ be built again (its type left no recipe; ADR 0015 decision 12):
\ unknown, the name and the type's slot recorded.
: lf-env-generated ( name d -- outcome )
  c" environment lf-env-lookup" lf-diag-generated-recursor lf-diag-note outcome-unknown ;
: lf-env-undecided ( name limit -- outcome )
  2dup ['] lf-slot-undecided? swap lf-env-earliest
  dup 0< if drop lf-env-unsupported else nip nip lf-env-k5-unknown then ;
: lf-env-decide ( name limit -- d outcome )
  2dup ['] lf-slot-usable? swap lf-env-matches case
    0 of lf-env-undecided no-result endof
    1 of ['] lf-slot-usable? swap lf-env-earliest outcome-ok endof
    >r 2drop -1 outcome-invalid r> endcase ;
: lf-env-early ( name limit -- d outcome )
  tuck ['] lf-slot-open? swap lf-env-earliest swap c" environment lf-env-lookup"
  lf-diag-too-early lf-diag-note -1 outcome-invalid ;
: lf-env-seek ( name limit -- d outcome )
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
\ block (named after its first type), is held the same way, by an
\ accepted (or added) type only when it is its block's first and the
\ block has an auxiliary type for that number (k from 1, no leading
\ zero; the recipe, plan task 5.2.5b).
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
  dup cell+ @ >r @ swap lf-env-earliest dup 0< if drop r> drop false else r> true then ;
: lf-env-holding ( prefix limit -- d class )
  lf-env-holders lf-env-holders# 2* cells bounds ?do
    2dup i lf-env-held if 2swap 2drop unloop exit then
  2 cells +loop 2drop -1 outcome-rejected ;
\ The k of rec_<k>, or 0 when no auxiliary recursor can be named so: a
\ leading zero, more than 19 digits, or a number beyond one cell (read
\ modulo 2^64 until review rvUNNI L1; 19 digits never wrap the double).
19 constant lf-env-k-digits
: lf-env-aux-k ( name -- k )
  lf-name-text 4 /string 2dup 1 min s" 0" compare 0= if 2drop 0 exit then
  dup lf-env-k-digits > if 2drop 0 exit then
  base @ >r decimal 0 0 2swap >number 2drop r> base ! if drop 0 then ;
: lf-env-first-type? ( d -- flag )
  dup lf-input-decl lf-idecl-header ?dup
  if lf-hdr-first lf-more-field = else drop false then ;
: lf-env-aux-count ( d -- n )
  lf-env lf-env-slot lf-slot-recipe @ lf-recipe-aux-shift rshift ;
: lf-env-aux-has? ( name d -- flag )
  dup lf-env-first-type? 0= if 2drop false exit then
  lf-env-aux-count swap lf-env-aux-k tuck >= swap 0> and ;
: lf-env-aux-held ( name d class -- d class )
  dup ok? 0= if rot drop exit then
  >r tuck lf-env-aux-has? if r> else r> 2drop -1 outcome-rejected then ;
\ The name of the types that may hold name, 0 when no type can.
: lf-env-type-name ( name -- prefix|0 )
  dup lf-env-rec-kind if lf-name-prefix@ else drop 0 then ;
: lf-env-reserving ( name limit -- d class )
  over lf-env-rec-kind >r over lf-env-type-name ?dup 0=
  if r> drop 2drop -1 outcome-rejected exit then
  swap lf-env-holding r> lf-rec-aux = if lf-env-aux-held else rot drop then ;

\ Lean's quotient (ADR 0015 Q1; review rvAX). add_quot (quot.cpp 47-104)
\ checks that none of Quot, Quot.mk, Quot.lift and Quot.ind is declared
\ (check_name, 53-56), then adds all four at once and marks the quotient
\ initialised; a later quotient declaration changes nothing (48-49). So
\ once one is initialised, those names are declared whatever the file
\ holds, and check_name refuses any other declaration of one of them.
\ LeanForth publishes one quotient record per slot, so the quotient
\ records below limit hold the four names (lf-env-quot-held-pass) -- declared
\ when one is accepted (the quotient is initialised), K5 when one is
\ undecided or unsupported, too early when one is not final -- (d class)
\ as lf-env-holding gives them; (-1 rejected) when none holds them, or
\ (lf-env-quot-holding) for a name not one of the four; (-1 full) when a
\ name cannot be made. A quotient record of another name is never
\ accepted (quot.fs), so the slots of the four names are all there is to
\ scan. Lean's quot_reduce_rec (quot.fs) can then match Quot.mk by name,
\ as Lean does.
: lf-env-quot-text ( k -- c-addr u )
  case 0 of s" Quot" endof  1 of s" Quot.mk" endof  2 of s" Quot.lift" endof
    s" Quot.ind" rot endcase ;
: lf-env-quot-name? ( name -- flag )
  false 4 0 ?do over i lf-env-quot-text lf-stmt-name? or loop nip ;
: lf-slot-quot? ( slot -- flag )
  lf-slot-index lf-input-decl lf-idecl-kind @ lf-kind-quotient = ;
: lf-slot-quot-open? ( slot -- flag ) dup lf-slot-open? swap lf-slot-quot? and ;
: lf-slot-quot-accepted? ( slot -- flag ) dup lf-slot-accepted? swap lf-slot-quot? and ;
: lf-slot-quot-undecided? ( slot -- flag )
  dup lf-slot-final? over lf-slot-undecided? and swap lf-slot-quot? and ;
: lf-slot-quot-unsupported? ( slot -- flag )
  dup lf-slot-final? over lf-slot-unsupported? and swap lf-slot-quot? and ;
create lf-env-quot-holders
  ' lf-slot-quot-open? , outcome-invalid ,  ' lf-slot-quot-accepted? , outcome-ok ,
  ' lf-slot-quot-undecided? , outcome-unknown ,
  ' lf-slot-quot-unsupported? , outcome-unsupported ,
here lf-env-quot-holders - 2 cells / constant lf-env-quot-holders#
\ The first slot below limit of one of the four names that passes test:
\ (d ok), (-1 ok) when there is none, (-1 full) when a name cannot be made.
: lf-env-quot-found ( limit test -- d|-1 outcome )
  4 0 ?do
    i lf-env-quot-text lf-stmt-intern 0= if drop 2drop -1 outcome-full unloop exit then
    over 3 pick lf-env-earliest dup 0< 0= if nip nip outcome-ok unloop exit then drop
  loop 2drop -1 outcome-ok ;
: lf-env-quot-held-pass ( limit -- d class )
  lf-env-quot-holders lf-env-quot-holders# 2* cells bounds ?do
    dup i @ lf-env-quot-found ok-then? 0= if nip -1 swap unloop exit then
    dup 0< 0= if nip i cell+ @ unloop exit then drop
  2 cells +loop drop -1 outcome-rejected ;
: lf-env-quot-holding ( name limit -- d class )
  swap lf-env-quot-name? if lf-env-quot-held-pass else drop -1 outcome-rejected then ;

\ Whether a type that may hold name below i, or a quotient record that
\ holds it, is not final (the scheduler's readiness, lf-env-ready?); a
\ quotient name that cannot be made counts as not final.
: lf-env-type-open? ( name i -- flag )
  swap lf-env-type-name ?dup 0= if drop false exit then
  swap ['] lf-slot-type-open? lf-env-any? ;
: lf-env-quot-open? ( name i -- flag )
  lf-env-quot-holding nip dup outcome-invalid = swap outcome-full = or ;
: lf-env-held-open? ( name i -- flag )
  2dup lf-env-quot-open? >r lf-env-type-open? r> or ;

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
\ One of the four quotient names with no slot of it usable while the
\ quotient is initialised (its record comes later in the file or is
\ missing, or a declaration of that name was refused): Lean's kernel
\ holds the constant add_quot made, no slot does; unknown (diagnostic 77,
\ the name and the quotient record's slot) until such a use is typed from
\ quot.fs's entry (a follow-up of plan task 5.2.4). Otherwise as a name
\ no type holds.
: lf-env-quot-absent ( name limit -- -1 outcome )
  2dup lf-env-quot-holding dup ok? if drop nip lf-env-generated no-result exit then
  dup outcome-full = if 2swap 2drop exit then lf-env-absent-as ;
: lf-env-n1 ( name limit outcome -- -1 outcome )
  dup outcome-rejected = 0= if nip nip no-result exit then
  drop 2dup lf-env-reserving dup outcome-rejected =
  if 2drop lf-env-quot-absent else lf-env-absent-as then ;
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
\ (started too early), or when two were usable. Recorded in the
\ candidate (lf-look-find); a generated recursor's answer is its holder's
\ slot, marked.
: lf-env-lookup-found ( name -- d outcome )
  0 lf-env-gen-state !
  lf-env-snapshot 0= if drop -1 outcome-invalid exit then nip
  over lf-env-name-ok? 0= if drop lf-env-bad-name exit then
  2dup lf-env-seek dup ok? if 2swap 2drop exit then nip lf-env-n1 ;
: lf-look-holder-answer ( -- answer )
  lf-env-genrec-of outcome-ok lf-look-answer lf-look-holder or ;
: lf-look-found ( d outcome -- answer )
  over 0< over ok? and if 2drop lf-look-holder-answer else lf-look-answer then ;
: lf-env-lookup-pass ( name -- d outcome )
  dup >r lf-env-lookup-found 2dup lf-look-found r> lf-look-find lf-look-key lf-env-noted ;
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
: lf-env-n2-quot ( d class -- outcome )
  dup outcome-full = if nip else lf-env-n2-held then ;
\ N2 for name below limit: no declaration of it that Lean's replay skips
\ (lf-env-unskipped: rejected, as lean4export's parser refuses the file,
\ before K5); no usable declaration of it (the slots of that
\ name: accepted, or added by Lean's kernel with a block rejected only by
\ B3, R2-1), and no accepted or added type T with name T.rec (Lean's
\ generated recursor, review rvI21 B2) (lf-env-unheld-pass); for any
\ declaration but a quotient record (quot.fs checks those as add_quot
\ does), also not one of the four quotient names once the quotient is
\ initialised (lf-env-fresh). ok, rejected, unknown, unsupported,
\ invalid or full, as lf-env-n2 and lf-env-n2-held say.
\ The name of a recursor Lean's kernel generates that the file leaves out
\ (B4: T.rec, or T.rec_k of a nested block) is no declaration of the
\ file, so the parser's refusal does not concern it, and replay never
\ added the skipped declaration of that name: lf-env-fresh-generated
\ runs every test but lf-env-unskipped (review rvUNNI M1).
: lf-env-unskipped ( name limit -- outcome )
  ['] lf-slot-skipped? swap lf-env-earliest
  dup 0< if drop outcome-ok else lf-env-declared then ;
: lf-env-unused ( name limit -- outcome )
  2dup lf-env-seek lf-env-n2 dup ok? 0= if nip nip exit then drop
  lf-env-reserving lf-env-n2-held ;
: lf-env-unheld-pass ( name limit -- outcome )
  2dup lf-env-unskipped dup ok? 0= if nip nip exit then drop lf-env-unused ;
: lf-env-unquot ( name limit outcome -- outcome )
  dup ok? 0= if nip nip exit then drop lf-env-quot-holding lf-env-n2-quot ;
\ An N2 query's answer, recorded under name with kind ("Lookups").
: lf-look-n2 ( name outcome kind -- outcome ) >r -1 swap rot r> lf-look-noted nip ;
: lf-env-fresh ( name limit -- outcome )
  over >r 2dup lf-env-unheld-pass lf-env-unquot r> swap lf-look-fresh lf-look-n2 ;
: lf-env-fresh-generated ( name limit -- outcome )
  over >r 2dup lf-env-unused lf-env-unquot r> swap lf-look-generated lf-look-n2 ;
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

\ Lean's replay skips unsafe constants and partial definitions, checking
\ nothing of them (Lean/Replay.lean 180-183; plan task 5.2.7). lf-env-skip
\ ends the check of the n declarations from the one checked on (a block's
\ members, or the declaration alone), all unsafe or partial: rejected,
\ marked skipped (lf-env-skipped!; diagnostic lf-diag-skipped, with the
\ kind and safety given) -- unless one has the name of an earlier
\ declaration of the input, whatever its outcome: rejected then
\ (lf-diag-already-declared, its name ID and that declaration), as
\ lean4export's parser refuses a name given twice (Parse.lean 78-80).
\ Invalid without a check's snapshot or with a corrupted name store.
: lf-slot-any ( slot -- true ) drop true ;
\ A scan's first slot d (-1 none), recorded under name with kind.
: lf-look-first ( d name kind -- d ) >r outcome-ok swap r> lf-look-noted drop ;
: lf-env-earlier ( d -- d'|-1 )
  lf-input-name dup ['] lf-slot-any lf-env-limit lf-env-earliest swap lf-look-any lf-look-first ;
: lf-env-twin ( k -- d d'|-1 ) lf-env-limit + dup lf-env-earlier ;
: lf-env-twice ( n -- d d' | -1 -1 )
  0 ?do i lf-env-twin dup 0< 0= if unloop exit then 2drop loop -1 -1 ;
: lf-env-given-twice ( d d' -- outcome )
  swap lf-input-name swap c" environment lf-env-skip" lf-diag-already-declared
  lf-diag-note outcome-rejected ;
: lf-env-unchecked ( kind safety -- outcome )
  c" environment lf-env-skip" lf-diag-skipped lf-diag-note true lf-env-skipped!
  outcome-rejected ;
: lf-env-skip-ready? ( -- flag )
  lf-env-checking dup if nip nip then lf-name-storage-valid? and ;
: lf-env-skip ( kind safety n -- outcome )
  lf-env-skip-ready? 0= if 2drop drop outcome-invalid exit then
  lf-env-twice dup 0< if 2drop lf-env-unchecked exit then
  2swap 2drop lf-env-given-twice ;
\ The name queries other modules make (inductive-block.fs,
\ inductive-nested.fs, quot.fs), each recorded ("Lookups"); the words
\ here use the unrecorded forms. lf-env-first records its test's kind: an
\ inductive type, any slot, or another module's test (lf-look-other,
\ which a later import cannot replay).
: lf-env-unheld ( name limit -- outcome )
  over >r lf-env-unheld-pass r> swap lf-look-unheld lf-look-n2 ;
: lf-env-find ( name limit -- d outcome ) over >r lf-env-seek r> lf-look-seek lf-look-noted ;
: lf-look-test ( test -- kind )
  dup ['] lf-slot-type? = if drop lf-look-type exit then
  ['] lf-slot-any = if lf-look-any else lf-look-other then ;
: lf-env-first ( name test limit -- d|-1 )
  >r 2dup r> lf-env-earliest -rot lf-look-test lf-look-first ;
: lf-env-quot-held ( limit -- d class ) lf-env-quot-held-pass 0 lf-look-quot lf-look-noted ;
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
\ An axiom's own bit (core/axiom-allowlist.fs), joined to the candidate's set
\ by its check (check-declaration.fs).
: lf-env-axiom! ( bits -- ) lf-env-cand lf-cand-axioms lf-or! ;
: lf-cand-union ( slot -- )
  dup lf-slot-axioms @ lf-env-cand lf-cand-axioms lf-or!
  lf-slot-provenance @ lf-env-cand lf-cand-provenance lf-or! ;
\ The snapshot's loader (env-snapshot.fs) fills a candidate from a saved
\ slot: lf-env-saved! marks it as taken from saved results (ADR 0012 E8:
\ provenance saved, which every user joins; the slot is marked saved).
: lf-env-saved! ( -- )
  true lf-env-cand lf-cand-saved ! lf-provenance-saved lf-env-cand lf-cand-provenance lf-or! ;
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
\ Where declaration d's verdict comes from (ADR 0020 D4, OQ-3; ADR 0012
\ E8): lf-origin-checked in this run, lf-origin-uses when checked here
\ but resting on saved results, lf-origin-saved when taken from a
\ snapshot and not checked here; checked when unreadable.
0 constant lf-origin-checked  1 constant lf-origin-uses  2 constant lf-origin-saved
: lf-slot-origin ( slot -- n )
  dup lf-slot-saved @ if drop lf-origin-saved exit then
  lf-slot-provenance @ lf-provenance-saved and 0<> lf-origin-uses and ;
: lf-env-origin ( d -- n ) lf-env-readable if lf-slot-origin else lf-origin-checked then ;
\ A run of saved results is a development run (E8): the environment's
\ mode, set by the snapshot's loader before any slot is published.
: lf-env-develop ( env -- ) lf-env-may-write lf-mode-development swap lf-envh-mode ! ;
\ Whether declaration d is one Lean's replay skips (lf-env-skipped!): its
\ outcome rejected, which reports call skipped; false when unreadable.
: lf-env-skipped? ( d -- flag ) lf-env-readable if lf-slot-skipped? else false then ;
: lf-env-axioms ( d -- bits outcome )
  lf-env-readable 0= if 0 outcome-invalid exit then
  dup lf-slot-accepted? if lf-slot-axioms @ outcome-ok else drop 0 outcome-invalid then ;
\ The shape of a usable declaration, (shape ok): an accepted inductive
\ type's (lf-shape-...), 0 for any other; else (0 invalid).
: lf-env-shape ( d -- shape outcome )
  lf-env-usable ok-then? if lf-slot-shape @ outcome-ok else 0 swap then ;
\ is_non_rec_structure (inductive.cpp 28-33) of usable slot d: (decl ok)
\ for an inductive type with one constructor (its declaration's list, the
\ block's own) and, as its shape says, no index and not recursive -- never
\ as the file's fields say (review rvCONV B2); (0 ok) for any other
\ declaration; unknown for an inductive type without a shape; or the
\ slot's failure. Structure eta and unit-like types (defeq.fs) and iota's
\ structure eta (iota.fs) ask this; projections read the shape's
\ numIndices (infer-proj.fs).
: lf-env-one-ctor? ( decl -- flag )
  lf-idecl-data ?dup if lf-ity-ctors@ nip 1 = else false then ;
: lf-env-flat? ( shape -- flag ) dup lf-shape-indices 0= swap lf-shape-rec? 0= and ;
: lf-env-shaped ( decl shape -- decl|0 outcome )
  dup lf-shape-known and 0= if 2drop 0 outcome-unknown exit then
  lf-env-flat? over lf-env-one-ctor? and 0= if drop 0 then outcome-ok ;
: lf-env-structure ( d -- decl|0 outcome )
  lf-env-usable ok-then? 0= if 0 swap exit then
  dup lf-slot-decl lf-idecl-kind @ lf-kind-inductive <> if drop 0 outcome-ok exit then
  dup lf-slot-decl swap lf-slot-shape @ lf-env-shaped ;
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
\ The allowlist's lookup (core/axiom-allowlist.fs lf-allow-found): the
\ accepted declaration named id within this context's snapshot and its
\ slot's warning bits, else 0 0; it records no dependency, and the
\ diagnostic a failed lookup notes is put back.
: lf-env-allow-slot ( d -- decl|0 bits )
  dup 0< if drop 0 0 exit then
  lf-env-usable ok-then? 0= if drop 0 0 exit then
  dup lf-slot-decl swap lf-slot-warnings @ ;
:noname ( id -- decl|0 bits )
  >r lf-diag@ r> lf-env-lookup-pass ok-then? if lf-env-allow-slot else drop 0 0 then
  2>r lf-diag! 2r> ; is lf-allow-found
\ A declaration's own axiom bit: an axiom's (core/axiom-allowlist.fs, whose
\ comparison is bounded by its texts, so its fuel is not limited here), 0
\ for any other kind; ok, or the comparison's failure.
: lf-own-axiom ( decl -- bit outcome )
  dup lf-idecl-kind @ lf-kind-axiom = 0= if drop 0 outcome-ok exit then
  max-n lf-stmt-fuel ! lf-axiom-bit ;
\ The axioms declaration d depends on (plan task 5.3.2 in part: the set
\ Lean's #print axioms lists): every accepted axiom among d and the
\ declarations it uses, directly or not, given to xt ( d' -- ) in
\ ascending order, within this context's snapshot. ok; full when the heap
\ has no room; invalid when slot d is not readable and accepted.
\ Each slot's set is worked out once per environment and snapshot, in
\ ascending order up to the slot asked for, and kept in this context, so
\ a report that asks for every declaration's set takes time linear in the
\ dependencies, not in the export per declaration (review rvAX L5). The
\ accepted axioms below the snapshot's limit are numbered in file order;
\ a slot's set is a row of bits over those numbers: its dependencies'
\ rows joined (a dependency is always an earlier slot, so no recursion),
\ with its own bit for an axiom. A row equal to the empty one (row 0) or
\ to a dependency's is shared, so rows are only made where a set grows.
begin-structure /lf-axd
  field: lf-axd-env     \ the identity of the environment rows are kept for, 0 none
  field: lf-axd-limit   \ its snapshot's limit
  field: lf-axd-done    \ slots whose row is known: those below done
  field: lf-axd-width   \ cells per row
end-structure
/lf-axd context-record: lf-axd-state
1 cells context-slab: lf-axd-rows      \ the rows, width cells each
1 cells context-slab: lf-axd-row-of    \ per slot: its row's number
1 cells context-slab: lf-axd-number    \ per axiom slot: its number
1 cells context-slab: lf-axd-axioms    \ per number: the axiom's slot
: lf-axd-cell-bits ( -- n ) 0 max-n begin ?dup while 1 rshift swap 1+ swap repeat 1+ ;
lf-axd-cell-bits constant lf-axd-bits   \ bits per cell
: lf-axd-width@ ( -- n ) lf-axd-state lf-axd-width @ ;
: lf-axd-row ( r -- addr ) lf-axd-width@ * lf-axd-rows slab-at ;
: lf-axd-top ( -- addr ) lf-axd-rows slab-top ;
: lf-axd-row-of@ ( d -- r ) lf-axd-row-of slab-at @ ;
: lf-dep-at ( k slot -- d ) lf-slot-deps @ + lf-env lf-env-pool store-slot @ ;
\ Lookup k of a published slot: its key and answer (two records each in
\ the lookup pool).
: lf-look-cell ( i -- x ) lf-env lf-env-looks store-slot @ ;
: lf-slot-look ( k slot -- key answer )
  lf-slot-looks @ swap 2* + dup lf-look-cell swap 1+ lf-look-cell ;
\ Numbering: the accepted axioms below the limit; room for the per-slot
\ arrays; row 0, empty; the key the rows are kept for.
: lf-axd-axiom? ( d -- flag )
  lf-env-readable 0= if false exit then
  dup lf-slot-accepted? swap lf-slot-decl lf-idecl-kind @ lf-kind-axiom = and ;
: lf-axd-number! ( d -- outcome )
  1 lf-axd-axioms slab-claim ok-then? 0= if nip exit then
  2dup lf-axd-axioms slab-at ! swap lf-axd-number slab-at ! outcome-ok ;
: lf-axd-numbered ( -- outcome )
  lf-env-limit 0 ?do
    i lf-axd-axiom? if i lf-axd-number! dup ok? 0= if unloop exit then drop then
  loop outcome-ok ;
: lf-axd-arrays ( -- outcome )
  lf-env-limit lf-axd-row-of slab-hold dup ok? 0= if exit then drop
  lf-env-limit lf-axd-number slab-hold ;
: lf-axd-width! ( -- )
  lf-axd-axioms slab-count lf-axd-bits /mod swap 0<> - 1 max lf-axd-state lf-axd-width ! ;
: lf-axd-empty ( -- outcome )
  lf-axd-width! lf-axd-width@ lf-axd-rows slab-claim nip
  dup ok? if 0 lf-axd-row lf-axd-width@ cells erase then ;
: lf-axd-key! ( -- )
  lf-env lf-envh-identity @ lf-axd-state lf-axd-env !
  lf-env-limit lf-axd-state lf-axd-limit !  0 lf-axd-state lf-axd-done ! ;
: lf-axd-reset ( -- outcome )
  0 lf-axd-state lf-axd-env ! lf-axd-rows slab-clear lf-axd-axioms slab-clear
  lf-axd-arrays dup ok? 0= if exit then drop
  lf-axd-numbered dup ok? 0= if exit then drop
  lf-axd-empty dup ok? if lf-axd-key! then ;
: lf-axd-current? ( -- flag )
  lf-axd-state dup lf-axd-env @ lf-env lf-envh-identity @ =
  swap lf-axd-limit @ lf-env-limit = and ;
: lf-axd-ready ( -- outcome ) lf-axd-current? if outcome-ok else lf-axd-reset then ;
\ Slot j's row: the empty row when it is not accepted; else, in the free
\ space above the rows, its dependencies' rows joined and its own bit,
\ then shared with an equal row or kept.
: lf-axd-or ( r -- )
  lf-axd-row lf-axd-top lf-axd-width@ cells bounds ?do
    dup @ i @ or i ! cell+
  1 cells +loop drop ;
: lf-axd-bit! ( k -- )
  lf-axd-bits /mod cells lf-axd-top + swap 1 swap lshift over @ or swap ! ;
: lf-axd-deps-or ( slot -- )
  dup lf-slot-count @ 0 ?do i over lf-dep-at lf-axd-row-of@ lf-axd-or loop drop ;
: lf-axd-join ( slot j -- )
  lf-axd-top lf-axd-width@ cells erase
  over lf-axd-deps-or swap lf-slot-decl lf-idecl-kind @ lf-kind-axiom =
  if lf-axd-number slab-at @ lf-axd-bit! else drop then ;
: lf-axd-same? ( r -- flag )
  lf-axd-row lf-axd-width@ cells lf-axd-top lf-axd-width@ cells compare 0= ;
: lf-axd-shared ( slot -- r|-1 )
  0 lf-axd-same? if drop 0 exit then
  dup lf-slot-count @ 0 ?do
    i over lf-dep-at lf-axd-row-of@ dup lf-axd-same? if nip unloop exit then drop
  loop drop -1 ;
: lf-axd-kept ( -- r outcome )
  lf-axd-width@ lf-axd-rows slab-claim ok-then?
  if lf-axd-width@ / outcome-ok else no-result then ;
: lf-axd-made ( j -- r outcome )
  dup lf-env-readable 0= if drop 0 outcome-ok exit then
  dup lf-slot-accepted? 0= if 2drop 0 outcome-ok exit then
  lf-axd-width@ lf-axd-rows slab-room ok-then? 0= if nip no-result exit then
  dup >r swap lf-axd-join r> lf-axd-shared
  dup 0< if drop lf-axd-kept else outcome-ok then ;
: lf-axd-upto ( d -- outcome )
  1+ lf-axd-state lf-axd-done @ over min ?do
    i lf-axd-made ok-then? 0= if unloop exit then i lf-axd-row-of slab-at !
    i 1+ lf-axd-state lf-axd-done !
  loop outcome-ok ;
\ The axioms of row r's bits, in order: those of one cell (x, its first
\ number k), then of each cell; no address is held while xt runs.
: lf-axd-cell ( xt x k -- xt )
  swap begin ?dup while
    dup 1 and if over lf-axd-axioms slab-at @ 3 pick execute then
    1 rshift swap 1+ swap
  repeat drop ;
: lf-axd-give ( d xt -- )
  swap lf-axd-row-of@ lf-axd-width@ 0 ?do
    dup lf-axd-row i cells + @ ?dup if rot swap i lf-axd-bits * lf-axd-cell swap then
  loop 2drop ;
: lf-env-axiom-deps ( d xt -- outcome )
  over lf-env-accepted nip ok? 0= if 2drop outcome-invalid exit then
  lf-axd-ready dup ok? 0= if nip nip exit then drop
  over lf-axd-upto dup ok? 0= if nip nip exit then drop lf-axd-give outcome-ok ;
\ Whether axiom slot d (one lf-env-axiom-deps gives) is outside the
\ allowlist, its own bit one that does not count as proved.
: lf-env-unlisted? ( d -- flag )
  lf-env lf-env-slot lf-slot-decl lf-own-axiom drop lf-env-unproved 0<> ;
