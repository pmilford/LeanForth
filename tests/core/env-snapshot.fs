\ Tests of the lookup lists and of the snapshot's round trip at the Forth
\ level (plan task 6.2.5, step SN3; kernel/environment.fs "Lookups",
\ kernel/env-snapshot.fs, cli/check-run.fs). Built with the I2 assertion
\ (lf-env-i2-checks, defined before loading): every pinned export and the
\ other fixture exports are checked, and
\ - no check reads a slot that none of its recorded queries answered
\   (lf-i2-misses 0);
\ - every dependency of every published slot is a slot its lookups
\   answered;
\ - every check recorded at least its own name's query (N2), and the lists
\   are ascending and distinct;
\ - the snapshot written after the run, loaded into a new run, publishes
\   every slot with the same outcome, fields and lists, provenance saved,
\   and gives back each declaration's fuel and diagnostic;
\ - a check whose lookup list cannot grow (the context's slab limited) is
\   published full with diagnostic lookups-full (100), whatever it found.
\ The command line's tests (tests/cli/test_leanforth.py, Snapshots) cover
\ the files, their determinism and the planted faults. Test-only.

create lf-env-i2-checks   \ compiles the I2 assertion into environment.fs
include ../support/heap-watch.fs   \ the refusals at the end
require ../../src/main.fs
include ../support/tester.fs
include ../support/checks.fs
include ../support/scratch.fs
decimal

s" leanforth-env-snapshot-test.lfsnap" scratch-file 2constant snap-file
\ The exports: the pinned ones with their manifests, then the fixtures.
create checked-exports
  s" tests/reference/composition.ndjson" 2,  s" tests/reference/constant-fixture.ndjson"
  2,
  s" tests/reference/identity.ndjson" 2,  s" tests/reference/poly-identity.ndjson" 2,
  s" tests/reference/type-identity.ndjson" 2,  s" tests/cli/chain.ndjson" 2,
  s" tests/cli/inductive.ndjson" 2,  s" tests/cli/irrelevance.ndjson" 2,
  s" tests/cli/nested.ndjson" 2,  s" tests/cli/sharing.ndjson" 2,
  s" tests/cli/sharing-universe.ndjson" 2,  s" tests/cli/unfold.ndjson" 2,
here checked-exports - 2 cells / constant checked#
create plain-exports
  s" tests/core/check-declaration-cases/composition-literal.ndjson" 2,
  s" tests/core/check-declaration-cases/composition-loose.ndjson" 2,
  s" tests/core/check-declaration-cases/composition-postulate.ndjson" 2,
  s" tests/core/check-declaration-cases/composition-twice.ndjson" 2,
  s" tests/core/check-declaration-cases/composition-unsafe.ndjson" 2,
  s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" 2,
  s" tests/core/check-declaration-cases/lambda-let.ndjson" 2,
  s" tests/core/check-declaration-cases/let-lambda.ndjson" 2,
  s" tests/core/check-declaration-cases/let-nondep.ndjson" 2,
  s" tests/core/check-declaration-cases/swap-max-far.ndjson" 2,
  s" tests/core/check-declaration-cases/swap-max.ndjson" 2,
  s" tests/core/ndjson-block.ndjson" 2,  s" tests/cli/jobs/dupl80.ndjson" 2,
  s" tests/cli/jobs/wide60.ndjson" 2,
here plain-exports - 2 cells / constant plain#
: export@ ( k table -- c-addr u ) swap 2* cells + 2@ ;

variable failures  0 failures !
: fails ( c-addr u -- ) ." FAILED: " type cr 1 failures +! ;
: must ( flag c-addr u -- ) rot if 2drop else fails then ;

\ ---- A fresh run, the I2 assertion and the lists.
: slot@ ( d -- slot ) lf-env lf-env-slot ;
: answers? ( d slot -- flag )
  false swap dup lf-slot-looked @ 0 ?do
    i over lf-slot-look nip lf-look-slot+1 3 pick 1+ = rot or swap
  loop drop nip ;
: deps-answered? ( d -- flag )
  slot@ true over lf-slot-count @ 0 ?do i 2 pick lf-dep-at 2 pick answers? and loop nip ;
: ascending? ( slot -- flag )
  true over lf-slot-looked @ 1 max 1 ?do
    i 1- 2 pick lf-slot-look drop i 3 pick lf-slot-look drop u< and
  loop nip ;
: own-name? ( d -- flag )
  dup lf-input-name lf-look-kinds * lf-look-fresh + swap slot@ false swap
  dup lf-slot-looked @ 0 ?do i over lf-slot-look drop 3 pick = rot or swap loop drop nip ;
: lists-ok? ( -- flag )
  true lf-input-count 0 ?do
    i deps-answered? and i slot@ ascending? and
  loop ;
: fresh ( c-addr u checked? -- )
  20000000 ck-start ck-load ok? s" load" must 0 lf-i2-misses ! ck-check
  ck-outcome ok? s" run" must ck-verdicts? s" view" must ;
: i2-and-lists ( c-addr u checked? -- )
  >r 2dup r> fresh lf-i2-misses @ 0= lists-ok? and
  if 2drop else ." I2 or lists: " fails then ;

\ ---- The round trip: the same outcome, fields and lists, provenance
\ saved; the same fuel and diagnostic.
create kept-then 4096 cells allot
: kept-cells ( -- n ) lf-input-count 4 * ;
: keep-then ( -- )
  kept-cells 4096 > abort" env-snapshot: too many declarations"
  lf-input-count 0 ?do
    i lf-env-outcome i 4 * cells kept-then + !  i ck-fuel-of i 4 * 1+ cells kept-then + !
    i ck-kept kept-code @ i 4 * 2 + cells kept-then + !
    i lf-env-axioms drop i 4 * 3 + cells kept-then + !
  loop ;
: same-now? ( d -- flag )
  dup lf-env-outcome over 4 * cells kept-then + @ =
  over ck-fuel-of 2 pick 4 * 1+ cells kept-then + @ = and
  over ck-kept kept-code @ 2 pick 4 * 2 + cells kept-then + @ = and
  over lf-env-axioms drop 2 pick 4 * 3 + cells kept-then + @ = and
  swap lf-env-origin lf-origin-saved = and ;
: reloaded ( -- )
  snap-file s" {}" ck-snapshot-save ok? s" save" must ck-release
  20000000 ck-start snap-file -1 ck-snapshot-load ok? s" snapshot load" must ck-check
  ck-outcome ok? s" snapshot run" must ck-verdicts? s" snapshot view" must ;
: round-trip ( c-addr u checked? -- )
  fresh keep-then reloaded
  true lf-input-count 0 ?do i same-now? and loop s" round trip" must ck-release ;

: each-export ( xt -- )
  checked# 0 ?do i checked-exports export@ true 3 pick execute loop
  plain# 0 ?do i plain-exports export@ false 3 pick execute loop drop ;
' i2-and-lists each-export
T{ failures @ -> 0 }T
' round-trip each-export
T{ failures @ -> 0 }T
: own-names? ( -- flag ) true lf-input-count 0 ?do i own-name? and loop ;
s" tests/reference/constant-fixture.ndjson" true fresh
T{ own-names? 1 lf-env-origin -> true lf-origin-checked }T
\ A rejected declaration keeps its lookups too (a later import replays
\ them): composition-wrong-argument fails at inference, after N2.
s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" false fresh
T{ 0 lf-env-outcome 0 own-name? -> outcome-rejected true }T

\ ---- A lookup list that cannot grow: full (diagnostic 100), here the
\ fixture's third declaration, which looks up two names, the context's
\ slab limited to one entry; then the slab is given back its limit.
: looks-limited ( n -- ) lf-cand-looks slab-free 2 cells swap lf-cand-looks slab-init drop
  ;
1 looks-limited
20000000 ck-start s" tests/reference/constant-fixture.ndjson" true ck-load drop ck-check
ck-verdicts? drop
T{ 0 lf-env-outcome 2 lf-env-outcome 2 ck-kept kept-code @
   -> outcome-ok outcome-full lf-diag-lookups-full }T
2 cells slab-limit-max looks-limited
ck-release

\ ---- A slot's own fields as the loader reads them (review FRK F5): each
\ forged in turn just past what the checker writes is refused.
create forged sl-fields# u32s allot
: forged-clear ( -- ) forged sl-fields# u32s erase ;
: forged? ( u k -- flag ) forged-clear forged fld! forged sl-sane? ;
T{ 0 sl-outcome forged? outcome-full sl-outcome forged? -> true true }T
T{ outcome-full 1+ sl-outcome forged? -> false }T
T{ 7 sl-marks forged? 8 sl-marks forged? -> true false }T
T{ lf-allowlist-bits sl-axioms forged? snap-axiom-bits invert sl-axioms forged? -> true false }T
T{ lf-warn-indices lf-warn-rec or lf-warn-reflexive or lf-warn-nested or lf-warn-no-recursor or
   lf-warn-quot-record or sl-warnings forged? -> true }T
T{ snap-warn-limit sl-warnings forged? -> false }T
T{ lf-recipe-raw sl-recipe forged? lf-recipe-raw lf-recipe-large or sl-recipe forged? -> true true }T
T{ lf-recipe-large sl-recipe forged? 4 sl-recipe forged? -> false false }T
T{ 3 lf-recipe-aux-shift lshift sl-recipe forged? -> true }T
T{ 3 lf-recipe-aux-shift lshift lf-recipe-raw or sl-recipe forged? -> false }T
T{ 5 true lf-shape sl-shape forged? 0 false lf-shape sl-shape forged? -> true true }T
T{ lf-shape-rec sl-shape forged? 4 sl-shape forged? -> false false }T
T{ forged ' sl-sane? rs-checked -> false }T
\ An answer: an outcome and a slot below the span's first, or the holder
\ bit with ok; never the holder bit with another outcome, nor 7.
create forged-snap /snap allot  forged-snap /snap erase  5 forged-snap snap-head !
: answer? ( d outcome -- flag ) lf-look-answer forged-snap answer-ok? ;
: holder? ( d outcome -- flag ) lf-look-answer lf-look-holder or forged-snap answer-ok? ;
T{ 4 outcome-ok answer? 4 outcome-rejected answer? -1 outcome-full answer? -> true true true }T
T{ 5 outcome-ok answer? -1 7 answer? -> false false }T
T{ 4 outcome-ok holder? 4 outcome-rejected holder? 4 outcome-full holder? -> true false false }T

\ ---- A key beyond the input as written (review FRK F4): without the
\ environment's tier of names or the canon tier, or for a number the
\ environment's tier does not hold, refused (invalid) and never read past
\ them; a name beyond made canon's keeps its kind.
s" tests/reference/constant-fixture.ndjson" true fresh
T{ lf-env-outer canon -> 0 0 }T
T{ 3 lf-look-kinds * canon-key -> -1 outcome-invalid }T
T{ lf-look-outside canon-key -> -1 outcome-invalid }T
s" tests/cli/nested.ndjson" true fresh
: top-outer ( -- key ) lf-env-outer tier-names cons-numbers 1- lf-look-kinds * lf-look-fresh + ;
T{ lf-env-outer 0<> canon -> true 0 }T
T{ top-outer canon-key -> -1 outcome-invalid }T
T{ snap-outers /outers erase ck-stage canon-tier -> outcome-ok }T
T{ top-outer canon-key swap lf-look-kinds 1- and -> outcome-ok lf-look-fresh }T
T{ lf-look-outside canon-key -> -1 outcome-invalid }T
outers-free ck-release

\ ---- The heap refusing (coverage COV2; tests/support/heap-watch.fs):
\ each allocation of a snapshot's save refused in turn is full; each of
\ its load (the run's context made first, then the refusal armed) is
\ full, or ok where the load does without the room (allocations 42-56
\ of the first load of tests/cli/inductive.ndjson today), never another
\ outcome; a save and a load with nothing refused are ok after.
s" tests/cli/inductive.ndjson" true fresh
: save ( -- outcome ) snap-file s" {}" ck-snapshot-save ;
: save-at ( k -- outcome left ) heap-refusals ! save heap-refusals @ 0 heap-refusals ! ;
: load-at ( k -- outcome left )
  20000000 ck-start heap-refusals ! snap-file -1 ck-snapshot-load
  heap-refusals @ 0 heap-refusals ! ck-release ;
\ The allocations a first run of xt ( k -- outcome left ) makes, and
\ whether each refused in turn gives full (ok when a later run, its
\ arrays grown by the first, no longer makes that allocation).
: made ( xt -- n ) max-n swap execute nip max-n swap - ;
: full-at? ( k xt -- flag ) execute 0= if outcome-full = else outcome-ok = then ;
: all-full? ( xt -- flag ) true over made 1+ 1 ?do i 2 pick full-at? and loop nip ;
T{ ' save-at made 0> ' save-at all-full? save -> true true outcome-ok }T
ck-release
: kept? ( outcome -- flag ) dup outcome-full = swap outcome-ok = or ;
: load-kept? ( -- flag )
  true ['] load-at made 1+ 1 ?do i load-at drop kept? and loop ;
T{ ' load-at made 0> load-kept? 1 load-at 0 load-at -> true true outcome-full 0 outcome-ok 0 }T
T{ depth -> 0 }T
snap-file delete-file drop
failures @ 0= [if] ." The lookup lists, I2 and the snapshot round trip hold." cr [then]
bye
