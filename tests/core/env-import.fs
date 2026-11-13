\ Tests of the import pass and of layers at the Forth level (plan task
\ 6.2.5, step SN4; kernel/env-import.fs, kernel/env-layers.fs,
\ kernel/environment.fs lf-env-replay). Built with the I2 assertion
\ (lf-env-i2-checks, defined before loading):
\ - lf-env-replay asks nothing for a key no import replays: names beyond
\   the input, another module's test;
\ - the dependent fixture (tests/cli/dependent.ndjson) checked against a
\   snapshot of its base (inductive.ndjson): the base's six declarations
\   taken, every outcome and fuel as its fresh check's, and no check (the
\   taken slots' publications included) reads a slot that no recorded
\   query answered (lf-i2-misses 0);
\ - the same against the base and the dependent export's layer: all
\   taken, the same outcomes;
\ - dep-sort sorts little-endian slot numbers;
\ - a taken slot whose saved lookups cannot all be asked again is
\   published invalid, never with the saved outcome (review FRK F3);
\ - out of room while a layer is entered is full, never invalid (review
\   FRI F1; heap refusals from tests/support/heap-watch.fs, loaded first).
\ The command line's tests (tests/cli/test_leanforth.py, Imports and
\ Layers) cover both ways on every fixture, the refusals and the planted
\ faults. Test-only.

include ../support/scratch.fs
include ../support/heap-watch.fs
create lf-env-i2-checks   \ compiles the I2 assertion into environment.fs
require ../../src/main.fs
include ../support/tester.fs
decimal

s" leanforth-env-import-base.lfsnap" scratch-file 2constant base-file
s" leanforth-env-import-layer.lfsnap" scratch-file 2constant layer-file
: dependent ( -- c-addr u ) s" tests/cli/dependent.ndjson" ;
variable failures  0 failures !
: must ( flag c-addr u -- ) rot if 2drop else ." failed: " type cr 1 failures +! then ;

\ Keys no import replays.
T{ lf-look-outside lf-env-replay -> false }T
T{ 5 lf-look-other lf-look-key lf-env-replay -> false }T


\ ---- The carry pass's helpers (plan steps 6.2.5c3-c5), and its run with
\ two workers (step c4), made here first: workers are made only in a
\ context whose stores no run used before (cli/check-run.fs
\ ck-workers-made). The snapshot of nested.ndjson of this build's
\ version (tests/snapshots/v<this>/), judged as if a step after it
\ reached the definitions (pretend): what looks one up is carried, judged
\ before it is handed out (env-schedule.fs lf-sched-pre!). Compared below
\ with the fresh check and the serial run.
variable pretended
: pretend ( k -- bits ) drop pretended @ ;
\ forging: every definition's saved axiom set made another (step c4's test).
variable forging  false forging !
: forge-defs ( -- )
  ck-import imp-sn@ 0 ?do
    i ck-import d-kind kind-def = if lf-allowlist-bits sl-axioms i ck-snap snap-slot fld! then
  loop ;
: carry-tier ( -- outcome )
  true ck-snap snap-carry ! ck-snap-tier forging @ if forge-defs then
  ['] pretend ck-import imp-steps ! lf-verdict-version 1+ ck-import imp-top ! ;
: carry-phase ( c-addr u -- outcome )
  ck-phase-begin -1 ['] carry-tier ck-snap-opened ck-snap-fails
  ck-staging ck-phase-end ck-staging ck-fail ;
: carry-alone ( c-addr u -- outcome )
  2dup ck-snap-named ck-jobs ck-state ck-jobs-kept ! 0 ck-state ck-jobs-asked !
  carry-phase dup ok? 0= if exit then drop ck-filling ck-stage-facts
  ck-feed-phase dup ok? if ck-input-facts ck-snap-slots then dup ck-state ck-loaded ! ;
create par-out 512 cells allot  create par-fuel 512 cells allot
create par-taken 512 cells allot  variable par-launched  variable par-n
: par-keep ( -- )
  lf-input-count dup par-n ! 0 ?do
    i lf-env-outcome par-out i cells + ! i ck-fuel-of par-fuel i cells + !
    i ck-taken? par-taken i cells + !
  loop ;
create this-path 64 allot  variable this-len
: this+ ( c-addr u -- ) tuck this-path this-len @ + swap move this-len +! ;
: this-nested ( -- c-addr u )
  0 this-len ! s" tests/snapshots/v" this+ lf-verdict-version 0 <# #s #> this+
  s" /nested.lfsnap" this+ this-path this-len @ ;
reach-kind-definition pretended ! 20000000 ck-start 2 ck-jobs! 0 0 ck-layers!
this-nested carry-alone ok? s" parallel load" must ck-check ck-outcome ok? s" parallel run" must
par-keep lf-sched-launched par-launched ! ck-release

\ The fresh check's outcomes and fuel, then the same export's through the
\ base's snapshot.
create fresh-outcomes 64 cells allot
create fresh-fuel 64 cells allot
: keep-fresh ( -- )
  lf-input-count 0 ?do
    i lf-env-outcome fresh-outcomes i cells + ! i ck-fuel-of fresh-fuel i cells + !
  loop ;
: same-as-fresh? ( -- flag )
  true lf-input-count 0 ?do
    i lf-env-outcome fresh-outcomes i cells + @ = and
    i ck-fuel-of fresh-fuel i cells + @ = and
  loop ;
: taken# ( -- n ) 0 lf-input-count 0 ?do i lf-env-origin lf-origin-saved = - loop ;

20000000 ck-start s" tests/cli/inductive.ndjson" true ck-load ok? s" base load" must ck-check
base-file s" {}" ck-snapshot-save ok? s" base save" must ck-release
20000000 ck-start dependent true ck-load ok? s" fresh load" must ck-check
ck-verdicts? s" fresh verdicts" must keep-fresh lf-input-count 13 = s" thirteen" must
ck-release

20000000 ck-start 0 0 ck-layers! base-file -1 ck-snapshot-import ok? s" import" must
0 lf-i2-misses ! dependent true ck-load ok? s" import load" must ck-check
T{ ck-outcome ck-taken# taken# ck-other# -> outcome-ok 6 6 0 }T
T{ ck-verdicts? same-as-fresh? lf-i2-misses @ -> true true 0 }T
layer-file s" {}" ck-snapshot-save ok? s" layer save" must ck-release

\ Base and layer: everything taken, as fresh.
create layers 2 cells allot  layer-file layers 2!
20000000 ck-start layers 1 ck-layers! base-file -1 ck-snapshot-import ok? s" layered" must
dependent true ck-load ok? s" layered load" must ck-check
T{ ck-outcome ck-taken# ck-layers# -> outcome-ok 13 1 }T
T{ ck-verdicts? same-as-fresh? -> true true }T
ck-release

\ A taken slot whose saved lookups cannot all be asked again (review FRK
\ F3): imp-fill publishes it invalid and take refuses it, never with the
\ saved outcome. The base's first slot, its first saved lookup's key
\ forged to one no import replays (lf-env-replay false), then taken by
\ hand in the environment the import pass would run in.
: first-look ( -- addr ) ss-looks ck-snap snap-block 0 start@ nip 8 * + ;
20000000 ck-start 0 0 ck-layers! base-file -1 ck-snapshot-import ok? s" forge import" must
dependent true ck-load ok? s" forge load" must ck-facts drop ck-env drop
T{ first-look u32-le@ lf-env-replay -> true }T
lf-look-outside first-look u32-le!
: published ( d -- outcome ) lf-env lf-env-slot lf-slot-outcome @ ;
T{ 0 0 ck-import take 0 published -> outcome-invalid outcome-invalid }T
ck-release

\ Sorting slot numbers.
create nums 16 allot
: num! ( u k -- ) 4 * nums + u32-le! ;
: num@ ( k -- u ) 4 * nums + u32-le@ ;
9 0 num! 3 1 num! 7 2 num! 1 3 num!
nums 4 dep-sort
T{ 0 num@ 1 num@ 2 num@ 3 num@ -> 1 3 7 9 }T
nums 0 dep-sort

\ ---- Out of room while a layer is entered (review FRI F1): the layer of
\ inductive.ndjson (two blocks with their recursors, constants with
\ universe arguments) written over a snapshot of identity.ndjson. Every
\ heap allocation the layered import makes, refused in turn, gives full;
\ and with the stage's tuples trimmed and their next growth refused, a
\ constant's universe arguments, a recursor's rules, the expressions and
\ the recursor's declaration are full (they were invalid).
s" leanforth-env-import-base2.lfsnap" scratch-file 2constant base2-file
s" leanforth-env-import-layer2.lfsnap" scratch-file 2constant layer2-file
20000000 ck-start s" tests/reference/identity.ndjson" true ck-load ok? s" base2 load" must
ck-check base2-file s" {}" ck-snapshot-save ok? s" base2 save" must ck-release
20000000 ck-start 0 0 ck-layers! base2-file -1 ck-snapshot-import ok? s" import2" must
s" tests/cli/inductive.ndjson" true ck-load ok? s" import2 load" must ck-check
T{ ck-outcome ck-taken# -> outcome-ok 0 }T
layer2-file s" {}" ck-snapshot-save ok? s" layer2 save" must ck-release
create layers2 2 cells allot  layer2-file layers2 2!
: layered2 ( -- outcome ) 20000000 ck-start layers2 1 ck-layers! base2-file -1 ck-snapshot-import ;
T{ layered2 ck-release -> outcome-ok }T
\ The allocations a layered import makes (a refusal never reached), and
\ the k-th refused: its outcome, and whether the refusal was reached.
: allocations ( -- n )
  max-n heap-refusals ! layered2 drop max-n heap-refusals @ - 0 heap-refusals ! ck-release ;
: refusing ( k -- outcome reached? )
  heap-refusals ! layered2 heap-refusals @ 0= 0 heap-refusals ! ck-release ;
: all-full? ( -- flag )
  true allocations 1+ 1 ?do i refusing swap outcome-full = and and loop ;
T{ allocations 50 > all-full? -> true true }T
\ The base and the layer's sections read by hand, as ck-snapshot-import
\ and env-layers.fs lay-open and ly-load do, up to the expressions.
: ly ( -- ly ) ck-lay lay-ly ;
: base2-read ( -- )
  20000000 ck-start base2-file -1 ck-snap snap-open drop ck-snap-read drop ck-firsts!
  ck-stage-slots ck-snap snap-read drop ;
: layer2-open ( -- )
  ck-stage ck-snap ck-snap snap-n @ ck-stage stage-tier tier-names cons-numbers ck-firsts
  ck-lay lay-init layer2-file ck-snap snap-fuel ck-lay lay-base @ snap-sum
  ck-lay lay-firsts @ ck-lay lay-snap snap-layer-open drop
  ck-lay lay-snap snap-tf tf-start drop ck-lay lay-ly-start ly ly-sections drop ;
: ly-early ( -- )
  lp-names ly ly-family drop lp-levels ly ly-family drop
  lp-texts ly ly-family drop ly ly-starts drop ;
: layer2-ready ( -- ) base2-read layer2-open ly-early ;
: layer2-done ( -- ) ck-lay lay-free ck-release ;
\ The tuples' slab at its count, its next growth refused.
: tuples-refused ( -- ) ly ly-tier tier-tuples cons-records slab-trim drop 1 heap-refusals ! ;
: own-list? ( t -- flag ) ly ly-base-list? 0= ;
: expr@ ( j -- addr ) lp-exprs ly ly-fam ly-fam-rec ;
: own-const? ( j -- flag )
  expr@ dup ly-head drop tag-const = if quad-b u32@ own-list? else drop false then ;
: first-const ( -- j|-1 )
  lp-exprs ly ly-units 0 ?do i own-const? if i unloop exit then loop -1 ;
: const-operands ( j -- a b ) expr@ dup quad-a u32@ swap quad-b u32@ ;
: recursor ( -- i|-1 )
  ly ly-decls# 0 ?do i ly ly-decl ly-kind kind-recursor = if i unloop exit then loop -1 ;
: rules-of ( i -- t ) ly ly-decl staged-more u32@ 5 swap ly ly-at drop ;
layer2-ready
T{ first-const 0< recursor 0< -> false false }T
T{ first-const const-operands tuples-refused ly ly-const nip nip -> outcome-full }T
T{ first-const const-operands ly ly-const nip nip -> outcome-ok }T
T{ ly ly-exprs -> outcome-ok }T
T{ recursor rules-of own-list? -> true }T
T{ recursor rules-of tuples-refused ly ly-rules -> -1 outcome-full }T
T{ recursor rules-of ly ly-rules nip -> outcome-ok }T
T{ recursor ly ly-decl tuples-refused ly ly-xlate-decl -> outcome-full }T
layer2-done
layer2-ready
T{ tuples-refused ly ly-exprs -> outcome-full }T
layer2-done

\ ---- Forged layers (review FRI B1, test gaps class 2): the layer's
\ sections read, one record changed in memory, then its records (or its
\ declarations) entered: each refusal is invalid and names the section
\ and the record (ly-why, ly-where); freed and read again, the same layer
\ enters (class 6).
: layer2-raw ( -- ) base2-read layer2-open ;
: rec ( j i -- addr ) ly ly-fam ly-fam-rec ;
: first-of ( i -- u ) ly ly-fam ly-fam-first @ ;
: lists ( -- addr ) ly ly-lists ly-fam-block @ ;
: why? ( c-addr u -- flag ) ly ly-why @ count compare 0= ;
: refused-at ( -- j ) ly ly-where @ ;
: forge! ( tag payload addr -- ) >r pack-head r> quad-head u32! ;
\ The first own record of family i with tag, -1 for none.
: first-tagged ( tag i -- j|-1 )
  dup ly ly-units 0 ?do
    2dup i swap rec ly-head drop = if 2drop i unloop exit then
  loop 2drop -1 ;
: records ( -- outcome ) ly ly-records ;
: refused? ( outcome c-addr u j -- flag ) refused-at = >r why? r> and swap outcome-invalid = and ;
: str-name ( -- j ) tag-name-str lp-names first-tagged ;
: an-app ( -- j ) tag-app lp-exprs first-tagged ;
\ A constant's head forged, its number kept (its tag may change).
variable forged
: forge-head ( tag payload -- ) first-const dup forged ! lp-exprs rec forge! ;
layer2-raw
T{ str-name 0< an-app 0< first-const 0< recursor 0< -> false false false false }T
layer2-done
\ The translators themselves: a payload only a named record may have; a
\ rule's items by position (a name, a number, an expression); a letE's
\ body record must follow it (here a constant is followed by none).
layer2-ready
T{ tag-const 1 ly ly-payload tag-app 0 ly ly-payload
  -> tag-const 1 outcome-invalid tag-app 0 outcome-ok }T
T{ 99999999 0 ly ly-rule-item nip 99999999 1 ly ly-rule-item 99999999 2 ly ly-rule-item nip
  -> outcome-invalid 99999999 outcome-ok outcome-invalid }T
T{ first-const lp-exprs ly ly-fam ly-fam-body nip -> outcome-invalid }T
layer2-done
\ A name's bytes past the pool's end, or in the base's bytes.
layer2-raw  99999999 str-name lp-names rec quad-b u32!
T{ records s" names" str-name refused? -> true }T
layer2-done
layer2-raw  0 str-name lp-names rec quad-b u32!
T{ records s" names" str-name refused? -> true }T
layer2-done
layer2-raw  lp-name-bytes first-of 1- str-name lp-names rec quad-b u32!
tag-name-str 1 str-name lp-names rec forge!
T{ records s" names" str-name refused? -> true }T
layer2-done
\ A list whose length runs past the section.
layer2-raw  99999 lists u32!
T{ records s" lists" 0 refused? -> true }T
layer2-done
\ A constant whose universe arguments name an item of a list, not its start.
layer2-raw  first-const lp-exprs rec quad-b dup u32@ 1+ swap u32!
T{ records s" expressions" first-const refused? -> true }T
layer2-done
\ A let without its body record after it.
layer2-raw  tag-let 0 forge-head
T{ records s" expressions" forged @ refused? -> true }T
layer2-done
\ An application that refers to itself, or to a later own expression.
layer2-raw  an-app lp-exprs first-of + an-app lp-exprs rec quad-a u32!
T{ records s" expressions" an-app refused? -> true }T
layer2-done
layer2-raw  an-app 1+ lp-exprs first-of + an-app lp-exprs rec quad-a u32!
T{ records s" expressions" an-app refused? -> true }T
layer2-done
\ A constant with a payload, and a record of no kind (a free variable,
\ which no export holds, and tag 31).
layer2-raw  tag-const 1 forge-head
T{ records s" expressions" forged @ refused? -> true }T
layer2-done
layer2-raw  tag-fvar 0 forge-head
T{ records s" expressions" forged @ refused? -> true }T
layer2-done
layer2-raw  31 0 forge-head
T{ records s" expressions" forged @ refused? -> true }T
layer2-done
\ A declaration of no kind, its records entered.
layer2-raw
T{ records -> outcome-ok }T
recursor forged !  30 0 pack-head forged @ ly ly-decl staged-head u32!
T{ ly ly-decls s" declarations" forged @ refused? -> true }T
layer2-done
\ The same layer, unforged, enters whole after all of these (class 6).
layer2-raw
T{ records ly ly-decls ly ly-where @ -> outcome-ok outcome-ok 0 }T
layer2-done
\ A layer holding an opaque declaration (review of refactor-fri L2): its
\ data, the names of its block, translated as a definition's.
s" leanforth-env-import-layer3.lfsnap" scratch-file 2constant layer3-file
: opaque-export ( -- c-addr u ) s" tests/core/check-block-cases/opaque.accepted.ndjson" ;
20000000 ck-start 0 0 ck-layers! base2-file -1 ck-snapshot-import ok? s" import3" must
opaque-export false ck-load ok? s" import3 load" must ck-check
layer3-file s" {}" ck-snapshot-save ok? s" layer3 save" must ck-release
create layers3 2 cells allot  layer3-file layers3 2!
: layered3 ( -- outcome ) 20000000 ck-start layers3 1 ck-layers! base2-file -1 ck-snapshot-import ;
T{ layered3 ck-release -> outcome-ok }T
layer3-file delete-file drop
T{ heap-refusals @ -> 0 }T
T{ depth -> 0 }T
base2-file delete-file drop  layer2-file delete-file drop

base-file delete-file drop  layer-file delete-file drop

\ ---- The carry pass (plan step 6.2.5c3; env-import.fs "The carry
\ pass"). The reach bits of a kind, by the export's kind numbers.
T{ kind-axiom kind-reach kind-def kind-reach kind-thm kind-reach kind-opaque kind-reach
   -> reach-kind-axiom reach-kind-definition reach-kind-theorem reach-kind-opaque }T
T{ kind-quot kind-reach kind-type kind-reach kind-ctor kind-reach -> reach-kind-quotient 0 0 }T
T{ kind-type kind-holds kind-recursor kind-holds kind-inductive kind-holds
   -> reach-block-any reach-block-any reach-block-any }T
T{ kind-def kind-holds kind-quot kind-holds -> 0 reach-quotient }T
T{ 8 lf-look-quot lf-look-key key-holds 8 lf-look-find lf-look-key key-holds -> reach-quotient 0 }T
T{ 3 outcome-ok lf-look-answer holder-holds 3 outcome-ok lf-look-answer lf-look-holder or
   holder-holds -> 0 reach-block-any }T
\ A snapshot of this build judged as if a step 10 after its version
\ reached what pretend gives (imp-top, imp-steps set by hand; no entry of
\ the window reaches less than everything yet): nested.ndjson against
\ its own snapshot. Every outcome and fuel is the fresh check's, I2 holds,
\ and the counts are as the pretended reach says.
s" leanforth-env-import-nested.lfsnap" scratch-file 2constant nested-snap
: nested-file ( -- c-addr u ) s" tests/cli/nested.ndjson" ;
create fresh-out 512 cells allot  create fresh-fuel2 512 cells allot
: keep-fresh2 ( -- )
  lf-input-count 512 > abort" env-import: too many declarations"
  lf-input-count 0 ?do
    i lf-env-outcome fresh-out i cells + ! i ck-fuel-of fresh-fuel2 i cells + !
  loop ;
: same-as-fresh2? ( -- flag )
  true lf-input-count 0 ?do
    i lf-env-outcome fresh-out i cells + @ = and i ck-fuel-of fresh-fuel2 i cells + @ = and
  loop ;
20000000 ck-start nested-file true ck-load ok? s" nested load" must ck-check
ck-verdicts? s" nested verdicts" must keep-fresh2
nested-snap s" {}" ck-snapshot-save ok? s" nested save" must ck-release
: carried-run ( bits -- )
  pretended ! 20000000 ck-start 0 0 ck-layers! nested-snap -1 ck-snapshot-import ok?
  s" carry import" must 9 ck-import imp-carry! ['] pretend ck-import imp-steps !
  lf-verdict-version 1+ ck-import imp-top ! 0 lf-i2-misses ! nested-file true ck-load ok?
  s" carry load" must ck-check ;
: why# ( why -- n ) 0 lf-input-count 0 ?do over i ck-import imp-reason = - loop nip ;
: reach10 ( -- why ) lf-verdict-version 1+ why-steps * why-reach + ;
: whys# ( -- n ) reach10 why# why-answers why# + why-outcome why# + ;
\ The pretended step reaches nested blocks only: those and what looks
\ them up are in its reach (35 of 107), the rest carried.
reach-block-nested carried-run
T{ ck-outcome ck-verdicts? same-as-fresh2? lf-i2-misses @ -> outcome-ok true true 0 }T
T{ ck-taken# reach10 why# why-answers why# why-outcome why# -> 72 35 0 0 }T
\ The labels of a carry run, the snapshot marked older by hand
\ (snap-carry): a carried result names the version it comes from, one
\ checked again says why (text); in JSON a carried result is the
\ snapshot's, never stale, also when the rest is (snap-stale).
: first-taken ( flag -- d ) lf-input-count 0 ?do i ck-taken? over = if drop i unloop exit then
  loop drop -1 ;
true ck-snap snap-carry !
[defined] >string-execute [if]
: says? ( d c-addr u -- flag ) rot ['] cli-verdict. >string-execute 2swap search nip nip ;
T{ true first-taken s" (from snapshot of verdict version 9, carried: this build's changes"
   says? -> true }T
T{ false first-taken s" (checked in this run: inside the reach of verdict version 10's change"
   says? -> true }T
[then]
T{ true first-taken cj-from s" snapshot" compare -> 0 }T
true ck-snap snap-stale !
T{ true first-taken cj-from s" snapshot" compare false first-taken ck-carried? -> 0 false }T
ck-release
\ It reaches everything: nothing carried; nothing: all carried.
reach-all carried-run
T{ ck-outcome same-as-fresh2? ck-taken# reach10 why# lf-input-count =
   -> outcome-ok true 0 true }T
ck-release
0 carried-run
T{ ck-outcome same-as-fresh2? ck-taken# lf-input-count = whys# -> outcome-ok true true 0 }T
ck-release
\ Definitions only: what looks one up is checked again for its answers.
reach-kind-definition carried-run
T{ ck-outcome same-as-fresh2? lf-i2-misses @ -> outcome-ok true 0 }T
T{ ck-taken# 0> reach10 why# 0> why-answers why# 0> -> true true true }T
T{ ck-taken# whys# + lf-input-count = -> true }T
ck-release
\ ---- A snapshot alone of a pretended older version (plan steps 6.2.5c3
\ and c5), loaded as ck-snapshot-load loads one, its record marked older
\ by hand (snap-carry) before its tier is read: nested.ndjson's results
\ carried outside the pretended reach (nested blocks), the rest checked,
\ every outcome and fuel as fresh; then written again as a base of this
\ build's versions, each carried slot marked taken (provenance 2), each
\ checked one not; that base loads as this build's, every outcome and fuel
\ as fresh.
s" leanforth-env-import-upgraded.lfsnap" scratch-file 2constant upgraded
create carried-flags 512 cells allot
: keep-carried ( -- ) lf-input-count 0 ?do i ck-taken? carried-flags i cells + ! loop ;
: taken-mark? ( d -- flag ) sl-provenance swap saved prov-taken and 0<> ;
: marks-kept? ( -- flag )
  true lf-input-count 0 ?do i taken-mark? carried-flags i cells + @ = and loop ;
reach-block-nested pretended ! 20000000 ck-start 0 0 ck-layers!
T{ nested-snap carry-alone -> outcome-ok }T
T{ ck-carrying? ck-check-word ' lf-check-declaration = -> true true }T
ck-check
T{ ck-outcome ck-verdicts? same-as-fresh2? ck-carried# reach10 why# -> outcome-ok true true 72 35 }T
keep-carried
T{ upgraded s" {}" ck-snapshot-save -> outcome-ok }T
ck-release
20000000 ck-start upgraded -1 ck-snapshot-load ok? s" upgraded load" must ck-check
T{ ck-outcome ck-carrying? same-as-fresh2? marks-kept? -> outcome-ok false true true }T
ck-release  upgraded delete-file drop
\ With --snapshot-stale-ok the rest is shown stale (published from the
\ snapshot, snap-fill), and nothing is written.
true snap-stale-allowed ! 20000000 ck-start 0 0 ck-layers!
T{ nested-snap carry-alone ck-check-word ' snap-fill = -> outcome-ok true }T
ck-check
T{ ck-outcome ck-carried# ck-stale? -> outcome-ok 72 true }T
T{ upgraded s" {}" ck-snapshot-save upgraded r/o open-file nip 0<> -> outcome-invalid true }T
false snap-stale-allowed ! ck-release
\ Without an input read (no import pass: released), no reason is kept.
T{ 0 ck-import imp-reason -> 0 }T
\ ---- I3 and the decision on readiness (plan step 6.2.5c4): definitions
\ pretended in reach are checked again and answer as their saved slots
\ (this build gives the same fields), so what looks one up is carried,
\ judged on its turn: serially, and with two workers the same set before
\ handing out (env-schedule.fs lf-sched-pre!). With every definition's
\ saved axiom set forged, a definition checked again answers otherwise,
\ and its users are checked again (why-answers).
create taken-serial 512 cells allot
: keep-taken ( -- ) lf-input-count 0 ?do i ck-taken? taken-serial i cells + ! loop ;
: taken-same? ( -- flag )
  true lf-input-count 0 ?do taken-serial i cells + @ i ck-taken? = and loop ;
: definitions-run ( jobs -- )
  reach-kind-definition pretended ! 20000000 ck-start ck-jobs! 0 0 ck-layers!
  nested-snap carry-alone ok? s" definitions load" must 0 lf-i2-misses ! ck-check ;
1 definitions-run
T{ ck-outcome same-as-fresh2? lf-i2-misses @ why-answers why# reach10 why# 0>
   -> outcome-ok true 0 0 true }T
T{ ck-carried# reach10 why# + lf-input-count = -> true }T
keep-taken ck-release
\ The parallel run, made first in this file (see its top), against the
\ fresh check and the serial run: the same outcomes, fuel and set carried.
: at ( i addr -- x ) swap cells + @ ;
: par-same-at? ( i -- flag )
  dup par-out at over fresh-out at = over par-fuel at 2 pick fresh-fuel2 at = and
  swap dup par-taken at swap taken-serial at = and ;
: par-same? ( -- flag ) true par-n @ 0 ?do i par-same-at? and loop ;
T{ par-launched @ 0> par-n @ 107 = par-same? -> true true true }T
true forging ! 1 definitions-run
T{ ck-outcome same-as-fresh2? why-answers why# 0> -> outcome-ok true true }T
false forging ! ck-release
\ A snapshot written at a fuel limit some checks ran out of: nothing in
\ the pretended reach, still every exhausted result checked again (C2),
\ as a fresh check at that limit gives it.
s" leanforth-env-import-low.lfsnap" scratch-file 2constant low-snap
3000 ck-start nested-file true ck-load ok? s" low load" must ck-check keep-fresh2
low-snap s" {}" ck-snapshot-save ok? s" low save" must ck-release
0 pretended ! 3000 ck-start 0 0 ck-layers! low-snap -1 ck-snapshot-import ok? s" low import" must
9 ck-import imp-carry! ' pretend ck-import imp-steps ! 10 ck-import imp-top !
nested-file true ck-load ok? s" low run" must ck-check
T{ ck-outcome same-as-fresh2? why-outcome why# 0> reach10 why# -> outcome-ok true true 0 }T
ck-release  low-snap delete-file drop
nested-snap delete-file drop
\ A base of an older verdict version is not carried under layers, nor
\ with an export and --snapshot-stale-ok (plan step 6.2.5c7): stale or
\ refused instead (check-run.fs ck-carry-or-stale).
20000000 ck-start
T{ layers 1 ck-layers! ck-uncarried? 0 0 ck-layers! ck-uncarried? -> true false }T
T{ true ck-state ck-importing ! ck-uncarried? true snap-stale-allowed ! ck-uncarried? -> false true }T
false snap-stale-allowed ! ck-release
T{ depth -> 0 }T
T{ failures @ -> 0 }T
failures @ 0= [if] ." The import pass, its I2 build and layers hold." cr [then]
bye
