\ The first checker end to end from lean4export NDJSON files (plan task
\ 2.2.3): the pinned exports of four fixtures (composition, type_identity,
\ poly_identity and the constant fixture, tests/reference/*.ndjson) are
\ read with the checker-input module src/import/checker-input.fs (each also checked
\ against its manifest) and
\ checked by check-declaration through the checked environment: every
\ declaration accepted, with a valid handle and no axioms. Four copies of
\ the composition export changed by hand (tests/core/check-declaration-cases)
\ reach the other outcomes: g applied to value instead of f value
\ (rejected; Lean's appTypeMismatch, row composition.wrong-argument of the
\ expected-results table), the statement assumed as an axiom
\ (unsupported, U1), a natural-number literal as the value (unsupported,
\ U2), a variable without a binder (invalid, V1), and the statement as an
\ unsafe definition (skipped, plan task 5.2.7). A further copy, with
\ a numeric name part of 2^64 (tests/cli/composition-huge-number.ndjson),
\ must stop reading as full.
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/import/checker-input.fs
require ../../src/kernel/check-declaration.fs

: must ( flag -- ) 0= abort" check-declaration-ndjson: refused" ;
100000 constant fuel
variable the-env

\ Read and check a file: the run's outcome; the environment stays current
\ for the queries below, and env-done frees it.
: checked ( c-addr u -- outcome )
  cin-read ok? must fuel 64 lf-check-input swap the-env ! lf-env-view ok? must ;
: env-done ( -- ) the-env @ lf-env-free ok? must ;
\ Declaration d accepted, with a handle valid in the view, and no axioms.
: accepted? ( d -- flag )
  dup lf-env-outcome ok? over lf-env-handle ok? >r lf-env-handle? ok? r> and and
  swap lf-env-axioms ok? swap 0= and and ;
: all-accepted? ( -- flag ) true lf-input-count 0 ?do i accepted? and loop ;
\ The number of declarations and whether all were accepted; then freed.
: verdicts ( -- n flag ) lf-input-count all-accepted? env-done ;
: last-outcome ( -- outcome code step )
  lf-input-count 1- lf-env-outcome lf-diag-code@ lf-check-step@ ;

T{ s" tests/reference/composition.ndjson" checked verdicts -> outcome-ok 1 true }T
T{ s" tests/reference/type-identity.ndjson" checked verdicts -> outcome-ok 1 true }T
T{ s" tests/reference/poly-identity.ndjson" checked verdicts -> outcome-ok 1 true }T
T{ s" tests/reference/constant-fixture.ndjson" checked verdicts -> outcome-ok 3 true }T

\ The changed copies: the run ends ok, the declaration does not.
: case-file ( c-addr u -- outcome code step )
  checked ok? must last-outcome env-done ;
T{ s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" case-file
  -> outcome-rejected lf-diag-argument-apart 7 }T
T{ s" tests/core/check-declaration-cases/composition-postulate.ndjson" case-file
  -> outcome-ok 0 lf-step-done }T
T{ s" tests/core/check-declaration-cases/composition-literal.ndjson" case-file
  -> outcome-unsupported lf-diag-unsupported-form 1 }T
T{ s" tests/core/check-declaration-cases/composition-loose.ndjson" case-file
  -> outcome-invalid lf-diag-out-of-scope 1 }T
\ The statement as an unsafe definition: skipped, as Lean's replay skips
\ it (plan task 5.2.7): rejected unchecked, its slot marked skipped.
: skipped-file ( c-addr u -- outcome code step flag )
  checked ok? must last-outcome lf-input-count 1- lf-env-skipped? env-done ;
T{ s" tests/core/check-declaration-cases/composition-unsafe.ndjson" skipped-file
  -> outcome-rejected lf-diag-skipped 1 true }T

\ The reader fails closed on a file that is not an export.
T{ s" tests/core/check-declaration-ndjson.fs" cin-read ok? -> false }T

\ With the manifest checked: the fixtures read as before; a changed copy
\ without a manifest is refused as invalid, with the manifest's reason,
\ and nothing is loaded; staged without the manifest, it reads.
: sealed? ( -- flag ) lf-input-sealed? ;
\ The reason cin-error gives is c-addr u.
: why? ( c-addr u -- flag ) cin-error 2>r 2drop drop 2r> compare 0= ;
T{ s" tests/reference/composition.ndjson" cin-read-checked sealed? -> outcome-ok true }T
T{ s" tests/reference/constant-fixture.ndjson" cin-read-checked lf-input-count
  -> outcome-ok 3 }T
: case-wrong ( -- c-addr u )
  s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" ;
T{ case-wrong cin-read-checked sealed? -> outcome-invalid false }T
T{ s" manifest missing, unreadable or too large" why? -> true }T
T{ case-wrong cin-read sealed? -> outcome-ok true }T

\ A handler's refusal carries its own reason, and the reader's line: an
\ inductive type (line 51 of the export of every record kind) is
\ unsupported. tests/cli/test_leanforth.py reaches full with a larger file.
: line@ ( -- line ) cin-error 2drop 2drop ;
T{ s" tests/core/reexport/kinds.ndjson" cin-read sealed? line@
  -> outcome-unsupported false 51 }T
T{ s" an inductive type (not supported yet)" why? -> true }T

\ A numeric name part is staged only when it fits a cell, never wrapped
\ into another number (another name): composition with the part 0 of
\ a._@._internal._hyg.0 changed to 2^64 is full, at its line, 12.
T{ s" 0" cin-digits s" 007" cin-digits -> 0 true 7 true }T
: max-text ( -- c-addr u ) max-n 0 <# #s #> ;
T{ max-text cin-digits -> max-n true }T
T{ s" 18446744073709551616" cin-digits s" 99999999999999999999999" cin-digits
  -> false false }T
T{ s" tests/cli/composition-huge-number.ndjson" cin-read
  sealed? line@ -> outcome-full false 12 }T
T{ s" a numeric name part larger than the check holds" why? -> true }T

\ ---------------------------------------------------------------------------
\ The same exports staged in the compact store (src/import/stage.fs) and
\ fed to the checker in file order (src/import/feed.fs, plan task 3.2.2):
\ the names stay in the shared input tier, the stores grow to the feed's
\ capacities, and every verdict is the same as above.
require ../../src/import/feed.fs
create stg /stage allot
create fdd /feed allot
: staged ( c-addr u -- ) 16 stg stage-init ok? must stg stage-load-unchecked ok? must ;
: fed ( c-addr u -- outcome ) staged stg fdd lf-feed ;
: unstage ( -- ) lf-name-detach stg stage-free ;
: fed-checked ( c-addr u -- outcome )
  fed ok? must fuel 64 lf-check-input swap the-env ! lf-env-view ok? must ;
T{ s" tests/reference/composition.ndjson" fed-checked verdicts unstage
   -> outcome-ok 1 true }T
T{ s" tests/reference/type-identity.ndjson" fed-checked verdicts unstage
   -> outcome-ok 1 true }T
T{ s" tests/reference/poly-identity.ndjson" fed-checked verdicts unstage
   -> outcome-ok 1 true }T
T{ s" tests/reference/constant-fixture.ndjson" fed-checked verdicts unstage
   -> outcome-ok 3 true }T
T{ s" tests/reference/identity.ndjson" fed-checked verdicts unstage -> outcome-ok 1 true }T
\ The room left for the checks (review rvKC M1): a let becomes 4 term nodes
\ and a projection 2, but each check still gets the whole feed-term-room
\ above the nodes the feed made. kinds.ndjson has 2 lets and 8 projections.
: term-room ( -- n ) lf-term-capacity lf-term-count @ - ;
T{ s" tests/core/reexport/kinds.ndjson" fed term-room unstage
   -> outcome-ok feed-term-room }T
\ A file without lets or projections never gets less (the expressions may
\ share nodes, so it may get more).
T{ s" tests/reference/composition.ndjson" fed term-room feed-term-room < unstage
   -> outcome-ok false }T
\ The room is a setting of the context (core/input.fs's lf-input-room!,
\ compact-store plan step S5): 0, the default, lets a check's scratch
\ grow up to feed-most; a limit set is the room each check gets.
T{ feed-term-room feed-most = feed-most 1 31 lshift u< -> true true }T
T{ 5000 lf-input-room! s" tests/core/reexport/kinds.ndjson" fed term-room unstage
   0 lf-input-room! -> outcome-ok 5000 }T
: fed-case ( c-addr u -- outcome code step ) fed-checked ok? must last-outcome env-done unstage ;
T{ s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" fed-case
  -> outcome-rejected lf-diag-argument-apart 7 }T
T{ s" tests/core/check-declaration-cases/composition-postulate.ndjson" fed-case
  -> outcome-ok 0 lf-step-done }T
\ The proof "3", a string literal, typed String (plan task 5.2.3): the
\ file declares no String, so pinned Lean 4.35.0's kernel rejects it
\ (unknown constant 'String'), as here; the first importer (case-file
\ above) still stages the literal as an unsupported form.
T{ s" tests/core/check-declaration-cases/composition-literal.ndjson" fed-case drop
  -> outcome-rejected lf-diag-unknown-constant }T
T{ s" tests/core/check-declaration-cases/composition-loose.ndjson" fed-case
  -> outcome-invalid lf-diag-out-of-scope 1 }T
\ A let (plan task 4.2.3), def withLet : Sort 1 := let x : Sort 1 :=
\ Sort 0; x with its nonDep flag set: fed as a let term whose leaf keeps
\ the flag, and accepted.
: let-file ( -- c-addr u ) s" tests/core/check-declaration-cases/let-nondep.ndjson" ;
T{ let-file fed 0 lf-input-decl lf-idecl-value @ dup lf-let? swap lf-let-nondep unstage
  -> outcome-ok true true }T
T{ let-file fed-case -> outcome-ok 0 lf-step-done }T
\ Ordering two universe parameters by name (Lean's is_norm_lt, under
\ level normalisation) reads the names of the input tier under the view:
\ def T.{u,v} : Sort (max v u + 2) := Sort (max u v + 1), which pinned
\ Lean 4.35.0 accepts (row universe.sort-max-swapped of the universe-scope
\ table), is accepted by both paths; with 100 names before u and v their
\ IDs lie beyond the entry store's 64 entries, and the fed check is still
\ accepted (the independent review's finding H1, 2026-11-03).
: swap-max ( -- c-addr u ) s" tests/core/check-declaration-cases/swap-max.ndjson" ;
: swap-max-far ( -- c-addr u ) s" tests/core/check-declaration-cases/swap-max-far.ndjson" ;
T{ swap-max case-file -> outcome-ok 0 lf-step-done }T
T{ swap-max fed-case -> outcome-ok 0 lf-step-done }T
T{ swap-max-far fed-case -> outcome-ok 0 lf-step-done }T
\ The same comparison made directly under the view: max u v and max v u
\ are equivalent, as they are without a view.
: param ( c-addr u -- level ) 0 -rot lf-name-str must lf-level-param must ;
: both-maxes ( -- l1 l2 )
  s" u" param s" v" param 2dup lf-level-max must -rot swap lf-level-max must ;
T{ both-maxes 1000 lf-level-equivalent -> true outcome-ok }T
T{ swap-max-far fed ok? both-maxes 1000 lf-level-equivalent -> true true outcome-ok }T
\ An attach that fails (no heap for the scratch tier: the first
\ allocation refused) leaves no view, frees what it made and resets the
\ names, so the input fed before is no longer intact and nothing of it can
\ be checked as if it were (the review's finding L1).
T{ lf-input-intact? lf-name-viewed? -> true true }T
live-blocks @ constant blocks-viewed
1 heap-refusals !
T{ stg stage-tier lf-name-attach ok? lf-name-viewed? lf-input-intact? -> false false false }T
T{ heap-refusals @ live-blocks @ blocks-viewed < -> 0 true }T
unstage
\ The stores grew past their defaults, and the names are the stage's: a
\ name made under the view that the stage has gets the stage's ID (here
\ from the stage's own text, which is copied first), a new one the next
\ number.
T{ s" tests/reference/composition.ndjson" fed lf-term-capacity lf-term-default >
   lf-input-indexed? -> outcome-ok true true }T
0 lf-input-name constant comp-name
T{ comp-name lf-name-prefix@ comp-name lf-name-text lf-name-str -> comp-name true }T
lf-name-numbers constant fresh-id
T{ 0 s" not.in.the.stage" lf-name-str -> fresh-id true }T
T{ fresh-id lf-name-text s" not.in.the.stage" compare fresh-id 7 lf-name-num nip
   -> 0 true }T
T{ comp-name fresh-id lf-name-equal? comp-name comp-name lf-name-equal? -> false true }T
\ Every name under the view was checked when it was made: its component
\ is well formed in either mode's sense, and the entry store's own audit
\ refuses an ID that is not one of its entries.
T{ comp-name lf-name-part-ok? fresh-id lf-name-part-ok? comp-name lf-name-entry-ok?
   -> true true false }T
unstage
T{ lf-input-indexed? -> false }T
\ A record the checker's stores do not hold is invalid, not full (the
\ review's finding L3): an expression whose tag is changed to a free
\ variable's, and a declaration whose kind is changed to one no reader
\ gives; feed-at names the record where the feed stopped.
: retag ( tag addr -- ) dup u32@ head-tag-mask invert and rot or swap u32! ;
T{ s" tests/reference/composition.ndjson" staged tag-fvar 1 stg stage-tier expr-record
   quad-head retag stg fdd lf-feed fdd feed-at -> outcome-invalid 1 }T
unstage
T{ swap-max staged 31 0 stg staged-at staged-head retag stg fdd lf-feed fdd feed-at
   -> outcome-invalid 0 }T
unstage
\ Only a sealed stage is fed.
T{ 16 stg stage-init stg fdd lf-feed -> outcome-ok outcome-invalid }T
stg stage-free

\ ---------------------------------------------------------------------------
\ The input view (compact-store plan step S5; src/core/terms.fs). By default
\ the feed reads the stage in place: input expression e is term number
\ 2e + 1, read with the checker's tag and fields (binder names and
\ information ignored), its identity the negative number invert 2e + 1,
\ which no birth serial is; term 2e is the lambda of a let or the leaf of
\ a projection e (none here: no term); a Sort, constant or literal has
\ its fields in the view's leaf table; the store's own records (copies of
\ mdata expressions and the nodes above them, then each check's scratch)
\ follow from lf-term-base. composition.ndjson has 21 expressions and no
\ let or projection.
T{ s" tests/reference/composition.ndjson" fed lf-term-viewed? lf-term-base lf-term-count @
   -> outcome-ok true 42 0 }T
T{ 1 lf-term-read 27 lf-term-read 31 lf-term-read
   -> lf-tag-symbolic-sort 0 0 true lf-tag-app 3 25 true lf-tag-lam 7 29 true }T
T{ 1 lf-term-identity 41 lf-term-identity 42 lf-term-valid? 0 lf-input-mark-count
   -> -2 true -42 true false 42 }T
T{ 0 lf-term-valid? 26 lf-term-valid? 1 lf-term-input-unit 41 lf-term-input-unit 2 lf-term-input-unit
   -> false false 0 true 20 true false }T
\ The input's fingerprint covers the view (its count of input nodes).
: view-base ( -- addr ) lf-term-view lf-tview-base ;
T{ lf-input-print lf-input-fingerprint = -> true }T
1 view-base +!
T{ lf-input-print lf-input-fingerprint = -> false }T
-1 view-base +!
\ Making a node equal to an input node gives that node: an application
\ and a bound variable found in the tier's table, a binder in the view's
\ binder table, a Sort in its leaf table; a new node is the store's.
T{ 3 25 lf-term-app 7 29 lf-term-lam 2 lf-term-bvar 0 lf-term-symbolic-sort lf-term-count @
   -> 27 true 31 true 3 true 1 true 0 }T
T{ 27 27 lf-term-app over lf-term-identity nip lf-term-count @
   -> 42 true true 1 }T
T{ 42 lf-term-identity drop 0> lf-input-rollback lf-term-count @ -> true outcome-ok 0 }T
unstage
T{ lf-term-viewed? lf-term-base -> false 0 }T
\ A constant read in place: its reference is the one the feed made, and a
\ constant made over that reference is the input node.
T{ s" tests/reference/constant-fixture.ndjson" fed 15 lf-term-tag@ 15 lf-term-second@
   -> outcome-ok lf-tag-constant 0 }T
T{ 15 lf-cterm-ref lf-cterm-new -> 15 -16 true }T
\ Attached without the feed, a leaf has no fields until it is given them,
\ once; a node that is no input leaf is refused.
T{ stg stage-tier lf-term-attach 15 lf-term-valid? 27 lf-term-valid? -> outcome-ok false true }T
T{ 5 0 1 15 lf-term-input-leaf 15 lf-term-read -> outcome-ok lf-tag-constant 5 0 true }T
T{ 5 0 1 15 lf-term-input-leaf 0 0 1 27 lf-term-input-leaf 0 0 1 9999 lf-term-input-leaf
   0 0 1 14 lf-term-input-leaf
   -> outcome-invalid outcome-invalid outcome-invalid outcome-invalid }T
T{ lf-term-detach lf-term-viewed? 15 lf-term-valid? -> outcome-ok false false }T
unstage
\ A let read in place (step S5, parts 4-5): withLet's value, expression
\ 3, is term 7, LET(Sort 0, its lambda 6) of the nonDep tag, the lambda
\ fun x : Sort 1 => x of the let's type and the body its second record
\ holds (whose own numbers 8 and 9 are no terms); its data word has the
\ lambda's range. Made again, the let, the lambda and an application of
\ input records are those input nodes.
T{ let-file fed 7 lf-term-read 6 lf-term-read 8 lf-term-valid? 9 lf-term-valid?
   -> outcome-ok lf-tag-let-nondep 3 6 true lf-tag-lam 1 5 true false false }T
T{ 6 lf-term-data@ drop lf-data-loose 7 lf-term-data@ drop lf-data-loose -> 0 0 }T
T{ 1 5 lf-term-lam 3 6 lf-tag-let-nondep lf-term-binary 3 6 lf-tag-let lf-term-binary
   lf-term-count @ -> 6 true 7 true 10 true 1 }T
unstage
\ A projection read in place: the record is PROJECTION(its leaf, its
\ structure term), the leaf the even number just below it, of field 0;
\ made again of that leaf and term it is the input node; a new leaf is a
\ store node, a projection of it too.
: proj-file ( -- c-addr u ) s" tests/core/check-block-cases/proj.data.ndjson" ;
: first-proj ( -- node )
  -1 lf-term-base 0 ?do i lf-term-valid? if i lf-term-tag@ lf-tag-projection =
    if drop i leave then then loop ;
: proj-parts ( node -- leaf e ) dup lf-proj-leaf swap lf-proj-struct ;
T{ proj-file fed first-proj 1 and first-proj lf-proj-leaf 1+ first-proj =
   -> outcome-ok 1 true }T
T{ first-proj proj-parts drop dup lf-term-tag@ swap lf-term-second@ -> lf-tag-proj 0 }T
T{ first-proj proj-parts lf-tag-projection lf-term-binary -> first-proj true }T
T{ first-proj lf-proj-struct 0 0 lf-proj-of ok? swap lf-term-base >= -> true true }T
unstage
\ The switch: copied, as before the view, no input node; a binder hook
\ (the print command's) copies too.
T{ true lf-feed-copy! s" tests/reference/composition.ndjson" fed lf-term-viewed?
   lf-term-count @ 21 >= -> outcome-ok false true }T
unstage false lf-feed-copy!
:noname ( term name kind -- ) 2drop drop ; constant no-binders
T{ s" tests/reference/composition.ndjson" staged stg fdd no-binders 0 lf-feed-hooked
   lf-term-viewed? -> outcome-ok false }T
unstage
\ The fields the feed gives an input literal (core/literals.fs,
\ core/string-literals.fs): no node made, the limbs or bytes kept in the
\ context's slab; text that is no number, or no UTF-8, is refused.
: one-limb ( first n -- n limb ) swap lf-lit-limbs slab-at @ ;
T{ s" 12" lf-lit-decimal -rot one-limb -> true 1 12 }T
T{ s" 0" lf-lit-decimal s" 1x" lf-lit-decimal -> 0 0 true false }T
create bad-utf8 255 c,
T{ bad-utf8 1 lf-str-fields nip nip s" ab" lf-str-fields rot drop
   -> outcome-invalid 2 outcome-ok }T
\ A let's lambda and the input lambda of the same type and body that
\ comes later in the file: one node when copied, and since step S5's
\ parts 4-5 two input nodes in place (the let's lambda is read in place
\ from the let's records), equal under Lean's ==: def withLet : Sort 1 :=
\ let x : Sort 1 := Sort 0; x, then def idSort : Sort 1 -> Sort 1 :=
\ fun x : Sort 1 => x. A lambda made equal to both is the first entered,
\ the let's.
: let-lam-file ( -- c-addr u ) s" tests/core/check-declaration-cases/let-lambda.ndjson" ;
: lams ( -- let-lam input-lam )
  0 lf-input-decl lf-idecl-value @ lf-let-binder 1 lf-input-decl lf-idecl-value @ ;
T{ let-lam-file fed lams 2dup = -rot 1000 lf-expr-equal ok? -> outcome-ok false true true }T
T{ lams drop dup lf-term-first@ swap lf-term-second@ lf-term-lam swap lams drop = -> true true }T
unstage
T{ true lf-feed-copy! let-lam-file fed lams = unstage false lf-feed-copy! -> outcome-ok true }T
T{ let-lam-file fed-checked verdicts unstage -> outcome-ok 2 true }T
\ An mdata expression and every node above it are copied, the rest read
\ in place: in stage-cases/marks.ndjson an mdata, an application and a
\ lambda over it, a let whose body it is and a projection of it (theorem
\ t's value): five expressions, seven store nodes (the let's lambda and
\ the projection's leaf besides).
T{ s" tests/core/stage-cases/marks.ndjson" fed lf-input-count 1- lf-input-decl lf-idecl-value @
   dup lf-term-base >= swap lf-term-tag@ lf-term-count @ -> outcome-ok true lf-tag-projection 7 }T
unstage
\ A let and the nodes above it are read in place, nothing copied.
T{ let-file fed 0 lf-input-decl lf-idecl-value @ lf-term-base < lf-term-count @
   -> outcome-ok true 0 }T
unstage

\ ADR 0012 E5 against the name-to-declaration array (ADR 0016 C4): with
\ names interned in the input tier, the environment reads a name's chain;
\ for every name, every limit and each slot test the chain gives what the
\ scan of every earlier declaration gives.
variable e5-name  variable e5-test  variable e5-limit
: e5-args ( -- name test limit ) e5-name @ e5-test @ e5-limit @ ;
: e5-same? ( -- flag )
  e5-args lf-env-chain-first e5-args lf-env-scan-first =
  e5-args lf-env-chain-matches e5-args lf-env-scan-matches = and ;
create e5-tests
  ' lf-slot-accepted? , ' lf-slot-undecided? , ' lf-slot-unsupported? , ' lf-slot-open? ,
  ' lf-slot-final? ,
here e5-tests - 1 cells / constant e5-tests#
variable e5-checks
: e5-tested? ( -- flag )
  true e5-tests# 0 ?do i cells e5-tests + @ e5-test ! e5-same? and 1 e5-checks +! loop ;
: e5-named? ( -- flag )
  true lf-name-numbers 0 ?do i e5-name ! e5-tested? and loop ;
: e5-all? ( -- flag )
  true lf-input-count 1+ 0 ?do i e5-limit ! e5-named? and loop ;
: e5-file ( c-addr u -- flag ) fed-checked ok? must e5-all? env-done unstage ;
T{ s" tests/reference/constant-fixture.ndjson" e5-file -> true }T
T{ s" tests/reference/composition.ndjson" e5-file -> true }T
T{ s" tests/core/check-declaration-cases/composition-postulate.ndjson" e5-file -> true }T
\ The theorem declared twice (a copy of the export with its last line
\ repeated): the second is rejected as already declared (N2), as Lean's
\ kernel does, by both paths; its chain holds both.
: twice ( -- c-addr u ) s" tests/core/check-declaration-cases/composition-twice.ndjson" ;
T{ twice case-file -> outcome-rejected lf-diag-already-declared 2 }T
T{ twice fed-case -> outcome-rejected lf-diag-already-declared 2 }T
T{ twice e5-file -> true }T
T{ e5-checks @ 500 > -> true }T
." E5 chain against scan: " e5-checks @ . ." lookups agree" cr

cases-done
bye
