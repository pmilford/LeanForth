\ The Meta layer's view of the library while a text runs (plan S1,
\ docs/design/S1_INTERFACE.md §1, §2 and §4; src/front/meta-env.fs's run
\ mode, src/front/lib-decode.fs, infer.fs's lf-meta-dec-level, the
\ instance-typed flag and the synthesis hooks), by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. S1's stand-in through the command line and the kernel (§11 row 2):
\    0 + 0 = 0 closed by by-rfl and accepted, 0 + 0 = 1 refused with 97
\    and Lean's text, nothing checked; the run mode left afterwards;
\ 2. every outcome of lf-menv-find and lf-libdec-decl: a library
\    declaration decoded (kind, name, parameters, type, value, hint and
\    height, inductive data of a type with its flags, a constructor and a
\    recursor with its K flag), the same record again (memo), a block
\    (no record), the last library handle and the first text one, a text
\    declaration found (lf-menv-add) with its universe parameters, an
\    unknown or invalid name, a number beyond the library, a kind beyond
\    the four, an expression not supported yet (mdata), imax, a reflexive
\    type, let and have, a big literal (the re-export library); facts without
\    data unsupported; binder kinds of a library and a text declaration;
\    getDecLevel's every case; the instance-typed flag and its rollback;
\    the stage's tier unchanged by decoding (review s1-meta-b M1);
\ 3. stack effects (every T{ }T checks the depth; a cell below a refused
\    find kept, review H1);
\ 4. lf-menv-reset, a new run's reset stores, lfc-library-close and a
\    failed lfc-library-open forget everything; the library's count frozen
\    while it is bound (a text handle keeps its meaning);
\ 5. the heap refusing each allocation of a decode in turn: never ok
\    before the last, full each time with no handle (H2), then decoded;
\    the same find again after each refusal decodes (a stopped walk
\    forgets its nodes under way), and nothing refused stays allocated;
\    a name's parts and its sought parts refused room: full, never
\    "unknown constant" (L1); a text declaration refused room in turn:
\    nothing kept.
include ../support/heap-watch.fs
require ../support/tester.fs
require ../../src/main.fs
decimal

: library ( -- c-addr u ) s" tests/front/whnf-slice.ndjson" ;
: elab-file ( -- c-addr u ) s" tests/front/whnf-slice.elab.ndjson" ;

\ ---- Terms by name.
create us 4 2* cells allot
: u! ( level i -- ) >r dup lf-level-identity drop swap r> 2* cells us + 2! ;
: cst ( c-addr u n -- t )
  >r lfa-intern lf-name-generation @ us r> lf-cref-new 0= abort" ref"
  lf-cterm-new 0= abort" const" drop ;
: app ( f a -- t ) lf-term-app 0= abort" app" ;
: made ( x outcome -- x ) ok? 0= abort" not made" ;
: level1 ( -- level ) 0 lf-level-succ 0= abort" level" ;
: nat ( -- t ) s" Nat" 0 cst ;
: nlit ( u -- t ) lf-hterm-cell 0= abort" lit" drop ;
\ @OfNat.ofNat.{0} Nat n (instOfNatNat n), as Lean elaborates n : Nat.
: num ( u -- t )
  >r 0 0 u! s" OfNat.ofNat" 1 cst nat app r@ nlit app s" instOfNatNat" 0 cst r> nlit app app ;
\ @HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b.
: inst-add ( -- t ) 0 0 u! s" instHAdd" 1 cst nat app s" instAddNat" 0 cst app ;
: plus ( a b -- t )
  >r >r 0 0 u! 0 1 u! 0 2 u! s" HAdd.hAdd" 3 cst nat app nat app nat app inst-add app
  r> app r> app ;
: eq-nat ( a b -- t ) >r >r level1 0 u! s" Eq" 1 cst nat app r> app r> app ;
: zero-add ( u -- type ) >r 0 num 0 num plus r> num eq-nat ;
: s1-true ( -- type ) 0 zero-add ;
: s1-false ( -- type ) 1 zero-add ;
: stating ( xt -- ) is lf-front-by-statement ;
: detail ( -- c-addr u ) 0 lfa-detail slab-at lfa-detail slab-count ;

\ ---- 1. Through the command line and the kernel: the slice's 437
\ declarations and the text's accepted, none NOT PROVED; the wrong twin
\ stops at by-rfl with Lean's text, and the run mode is left (lfc-empty).
: tally ( k -- n ) cli-count-of @ ;
: check ( c-addr u -- code )
  cli-options library cli-state opt-env 2! elab-file cli-state opt-elab 2! cli-check ;
: nm ( c-addr u -- name ) lfa-intern ;
: d-of ( c-addr u -- d ) nm lf-menv-find made ;
\ With the data read (the run mode bound by cli-check), facts and status
\ of a library declaration while the text runs: HAdd.hAdd is a projection
\ function, semireducible (the stand-in asks before it gives the statement).
variable fact  2variable status
: probed ( -- type )
  s" HAdd.hAdd" d-of dup lf-menv-proj-fn? drop fact ! lf-menv-status status 2! s1-true ;
' probed stating
T{ s" tests/front/09-zero-add-rfl.lf" check outcome-ok tally cli-not-proved @ lf-libdec-count
   -> 0 438 0 0 }T
T{ fact @ status 2@ -> true 0 outcome-ok }T
' s1-false stating
T{ s" tests/front/10-zero-add-wrong.lf" check lf-author-code lf-libdec-stage -> 4 97 0 }T
T{ detail s\"   0 + 0\nis not definitionally equal to the right-hand side\n  1\n\n⊢ 0 + 0 = 1"
   compare -> 0 }T

\ ---- 2. The run mode over the slice (lfc-library-open), no data read.
\ The stores given a text run's room (lfc-rooms, as check-lf.fs does).
T{ library true lfc-library-open lfc-rooms -> outcome-ok outcome-ok }T
lf-author-begin
\ The stage's tier as read: decoding adds no name, expression or level to
\ it (checked below, after the decodes and the text's names sought).
: tier# ( -- names exprs levels )
  ck-stage stage-tier >r r@ tier-names cons-numbers r@ tier-exprs cons-numbers
  r> tier-levels cons-numbers ;
tier# constant levels0 constant exprs0 constant names0
: lib? ( d -- flag ) lf-libdec-count u< ;
T{ s" Nat.add" d-of dup lib? swap lf-menv-kind -> true lf-kind-definition }T
T{ s" Nat.add" d-of lf-menv-name s" Nat.add" nm = -> true }T
T{ s" Nat.add" d-of dup lf-menv-type lf-term-tag@ swap lf-menv-value nip -> lf-tag-pi true }T
T{ s" Nat.add" d-of lf-menv-hint drop s" Eq" d-of lf-menv-params nip -> lf-hint-regular 1 }T
T{ s" Eq" d-of lf-menv-params drop @ lf-name-valid? s" Eq" d-of lf-menv-value -> true false }T
T{ s" Eq.refl" d-of dup lf-menv-kind swap lf-menv-data lf-ict-induct lf-more-field s" Eq" nm =
   -> lf-kind-constructor true }T
T{ s" Nat" d-of lf-menv-data lf-ity-ctors@ nip s" Nat.rec" d-of lf-menv-data lf-irc-rules@ nip
   -> 2 2 }T
T{ s" Nat.rec" d-of lf-menv-data lf-irc-rules@ drop lf-irule-ctor s" Nat.zero" nm = -> true }T
\ Decoded facts as the stage holds them: Nat.add's height (regular, 1),
\ Eq.rec a K recursor and Nat.rec none, Nat recursive and Eq not.
T{ s" Nat.add" d-of dup lf-menv-hint nip swap ck-stage staged-hint@ -> 1 1 }T
: k-of ( c-addr u -- flag ) d-of lf-menv-data lf-irc-k lf-more-field ;
T{ s" Eq.rec" k-of s" Nat.rec" k-of -> true false }T
: rec-bit ( c-addr u -- u )
  d-of lf-menv-data lf-ity-flags lf-more-field lf-ity-rec-bit and ;
T{ s" Nat" rec-bit s" Eq" rec-bit -> lf-ity-rec-bit 0 }T
\ A block (the stage's first declaration) has no record; the last
\ library handle reads the library's declaration; binder kinds of a
\ number beyond the library: none, invalid.
T{ 0 ck-stage staged-kind@ 0 lf-libdec-decl -> kind-inductive -1 outcome-invalid }T
: last-d ( -- d ) lf-libdec-count 1- ;
T{ last-d lf-menv-kind last-d lf-libdec-decl drop lf-libdec-dname last-d lf-menv-name =
   -> lf-kind-definition true }T
T{ lf-libdec-count lbd-parts lf-libdec-kinds lbd-parts slab-count -> outcome-invalid 0 }T
\ The same record again: memoized, nothing decoded twice.
: rec-of ( c-addr u -- r n ) d-of lf-libdec-decl drop lbd-records slab-count ;
: alike ( r1 n1 r2 n2 -- f1 f2 ) rot = >r = r> ;
T{ s" Nat.add" rec-of s" Nat.add" rec-of alike -> true true }T
\ Unknown, invalid; a number beyond the library; facts with no data.
T{ s" No.such" nm lf-menv-find -1 lf-menv-find -> -1 outcome-invalid -1 outcome-invalid }T
T{ lf-libdec-count lf-libdec-decl -1 lf-libdec-decl -> -1 outcome-invalid -1 outcome-invalid }T
T{ s" Nat.add" d-of lf-menv-status s" Nat.add" d-of lf-menv-matcher?
   -> -1 outcome-unsupported false outcome-unsupported }T
\ Binder kinds from the tier's tags: HAdd.hAdd {α β γ} [self] (a b).
: kinds ( d -- k0 k3 k4 n ) lf-menv-kinds >r dup @ over 3 cells + @ rot 4 cells + @ r> ;
T{ s" HAdd.hAdd" d-of kinds -> 1 3 0 6 }T

\ ---- 2. A text declaration made visible at its hand-over (lf-menv-add):
\ found before the library, its kind, type and binder kinds as written.
' s1-true stating
T{ s" theorem zz 0 0 + 0 = := by by-sorry end zz" lf-author-begin lf-author-text -> outcome-ok }T
T{ s" zz" d-of dup lib? 0= swap lf-menv-kind -> true lf-kind-theorem }T
T{ s" zz" d-of dup lf-menv-value nip swap lf-menv-kinds nip -> true 0 }T
T{ s" zz" d-of lf-menv-status s" zz" d-of lf-menv-matcher? -> 0 outcome-ok false outcome-ok }T
T{ s" zz" d-of dup lf-menv-name s" zz" nm = swap lf-menv-hint -> true lf-hint-opaque 0 }T
T{ s" zz" d-of dup lf-menv-params nip swap lf-menv-data s" zz" d-of lf-menv-type lf-term-tag@
   -> 0 0 lf-tag-app }T
create fake /lf-fdecl allot
: pi-kinded ( -- t )
  nat nat lf-term-pi 0= abort" pi" dup s" a" nm 1 lf-pres-binder! made
  nat swap lf-term-pi 0= abort" pi" dup s" b" nm 3 lf-pres-binder! made ;
: fake! ( -- )
  fake /lf-fdecl erase lf-decl-def fake lf-fdecl-kind ! s" yy" nm fake lf-fdecl-name !
  pi-kinded fake lf-fdecl-type ! nat fake lf-fdecl-value ! ;
: two-kinds ( d -- k0 k1 n ) lf-menv-kinds >r dup @ swap cell+ @ r> ;
T{ fake! fake lf-menv-add s" yy" d-of two-kinds -> outcome-ok 3 1 2 }T
\ A kind beyond the four is refused, not taken for another.
T{ fake! 4 fake lf-fdecl-kind ! fake lf-menv-add -1 fake lf-fdecl-kind ! fake lf-menv-add
   -> outcome-invalid outcome-invalid }T
\ One with a universe parameter, u: each allocation refused in turn
\ answers full and keeps nothing (uu not found), until it is made.
: uu! ( -- )
  fake! s" uu" nm fake lf-fdecl-name ! 1 fake lf-fdecl-universes !
  s" u" nm fake lf-fdecl-universe ! ;
: uu-at ( k -- outcome ) heap-refusals ! uu! fake lf-menv-add 0 heap-refusals ! ;
: uu-kept? ( outcome -- flag ) ok? s" uu" nm lf-menv-find nip ok? = ;
variable worst
: uu-sound? ( outcome -- flag ) dup uu-kept? swap dup ok? swap outcome-full = or and ;
: uu-note ( outcome -- outcome ) dup uu-sound? 0= if dup worst ! then ;
: uu-refused ( -- k ) 0 begin 1+ dup uu-at uu-note ok? until ;
T{ outcome-ok worst ! uu-refused 1 > worst @ -> true outcome-ok }T
T{ s" uu" d-of lf-menv-params swap @ s" u" nm = -> 1 true }T
\ The tier unchanged by every decode and every name sought above.
T{ tier# -> names0 exprs0 levels0 }T
\ The library's count is the stage's when bound: a stage that grows
\ while bound adds no declaration, and a text handle (0, the first after
\ none) keeps its meaning.
create growing /stage allot
T{ 12 growing stage-init growing lf-menv-library! fake! fake lf-menv-add s" yy" d-of
   -> outcome-ok outcome-ok 0 }T
T{ library growing stage-read-unchecked lf-libdec-count 0 lf-menv-name s" yy" nm =
   -> outcome-ok 0 true }T
T{ s" Nat.add" nm lf-menv-find -> -1 outcome-invalid }T
ck-stage lf-menv-library!  growing stage-free
\ A new run's reset stores forget the text list and every decoded record.
T{ lf-author-begin s" zz" nm lf-menv-find s" Nat.add" d-of drop lbd-records slab-count
   -> -1 outcome-invalid 1 }T

\ ---- 2. getDecLevel: Nat : Type gives 0; a proposition's level 0 is
\ "invalid universe level"; an assignable ?u becomes succ ?w (the answer
\ ?w), a read-only one is invalid; max (a+1) (b+1) gives max a b.
: prop ( -- t ) 0 lf-term-symbolic-sort 0= abort" sort" ;
T{ nat lf-meta-dec-level prop lf-meta-dec-level -> 0 outcome-ok 0 outcome-ok }T
T{ s" True" 0 cst lf-meta-dec-level -> -1 outcome-invalid }T
variable lu
: sort-of ( level -- t ) lf-term-symbolic-sort 0= abort" sort" ;
: typed-mvar ( -- t ) lf-level-mvar-new made dup lu ! sort-of mv-natural lf-mvar-new made ;
T{ typed-mvar lf-meta-dec-level made lu @ lf-level-mvar-value drop lf-level-first@ = -> true }T
T{ typed-mvar false lf-mctx-depth{ made swap lf-meta-dec-level rot }lf-mctx-depth
   -> -1 outcome-invalid outcome-ok }T
: param ( c-addr u -- level ) nm lf-level-param 0= abort" param" ;
: succ ( level -- level' ) lf-level-succ 0= abort" succ" ;
: two ( -- t ) s" a" param succ s" b" param succ lf-level-max 0= abort" max" sort-of ;
: max-ab ( -- level ) s" a" param s" b" param lf-level-max 0= abort" max" ;
T{ two lf-lctx-local made lf-meta-dec-level made max-ab lf-meta-level= -> true outcome-ok }T
\ max (a+1) b: b does not decrement, so neither does the max.
: one-side ( -- t ) s" a" param succ s" b" param lf-level-max 0= abort" max" sort-of ;
T{ one-side lf-lctx-local made lf-meta-dec-level -> -1 outcome-invalid }T
T{ lfa-e-universe-level lf-author-outcome -> outcome-invalid }T

\ ---- 2. The instance-typed flag: set, rolled back with its scope; an
\ assignment to an instance-typed metavariable is unsupported (S1
\ appendix D, until s1-synth); the hooks answer unsupported.
variable im
T{ nat mv-natural lf-mvar-new made dup im ! lf-mvar-inst? -> false }T
T{ lf-mctx-mark made im @ lf-mvar-mark-inst swap lf-mctx-rollback im @ lf-mvar-inst?
   -> outcome-ok outcome-ok false }T
T{ im @ lf-mvar-mark-inst im @ lf-mvar-inst? 0 lf-mvar-mark-inst -> outcome-ok true outcome-invalid }T
T{ im @ 0 num lf-meta-defeq -> false outcome-unsupported }T
T{ im @ lf-meta-synth-pending nat lf-meta-synth
   -> false outcome-unsupported -1 false outcome-unsupported }T

\ ---- 4. lf-menv-reset leaves the run mode: nothing found.
T{ lf-menv-reset s" Nat.add" nm lf-menv-find nip lf-libdec-count -> outcome-invalid 0 }T

\ ---- 5. The heap refusing each allocation of a decode in turn: ok, or
\ full with no handle.
: decode-at ( k -- d outcome )
  ck-stage lf-menv-library! heap-refusals ! s" Nat.rec" nm lf-menv-find
  0 heap-refusals ! ;
: refusal-ok? ( d outcome -- flag )
  dup ok? if 2drop true else outcome-full = swap 0< and then ;
: refusal-note ( d outcome -- outcome ) tuck refusal-ok? 0= if dup worst ! then ;
: each-refused ( -- k ) 0 begin 1+ dup decode-at refusal-note ok? until ;
variable refusals
T{ outcome-ok worst ! each-refused dup refusals ! 1 > worst @ -> true outcome-ok }T
\ After each refusal the same find again, the library still bound,
\ decodes; and once it is bound again nothing refused stays allocated.
: again-at ( k -- outcome ) decode-at 2drop s" Nat.rec" nm lf-menv-find nip ;
: all-again? ( -- flag ) true refusals @ 1+ 1 do i again-at ok? and loop ;
: blocks-at ( k -- n ) decode-at 2drop ck-stage lf-menv-library! live-blocks @ ;
: no-leak? ( -- flag )
  0 blocks-at true refusals @ 1+ 1 do over i blocks-at = and loop nip ;
T{ all-again? no-leak? -> true true }T
\ isDefEqUnitLike between two free variables of type PUnit, PUnit decoded
\ first: each allocation refused in turn gives full or true, never a read
\ of the data of PUnit.unit when its decode was refused (H2).
: punit ( -- t ) level1 0 u! s" PUnit" 1 cst ;
punit lf-lctx-local made constant fv  punit lf-lctx-local made constant fw
: unit-at ( k -- flag outcome )
  ck-stage lf-menv-library! s" PUnit" d-of drop heap-refusals ! fv fw lf-meta-defeq
  0 heap-refusals ! ;
: unit-ok? ( flag outcome -- flag ) dup ok? if drop else nip outcome-full = then ;
: unit-note ( flag outcome -- outcome ) tuck unit-ok? 0= if dup worst ! then ;
: unit-refused ( -- k ) 0 begin 1+ dup unit-at unit-note ok? until ;
T{ outcome-ok worst ! unit-refused 1 > worst @ -> true outcome-ok }T
\ getStuckMVar? of Nat.rec over the constant Nat.add, the library's
\ decodes forgotten and each allocation refused in turn: full whenever a
\ refusal fired (Nat.add's decode among them, which whnf.fs keeps as its
\ fault), else unsupported (Nat.add is no constructor), never another.
: rec-on ( major -- t ) >r level1 0 u! s" Nat.rec" 1 cst nat app nat app nat app r> app ;
s" Nat.add" 0 cst rec-on constant stuck-term
: stuck-at ( k -- flag outcome fired? )
  ck-stage lf-menv-library! heap-refusals ! stuck-term lf-whnf-stuck heap-refusals @ 0=
  0 heap-refusals ! ;
: stuck-ok? ( flag outcome fired? -- flag )
  if outcome-full = else outcome-unsupported = then swap 0= and ;
: stuck-refused ( -- k ) 0 begin 1+ dup stuck-at 2dup >r >r stuck-ok? 0= if 1 worst ! then
  r> r> 0= swap outcome-unsupported = and until ;
T{ outcome-ok worst ! stuck-refused 2 > worst @ -> true outcome-ok }T
\ The same with Nat.rec decoded first and the records' slab trimmed to
\ it: Nat.add's decode is the one that needs room, refused: full.
: stuck-full ( -- flag outcome )
  ck-stage lf-menv-library! s" Nat.rec" d-of drop lbd-records slab-trim drop
  1 heap-refusals ! stuck-term lf-whnf-stuck 0 heap-refusals ! ;
T{ stuck-full -> false outcome-full }T
\ A name's parts on a slab with room for one: the second part's room
\ refused, a find answers full and keeps the cell below it, as does a
\ tier name's run name.
: one-room ( -- ) lbd-parts slab-clear lbd-parts slab-trim drop ;
: refuse-one ( -- ) 1 heap-refusals ! ;
T{ one-room 777 s" Nat.add" nm refuse-one lf-menv-find 0 heap-refusals !
   -> 777 -1 outcome-full }T
T{ 777 s" Nat.add" d-of ck-stage staged-name@ one-room refuse-one lf-libdec-run-name
   0 heap-refusals ! -> 777 -1 outcome-full }T
\ A sought part refused room (the parts' slab grown again, then the
\ tier's names filled to their slab's capacity, by the test): full, not
\ "unknown constant".
: tier-names@ ( -- cons ) ck-stage stage-tier tier-names ;
: names-full? ( -- flag ) tier-names@ cons-records dup slab-count swap slab-capacity = ;
: name-add ( u -- ) 0 swap ck-stage stage-tier name-num 2drop ;
: fill-names ( -- ) 1000000 begin names-full? 0= while dup name-add 1+ repeat drop ;
T{ s" Nat.add" d-of drop fill-names s" Nat.add" nm refuse-one lf-menv-find
   0 heap-refusals ! -> -1 outcome-full }T
\ The same for getDecLevel's assignment (?u := succ ?w); a type whose
\ level cannot be inferred passes its failure on.
: dec-at ( k -- level outcome )
  typed-mvar swap heap-refusals ! lf-meta-dec-level 0 heap-refusals ! ;
: dec-refused ( -- k ) 0 begin 1+ dup dec-at refusal-note ok? until ;
T{ outcome-ok worst ! dec-refused 0> worst @ -> true outcome-ok }T
T{ 0 lf-term-bvar drop lf-meta-dec-level nip -> outcome-invalid }T

\ ---- 2. The re-export test's library, every record kind of the
\ exporter (tests/core/reexport/kinds.lean): Nat.add's type holds an
\ mdata node there (--export-mdata), an expression not supported yet;
\ imax in a level (Sort (imax u v)), a reflexive type's flags, let and
\ have values and a literal beyond 64 bits decode.
: kinds-lib ( -- c-addr u ) s" tests/core/reexport/kinds.ndjson" ;
T{ kinds-lib false lfc-library-open s" Nat.add" nm lf-menv-find
   -> outcome-ok -1 outcome-unsupported }T
: codomain-level ( c-addr u -- level ) d-of lf-menv-type lf-term-second@ lf-term-second@
  lf-term-first@ ;
T{ s" ReexportKinds.arrow" codomain-level lf-level-tag@ -> lf-level-tag-imax }T
T{ s" ReexportKinds.Wide" d-of lf-menv-data lf-ity-flags lf-more-field
   -> lf-ity-rec-bit lf-ity-reflexive-bit or }T
: valued? ( c-addr u -- flag ) d-of lf-menv-value nip ;
T{ s" ReexportKinds.kept" valued? s" ReexportKinds.twice" valued? s" ReexportKinds.big" valued?
   -> true true true }T
\ A declaration that cannot be decoded is no unknown constant (plan S2):
\ whnfCore of Nat.add 1 2, getStuckMVar? of it and inferType of Nat.add
\ pass unsupported on, as do whnfCore of a recursor whose major premise
\ is the constant Nat.add alone (the premise's unfolding asks first) and
\ getStuckMVar? of it (the premise's kind asked: whnf.fs's fault).
: add-12 ( -- t ) s" Nat.add" 0 cst 1 nlit app 2 nlit app ;
T{ add-12 lf-whnf-core add-12 lf-whnf-stuck s" Nat.add" 0 cst lf-infer nip
   -> -1 outcome-unsupported false outcome-unsupported outcome-unsupported }T
T{ s" Nat.add" 0 cst rec-on dup lf-whnf-core rot lf-whnf-stuck
   -> -1 outcome-unsupported false outcome-unsupported }T
\ Nat.rec over Nat.zero (iota) with each allocation refused in turn, the
\ library's decodes forgotten first: full or the minor premise (the
\ constant Nat), never unsupported (wc-induct-data passes a refused
\ decode of Nat on as full).
s" Nat.zero" 0 cst rec-on constant iota-term
: iota-at ( k -- e outcome )
  ck-stage lf-menv-library! heap-refusals ! iota-term lf-whnf-core 0 heap-refusals ! ;
: iota-ok? ( e outcome -- flag ) dup ok? if 2drop true else nip outcome-full = then ;
: iota-note ( e outcome -- outcome ) 2dup iota-ok? 0= if dup worst ! then nip ;
: iota-refused ( -- k ) 0 begin 1+ dup iota-at iota-note ok? until ;
T{ outcome-ok worst ! iota-refused 1 > worst @ iota-term lf-whnf-core swap lf-term-const?
   -> true outcome-ok outcome-ok true }T

\ ---- 4. lfc-library-close leaves the run mode; a failed re-open leaves
\ none bound to the stage it freed.
T{ lfc-library-close lf-libdec-stage lf-libdec-count -> 0 0 }T
T{ library true lfc-library-open lf-libdec-stage ck-stage = -> outcome-ok true }T
T{ s" tests/front/no-such.ndjson" true lfc-library-open lf-libdec-stage lf-libdec-count
   -> outcome-invalid 0 0 }T
T{ s" Nat.add" nm lf-menv-find -> -1 outcome-invalid }T
T{ lfc-library-close lf-libdec-count lfc-empty lfc-rooms-back -> 0 outcome-ok }T
T{ depth -> 0 }T
cr .( menv-run.fs: all tests passed) cr
