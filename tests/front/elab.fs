\ The elaborator (plan S1, FE1e6-7; src/front/elab-pending.fs,
\ elab-app.fs, elab-term.fs, elab-decl.fs) over the S1 slice and its
\ elaboration data (tests/front/s1-slice.ndjson, format 3), in the
\ command line's run mode, with Lean's instance search (synth.fs) and the
\ data's default instances, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md. Stand-ins replace the search
\ (defeq.fs's hook lf-meta-synth) or the default instances
\ (lf-elab-default-instances) only where a test says so, and are put
\ back after it. tests/front/check_elab.py runs the S1 files through
\ bin/leanforth against pinned Lean.
\ 1. Every outcome: terms (numerals through default instances, 0 + 0 = 0
\    and 2 + 2 = 4, term and tactic proofs, applications with implicit
\    arguments, binrel% with and with no max type), Lean's errors 125,
\    126, 127, 129, 131 (twice: analyze and ensureHasType), 140 and 141
\    (#check inside a declaration or a tactic block), the search's own
\    refusal 119 (a
\    tried instance the slice leaves out), unsupported 132, 135, 136,
\    137, 139 (a level metavariable left in a statement), exhausted 138
\    at a declaration and at a tactic step;
\ 2. malformed: a variable slot no binder has;
\ 3. stack effects (every T{ }T checks the depth);
\ 4. whole runs: declarations in a row, a failure, then a fresh one;
\ 5. resources: the budget per declaration, and the elaborator's own
\    visits spending it;
\ 6. state: after a failure the next declaration is as in a fresh run;
\    the default instances' rollback; the pending list's window around
\    lf-elab-synth{ }lf-elab-synth; a Lean error caught by commitWhen;
\ 7. regression pins: the golden traces of C17 and C1 (with lazy delta's
\    unfolding of outParam, as pinned Lean's isDefEq.delta trace).
include ../support/heap-watch.fs
require ../support/tester.fs
require ../../src/main.fs
decimal

: library ( -- c-addr u ) s" tests/front/s1-slice.ndjson" ;
: data ( -- c-addr u ) s" tests/front/s1-slice.elab.ndjson" ;
T{ library true lfc-library-open -> outcome-ok }T
T{ data ck-stage ck-stage stage-manifest manifest-digest elab-read -> outcome-ok }T
T{ lfc-rooms -> outcome-ok }T

\ ---- Terms by name, at given levels.
create us 4 2* cells allot
: u! ( level i -- ) >r dup lf-level-identity drop swap r> 2* cells us + 2! ;
: cst ( c-addr u n -- t )
  >r lfa-intern lf-name-generation @ us r> lf-cref-new 0= abort" ref"
  lf-cterm-new 0= abort" const" drop ;
: app ( f a -- t ) lf-term-app 0= abort" app" ;
: level1 ( -- level ) 0 lf-level-succ 0= abort" level" ;
: nat ( -- t ) s" Nat" 0 cst ;
: nlit ( u -- t ) lf-hterm-cell 0= abort" lit" drop ;
: num ( u -- t )   \ @OfNat.ofNat.{0} Nat (nat_lit u) (instOfNatNat (nat_lit u))
  >r 0 0 u! s" OfNat.ofNat" 1 cst nat app r@ nlit app s" instOfNatNat" 0 cst r> nlit app app ;
: eq-nat ( a b -- t ) >r >r level1 0 u! s" Eq" 1 cst nat app r> app r> app ;
: refl-nat ( a -- t ) >r level1 0 u! s" Eq.refl" 1 cst nat app r> app ;
: zero ( -- t ) s" Nat.zero" 0 cst ;
: nat3 ( c-addr u -- t ) 3 >r 0 0 u! 0 1 u! 0 2 u! r> cst nat app nat app nat app ;
: hadd ( a b -- t )   \ @HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b
  >r >r s" HAdd.hAdd" nat3 0 0 u! s" instHAdd" 1 cst nat app s" instAddNat" 0 cst app app
  r> app r> app ;
: same? ( a b -- flag ) lf-meta-eqv drop ;

\ ---- Stand-ins (each test that sets one puts the real word back).
: real-synth ( -- ) ['] lf-synth-instance is lf-meta-synth ;
: real-defaults ( -- ) ['] lf-default-instances is lf-elab-default-instances ;
: no-defaults ( class -- addr n outcome ) drop 0 0 outcome-ok ;
: head-named? ( t c-addr u -- flag ) rot lf-meta-head -rot lf-meta-const-named? ;
\ No instance of Add (Lean's failed to synthesize, inside commitWhen);
\ any other problem to the search.
: add-none ( type -- inst flag outcome )
  dup s" Add" head-named? if drop -1 false outcome-ok else lf-synth-instance then ;
\ A search that fails with no Lean error for Add (as a corrupt state
\ would): invalid, recorded as 76, never caught.
: add-broken ( type -- inst flag outcome )
  dup s" Add" head-named? if drop -1 false outcome-invalid else lf-synth-instance then ;
\ OfNat problems always stuck (Lean's undef), for synthesis that fails
\ only when nothing may wait any more.
: of-nat-stuck ( type -- inst flag outcome )
  dup s" OfNat" head-named? if drop -1 false lf-meta-stuck else lf-synth-instance then ;
\ No instance of OfNat at all: failed to synthesize.
: no-of-nat ( type -- inst flag outcome )
  dup s" OfNat" head-named? if drop -1 false outcome-ok else lf-synth-instance then ;
\ OfNat's default instances: first HAdd's instHAdd, which fails to unify
\ and is rolled back, then instOfNatNat.
: dflt-named ( c-addr u -- v )
  lfa-intern lf-menv-data-decl 0= abort" decl"
  elab-default elab-count 0 ?do i elab-default@ drop nip over = if drop i unloop exit then
  loop true abort" no default" ;
create two-defaults 2 cells allot
\ HAdd's default instances twice: hasHeterogeneousDefaultInstances
\ scans them (two or more), neither heterogeneous.
: two-hadd ( class -- addr n outcome )
  drop s" instHAdd" dflt-named dup two-defaults ! two-defaults cell+ ! two-defaults 2
  outcome-ok ;
: wrong-first ( class -- addr n outcome )
  drop s" instHAdd" dflt-named two-defaults ! s" instOfNatNat" dflt-named two-defaults cell+ !
  two-defaults 2 outcome-ok ;

\ ---- Running texts.
: nrun ( c-addr u -- outcome ) lf-author-begin lf-author-text ;
: err ( -- code line col ) lf-author-code lfa-error lfa-err-at @ lfa-pos> ;
: see-at ( -- line col ) lfa-error lfa-err-see @ lfa-pos> ;
: nfails ( c-addr u -- code line col ) nrun drop err ;
: decl0 ( -- decl ) lf-author-count begin 1- dup lfa-library? 0= until lf-author-decl ;
: ty ( -- t ) decl0 lf-fdecl-type @ ;
: va ( -- t ) decl0 lf-fdecl-value @ ;

\ ---- 7. Golden traces (FE1E 1.6) of C17, 0 + 0 = 0, and C1, 0 + n = n,
\ first, as in a fresh run (the metavariables' numbers are a fresh run's):
\ pinned Lean's order of events (tests/front/s1-c17.lean's trace: the
\ three numerals' instance problems stuck and resumed in each tree's
\ round, elabAppArgs of HAdd.hAdd with ?α ?β ?γ ?self and the two
\ operands, finalize's HAdd problem stuck, then the default instances:
\ instHAdd rolled back while ?α is open, instOfNatNat, instHAdd again;
\ C1: analyze's max type Nat, hasHomogeneousInstance's mkAppM, finalize).
\ Lazy delta unfolds outParam where pinned Lean's isDefEq.delta trace
\ does: never for C17's statement, three times for C1's (mkAppM at
\ default transparency, the search's assignOutParams at instances).
: golden ( c-addr u -- c-addr' u' ) slurp-file ;
true lf-elab-trace!
T{ s" axiom c17 0 0 + 0 = end c17" nrun -> outcome-ok }T
T{ lf-elab-trace s" tests/front/s1-c17.trace" golden compare -> 0 }T
T{ s" axiom c1 Nat explicit: n 0 n + n = end c1" nrun -> outcome-ok }T
T{ lf-elab-trace s" tests/front/s1-c1.trace" golden compare -> 0 }T
false lf-elab-trace!

\ ---- 5. No room, at theorem t's allocations in turn (review s1-elab
\ re-check M2): the k-th from its start refused, for every 61st k from 1
\ (t makes about 4,300; all of them would take 20 s), t stops with no
\ room for terms (60), or, where only a cache could not grow (core's
\ stamps), is made as without the refusal; past the last, it is made.
: t-text ( -- c-addr u ) s" theorem t 0 0 + 0 = := by by-rfl end t" ;
: t-made? ( -- flag )
  ty 0 num 0 num hadd 0 num eq-nat same? va 0 num 0 num hadd refl-nat same? and ;
: t-refused ( k -- outcome refused? )
  heap-refusals ! t-text nrun heap-refusals @ 0= 0 heap-refusals ! ;
: t-good? ( outcome refused? -- flag )
  swap ok? if drop t-made? else lf-author-code 60 = and then ;
variable sweep-good
: sweep-step ( k -- k' more? )
  61 + dup t-refused dup >r t-good? sweep-good @ and sweep-good ! r> ;
: sweep ( -- k flag ) true sweep-good ! -60 begin sweep-step 0= until sweep-good @ ;
T{ sweep swap 1000 > -> true true }T
T{ t-text nrun t-made? -> outcome-ok true }T

\ ---- 1. Terms. 0 = 0: binrel% with no max type, both numerals pending,
\ then default instances in the statement's synthesis (instOfNatNat,
\ priority 100, after 1000 and 500 found none); by-rfl closes it.
T{ s" theorem z0 0 0 = := by by-rfl end z0" nrun -> outcome-ok }T
T{ ty 0 num 0 num eq-nat same? va lf-term-app? -> true true }T
\ The term proof 0 Eq.refl: finalize compares @Eq Nat (OfNat.ofNat ..)
\ with @Eq ?α (OfNat.ofNat ?T ..) by lazy delta (S2 merge A).
T{ s" theorem z0b 0 0 = := 0 Eq.refl end z0b" nrun ty 0 num 0 num eq-nat same?
   va 0 num refl-nat same? -> outcome-ok true true }T
\ Nat.zero = 0: max type Nat, the numeral's ?T unified with it (applyCoe).
T{ s" axiom z1 Nat.zero 0 = end z1" nrun -> outcome-ok }T
T{ ty zero 0 num eq-nat same? -> true }T
\ A numeral against Nat (Nat.succ's binder): its instance found at once.
T{ s" axiom z2 0 Nat.succ 1 = end z2" nrun -> outcome-ok }T
: nsucc ( t -- t' ) s" Nat.succ" 0 cst swap app ;
T{ ty 0 num nsucc 1 num eq-nat same? -> true }T
\ Parameters: n : Nat, its variable in the statement and the proof.
T{ s" theorem z3 Nat explicit: n n n = := n Eq.refl end z3" nrun -> outcome-ok }T
T{ ty lf-term-pi? ty lf-term-first@ nat same? va lf-term-lam? -> true true true }T
\ A tactic proof: by-rfl on the elaborated statement; by-exact's term.
T{ s" theorem z4 Nat.zero Nat.zero = := by by-rfl end z4" nrun -> outcome-ok }T
T{ s" theorem z5 Nat.zero Nat.zero = := by Nat.zero Eq.refl by-exact end z5" nrun
   -> outcome-ok }T
T{ va zero refl-nat same? -> true }T
\ An axiom's statement alone.
T{ s" axiom z6 Nat.zero 0 = end z6" nrun ty zero 0 num eq-nat same? va -> outcome-ok true -1 }T
\ S1's end: 0 + 0 = 0 by rfl, binop% under binrel%, HAdd's default
\ instance instHAdd and then Add Nat; @Eq.refl.{1} Nat (0 + 0).
T{ s" theorem t 0 0 + 0 = := by by-rfl end t" nrun -> outcome-ok }T
T{ ty 0 num 0 num hadd 0 num eq-nat same? va 0 num 0 num hadd refl-nat same? -> true true }T
\ HAdd.hAdd applied by name (Lean.Internal.coeM is in the slice, so its
\ result is the out-parameter of its local instance: finalize
\ synthesizes, as Lean's resultIsOutParamSupport); @OfNat.ofNat ?a 0 ?i
\ against Nat.succ's Nat (pinned Lean: axiom p2 : Nat.succ (OfNat.ofNat
\ 0) = ...): finalize's trySynthesizeAppInstMVars fills OfNat Nat 0 and
\ takes it out of the list.
T{ s" theorem q4 Nat.zero Nat.zero HAdd.hAdd Nat.zero Nat.zero HAdd.hAdd = := Nat.zero Nat.zero HAdd.hAdd Eq.refl end q4"
   nrun ty zero zero hadd zero zero hadd eq-nat same? -> outcome-ok true }T
T{ s" axiom p2 0 OfNat.ofNat Nat.succ Nat.zero Nat.succ = end p2" nrun -> outcome-ok }T
\ A leaf of unknown type under +, with two default instances of HAdd
\ (a stand-in list): hasHeterogeneousDefaultInstances scans them, finds
\ neither heterogeneous, and the leaf is made the max type's.
' two-hadd is lf-elab-default-instances
T{ s" axiom c1h Nat explicit: n 0 n + n = end c1h" nrun -> outcome-ok }T
real-defaults
\ C16, 2 + 2 = 4, by rfl (Nat literals in isDefEq).
T{ s" theorem z7 2 2 + 4 = := by by-rfl end z7" nrun ty 2 num 2 num hadd 4 num eq-nat same?
   -> outcome-ok true }T

\ ---- 1. Lean's errors, each at end (or the tactic's word) with the
\ syntax's place as the second position.
\ OfNat Bool 0 (the numeral at Bool, the max type): on the slice the
\ search tries an instance the slice leaves out (119, synth.fs's code);
\ with no OfNat instance at all, Lean's failed to synthesize (125).
T{ s" theorem e1 Bool.true 0 = := Bool.true Eq.refl end e1" nfails see-at
   -> 119 1 47 1 22 }T
' no-of-nat is lf-meta-synth
T{ s" theorem e1 Bool.true 0 = := Bool.true Eq.refl end e1" nfails see-at
   -> 125 1 47 1 22 }T
real-synth
\ typeclass instance problem is stuck: no default instance to fire; at
\ the oldest pending numeral, column 12 as pinned Lean's (the smallest
\ syntax range, the earliest first).
' no-defaults is lf-elab-default-instances
T{ s" theorem e2 0 0 = := 0 Eq.refl end e2" nfails see-at -> 126 1 31 1 12 }T
real-defaults
\ numerals are data: 0 against the proposition Nat.zero = Nat.zero.
T{ s" theorem e3 Nat.zero Nat.zero = := 0 end e3" nfails see-at -> 127 1 37 1 35 }T
\ A coercion Lean would look for: Nat.zero = Bool.true is uncomparable in
\ analyze and CoeT is in the slice (131 there); Bool.true as a proof of
\ Nat.zero = Nat.zero is ensureHasType's coercion (131 at end).
T{ s" theorem e4 Nat.zero Bool.true = := by by-sorry end e4" nfails see-at
   -> 131 1 48 1 31 }T
T{ s" theorem e4b Nat.zero Nat.zero = := Bool.true end e4b" nfails see-at
   -> 131 1 46 1 36 }T
\ type expected (ensureType): Nat.zero as a statement (pinned Lean: "type
\ expected, got (Nat.zero : Nat)").
T{ s" axiom q3 Nat.zero end q3" nfails see-at -> 130 1 19 1 10 }T
\ #check of a term the elaborator refuses (131), and a #check line whose
\ printing fails (the printer limited to one nested visit: no room, 60;
\ review s1-elab L, the printer's outcome passed on).
T{ s" Nat.zero Bool.true = #check" nfails see-at -> 131 1 22 1 20 }T
1 lf-print-limit! drop
T{ s" 0 0 + 0 = #check" nfails lfa-error lfa-err-see @ -> 60 1 11 -1 }T
lf-print-default-limit lf-print-limit! drop
\ A recursor applied: elaborating as an eliminator (FE5).
T{ s" Nat.zero ' Nat.rec Nat.zero $ #check" nfails see-at -> 135 1 31 1 12 }T
\ #check of a constant alone: Lean prints its signature (FE2).
T{ s" Nat.zero #check" nfails see-at -> 137 1 10 1 1 }T
\ #check of a numeral: 0 : Nat by the default instance; with none, a
\ hole left (FE2).
T{ s" 0 #check" nrun -> outcome-ok }T
' no-defaults is lf-elab-default-instances
T{ s" 0 #check" nfails see-at -> 137 1 3 1 1 }T
real-defaults
\ The tactics' term (by-exact through lf-tac-elab, review s1-elab H2):
\ its elaboration fails, numerals are data (127 at by-exact); its
\ synthesis with no postponing finds a problem stuck (126). The same for
\ a term proof's synthesis after elabTermEnsuringType (126 at end).
T{ s" theorem x1 Nat.zero Nat.zero = := by 0 by-exact end x1" nfails see-at
   -> 127 1 40 1 38 }T
' of-nat-stuck is lf-meta-synth  ' no-defaults is lf-elab-default-instances
T{ s" theorem x2 Nat := by 0 by-exact end x2" nfails see-at -> 126 1 24 1 22 }T
T{ s" theorem x3 Nat := 0 end x3" nfails see-at -> 126 1 21 1 19 }T
real-synth real-defaults
\ #check is a command (review s1-elab M1): inside a declaration and of a
\ binder's variable it is error 140, Lean's "unexpected token '#check';
\ expected term"; inside a tactic block, which Lean would end there, 141.
T{ s" theorem m1 Nat.zero Nat.zero = #check Nat.zero Nat.zero = := by by-rfl end m1"
   nfails -> 140 1 32 }T
T{ s" theorem m2 Nat explicit: n n #check n n = := n Eq.refl end m2" nfails -> 140 1 30 }T
T{ s" theorem m3 Nat.zero Nat.zero = := by Nat.zero #check by-rfl end m3" nfails
   -> 141 1 47 }T
T{ s" theorem m4 Nat.zero Nat.zero = := Nat.zero #check Eq.refl end m4" nfails
   -> 140 1 44 }T
\ A statement left with a level metavariable (PUnit.{?u}): Lean's
\ levelMVarToParam (pinned Lean: h3.{u_1} : PUnit.{u_1}), not supported
\ yet (139, S5), at the statement; never handed over.
T{ s" axiom h3 PUnit end h3" nfails see-at -> 139 1 16 1 10 }T
\ The budget: three steps are not enough for a declaration (138), the
\ next declaration has the whole budget again.
T{ 3 lf-elab-fuel! s" theorem e6 Nat.zero Nat.zero = := by by-rfl end e6" nfails
   -> 138 1 45 }T
T{ lf-meta-default-budget lf-elab-fuel!
   s" theorem e7 Nat.zero Nat.zero = := by by-rfl end e7" nrun -> outcome-ok }T
\ The elaborator's own visits spend the budget too (Lean's
\ maxHeartbeats counts them): axiom a6 Nat takes seven steps, two of
\ them the elaborator's visits; six are not enough.
T{ 7 lf-elab-fuel! s" axiom a6 Nat end a6" nrun -> outcome-ok }T
T{ 6 lf-elab-fuel! s" axiom a7 Nat end a7" nfails -> 138 1 14 }T
lf-meta-default-budget lf-elab-fuel!

\ ---- 2. Malformed and unknown: a variable no parameter gives; a name
\ the library lacks is the reader's (error 1, before elaboration); the
\ type of a term that is no live metavariable (mvars.fs).
T{ zero lf-mvar-type-instantiated -> -1 outcome-invalid }T
T{ lf-elab-reset 7 syn-k-var 0 syn-new drop swap syn-a! -1 lf-elab-term
   -> -1 outcome-invalid }T

\ ---- 1. Direct calls: a function whose type is a metavariable, with an
\ argument (tryPostponeIfMVar, 132); a free variable of a pi type (its
\ binder's kind unknown, 136).
: sort1 ( -- t ) level1 lf-term-symbolic-sort 0= abort" sort" ;
: fvar-of ( type -- fvar ) lf-lctx-local 0<> abort" fvar" ;
: app-visit ( -- term outcome ) 0 0 ['] lf-elab-app-call lf-elab-visit ;
: app-run ( f -- term outcome ) -1 lf-elab-app-new drop app-visit ;
: app-run1 ( f a -- term outcome )
  swap -1 lf-elab-app-new drop lf-elab-app-term+ drop app-visit ;
T{ lf-elab-reset sort1 mv-natural lf-mvar-new drop fvar-of zero app-run1 nip
   -> outcome-unsupported }T
T{ lf-elab-error drop -> 132 }T
T{ lf-elab-reset nat nat lf-term-pi drop fvar-of app-run nip lf-elab-error drop
   -> outcome-unsupported 136 }T

\ ---- 6. synthesizeInstMVarCore on an instance metavariable assigned
\ already: the search's instOfNatNat 0 compared with the value; equal,
\ filled; @OfNat.mk Nat 0 1, not defeq, is Lean's containsPendingMVar
\ case, not ported (139).
: of-nat0 ( -- t ) 0 0 u! s" OfNat" 1 cst nat app 0 nlit app ;
: inst-mvar ( -- mvar ) of-nat0 mv-synthetic lf-mvar-new drop ;
: inst0 ( -- t ) s" instOfNatNat" 0 cst 0 nlit app ;
: mk1 ( -- t ) 0 0 u! s" OfNat.mk" 1 cst nat app 0 nlit app 1 nlit app ;
T{ lf-elab-reset inst-mvar dup inst0 lf-mvar-assign swap lf-elab-synth-core
   -> outcome-ok true outcome-ok }T
T{ lf-elab-reset inst-mvar dup mk1 lf-mvar-assign swap lf-elab-synth-core
   lf-elab-error drop -> outcome-ok false outcome-unsupported 139 }T

\ ---- 6. A Lean error inside commitWhen is caught: with no Add instance,
\ instHAdd's attempt for HAdd ?a ?b ?c fails ([Add ?a]: failed to
\ synthesize, caught) and is rolled back; the numerals' default instance
\ then makes HAdd Nat Nat ?c, which the search answers.
' add-none is lf-meta-synth
T{ s" 0 0 + #check" nrun lf-author-code lf-elab-error -> outcome-ok 0 0 -1 }T
\ A failure that is no Lean error (malformed state, 76) is not caught
\ (review s1-elab M3): the run stops there.
' add-broken is lf-meta-synth
T{ s" 0 0 + #check" nfails -> 76 1 7 }T
real-synth
\ A rollback the context refuses (a mark it never gave) after a failed
\ attempt: false and the refusal, the caller's cells kept, and the
\ refusal recorded as 76 in place of the Lean error before it (review
\ s1-elab re-check H1), so an outer catch never forgets it.
T{ lf-elab-reset 125 lf-elab-fail drop 12345 -77 false outcome-invalid ep-when-failed
   lf-elab-error drop -> 12345 false outcome-invalid 76 }T
T{ outcome-invalid lf-elab-catch -> false }T
\ synthesizePending on a list of two instance problems (a default
\ instance's binders), the newest first as Lean prepends them: OfNat ?g 0
\ is stuck until HAdd Nat Nat ?g, answered, makes ?g Nat; a second pass
\ (synthesizeUsingInstances' loop) fills it, with no default instance.
: type0 ( -- t ) 0 lf-level-succ drop lf-term-symbolic-sort drop ;
: ofnat-of ( t -- t' ) 0 0 u! s" OfNat" 1 cst swap app 0 nlit app ;
: hadd-nat-nat ( g -- t ) >r 0 0 u! 0 1 u! 0 2 u! s" HAdd" 3 cst nat app nat app r> app ;
: inst-of ( type -- mvar ) mv-synthetic lf-mvar-new drop ;
: c-run ( first -- flag outcome ) 0 ep-frames-ready ['] ep-c-call frame-through drop ;
variable g  variable i1  variable i2  variable first-goal
T{ lf-elab-reset type0 mv-natural lf-mvar-new swap g ! -> outcome-ok }T
T{ g @ hadd-nat-nat inst-of i1 !  g @ ofnat-of inst-of i2 !  ep-goals slab-count first-goal !
   i1 @ ep-goals slab-push i2 @ ep-goals slab-push -> outcome-ok outcome-ok }T
' no-defaults is lf-elab-default-instances
true lf-elab-trace!
T{ first-goal @ c-run g @ lf-instantiate-mvars drop nat same? -> true outcome-ok true }T
\ Both filled: the one removed is the one tried (review s1-elab re-check H2).
T{ i1 @ lf-instantiate-mvars drop lf-mvar? i2 @ lf-instantiate-mvars drop lf-mvar? -> false false }T
\ The first problem tried is OfNat's, the newest.
T{ lf-elab-trace s" synth @OfNat ?m." search nip swap lf-elab-trace drop - -> true 0 }T
false lf-elab-trace!
real-defaults
\ A default instance that fails to unify is rolled back, and the next one
\ is tried.
' wrong-first is lf-elab-default-instances
true lf-elab-trace!
T{ s" theorem w1 0 0 = := by by-rfl end w1" nrun ty 0 num 0 num eq-nat same?
   -> outcome-ok true }T
: trace-has? ( c-addr u -- flag ) lf-elab-trace 2swap search nip nip ;
T{ s" instHAdd: rolled back" trace-has? s" instOfNatNat: ok" trace-has? -> true true }T
false lf-elab-trace!
real-defaults

\ ---- 6. The tactics' hook (Tactic.elabTerm) and withSynthesize's end:
\ postponing (Lean's mayPostpone) leaves 0's OfNat problem pending, its
\ type ?T open; }lf-elab-synth with postponing still runs the default
\ loop, then the pending list outside the bracket is back.
: zero-node ( -- node ) syn-k-num 0 syn-new drop 0 syn-a! ;
: open-type? ( term -- flag ) lf-infer drop lf-instantiate-mvars drop lf-mvar? ;
T{ lf-elab-reset zero-node -1 true lf-tac-elab swap open-type? lf-elab-pending#
   -> outcome-ok true 1 }T
T{ lf-elab-reset zero-node -1 false lf-tac-elab swap open-type? lf-elab-pending#
   -> outcome-ok false 0 }T
variable t1  variable t2  variable outer-saved
T{ lf-elab-reset zero-node -1 true lf-tac-elab swap t1 ! lf-elab-pending# -> outcome-ok 1 }T
T{ lf-elab-synth{ outer-saved ! lf-elab-pending# zero-node -1 true lf-tac-elab swap t2 !
   lf-elab-pending# -> 0 outcome-ok 1 }T
T{ outer-saved @ lf-postpone-yes }lf-elab-synth t2 @ open-type? t1 @ open-type? lf-elab-pending#
   -> outcome-ok false true 1 }T
\ hasHeterogeneousDefaultInstances' test of one default instance's type:
\ C a b c with b (a left leaf's side) or a (a right one's) headed by the
\ max type's constant: HAdd Nat Bool Bool has Nat on the left only.
: bool ( -- t ) s" Bool" 0 cst ;
: hetero ( -- t ) 0 0 u! 0 1 u! 0 2 u! s" HAdd" 3 cst nat app bool app bool app ;
T{ s" Nat" lfa-intern true hetero et-def-hit? s" Nat" lfa-intern false hetero et-def-hit?
   -> false true }T

\ ---- 6. trySynthesizeAppInstMVars's try ... catch (review s1-elab
\ re-check H2): OfNat.ofNat Nat.zero against Nat, its instance problem
\ tried at finalize; a search that answers none once (Lean's failed to
\ synthesize, caught there) leaves it to synthesizeAppInstMVars, whose
\ search fills it.
variable armed
: none-once ( type -- inst flag outcome )
  armed @ over s" OfNat" head-named? and if 0 armed ! drop -1 false outcome-ok
  else lf-synth-instance then ;
' none-once is lf-meta-synth  true armed !
T{ s" axiom p3 Nat.zero OfNat.ofNat Nat.succ Nat.zero Nat.succ = end p3" nrun armed @
   -> outcome-ok 0 }T
real-synth
\ A search answer isDefEq cannot assign (review s1-elab re-check L2):
\ Lean's 129, the instance on the next line (indentExpr), at #check and
\ in a tactic's term.
: wrong-found ( type -- inst flag outcome )
  dup s" OfNat" head-named? if drop zero true outcome-ok else lf-synth-instance then ;
: detail ( -- c-addr u ) 0 lfa-detail slab-at lfa-detail slab-count ;
' wrong-found is lf-meta-synth
T{ s" 0 #check" nfails detail s"   Nat.zero" compare -> 129 1 3 0 }T
T{ s" theorem w2 Nat := by 0 by-exact end w2" nfails detail s"   Nat.zero" compare
   -> 129 1 24 0 }T
real-synth
T{ s" 0 0 + #check" nrun detail nip -> outcome-ok 0 }T

\ ---- 1. Type annotations (Expr.lean:1716-1745; review s1-elab re-check
\ H2): optParam a b and autoParam a b, outParam a, each with that many
\ arguments only; consumeTypeAnnotations gives a, again while one is at
\ the top, and leaves one inside a term as it is.
: opt ( a b -- t ) >r >r level1 0 u! s" optParam" 1 cst r> app r> app ;
: auto ( a b -- t ) >r >r level1 0 u! s" autoParam" 1 cst r> app r> app ;
: outp ( a -- t ) >r level1 0 u! s" outParam" 1 cst r> app ;
: annot? ( t -- opt-auto? out? ) dup lf-meta-opt-auto? swap lf-meta-out-param? ;
: consumed ( t -- t' ) lf-meta-consume-annotations ;
T{ nat zero opt annot? nat zero auto annot? nat outp annot? -> true false true false false true }T
T{ nat zero opt consumed nat same? nat zero auto consumed nat same? nat outp consumed nat same?
   -> true true true }T
T{ nat outp zero opt outp consumed nat same? nat zero opt outp consumed nat same? -> true true }T
: opt1 ( -- t ) level1 0 u! s" optParam" 1 cst nat app ;
: out2 ( -- t ) nat outp nat app ;
: out0 ( -- t ) level1 0 u! s" outParam" 1 cst ;
T{ opt1 annot? out2 annot? out0 annot? nat annot? -> false false false false false false false false }T
T{ opt1 dup consumed = out2 dup consumed = nat dup consumed = -> true true true }T
T{ nat outp nat lf-term-pi drop dup consumed = -> true }T
\ The body under every leading pi (lf-meta-forall-body): Nat → Nat →
\ Bool gives Bool, a body's annotation kept; no pi, the term itself.
: pi2 ( -- t ) nat nat bool lf-term-pi drop lf-term-pi drop ;
T{ pi2 lf-meta-forall-body bool same? nat dup lf-meta-forall-body = -> true true }T
T{ nat nat outp lf-term-pi drop lf-meta-forall-body nat outp same? -> true }T
\ Binder kinds by index (lf-menv-kind@): HAdd.hAdd {α β γ} [self] (a b);
\ k = n, a negative k and a declaration with no binder give none.
: decl-of ( c-addr u -- d ) lfa-intern lf-menv-find ok? 0= abort" decl" ;
: hadd-d ( -- d ) s" HAdd.hAdd" decl-of ;
T{ hadd-d 0 lf-menv-kind@ hadd-d 3 lf-menv-kind@ hadd-d 5 lf-menv-kind@
   -> lf-binder-implicit true lf-binder-instance true lf-binder-default true }T
T{ hadd-d 6 lf-menv-kind@ hadd-d -1 lf-menv-kind@ s" Nat" decl-of 0 lf-menv-kind@
   -> false false false }T
\ The elaboration data's declaration and back (lf-menv-of-data, the run
\ mode: the library's own number, decoded); none outside the library.
T{ s" HAdd.hAdd" lfa-intern lf-menv-data-decl drop lf-menv-of-data swap hadd-d =
   -> outcome-ok true }T
T{ -1 lf-menv-of-data lf-libdec-count lf-menv-of-data -> -1 outcome-invalid -1 outcome-invalid }T


\ ---- 6. After every failure above, a fresh declaration elaborates as in
\ a fresh run; the stack is as it was.
T{ s" theorem z8 0 0 = := by by-rfl end z8" nrun ty 0 num 0 num eq-nat same?
   -> outcome-ok true }T
T{ depth -> 0 }T
cr .( elab.fs: all tests passed) cr
bye
