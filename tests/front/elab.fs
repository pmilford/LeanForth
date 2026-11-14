\ The elaborator (plan S1, FE1e6-7; src/front/elab-pending.fs,
\ elab-app.fs, elab-term.fs, elab-decl.fs) over the S1 slice and its
\ elaboration data (tests/front/s1-slice.ndjson), by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md. Instance search (plan FE1e5,
\ synth.fs) and the instance tables' default instances (s1-synth's
\ instances.fs) are not on this branch: stand-ins answer the S1 problems
\ as pinned Lean does (tests/front/synth-tried.lean on s1-synth: OfNat ?T
\ 0 stuck, OfNat Nat n instOfNatNat n, anything else none) and read the
\ default instances from the data; tests/front/check_elab.py runs the same
\ cases through bin/leanforth against pinned Lean where no stand-in is
\ needed. SWITCH (when synth.fs and instances.fs land): drop the stand-ins
\ below and set the hooks to the real words; the expected terms stay.
\ 1. Every outcome: terms (numerals through default instances, a term
\    proof, applications with implicit arguments, binrel% with and with
\    no max type), Lean's errors 125, 126, 127, 131 (and 130's twin),
\    unsupported 132, 135, 136, 137, 139 (the C16 path, until lazy
\    delta: S2 merge A), exhausted 138 at a declaration and at a
\    tactic step (91);
\ 2. malformed: a variable slot no binder has; an unknown constant;
\ 3. stack effects (every T{ }T checks the depth);
\ 4. whole runs: declarations in a row, a failure, then a fresh one;
\ 5. resources: the budget per declaration;
\ 6. state: after a failure the next declaration is as in a fresh run.
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
: same? ( a b -- flag ) lf-meta-eqv drop ;

\ ---- Stand-ins for synth.fs and instances.fs (see the header).
create spine 8 cells allot
: head-args ( t -- head n )   \ the spine's arguments into spine, last first
  0 begin over lf-term-app? while
    over lf-term-second@ over cells spine + ! 1+ swap lf-term-first@ swap repeat ;
: arg@ ( n i -- t ) - 1- cells spine + @ ;   \ argument i of n (from 0)
: cname ( c -- name ) lf-term-first@ lf-cref-slot lf-cref-name@ drop ;
: named? ( t c-addr u -- flag )
  rot dup lf-term-const? if cname -rot lfa-intern = else drop 2drop false then ;
: of-nat-answer ( n -- inst flag outcome )
  dup 0 arg@ lf-instantiate-mvars drop dup lf-mvar? if 2drop -1 false lf-meta-stuck exit then
  nat lf-meta-eqv drop 0= if drop -1 false outcome-ok exit then
  1 arg@ s" instOfNatNat" 0 cst swap app true outcome-ok ;
\ HAdd a b c: stuck while a or b is a metavariable; for Nat Nat the
\ instance, the out-parameter c made Nat by isDefEq (assignOutParams).
: nat? ( t -- flag ) lf-instantiate-mvars drop nat lf-meta-eqv drop ;
: mvar-arg? ( n i -- flag ) arg@ lf-instantiate-mvars drop lf-mvar? ;
: inst-hadd ( -- t ) 0 0 u! s" instHAdd" 1 cst nat app s" instAddNat" 0 cst app ;
: out-nat ( n -- inst flag outcome )
  2 arg@ nat lf-elab-defeq dup ok? 0= if nip -1 false rot exit then
  drop if inst-hadd true else -1 false then outcome-ok ;
: hadd-answer ( n -- inst flag outcome )
  dup 0 mvar-arg? over 1 mvar-arg? or if drop -1 false lf-meta-stuck exit then
  dup 0 arg@ nat? over 1 arg@ nat? and 0= if drop -1 false outcome-ok exit then out-nat ;
: stand-synth ( type -- inst flag outcome )
  head-args swap dup s" OfNat" named? if drop of-nat-answer exit then
  s" HAdd" named? if hadd-answer else drop -1 false outcome-ok then ;
' stand-synth is lf-meta-synth
: stand-class? ( type -- class true outcome | false outcome )
  head-args drop dup lf-term-const? 0= if drop false outcome-ok exit then
  lf-meta-const-decl 0= if false outcome-ok exit then
  dup elab-class-of if drop true outcome-ok else drop false outcome-ok then ;
' stand-class? is lf-elab-class?
create defs 16 cells allot  variable defs#
: def+ ( class j -- class ) 2dup elab-default@ 2drop = if defs#  @ cells defs + ! 1 defs# +!
  else drop then ;
: stand-defaults ( class -- addr n outcome )
  0 defs# ! elab-default elab-count 0 ?do i def+ loop drop defs defs# @ outcome-ok ;
' stand-defaults is lf-elab-default-instances
: no-defaults ( class -- addr n outcome ) drop defs 0 outcome-ok ;

\ ---- Running texts.
: nrun ( c-addr u -- outcome ) lf-author-begin lf-author-text ;
: err ( -- code line col ) lf-author-code lfa-error lfa-err-at @ lfa-pos> ;
: see-at ( -- line col ) lfa-error lfa-err-see @ lfa-pos> ;
: nfails ( c-addr u -- code line col ) nrun drop err ;
: decl0 ( -- decl ) lf-author-count begin 1- dup lfa-library? 0= until lf-author-decl ;
: ty ( -- t ) decl0 lf-fdecl-type @ ;
: va ( -- t ) decl0 lf-fdecl-value @ ;

\ ---- 1. Terms. 0 = 0: binrel% with no max type, both numerals pending,
\ then default instances in the statement's synthesis (instOfNatNat,
\ priority 100, after 1000 and 500 found none); by-rfl closes it.
T{ s" theorem z0 0 0 = := by by-rfl end z0" nrun -> outcome-ok }T
T{ ty 0 num 0 num eq-nat same? va lf-term-app? -> true true }T
\ The term proof 0 Eq.refl: finalize compares @Eq Nat (OfNat.ofNat ..)
\ with @Eq ?α (OfNat.ofNat ?T ..), a definition at both heads, which
\ needs lazy delta (S2 merge A; SWITCH: then ok, the value
\ @Eq.refl.{1} Nat (OfNat 0)): not supported yet, never another term.
T{ s" theorem z0b 0 0 = := 0 Eq.refl end z0b" nfails -> 139 1 32 }T
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

\ ---- 1. Lean's errors, each at end (or the tactic's word) with the
\ syntax's place as the second position.
\ failed to synthesize OfNat Bool 0 (the numeral at Bool, the max type).
T{ s" theorem e1 Bool.true 0 = := Bool.true Eq.refl end e1" nfails see-at
   -> 125 1 47 1 22 }T
\ typeclass instance problem is stuck: no default instance to fire; at
\ the newest pending numeral.
' no-defaults is lf-elab-default-instances
T{ s" theorem e2 0 0 = := 0 Eq.refl end e2" nfails see-at -> 126 1 31 1 14 }T
' stand-defaults is lf-elab-default-instances
\ numerals are data: 0 against the proposition Nat.zero = Nat.zero.
T{ s" theorem e3 Nat.zero Nat.zero = := 0 end e3" nfails see-at -> 127 1 37 1 35 }T
\ A coercion Lean would look for: Nat.zero = Bool.true (uncomparable,
\ CoeT not in the slice), then ensureHasType Nat Bool.true.
T{ s" theorem e4 Nat.zero Bool.true = := by by-sorry end e4" nfails see-at
   -> 131 1 48 1 31 }T
\ A recursor applied: elaborating as an eliminator (FE5).
T{ s" Nat.zero ' Nat.rec Nat.zero $ #check" nfails see-at -> 135 1 31 1 12 }T
\ #check of a constant alone: Lean prints its signature (FE2).
T{ s" Nat.zero #check" nfails see-at -> 137 1 10 1 1 }T
\ #check of a numeral with no default instance: a hole left (FE2).
' no-defaults is lf-elab-default-instances
T{ s" 0 #check" nfails see-at -> 137 1 3 1 1 }T
' stand-defaults is lf-elab-default-instances
\ 2 + 2 = 4 (C16): HAdd.hAdd's out-parameter ?γ := Nat needs outParam
\ unfolded (lazy delta, S2 merge A; SWITCH: then the term of C16): not
\ supported yet, never another term.
T{ s" theorem e5 2 2 + 4 = := by by-sorry end e5" nfails see-at -> 139 1 37 1 20 }T
\ The budget: three steps are not enough for a declaration (138), the
\ next declaration has the whole budget again.
T{ 3 lf-elab-fuel! s" theorem e6 Nat.zero Nat.zero = := by by-rfl end e6" nfails
   -> 138 1 45 }T
T{ lf-meta-default-budget lf-elab-fuel!
   s" theorem e7 Nat.zero Nat.zero = := by by-rfl end e7" nrun -> outcome-ok }T

\ ---- 2. Malformed and unknown: a variable no parameter gives; a name
\ the library lacks is the reader's (error 1, before elaboration).
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

\ ---- 7. Golden traces (FE1E 1.6) of C17, 0 + 0 = 0, and C1, 0 + n = n,
\ as far as they run before lazy delta (S2 merge A: SWITCH, then to their
\ ends, with synth.fs's own synthesis lines): pinned Lean's order of
\ events (tests/front/s1-c17.lean's trace: the three numerals' instance
\ problems stuck and resumed in each tree's round, then elabAppArgs of
\ HAdd.hAdd with ?α ?β ?γ ?self and the two operands, finalize's HAdd
\ problem stuck; C1: analyze's max type Nat, then hasHomogeneousInstance's
\ mkAppM, where outParam must unfold), each event a line.
: golden ( c-addr u -- c-addr' u' ) slurp-file ;
true lf-elab-trace!
T{ s" axiom c17 0 0 + 0 = end c17" nfails see-at -> 139 1 21 1 19 }T
T{ lf-elab-trace s" tests/front/s1-c17.trace" golden compare -> 0 }T
T{ s" axiom c1 Nat explicit: n 0 n + n = end c1" nfails see-at -> 139 1 36 1 34 }T
T{ lf-elab-trace s" tests/front/s1-c1.trace" golden compare -> 0 }T
false lf-elab-trace!

\ ---- 6. After every failure above, a fresh declaration elaborates as in
\ a fresh run; the stack is as it was.
T{ s" theorem z7 0 0 = := by by-rfl end z7" nrun ty 0 num 0 num eq-nat same?
   -> outcome-ok true }T
T{ depth -> 0 }T
cr .( elab.fs: all tests passed) cr
bye
