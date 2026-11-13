\ The Meta layer's view of the library while a text runs (plan S1,
\ docs/design/S1_INTERFACE.md §1, §2 and §4; src/front/meta-env.fs's run
\ mode, src/front/lib-decode.fs, infer.fs's lf-meta-dec-level, the
\ instance-typed flag and the synthesis hooks), by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. S1's stand-in through the command line and the kernel (§11 row 2):
\    0 + 0 = 0 closed by by-rfl and accepted, 0 + 0 = 1 refused with 97
\    and Lean's text, nothing checked; the run mode left afterwards;
\ 2. every outcome of lf-menv-find and lf-libdec-decl: a library
\    declaration decoded (kind, name, parameters, type, value, hint,
\    inductive data of a type, a constructor and a recursor), the same
\    record again (memo), a text declaration found (lf-menv-add), an
\    unknown or invalid name, a number beyond the library; facts without
\    data unsupported; binder kinds of a library and a text declaration;
\    getDecLevel's every case; the instance-typed flag and its rollback;
\ 3. stack effects (every T{ }T checks the depth);
\ 4. lf-menv-reset and a new run's reset stores forget everything;
\ 5. the heap refusing each allocation of a decode in turn: never ok
\    before the last, full each time, then decoded.
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
' s1-true stating
T{ s" tests/front/09-zero-add-rfl.lf" check outcome-ok tally cli-not-proved @ lf-libdec-count
   -> 0 438 0 0 }T
' s1-false stating
T{ s" tests/front/10-zero-add-wrong.lf" check lf-author-code lf-libdec-stage -> 4 97 0 }T
T{ detail s\"   0 + 0\nis not definitionally equal to the right-hand side\n  1\n\n⊢ 0 + 0 = 1"
   compare -> 0 }T

\ ---- 2. The run mode over the slice (lfc-library-open), no data read.
\ The stores given a text run's room (lfc-rooms, as check-lf.fs does).
T{ library true lfc-library-open lfc-rooms -> outcome-ok outcome-ok }T
lf-author-begin
: nm ( c-addr u -- name ) lfa-intern ;
: d-of ( c-addr u -- d ) nm lf-menv-find made ;
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
create fake /lf-fdecl allot
: pi-kinded ( -- t )
  nat nat lf-term-pi 0= abort" pi" dup s" a" nm 1 lf-pres-binder! made
  nat swap lf-term-pi 0= abort" pi" dup s" b" nm 3 lf-pres-binder! made ;
: fake! ( -- )
  fake /lf-fdecl erase lf-decl-def fake lf-fdecl-kind ! s" yy" nm fake lf-fdecl-name !
  pi-kinded fake lf-fdecl-type ! nat fake lf-fdecl-value ! ;
: two-kinds ( d -- k0 k1 n ) lf-menv-kinds >r dup @ swap cell+ @ r> ;
T{ fake! fake lf-menv-add s" yy" d-of two-kinds -> outcome-ok 3 1 2 }T
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

\ ---- 5. The heap refusing each allocation of a decode in turn.
: decode-at ( k -- outcome )
  ck-stage lf-menv-library! heap-refusals ! s" Nat.rec" nm lf-menv-find nip 0 heap-refusals ! ;
variable worst
: refusal-ok? ( outcome -- flag ) dup ok? swap outcome-full = or ;
: each-refused ( -- k )
  0 begin 1+ dup decode-at dup refusal-ok? 0= if dup worst ! then ok? until ;
T{ outcome-ok worst ! each-refused 1 > worst @ -> true outcome-ok }T
T{ lfc-library-close lf-libdec-count lfc-empty lfc-rooms-back -> 0 outcome-ok }T
T{ depth -> 0 }T
cr .( menv-run.fs: all tests passed) cr
