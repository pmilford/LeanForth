\ Unit tests of simp group 4, pass 2 (plan row FE9, docs/design/
\ TACTIC_SIMP.md; the plan .claude/work/briefs/simp-group-4-architect.md
\ sections 1 and 3): Lean's Step at the walk's pre and post steps
\ (src/front/simp/main.fs), the simproc interface and guards
\ (simp/simprocs.fs), the Core and Nat ports (simp/simprocs/core.fs,
\ nat.fs) and the default set's candidate loop (simp/default-set.fs),
\ over the simp slice and its format-4.1 data, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. interfaces: every port's name the data's, a slice simproc without a
\    port given its family's guard, a record whose phase or kind is not
\    its port's refused, a term of another head continue (reduceGT given
\    an LT.lt);
\ 2. outcomes: each port's done, visit and continue; each guard's
\    unsupported and continue; extra arguments put back;
\ 3. state: a nested walk (reduceIte's condition) inside a running
\    query; each query's candidates read from its own base and cut back;
\    the step counts of a post done and a pre visit pinned;
\ 4. resources: every heap allocation of a run with simprocs refused in
\    turn: full or the answer.
\ Nothing here accepts a theorem: only the kernel's check does.
include ../../../support/heap-watch.fs
require ../../../support/tester.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/simp-slice.ndjson" true lfc-library-open -> outcome-ok }T
lf-author-begin
T{ s" tests/front/simp-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
: made ( x outcome -- x ) ok? 0= abort" simp-procs: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: simp ( e -- e' h ) lf-simp-max-steps lf-simp ;
: thrown ( x xt -- outcome ) catch ?dup if nip lf-meta-outcome else 2drop outcome-ok then ;
: tried ( e p extra -- outcome )
  ['] lf-simproc-try catch ?dup if nip nip nip lf-meta-outcome else 2drop drop outcome-ok then ;
: stepped ( e post? -- e' h step ) lf-simp-procs ;
: refused ( e post? -- outcome )
  ['] stepped catch ?dup if nip nip lf-meta-outcome else 2drop drop outcome-ok then ;
: head? ( e c-addr u -- flag ) rot lf-meta-head -rot lf-meta-const-named? ;
: passed? ( e e' h step -- flag ) lf-simp-continue = swap lf-simp-none? and -rot = and ;
nat s" x" binder constant x0   nat s" y" binder constant y0
nat nat lf-term-pi lf-made! dup s" f" binder constant f0   s" g" binder constant g0
0 lf-term-sort lf-made! s" p" binder constant p0
s" Decidable" lf-mk-const0 p0 lf-mk-app s" hp" binder constant hp0
: lit# ( u -- e ) lf-meta-nat-lit made ;
: raw ( u -- e ) lf-nat-lit made ;
\ HOp.hOp Nat Nat Nat (instHOp Nat instOpNat) a b, Lean's elaborated form.
: nat3 ( c-addr u -- f ) 0 0 0 3 lf-mk-const nat lf-mk-app nat lf-mk-app nat lf-mk-app ;
: inst-h ( c-addr u c-addr2 u2 -- i )
  2>r 0 1 lf-mk-const nat lf-mk-app 2r> lf-mk-const0 lf-mk-app ;
: nat-op ( a b c-addr u i -- e ) >r nat3 r> lf-mk-app -rot 2 lf-mk-app-n ;
: +n ( a b -- e ) s" HAdd.hAdd" s" instHAdd" s" instAddNat" inst-h nat-op ;
: *n ( a b -- e ) s" HMul.hMul" s" instHMul" s" instMulNat" inst-h nat-op ;
: lt-like ( a b c-addr u -- e ) 0 1 lf-mk-const nat lf-mk-app s" instLTNat" lf-mk-const0
  lf-mk-app -rot 2 lf-mk-app-n ;
: ite-of ( c i t e -- ite )
  2>r 2>r s" ite" nat lf-level! lf-mk-const1 nat lf-mk-app 2r> 2 lf-mk-app-n 2r> 2 lf-mk-app-n ;
: ite ( c t e -- ite ) 2>r dup lf-mk-decide lf-term-second@ 2r> ite-of ;
: proc ( c-addr u -- p )   \ the slice's simproc record of a name
  simp-proc-count 0 do 2dup i simp-proc-name compare 0= if 2drop i unloop exit then loop
  2drop -1 ;
: cands# ( e post? -- n ) ds-cands >r ds-out slab-cut drop r> ;
lf-simp-default

\ ---- 1. Interfaces. The ports' names are the data's (each found); a
\ simproc without one gets its family's guard (the literal families' or,
\ for others, unsupported wherever its keys match).
: port? ( p -- flag ) sp-entry 0<> ;
: ported# ( -- n ) 0 simp-proc-count 0 do i port? - loop ;
T{ s" reduceIte" proc port? s" Nat.reduceAdd" proc port? s" Nat.reduceEqDiff" proc port?
   s" reduceCtorEq" proc port? s" Int.reduceAdd" proc port? -> true true true true false }T
T{ s" Int.reduceAdd" proc sp-family ' sp-lit-guard = s" Array.reduceGetElem" proc sp-family
   ' sp-crude = s" UInt8.reduceEq" proc sp-family ' sp-lit-guard = -> true true true }T
T{ ported# -> 22 }T
\ A record whose phase or kind is not its port's: unsupported (data of
\ another Lean); its flags put back.
: add-p ( -- p ) s" Nat.reduceAdd" proc ;
: two+three ( -- e ) 2 lit# 3 lit# +n ;
false add-p ssp ssp-post !
T{ two+three add-p 0 tried -> outcome-unsupported }T
true add-p ssp ssp-post !  false add-p ssp ssp-dsimproc !
T{ two+three add-p 0 tried -> outcome-unsupported }T
true add-p ssp ssp-dsimproc !
T{ two+three add-p 0 lf-simproc-try rot drop -> lf-simp-none lf-simp-done }T
\ Another head than the port's continues: Nat.reduceGT given 2 < 3 (an
\ LT.lt term, as GT.gt's keys are LT.lt's).
: 2<3 ( -- e ) 2 lit# 3 lit# s" LT.lt" lt-like ;
T{ 2<3 dup s" Nat.reduceGT" proc 0 lf-simproc-try passed? -> true }T

\ ---- 2. The Nat ports: done with the operation's literal (mkNatLit's
\ term), no proof; an operand with no lit-value continue.
: lit-value ( e -- u ) dup s" OfNat.ofNat" head? 0= abort" no literal" 1 3 lf-meta-nth-arg lf-lit-cell ;
: folded ( e -- u ) true stepped lf-simp-done <> abort" not done" drop lit-value ;
T{ two+three folded 7 lit# 6 lit# *n folded 2 raw 3 raw +n folded -> 5 42 5 }T
T{ x0 3 lit# +n dup true stepped passed? -> true }T
\ Each operation of the table (Nat.lean:63-104), through its port (the
\ instance argument, which the ports do not read, Nat itself here).
: done-value ( e' h step -- u ) lf-simp-done <> abort" not done" drop lit-value ;
: tried-on ( e c-addr u -- u ) proc 0 lf-simproc-try done-value ;
\ A port whose record the slice lacks (its root's constant), by its entry.
: ported-on ( e c-addr u -- u ) sp-ports name-table-find sp-call done-value ;
: nat-bin ( u1 u2 c-addr u -- e ) 2>r lit# swap lit# swap 2r> nat3 nat lf-mk-app -rot 2 lf-mk-app-n ;
T{ 17 5 s" HSub.hSub" nat-bin s" Nat.reduceSub" tried-on 17 5 s" HDiv.hDiv" nat-bin s" Nat.reduceDiv" tried-on
   17 5 s" HMod.hMod" nat-bin s" Nat.reduceMod" tried-on -> 12 3 2 }T
T{ 12 10 s" HAnd.hAnd" nat-bin s" Nat.reduceAnd" ported-on
   12 10 s" HOr.hOr" nat-bin s" Nat.reduceOr" ported-on
   12 10 s" HXor.hXor" nat-bin s" Nat.reduceXor" ported-on -> 8 14 6 }T
T{ 3 2 s" HShiftLeft.hShiftLeft" nat-bin s" Nat.reduceShiftLeft" ported-on
   12 2 s" HShiftRight.hShiftRight" nat-bin s" Nat.reduceShiftRight" ported-on -> 12 3 }T
T{ 2 10 s" HPow.hPow" nat-bin s" Nat.reducePow" tried-on -> 1024 }T
\ An exponent above exponentiation.threshold (256): continue, as
\ checkExponent answers.
T{ 2 300 s" HPow.hPow" nat-bin dup s" Nat.reducePow" proc 0 lf-simproc-try passed? -> true }T
: gcd ( u1 u2 -- e ) lit# swap lit# swap s" Nat.gcd" lf-mk-const0 -rot 2 lf-mk-app-n ;
T{ 12 18 gcd s" Nat.reduceGcd" tried-on -> 6 }T
: succ ( u -- e ) lit# s" Nat.succ" lf-mk-const0 swap lf-mk-app ;
T{ 41 succ s" Nat.reduceSucc" tried-on -> 42 }T
T{ x0 s" Nat.succ" lf-mk-const0 swap lf-mk-app dup s" Nat.reduceSucc" proc 0 lf-simproc-try
   passed? -> true }T
\ BEq and bne: a Bool constant, done, no proof.
: beq ( u1 u2 c-addr u -- e ) 2>r lit# swap lit# swap 2r> 0 1 lf-mk-const nat lf-mk-app
  s" instBEqOfDecidableEq" 0 1 lf-mk-const nat lf-mk-app s" instDecidableEqNat" lf-mk-const0
  lf-mk-app lf-mk-app -rot 2 lf-mk-app-n ;
: booled ( e c-addr u -- e' flag ) sp-ports name-table-find sp-call lf-simp-done = nip ;
T{ 2 3 s" BEq.beq" beq s" Nat.reduceBEq" booled swap s" Bool.false" head? -> true true }T
T{ 2 3 s" bne" beq s" Nat.reduceBNe" booled swap s" Bool.true" head? -> true true }T
T{ 3 3 s" bne" beq s" Nat.reduceBNe" booled swap s" Bool.false" head? -> true true }T
\ evalPropStep: True by eq_true_of_decide p d (Eq.refl true), done.
T{ s" True" lf-mk-const0 true lf-simp-eval-prop lf-simp-done = swap s" eq_true_of_decide" head?
   rot s" True" head? -> true true true }T
T{ s" True" lf-mk-const0 false lf-simp-eval-prop drop s" eq_false_of_decide" head?
   swap s" False" head? -> true true }T

\ ---- 2. The Core ports, in the walk (their condition's nested simp
\ needs one). reduceIte: True and False choose a branch with
\ ite_eq_left_of_eq_true / ite_eq_right_of_eq_false applied to the five
\ arguments and the condition's proof (Eq.refl when none); visit.
: true-c ( -- e ) s" True" lf-mk-const0 ;   : false-c ( -- e ) s" False" lf-mk-const0 ;
T{ true-c x0 y0 ite simp s" ite_eq_left_of_eq_true" head? -> x0 true }T
T{ false-c x0 y0 ite simp s" ite_eq_right_of_eq_false" head? -> y0 true }T
\ The proof's last argument: Eq.refl True for a condition with no proof.
T{ true-c x0 y0 ite simp nip lf-term-second@ s" Eq.refl" head? -> true }T
\ A condition the nested walk simplifies: 2 + 3 = 5 is True by
\ Nat.reduceAdd and eq_self, its proof the branch's.
: cond5 ( -- e ) two+three 5 lit# lf-mk-eq ;
T{ cond5 x0 y0 ite simp nip lf-term-second@ s" eq_self" head? -> true }T
\ A condition left as it is (a Prop variable): reduceIte, then
\ dreduceIte (outside dsimp) continue; the ite is left (ite_congr).
T{ p0 hp0 x0 y0 ite-of ' simp thrown -> outcome-ok }T
\ Extra arguments (getMatchWithExtra): (if True then f else g) x is
\ reduceIte's with x put back, its proof through mkCongrFun's general
\ build, which answers unsupported until plan SL1b (app-builder.fs).
: nat>nat ( -- t ) nat nat lf-term-pi lf-made! ;
: fun-ite ( -- e ) s" ite" nat>nat lf-level! lf-mk-const1 nat>nat lf-mk-app true-c lf-mk-app
  s" instDecidableTrue" lf-mk-const0 lf-mk-app f0 lf-mk-app g0 lf-mk-app ;
T{ fun-ite x0 lf-mk-app ' simp thrown -> outcome-unsupported }T
\ reduceDIte: (fun h => x) (of_eq_true True pr), head-beta reduced to x.
: dite-tt ( -- e ) s" dite" nat lf-level! lf-mk-const1 nat lf-mk-app true-c lf-mk-app
  s" instDecidableTrue" lf-mk-const0 lf-mk-app ;
create h-cell 0 ,
: k-of ( prop v -- lam ) swap s" h" binder h-cell ! h-cell 1 lf-mk-lambda-fvars ;
: not-tt ( -- e ) s" Not" lf-mk-const0 true-c lf-mk-app ;
: dite-x ( -- e ) dite-tt true-c x0 k-of lf-mk-app not-tt y0 k-of lf-mk-app ;
T{ dite-x simp s" dite_eq_left_of_eq_true" head? -> x0 true }T

\ ---- 2. Guards. Nat's Diff family: both sides offsets (a literal, an
\ addition of one, Nat.succ) unsupported; else continue.
: diff ( a b -- outcome ) lf-mk-eq s" Nat.reduceEqDiff" proc 0 tried ;
T{ x0 1 lit# +n 3 lit# diff x0 3 lit# diff x0 y0 +n 3 lit# diff 2 lit# 3 lit# diff
   -> outcome-unsupported outcome-ok outcome-ok outcome-unsupported }T
\ reduceCtorEq: constructors of different names unsupported; the same,
\ or a side with none, continue.
: ctor ( a b -- outcome ) lf-mk-eq s" reduceCtorEq" proc 0 tried ;
T{ x0 1 lit# +n 0 raw ctor x0 0 lit# ctor x0 1 lit# +n y0 1 lit# +n ctor 0 raw 0 raw ctor
   -> outcome-unsupported outcome-ok outcome-ok outcome-ok }T
T{ 2 lit# 3 lit# ctor 1 raw 0 raw ctor -> outcome-unsupported outcome-unsupported }T
\ The literal families' guard: every explicit operand a literal's form
\ unsupported; one that is none continue.
: int-add ( a b -- outcome ) +n s" Int.reduceAdd" proc 0 tried ;
T{ 2 lit# 3 lit# int-add x0 3 lit# int-add -> outcome-unsupported outcome-ok }T
\ Others, unsupported wherever their keys match.
T{ x0 x0 lf-mk-eq s" Char.Nat.reduceEqDigitChar" proc 0 tried
   x0 s" Char.Nat.reduceEqDigitChar" proc 0 tried -> outcome-unsupported outcome-ok }T
T{ x0 s" Array.reduceGetElem" proc 0 tried -> outcome-unsupported }T

\ ---- 3. The walk's steps: a post done (Nat.reduceAdd) is cached as it
\ is, a pre visit (reduceIte) simplified again; the counts pinned.
T{ two+three simp swap lit-value lf-simp-steps -> lf-simp-none 5 4 }T
T{ true-c x0 y0 ite simp drop lf-simp-steps -> x0 3 }T
\ A visit's result simplified again from its pre step: the inner ite is
\ reduceIte's too.
T{ true-c true-c x0 y0 ite y0 ite simp drop lf-simp-steps -> x0 5 }T
\ Each query reads its candidates from its own base and cuts back: a
\ candidate left below by hand (reduceIte's) is not 2 + 3's.
: fake ( -- ) s" reduceIte" proc ds-out slab-push drop 0 ds-out slab-push drop ;
ds-out slab-clear
T{ ds-out slab-count fake ds-out slab-count -> 0 2 }T
T{ two+three true stepped nip nip ds-out slab-count -> lf-simp-done 2 }T
ds-out slab-clear
T{ two+three true cands# x0 true cands# -> 1 0 }T
\ dsimp's question: a dsimproc candidate (none of a variable's).
T{ x0 false lf-simp-dprocs? x0 true lf-simp-dprocs? -> false false }T

\ ---- 4. Every heap allocation of a run with simprocs refused in turn:
\ full or the answer (if 2 + 3 = 5 then x else y is x).
: simp-pass ( e -- e' outcome )
  ['] simp catch ?dup 0= if drop outcome-ok exit then
  nip -1 swap dup lf-meta-thrown? 0= if throw then lf-meta-outcome ;
: slabs-anew ( -- )
  sm-acts sweep-slab-anew sr-frames sweep-slab-anew sr-cands sweep-slab-anew
  sr-xs sweep-slab-anew ds-out sweep-slab-anew simp-thms sweep-slab-anew ;
: procs-pass ( e -- e' outcome ) lf-simp-default simp-pass ;
' slabs-anew sweep-slabs-xt !
T{ cond5 x0 y0 ite ' procs-pass heap-sweep nip -> 0 }T
' noop sweep-slabs-xt !

.( simp-procs test.fs: all tests passed) cr
bye
