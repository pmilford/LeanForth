\ Unit tests of simp group 4, pass 2 (plan row FE9, docs/design/
\ TACTIC_SIMP.md; the plan .claude/work/briefs/simp-group-4-architect.md
\ sections 1 and 3): Lean's Step at the walk's pre and post steps
\ (src/front/simp/main.fs), the simproc interface and guards
\ (simp/simprocs.fs), the Core and Nat ports (simp/simprocs/core.fs,
\ nat.fs) and the default set's candidate loop (simp/default-set.fs),
\ over the simp slice and its format-4.1 data, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. interfaces: every simproc of the slice and of Init's default set
\    (tests/front/simp-data/init-simprocs.fs) one row of its phase and
\    kind (a port, a named guard, or simprocs/guards.fs's table), a name
\    with no row unsupported, a record whose phase or kind is not its
\    row's refused, a term of another head continue (reduceGT given an
\    LT.lt);
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
: c0 ( c-addr u -- e ) lf-mk-const0 ;
: cands# ( e post? -- n ) ds-cands >r ds-out slab-cut drop r> ;
lf-simp-default

\ ---- 1. Interfaces. Every simproc has a row by its name (review B1):
\ the slice's, and each of Init's 341 with its phase and kind, and no
\ row for another name.
: port? ( p -- flag ) sp-entry 0<> ;
: ported# ( -- n ) 0 simp-proc-count 0 do i port? - loop ;
T{ s" reduceIte" proc port? s" Nat.reduceAdd" proc port? s" Nat.reduceEqDiff" proc port?
   s" reduceCtorEq" proc port? s" Int.reduceAdd" proc port? -> true true true true true }T
T{ ported# -> simp-proc-count }T
: row-xt ( c-addr u -- xt ) sp-ports name-table-find sp-data sp-xt @ ;
T{ s" Int.reduceAdd" row-xt ' sp-lit-port = s" Array.reduceGetElem" row-xt ' sp-crude-port =
   s" UInt8.reduceEq" row-xt ' sp-lit-port = s" List.reduceReplicate" row-xt ' sp-crude-port =
   -> true true true true }T
T{ s" BitVec.reduceShiftLeftShiftLeft" row-xt s" BitVec.reduceShiftRightShiftRight" row-xt
   s" BitVec.reduceHShiftLeft'" row-xt s" BitVec.reduceHShiftRight'" row-xt
   -> ' sp-crude-port dup 2dup }T
variable rows-seen  variable rows-bad  variable rows-laid
: row-fits? ( entry c-addr u c-addr2 u2 -- flag )   \ the phase and kind as written
  s" d" compare 0= >r s" pre" compare 0= swap sp-data dup sp-pre @ rot = swap sp-dsimp @ r> = and ;
: init-simproc: ( "name" "phase" "kind" -- )
  1 rows-seen +!  parse-name sp-ports name-table-find parse-name parse-name 2>r 2>r
  ?dup if 2r> 2r> row-fits? else 2r> 2r> 2drop 2drop false then 0= negate rows-bad +! ;
include ../../simp-data/init-simprocs.fs
: laid+ ( entry -- ) drop 1 rows-laid +! ;
sp-ports ' laid+ name-table-each
T{ rows-bad @ rows-seen @ rows-laid @ -> 0 341 341 }T
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
\ A name with no row (another Lean's simproc): unsupported wherever its
\ keys match (Nat.reduceAdd's record read as Nat.reduceAd).
add-p constant add-r   -1 add-r ssp ssp-name-u +!
T{ add-r simp-proc-name s" Nat.reduceAd" compare x0 3 lit# +n add-r 0 tried
   -> 0 outcome-unsupported }T
1 add-r ssp ssp-name-u +!
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
\ An operand with no value: the second (2 + x), an OfNat of another type.
: of-bool ( -- e ) s" OfNat.ofNat" 0 1 lf-mk-const s" Bool" c0 lf-mk-app 2 raw lf-mk-app x0 lf-mk-app ;
T{ 2 lit# x0 +n dup true stepped passed? of-bool 3 lit# +n dup true stepped passed? -> true true }T
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
: pow-x ( -- e ) s" HPow.hPow" nat3 nat lf-mk-app x0 2 lit# 2 lf-mk-app-n ;
T{ pow-x dup s" Nat.reducePow" proc 0 lf-simproc-try passed? -> true }T
\ reduceLT and reduceGT: no value continue; on numerals evalPropStep:
\ True or False, done, by eq_true_of_decide or eq_false_of_decide.
: gt-like ( a b -- e ) s" GT.gt" lt-like ;
: lt-tried ( e c-addr u -- outcome ) proc 0 tried ;
T{ x0 3 lit# s" LT.lt" lt-like s" Nat.reduceLT" lt-tried x0 3 lit# gt-like s" Nat.reduceGT" lt-tried
   -> outcome-ok outcome-ok }T
: lt-decided ( e c-addr u -- e' flag )
  proc 0 lf-simproc-try lf-simp-done = swap s" eq_true_of_decide" head? and ;
T{ 2<3 s" Nat.reduceLT" lt-decided swap s" True" head? -> true true }T
T{ 3 lit# 2 lit# gt-like s" Nat.reduceGT" lt-decided swap s" True" head? -> true true }T
T{ 3 lit# 2 lit# s" LT.lt" lt-like s" Nat.reduceLT" proc 0 lf-simproc-try drop
   s" eq_false_of_decide" head? swap s" False" head? -> true true }T
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
\ Its False branch (review M1): (fun h => y) (of_eq_false False pr), y, by
\ dite_eq_right_of_eq_false.
: dite-ff ( -- e ) s" dite" nat lf-level! lf-mk-const1 nat lf-mk-app false-c lf-mk-app
  s" instDecidableFalse" lf-mk-const0 lf-mk-app ;
: not-ff ( -- e ) s" Not" lf-mk-const0 false-c lf-mk-app ;
: dite-y ( -- e ) dite-ff false-c x0 k-of lf-mk-app not-ff y0 k-of lf-mk-app ;
T{ dite-y simp s" dite_eq_right_of_eq_false" head? -> y0 true }T
\ A branch that uses its hypothesis (dite Prop False _ (fun h => True)
\ (fun h => h = h)): reduceDIte gives h = h at h := of_eq_false False pr,
\ which the walk does not simplify yet (congruence over a proof): not
\ supported (review M1; plan 9.4.8z14).
: prop-t ( -- t ) 0 lf-term-sort lf-made! ;
not-ff s" hn" binder constant hn0
not-ff prop-t lf-term-pi lf-made! s" q" binder constant q0
: lam1 ( body fvar -- lam ) h-cell ! h-cell 1 lf-mk-lambda-fvars ;
: level1 ( -- u ) 0 lf-level-succ 0= abort" level" ;
: dite-p ( -- e ) s" dite" level1 lf-mk-const1 prop-t lf-mk-app false-c lf-mk-app
  s" instDecidableFalse" lf-mk-const0 lf-mk-app false-c true-c k-of lf-mk-app
  hn0 hn0 lf-mk-eq hn0 lam1 lf-mk-app ;
T{ dite-p ' simp thrown -> outcome-unsupported }T

\ ---- 2. Guards. Nat's Diff family: both sides offsets (a literal, an
\ addition of one, Nat.succ) unsupported; else continue.
: diff ( a b -- outcome ) lf-mk-eq s" Nat.reduceEqDiff" proc 0 tried ;
T{ x0 1 lit# +n 3 lit# diff x0 3 lit# diff x0 y0 +n 3 lit# diff 2 lit# 3 lit# diff
   -> outcome-unsupported outcome-ok outcome-ok outcome-unsupported }T
\ Nat.succ x is an offset too (NatOffset.fromExpr?, Nat.lean:168; review M1).
T{ s" Nat.succ" c0 x0 lf-mk-app 3 lit# diff -> outcome-unsupported }T
\ reduceCtorEq: constructors of different names unsupported; the same,
\ or a side with none, continue.
: ctor ( a b -- outcome ) lf-mk-eq s" reduceCtorEq" proc 0 tried ;
T{ x0 1 lit# +n 0 raw ctor x0 0 lit# ctor x0 1 lit# +n y0 1 lit# +n ctor 0 raw 0 raw ctor
   -> outcome-unsupported outcome-ok outcome-ok outcome-ok }T
T{ 2 lit# 3 lit# ctor 1 raw 0 raw ctor -> outcome-unsupported outcome-unsupported }T
\ A side whose head is no constructor but whose whnf is one (constructorApp'?'s
\ whnf, CtorRecognizer.lean:97; review M1): (fun h => Nat.zero) x beside an
\ offset, unsupported.
T{ x0 1 lit# +n nat s" Nat.zero" c0 k-of x0 lf-mk-app ctor -> outcome-unsupported }T
\ A constructor at the head: Nat.zero beside an offset (unsupported),
\ Nat.succ itself on both sides, Bool's two constructors (unsupported).
T{ s" Nat.zero" c0 x0 1 lit# +n ctor s" Nat.succ" c0 dup ctor s" Bool.true" c0 s" Bool.false" c0 ctor
   -> outcome-unsupported outcome-ok outcome-unsupported }T
\ The literal families' guard: every explicit operand a literal's form
\ unsupported; one that is none continue.
: int-add ( a b -- outcome ) +n s" Int.reduceAdd" proc 0 tried ;
T{ 2 lit# 3 lit# int-add x0 3 lit# int-add -> outcome-unsupported outcome-ok }T
T{ 2 raw 3 raw int-add -> outcome-unsupported }T
\ An argument beyond its head's parameters (x applied to y): checked.
T{ x0 y0 lf-mk-app dup sp-lit-guard passed? -> true }T
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
T{ two+three true lf-simp-dprocs? 2<3 true lf-simp-dprocs? -> true false }T
\ The dsimp guard refuses a node a dsimproc could change (a stand-in
\ hook answering yes), and a pre simproc's done is cached as it is (a
\ stand-in answering y for every term at its pre step).
: yes ( e post? -- flag ) 2drop true ;
: pre-y ( e post? -- e' h step ) if lf-simp-pass else drop y0 lf-simp-none lf-simp-done then ;
' yes is lf-simp-dprocs?
T{ x0 sm-kept? -> false }T
' ds-dprocs-run is lf-simp-dprocs?   ' pre-y is lf-simp-procs
T{ x0 simp lf-simp-steps -> y0 lf-simp-none 1 }T
' ds-procs-run is lf-simp-procs
\ The dsimp scan (pass 3): every node of an argument dsimp would visit.
\ Kept: f (g x) (variables applied), a numeral (its raw literal not
\ visited, doNotVisitOfNat), Nat; refused: 2 + 3 (Nat.reduceAdd, a
\ dsimproc, at the top), f (2 + 3) (at a part), a raw literal (folded
\ by dsimpReduce), a lambda, an application of a lambda (beta), f x
\ with too many nodes to scan.
: f(g(x)) ( -- e ) f0 g0 x0 lf-mk-app lf-mk-app ;
create x-cell x0 ,
: lam-x ( -- e ) x0 x-cell 1 lf-mk-lambda-fvars ;
T{ f(g(x)) sm-kept? 7 lit# sm-kept? nat sm-kept? -> true true true }T
T{ two+three sm-kept? f0 two+three lf-mk-app sm-kept? 7 raw sm-kept? -> false false false }T
T{ lam-x sm-kept? lam-x x0 lf-mk-app sm-kept? -> false false }T
\ A recursor's application (iota) and a string literal refused.
: str-ab ( -- e ) s" ab" lf-str-new made drop ;
T{ s" Nat.rec" 0 lf-mk-const1 x0 lf-mk-app sm-kept? str-ab sm-kept? -> false false }T
: deep ( n -- e ) x0 swap 0 ?do f0 swap lf-mk-app loop ;
T{ 30 deep sm-kept? 70 deep sm-kept? -> true false }T
\ A set that is not the default one: no simprocs.
lf-simp-set-new
T{ two+three dup true lf-simp-procs passed? two+three true lf-simp-dprocs? -> true false }T
lf-simp-default

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

\ ---- The dsimp scan's tests and a rewrite's cut (review M1): a node a
\ post rfl lemma matches (Nat.add_zero, rfl and post) is not free of rfl
\ candidates; a left-out lemma may be rfl (its proof is not known); a
\ rule's metavariables (sr-xs) are cut back once its rewrite is done.
lf-simp-default
T{ x0 0 lit# +n sm-rfl-free? -1 sth-v-rfl -> false true }T
T{ x0 0 lit# +n simp 2drop sr-xs slab-count -> 0 }T

\ ---- 5. Sealed (review B3), last, as a context made seals the table
\ for the rest of the run: a row then aborts, the table unchanged (as
\ the tactic registry's rows, tactic-run.fs's lfr-open).
: late-row ( -- ior ) s" sp-lit-d: Late.simproc" ['] evaluate catch dup if nip nip then ;
context-new throw constant sealed-context
0 rows-laid !  sp-ports ' laid+ name-table-each
T{ context-sealed? late-row s" Late.simproc" sp-ports name-table-find rows-laid @
   -> true -2 0 341 }T

.( simp-procs test.fs: all tests passed) cr
bye
