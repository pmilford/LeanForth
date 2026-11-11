\ Definite rejection (ADR 0011; plan task 2.2.1): the level computations
\ (witness evaluation, normalizes_to_zero, rule D1), the fuel an undecided
\ comparison keeps for the analysis, the head kinds of reduced terms, the
\ rules of inference (F1, S2, D1-D5) and of the probes (S1, S3, D1-D5 for
\ the declaration), each with the cases where it must not apply (K1-K4),
\ and the analysis's own bookkeeping: it only ever turns unknown into
\ rejected, leaves the arena, binder context and aside flag as it found
\ them, and stays unknown when it runs out of fuel, room or frames. The
\ table cases of docs/reviews/FIRST_CHECKER_EXPECTED.md are compared with
\ pinned Lean by make test-first-checker-differential; the rejections here
\ are those of the same rules, each noted with Lean's exception.
\ Test-only; nothing here accepts a theorem.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/main.fs
include ../support/plain-terms.fs

\ ---------------------------------------------------------------------------
\ Levels. fresh-session: 0 zero, 1-4 succ^n zero, level-u and level-v, both
\ parameters in the context.
fresh-session
: next-level ( level -- level' ) lf-level-succ must ;
: max-of ( a b -- level ) lf-level-max must ;
: imax-of ( a b -- level ) lf-level-imax must ;
: witness ( root w -- value status ) 1000 swap lf-level-value-witness ;
T{ level-u -1 witness -> 1 outcome-ok }T
T{ level-u 0 witness -> 0 outcome-ok }T
T{ level-u u-name witness -> 1 outcome-ok }T
T{ level-u v-name witness -> 0 outcome-ok }T
level-u level-v imax-of constant imax-uv
T{ imax-uv u-name witness -> 0 outcome-ok }T
T{ imax-uv v-name witness -> 1 outcome-ok }T
\ The other modes are unchanged afterwards: free parameters stay symbolic.
T{ level-u 1000 lf-level-value -> -1 outcome-unknown }T
\ Failures leave no fuel: a parameter outside the context, too little fuel.
0 s" w" lf-name-str must lf-level-param must constant level-w
T{ 7 lf-lvalue-fuel ! level-w -1 witness lf-lvalue-fuel @ -> -1 outcome-invalid 0 }T
T{ 7 lf-lvalue-fuel ! imax-uv 2 -1 lf-level-value-witness lf-lvalue-fuel @
  -> -1 outcome-exhausted 0 }T
T{ imax-uv -1 -1 lf-level-value-witness -> -1 outcome-invalid }T

\ normalizes_to_zero: zero, max of zeros, imax with a zero right side.
: zero? ( root -- flag status ) 1000 lf-level-zero? ;
T{ 0 zero? -> true outcome-ok }T
T{ 1 zero? -> false outcome-ok }T
T{ level-u zero? -> false outcome-ok }T
T{ level-u 0 imax-of zero? -> true outcome-ok }T
T{ 0 level-u imax-of zero? -> false outcome-ok }T
T{ 0 level-u 0 imax-of max-of zero? -> true outcome-ok }T
T{ level-w zero? -> false outcome-invalid }T
T{ imax-uv 1 lf-level-zero? -> false outcome-exhausted }T

\ Witnesses: some assignment gives different values (rule D1 before ADR
\ 0011 Amendment 1; D1 is now Lean's is_equivalent false,
\ lf-level-inequivalent?, and the witnesses check it below).
: apart? ( a b -- flag status ) 1000 lf-level-apart? ;
T{ level-u dup next-level apart? -> true outcome-ok }T
T{ level-u level-v apart? -> true outcome-ok }T
T{ 1 2 apart? -> true outcome-ok }T
T{ level-u dup dup max-of apart? -> false outcome-ok }T
T{ level-u level-v max-of level-v level-u max-of apart? -> false outcome-ok }T
T{ 0 level-u 0 imax-of apart? -> false outcome-ok }T
T{ level-u level-w apart? -> false outcome-invalid }T
T{ level-u level-v -1 lf-level-apart? -> false outcome-invalid }T
T{ level-u level-v 2 lf-level-apart? lf-lvalue-fuel @ -> false outcome-exhausted 0 }T

\ Random levels against independent models: normalizes_to_zero exactly as
\ Lean writes it (level.cpp 174-187), and evaluation under the witnesses
\ (every parameter 0; u alone 1; v alone 1). The witnesses must agree
\ with the models; D1 must hold whenever a witness tells two levels apart
\ (Lean's normalize keeps values) and never for two levels level-compare
\ finds equal.
variable level-seed
: level-rnd ( n -- u )
  level-seed @ 1103515245 * 12345 + dup level-seed ! 16 rshift 32767 and swap mod ;
: lean-nz? ( level -- flag )
  lf-level-read must rot case
    lf-level-tag-zero of 2drop true endof
    lf-level-tag-max of recurse if recurse else drop false then endof
    lf-level-tag-imax of nip recurse endof
    >r 2drop false r> endcase ;
: model ( level w -- n )
  >r lf-level-read must rot case
    lf-level-tag-zero of 2drop r> drop 0 endof
    lf-level-tag-succ of drop r> recurse 1+ endof
    lf-level-tag-param of drop r> = 1 and endof
    lf-level-tag-max of r@ recurse swap r> recurse max endof
    lf-level-tag-imax of r@ recurse swap r> recurse
      swap dup 0= if nip else max then endof
    true abort" level tag" endcase ;
: differ? ( a b w -- flag ) tuck model >r model r> <> ;
: model-apart? ( a b -- flag )
  2dup 0 differ? >r 2dup u-name differ? >r v-name differ? r> or r> or ;
: some-level ( -- level ) lf-level-count @ level-rnd ;
: grow ( -- )
  3 level-rnd case 0 of some-level lf-level-succ endof
    1 of some-level some-level lf-level-max endof
    drop some-level some-level lf-level-imax 0 endcase 2drop ;
\ Levels are hash-consed (compact-store plan step S4): a level grown equal
\ to an existing one adds none, so a round tries a bounded number of times.
: grow-levels ( -- )
  1000 0 do lf-level-count @ lf-level-capacity < 0= if leave then grow loop ;
\ A shared DAG can stand for a tree too large for the fuel given: such a
\ level is exhausted and skipped (the models would take as long).
variable model-checks
: check-zero ( level -- )
  dup zero? ok? if swap lean-nz? <> abort" normalizes_to_zero" 1 model-checks +!
  else 2drop then ;
: check-d1 ( a b witness-apart -- )
  >r 2dup 10000 lf-level-inequivalent? ok? 0= if 2drop drop r> drop exit then
  dup 0= r> and abort" a witness tells them apart, is_equivalent holds"
  -rot 10000 lf-level-compare ok? and abort" D1 but equal" ;
: check-apart ( a b -- )
  2dup apart? ok? 0= if drop 2drop exit then
  >r 2dup model-apart? r@ <> abort" witness model"
  r> check-d1 1 model-checks +! ;
: model-round ( seed -- )
  level-seed ! fresh-session grow-levels
  lf-level-count @ 0 do i check-zero loop
  200 0 do some-level some-level check-apart loop ;
: model-rounds ( -- ) 0 model-checks ! 20 0 do i 1+ model-round loop ;
model-rounds
T{ model-checks @ 5000 > -> true }T
.( level checks against the models: ) model-checks @ . cr

\ ---------------------------------------------------------------------------
\ Keeping comparisons: the outcome is the same; only an undecided level
\ comparison (Lean's is_equivalent false, ADR 0011 Amendment 1) keeps its
\ fuel instead of none, concrete levels such as 1 and 2 too. A conversion
\ of two Sorts of inequivalent levels is Lean's no, rejected since plan
\ task 4.2.2d, which leaves no fuel, keeping or not (only an unknown
\ comparison keeps it).
fresh-session
T{ level-u level-v 1000 lf-level-compare lf-lcmp-fuel @ -> outcome-unknown 0 }T
T{ level-u level-v 1000 lf-level-compare-keeping lf-lcmp-fuel @ 0>
  -> outcome-unknown true }T
: both-modes ( a b fuel -- status status' same-fuel? )
  >r 2dup r@ lf-level-compare lf-lcmp-fuel @ 2swap r> lf-level-compare-keeping
  lf-lcmp-fuel @ rot = ;
T{ 1 2 1000 both-modes -> outcome-unknown outcome-unknown false }T
T{ level-u level-u 1000 both-modes -> outcome-ok outcome-ok true }T
T{ level-u level-v 3 both-modes -> outcome-exhausted outcome-exhausted true }T
T{ level-u level-v -1 lf-level-compare-keeping lf-lcmp-fuel @ -> outcome-invalid 0 }T
: sorts ( -- su sid sv vid ) level-u make-sort handle level-v make-sort handle ;
T{ sorts 1000 lf-mixed-convert lf-mconvert-fuel @ -> outcome-rejected 0 }T
T{ sorts 1000 lf-mixed-convert-keeping lf-mconvert-fuel @ 0> -> outcome-rejected false }T
\ The flag is per call: a keeping call does not leak into the next one.
T{ sorts 1000 lf-mixed-convert lf-mconvert-fuel @ -> outcome-rejected 0 }T

\ ---------------------------------------------------------------------------
\ Head kinds of reduced terms.
fresh-session
: kind ( node -- kind ) lf-mhead-kind ;
T{ 0 make-sort kind -> lf-head-sort }T
T{ 0 make-sort dup make-pi kind -> lf-head-pi }T
T{ 0 make-sort 0 make-var make-lam kind -> lf-head-lam }T
T{ 0 make-var kind -> lf-head-var }T
T{ 0 make-var 1 make-var make-app 2 make-var make-app kind -> lf-head-var }T
T{ 0 make-var 1 make-var make-app 2 make-var make-app lf-mhead-spine nip -> 2 }T
T{ 0 make-sort 0 make-var make-app kind -> lf-head-applied }T
T{ 0 make-sort dup make-pi 0 make-var make-app kind -> lf-head-applied }T
T{ 0 make-sort 0 make-var make-lam 0 make-var make-app kind -> lf-head-none }T
T{ 0 lf-term-sort must kind -> lf-head-none }T
T{ -1 kind 99 kind -> lf-head-none lf-head-none }T
create no-formals 1 cells allot
: intern ( c-addr u -- name ) 0 -rot lf-name-str must ;
: constant-node ( name -- node )
  lf-name-generation @ no-formals 0 lf-cref-new must lf-cterm-new must drop ;
T{ s" k" intern constant-node kind -> lf-head-constant }T
T{ s" k" intern constant-node 0 make-var make-app kind -> lf-head-constant }T
T{ lf-head-lam lf-mhead-shape? lf-head-applied lf-mhead-shape? -> true false }T

\ ---------------------------------------------------------------------------
\ Inference. Each term is built in a fresh session; the outcome, the code
\ and first number recorded, and Lean's verdict on the same term. The
\ rejections named after ADR 0011's rules D1-D5 are Lean's is_def_eq
\ answering no since plan task 4.2.2d (the first number, once the mask of
\ the rules used, is 0).
variable tok
: infer ( root -- type identity status ) >r tok @ r> handle 50000 lf-mixed-infer ;
: checked ( root -- status code n1 )
  lf-diag-clear infer nip nip lf-diag@ nip nip swap ;
: fresh ( -- ) fresh-session empty-token tok ! ;
\ k : Type, a candidate signature (an unchecked assumption).
: k-node ( -- node ) s" k" intern constant-node ;
: with-k ( -- )
  fresh tok @ s" k" intern 1 make-sort handle no-formals 0 50000 lf-msp-put ok? must ;
\ F1: fun (A : Prop) (x : A) => x x (Lean: funExpected).
: f1-term ( -- node )
  fresh 0 make-sort 0 make-var 0 make-var 0 make-var make-app make-lam make-lam ;
T{ f1-term checked drop -> outcome-rejected lf-diag-function-expected }T
\ The function's type is the constant k: it may unfold (K1), unknown;
\ since plan task 4.2.2c Lean's whnf (whnf.fs) says so, as a signature
\ candidate does not say whether k has a value.
: f1-k1 ( -- node ) with-k k-node 0 make-var 0 make-sort make-app make-lam ;
T{ f1-k1 checked drop -> outcome-unknown lf-diag-needs-unfolding }T
\ S2: fun (x : fun (y : Prop) => y) => x, and fun (A : Prop) (h : A)
\ (x : h) => x (Lean: typeExpected for both).
: s2-term ( -- node ) fresh 0 make-sort 0 make-var make-lam 0 make-var make-lam ;
T{ s2-term checked drop -> outcome-rejected lf-diag-domain-type }T
: s2-var ( -- node )
  fresh 0 make-sort 0 make-var 0 make-var 0 make-var make-lam make-lam make-lam ;
T{ s2-var checked drop -> outcome-rejected lf-diag-domain-type }T
\ The domain's type is the constant k (K1): unknown, as before. A beta
\ redex that reduces to a Sort is a type since plan task 4.2.2c, whose
\ whnf reduces it, as Lean's ensure_sort_core does: accepted.
: s2-k1 ( -- node ) with-k k-node 0 make-var 0 make-var make-lam make-lam ;
T{ s2-k1 checked drop -> outcome-unknown lf-diag-needs-unfolding }T
: beta-prop ( -- node ) 1 make-sort 0 make-var make-lam 0 make-sort make-app ;
: s2-beta ( -- node ) fresh beta-prop 0 make-var 0 make-var make-lam make-lam ;
T{ s2-beta checked drop -> outcome-ok lf-diag-none }T
\ D1: fun (f : Prop -> Prop) => f Prop (appTypeMismatch).
: d1-term ( -- node )
  fresh 0 make-sort 0 make-sort make-pi 0 make-var 0 make-sort make-app make-lam ;
T{ d1-term checked -> outcome-rejected lf-diag-argument-apart 0 }T
\ D2: fun (A : Prop) (f : A -> Prop) => f A (appTypeMismatch).
: d2-term ( -- node )
  fresh 0 make-sort 0 make-var 0 make-sort make-pi 0 make-var 1 make-var make-app
  make-lam make-lam ;
T{ d2-term checked -> outcome-rejected lf-diag-argument-apart 0 }T
\ D3: fun (A B : Prop) (f : A -> Prop) (b : B) => f b (appTypeMismatch).
: d3-term ( -- node )
  fresh 0 make-sort 0 make-sort 1 make-var 0 make-sort make-pi 1 make-var
  1 make-var 0 make-var make-app make-lam make-lam make-lam make-lam ;
T{ d3-term checked -> outcome-rejected lf-diag-argument-apart 0 }T
\ D4 then D2: fun (A : Prop) (f : (A -> A) -> Prop) (g : A -> Prop) => f g.
: d4-term ( -- node )
  fresh 0 make-sort 0 make-var 1 make-var make-pi 0 make-sort make-pi
  1 make-var 0 make-sort make-pi 1 make-var 0 make-var make-app
  make-lam make-lam make-lam ;
T{ d4-term checked -> outcome-rejected lf-diag-argument-apart 0 }T
\ D5 then D3: fun (A : sort) (P : A -> Prop) (x y : A) (k : P x -> Prop)
\ (h : P y) => k h. With A : Type, Lean says appTypeMismatch; with
\ A : Prop, x and y are proofs and Lean equates them (formerly K2): ok,
\ by proof irrelevance (step 4, plan task 4.2.5).
: d5-term ( sort-level -- node )
  fresh make-sort 0 make-var 0 make-sort make-pi 1 make-var 2 make-var
  2 make-var 1 make-var make-app 0 make-sort make-pi 3 make-var 1 make-var make-app
  1 make-var 0 make-var make-app make-lam make-lam make-lam make-lam make-lam make-lam ;
T{ 1 d5-term checked -> outcome-rejected lf-diag-argument-apart 0 }T
T{ 0 d5-term checked 2drop -> outcome-ok }T
\ Formerly K3: fun (A : Type) (P : A -> Prop) (k : (A -> Prop) -> Prop)
\ (q : k (fun y => P y) -> Prop) (h : k P) => q h: equal only by eta, which
\ Lean uses (it accepts), and so does LeanForth since plan task 4.2.4 (ok).
: k3-term ( -- node )
  fresh 1 make-sort 0 make-var 0 make-sort make-pi
  1 make-var 0 make-sort make-pi 0 make-sort make-pi
  0 make-var 2 make-var 2 make-var 0 make-var make-app make-lam make-app
  0 make-sort make-pi 1 make-var 2 make-var make-app 1 make-var 0 make-var make-app
  make-lam make-lam make-lam make-lam make-lam ;
T{ k3-term checked 2drop -> outcome-ok }T
\ Formerly K4: fun (A : Sort u) (f : Sort (max u u) -> Prop) => f A:
\ Lean's level normalisation equates them (it accepts), and so does
\ LeanForth since ADR 0011 Amendment 1 (ok).
: k4-term ( -- node )
  fresh level-u make-sort level-u level-u max-of make-sort 0 make-sort make-pi
  0 make-var 1 make-var make-app make-lam make-lam ;
T{ k4-term checked 2drop -> outcome-ok }T
\ K1: fun (A : Type) (f : k -> Prop) (x : A) => f x: A against the
\ constant k, a signature candidate that does not say whether it unfolds
\ (K1, diagnostic 64): unknown.
: k1-term ( -- node )
  with-k 1 make-sort k-node 0 make-sort make-pi 1 make-var
  1 make-var 0 make-var make-app make-lam make-lam make-lam ;
T{ k1-term checked drop -> outcome-unknown lf-diag-needs-unfolding }T

\ Bookkeeping after a rejection and after an undecided analysis: the arena
\ counts are back, no binder is left, rules are on, no fuel is left.
: counts ( -- t l c ) lf-term-count @ lf-level-count @ lf-cref-count @ ;
: same-counts? ( t l c -- flag )
  lf-cref-count @ = >r lf-level-count @ = >r lf-term-count @ = r> and r> and ;
: tidy? ( t l c -- flag )
  same-counts? lf-minfer-context-depth @ 0= and lf-minfer-deciding? and
  lf-minfer-fuel @ 0= and ;
: tidy-after ( root -- status flag ) >r counts r> checked 2drop >r tidy? r> swap ;
T{ 1 d5-term tidy-after -> outcome-rejected true }T
T{ k1-term tidy-after -> outcome-unknown true }T

\ Fuel: with too little the check is exhausted, before the comparison or
\ when the analysis runs out (ADR 0008: with more it might reject; since
\ plan task 4.2.2c, unknown before), and rejected with enough; never
\ anything else.
variable sweep-root
variable seen
: saw ( outcome -- ) 1 swap lshift seen @ or seen ! ;
: sweep-step ( fuel -- outcome )
  lf-diag-clear >r tok @ sweep-root @ handle r> lf-mixed-infer nip nip
  dup outcome-unknown = if lf-diag-code@ lf-diag-undecided <> abort" record" then ;
: fuel-sweep ( -- outcome )
  0 seen ! 1 d5-term sweep-root ! 0
  3000 0 do drop i sweep-step dup saw loop ;
T{ fuel-sweep -> outcome-rejected }T
: outcome-set ( outcome... n -- mask ) 0 swap 0 ?do 1 rot lshift or loop ;
T{ seen @ outcome-exhausted outcome-rejected 2 outcome-set = -> true }T
\ Room: with a store filled up to a few free nodes, full, before the
\ comparison or when the analysis lacks room (unknown there before plan
\ task 4.2.2c), rejected with enough.
: fill-to ( free -- )
  lf-term-capacity swap -
  false lf-term-sharing!
  begin dup lf-term-count @ > while 0 lf-term-bvar must drop repeat drop true lf-term-sharing! ;
: room-step ( free -- outcome ) 1 d5-term sweep-root ! fill-to 50000 sweep-step ;
: room-sweep ( -- )
  0 seen ! 40 0 do i room-step saw loop ;
: seen-all? ( mask -- flag ) seen @ over and = ;
room-sweep
T{ outcome-full outcome-rejected 2 outcome-set seen-all? -> true }T
T{ seen @ outcome-full outcome-rejected 2 outcome-set invert and -> 0 }T
.( room sweep outcomes seen, as bits: ) seen @ . cr

\ Since plan task 4.2.2d the comparisons are Lean's is_def_eq (defeq.fs),
\ whose no is a rejection, and ADR 0011's analysis (D1-D5, P1-P4) is
\ retired: the pairs that pinned its rules, white-box, now pin the port's
\ answer through lf-minfer-agree (a job started, so that the comparison
\ has inference's typer): rejected where the analysis showed them apart;
\ where it did not, since plan tasks 4.2.4 and 4.2.5, Lean's yes by eta
\ or proof irrelevance (formerly unknown, diagnostics 88 and 87). Two
\ Sorts are apart exactly when
\ Lean's is_equivalent is false for their levels, never just because the
\ levels are written differently.
: port ( left right -- outcome ) lf-minfer-agree nip ;
: sorts-agree ( a b -- outcome )
  make-sort swap make-sort swap tok @ 1000 lf-minfer-start port ;
fresh
T{ level-u level-u level-u max-of sorts-agree -> outcome-ok }T
T{ level-u level-v max-of level-v level-u max-of sorts-agree -> outcome-ok }T
T{ level-u level-v sorts-agree -> outcome-rejected }T
T{ 1 level-u next-level imax-of 1 level-u next-level max-of sorts-agree -> outcome-rejected }T
: two-sorts ( -- s0 s1 ) fresh 0 make-sort 1 make-sort tok @ 1000 lf-minfer-start ;
T{ two-sorts port -> outcome-rejected }T
\ No fuel at all: exhausted, never a verdict.
T{ fresh 0 make-sort 1 make-sort tok @ 0 lf-minfer-start port -> outcome-exhausted }T
\ A context for the tests below: each variable a free variable of the
\ local context (core/local-context.fs) of the given type, made in a job
\ started with lf-minfer-start (which empties the local context); the
\ terms over them are closed, as every term inference compares is.
: bind ( type -- fvar ) lf-lctx-local ok? must ;
variable ctx-a variable ctx-p variable ctx-x variable ctx-y
variable ctx-a1 variable ctx-b1 variable ctx-g variable ctx-q
\ Eta, in the context A : Type, P Q : A -> Prop: P against fun (y : A) =>
\ P y is Lean's yes in both orders (eta, step 11, plan task 4.2.4), Q
\ against it Lean's no, and so is P against Prop.
: eta-context ( -- )
  fresh tok @ 1000 lf-minfer-start 1 make-sort bind ctx-a !
  ctx-a @ 0 make-sort make-pi bind ctx-p ! ctx-a @ 0 make-sort make-pi bind ctx-q ! ;
: eta-of-p ( -- node ) ctx-a @ ctx-p @ 0 make-var make-app make-lam ;
T{ eta-context ctx-p @ eta-of-p port -> outcome-ok }T
T{ eta-context eta-of-p ctx-p @ port -> outcome-ok }T
T{ eta-context ctx-q @ eta-of-p port -> outcome-rejected }T
T{ eta-context eta-of-p ctx-q @ port -> outcome-rejected }T
T{ eta-context ctx-p @ 0 make-sort port -> outcome-rejected }T
\ Proof irrelevance (step 4, plan task 4.2.5): two proofs of one
\ proposition are Lean's yes, while the same terms as data are Lean's no.
\ Context A : Type, P : Sort s, x : A -> P, y : P, a b : A. With s = 0,
\ x a, x b and y are proofs; with s = 1, x a and x b differ by their
\ arguments, and x a and y by their heads. Proofs of two different
\ propositions, x : A and y : P with A P : Prop, are Lean's no.
: proof-context ( s -- )
  fresh tok @ 100000 lf-minfer-start 1 make-sort bind ctx-a ! make-sort bind ctx-p !
  ctx-a @ ctx-p @ make-pi bind ctx-x ! ctx-p @ bind ctx-y !
  ctx-a @ bind ctx-a1 ! ctx-a @ bind ctx-b1 ! ;
: x-a ( -- node ) ctx-x @ ctx-a1 @ make-app ;
: x-b ( -- node ) ctx-x @ ctx-b1 @ make-app ;
: y-var ( -- node ) ctx-y @ ;
T{ 0 proof-context x-a x-b port -> outcome-ok }T
T{ 0 proof-context x-a y-var port -> outcome-ok }T
T{ 1 proof-context x-a x-b port -> outcome-rejected }T
T{ 1 proof-context x-a y-var port -> outcome-rejected }T
: two-proofs ( -- x y )
  fresh tok @ 100000 lf-minfer-start 0 make-sort bind 0 make-sort bind
  swap bind swap bind ;
T{ two-proofs port -> outcome-rejected }T
T{ two-proofs swap port -> outcome-rejected }T
\ is_def_eq_binding gives the bodies the right (expected) side's domain
\ (ADR 0003 Amendment 1, B2). Left: (x : Sort 1) -> (h j : x -> Prop) ->
\ (z : x) -> j z; right: the same with x : (fun (X : Sort 2) => X) (Sort
\ 1), a redex equal to Sort 1, and h z: Lean's no, in both orders.
: x-to-prop ( k -- node ) make-var 0 make-sort make-pi ;
: d4-pair ( -- left right )
  fresh tok @ 100000 lf-minfer-start
  1 make-sort 0 x-to-prop 1 x-to-prop 2 make-var 1 make-var 0 make-var make-app
  make-pi make-pi make-pi make-pi
  2 make-sort 0 make-var make-lam 1 make-sort make-app
  0 x-to-prop 1 x-to-prop 2 make-var 2 make-var 0 make-var make-app
  make-pi make-pi make-pi make-pi ;
T{ d4-pair port -> outcome-rejected }T
T{ d4-pair swap port -> outcome-rejected }T
\ Two lambdas, fun (h : X) => h and fun (h : X) => g h, in the context
\ X : Sort s, g : X -> X: proofs when s = 0 (Lean's yes: the bodies h and
\ g h are proofs of X), Lean's no when s = 1.
: lam-context ( s -- )
  fresh tok @ 100000 lf-minfer-start make-sort bind ctx-a ! ctx-a @ dup make-pi bind ctx-g ! ;
: lam-pair ( -- left right )
  ctx-a @ 0 make-var make-lam ctx-a @ ctx-g @ 0 make-var make-app make-lam ;
T{ 0 lam-context lam-pair port -> outcome-ok }T
T{ 0 lam-context lam-pair swap port -> outcome-ok }T
T{ 1 lam-context lam-pair port -> outcome-rejected }T
\ Under a binder a head may be a bound variable (the comparison's own
\ binder) or a free variable (inference's), and the two are different
\ variables even when their numbers agree: in the context x : Type (the
\ local context's entry 0), (y : Type) -> y against (y : Type) -> x is
\ Lean's no.
: head-pair ( -- left right )
  fresh tok @ 100000 lf-minfer-start 1 make-sort bind ctx-x !
  1 make-sort 0 make-var make-pi 1 make-sort ctx-x @ make-pi ;
T{ head-pair 2drop ctx-x @ lf-fvar-number -> 0 }T
T{ head-pair port -> outcome-rejected }T
\ Whether a term is a proof is Lean's normalizes_to_zero of its type's
\ type, not the level's spelling. Context P : Sort l, Q : P -> Prop,
\ p q : P; the pair Q p against Q q. Sort (imax u 0) and Sort (max 0 0)
\ are Prop, so p and q are proofs (Lean's yes: the table's
\ proof-irrelevance-imax and -max-zero rows); under Sort u or Type they
\ are not (Lean's no).
: level-context ( level -- )
  tok @ 100000 lf-minfer-start make-sort bind ctx-p ! ctx-p @ 0 make-sort make-pi bind ctx-q !
  ctx-p @ bind ctx-a1 ! ctx-p @ bind ctx-b1 ! ;
: q-pair ( -- left right ) ctx-q @ ctx-a1 @ make-app ctx-q @ ctx-b1 @ make-app ;
: q-port ( level -- outcome ) level-context q-pair port ;
T{ fresh level-u 0 imax-of q-port -> outcome-ok }T
T{ fresh 0 0 max-of q-port -> outcome-ok }T
T{ fresh 0 q-port -> outcome-ok }T
T{ fresh level-u q-port -> outcome-rejected }T
T{ fresh 1 q-port -> outcome-rejected }T
\ The typer (inference aside, Lean's infer-only mode) leaves the aside
\ flag as it found it, off or on.
: aside-after ( node -- aside ) lf-minfer-frames lf-minfer-typed 2drop lf-minfer-aside @ ;
T{ 0 proof-context y-var aside-after -> false }T
T{ 1 proof-context true lf-minfer-aside ! x-a aside-after -> true }T
\ A comparison gives back what it allocated: (fun X : Type => X -> X)
\ Prop reduces to a new Pi, Lean's no against Type; the counts are as
\ before.
: redex-pair ( -- left right )
  fresh 1 make-sort 0 make-var 1 make-var make-pi make-lam 0 make-sort make-app
  1 make-sort tok @ 1000 lf-minfer-start ;
: port-tidy ( left right -- outcome same-counts? )
  counts 2>r >r port r> 2r> same-counts? ;
T{ redex-pair port-tidy -> outcome-rejected true }T

\ ---------------------------------------------------------------------------
\ The probes. identity: forall (P : Prop) (x : P), P; and over Type.
: id-claim ( sort -- node ) make-sort 0 make-var 1 make-var make-pi make-pi ;
: id-value ( sort -- node ) make-sort 0 make-var 0 make-var make-lam make-lam ;
: bad-value ( sort -- node ) make-sort 0 make-var 1 make-var make-lam make-lam ;
: probe ( claim value fuel theorem? -- status code n1 )
  lf-diag-clear >r >r >r handle tok @ -rot r> handle r>
  r> if lf-mixed-theorem-probe else lf-mixed-definition-probe then
  lf-diag@ nip nip swap ;
: pair ( sort -- claim value ) fresh dup id-claim swap id-value ;
T{ 0 pair 50000 true probe 2drop -> outcome-ok }T
T{ 0 pair 50000 false probe 2drop -> outcome-ok }T
\ S3: over Type the statement is a type (thmTypeIsNotProp); as a
\ definition it is fine. The recorded number is the statement's level.
T{ 1 pair 50000 true probe drop -> outcome-rejected lf-diag-not-proposition }T
T{ 1 pair 50000 false probe 2drop -> outcome-ok }T
\ Over Sort u: Sort (imax (u+1) (imax u u)), not zero when u = 1.
: u-pair ( -- claim value ) fresh level-u id-claim level-u id-value ;
T{ u-pair 50000 true probe drop -> outcome-rejected lf-diag-not-proposition }T
\ S1: a lambda as the claimed type (typeExpected), both probes.
: s1-pair ( -- claim value ) fresh 0 id-value dup ;
T{ s1-pair 50000 true probe drop -> outcome-rejected lf-diag-type-expected }T
T{ s1-pair 50000 false probe drop -> outcome-rejected lf-diag-type-expected }T
\ D at the declaration: the value returns P, a proposition, where a proof
\ of P is claimed (declTypeMismatch; D2 under D4 before plan task 4.2.2d).
T{ fresh 0 id-claim 0 bad-value 50000 true probe
  -> outcome-rejected lf-diag-value-apart 0 }T
\ A claim whose binder domain's type is a redex: unknown until plan task
\ 4.2.2c (no rule), accepted since, as by Lean (its whnf is a Sort).
: beta-claim ( -- claim value )
  fresh beta-prop 0 make-var 1 make-var make-pi make-pi beta-prop 0 make-var 0 make-var
  make-lam make-lam ;
T{ beta-claim 50000 true probe drop -> outcome-ok lf-diag-none }T
\ Invalid, exhausted and full, for the theorem probe too.
T{ 0 pair -1 true probe 2drop -> outcome-invalid }T
T{ 0 pair 10 true probe 2drop -> outcome-exhausted }T
T{ 0 pair 2 fill-to 50000 true probe 2drop -> outcome-full }T
T{ depth -> 0 }T
bye
