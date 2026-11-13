\ Unit tests of the instance table and its keys (plans FE1e2 and FE1e3;
\ src/front/discr-keys.fs, src/front/instances.fs) over the Init slice
\ tests/front/whnf-slice.ndjson and its elaboration data (20 instances,
\ 476 left out, 18 classes, 8 default instances): every instance's class
\ and keys recomputed equal to the data's (§4); isClass?; getUnify and
\ getInstances on S1's problems, in pinned Lean's order (its lists in
\ tests/front/synth-tried.lean's trace, here by name and rank); the
\ outcomes: unsupported (a pi goal, a definition at a key, a star root),
\ invalid (no class), stuck (a reducible head with a metavariable under
\ isDefEqStuckEx), exhausted (the budget) and full (each heap request
\ refused in turn); and that no check leaves a depth or a mark open.
\ Every T{ }T checks the data stack's depth.
include ../support/tester.fs
include ../support/heap-watch.fs
\ Every module first: a context member declared after menv-load would
\ move the context under the loaded slice.
require ../../src/front/instances.fs
require ./whnf-cases.fs

: names= ( name c-addr u -- flag ) menv-name = ;
: inst-named ( c-addr u -- i ) menv-name elab-decl-of drop elab-instance-of drop ;
: ?tv ( level -- t ) lf-level-succ must sort mv-natural lf-mvar-new made ;
: ?lv ( -- level ) lf-level-mvar-new made ;
: num ( u -- t ) lf-hterm-cell must drop ;
: add ( t -- t' ) >r ?lv 1 s" Add" cn r> app ;
: ofnat ( t u -- t2 ) >r >r ?lv 1 s" OfNat" cn r> app r> num app ;
: hadd ( a b c -- t ) >r >r >r l0 l0 ?lv 3 s" HAdd" cn r> app r> app r> app ;
: add0 ( t -- t' ) >r l0 1 s" Add" cn r> app ;
: cands ( type -- addr n ) lf-inst-candidates made ;
: last-v ( addr n -- v ) 1- cells + @ ;
: first-v ( addr n -- v ) drop @ ;
: v-named? ( v c-addr u -- flag ) rot elab-instance@ 2drop elab-decl-name -rot names= ;
: depth-ok? ( -- flag ) lf-mctx-depth 0= lf-mctx-marks 0= and ;
: last-named? ( addr n c-addr u -- n flag ) 2>r tuck last-v 2r> v-named? ;
: first-named? ( addr n c-addr u -- n flag ) 2>r tuck first-v 2r> v-named? ;
: last-left ( addr n -- n flag ) tuck last-v lf-inst-left-out? ;
: add-nat-shape ( addr n -- n last? first-left? )
  2dup first-v lf-inst-left-out? >r s" instAddNat" last-named? r> ;

\ ---- §4: every instance of the slice checked, none unverified.
: check-all ( -- n ) 0 elab-instance elab-count 0 ?do i lf-inst-check ok? if 1+ then loop ;
T{ check-all depth-ok? -> 20 true }T

\ ---- isClass?
T{ nat add0 lf-class? -> s" Add" menv-name elab-decl-of drop true outcome-ok }T
T{ nat lf-class? -> false outcome-ok }T
T{ nat nat tpi lf-class? -> false outcome-ok }T
T{ nat nat add0 tpi lf-class? -> s" Add" menv-name elab-decl-of drop true outcome-ok }T
T{ 0 bv lf-class? -> false outcome-ok }T

\ ---- getInstances on S1's problems (Lean: OfNat Nat 0 has three
\ candidates, the last instOfNatNat; HAdd Nat Nat ?c one, instHAdd; Add
\ Nat three, the last instAddNat; the stuck ones end in the left-out
\ instOfNatQ, String.instHAddCharRaw and instAddQ).
lf-defeq-elab lf-defeq-stuck or lf-defeq-flags!
T{ nat 0 ofnat cands s" instOfNatNat" last-named? -> 3 true }T
T{ nat nat lv1 ?tv hadd cands s" instHAdd" first-named? -> 1 true }T
T{ nat add cands add-nat-shape -> 3 true true }T
T{ lv1 ?tv 0 ofnat cands nip -> 23 }T
T{ lv1 ?tv 0 ofnat cands last-v dup lf-inst-left-out? swap invert elab-left-out@ nip nip
   -> true elab-not-exported }T
T{ lv1 ?tv lv1 ?tv lv1 ?tv hadd cands last-left -> 7 true }T
T{ lv1 ?tv add cands nip -> 26 }T
T{ lf-inst-checked# lf-inst-unverified# depth-ok? -> 3 0 true }T

\ getUnify visits the star child first (Main.lean:597): Add Nat's tree
\ gives the two left out (star) before instAddNat (Nat), before sorting.
T{ nat add lf-inst-unify drop drop @ lf-inst-left-out? -> true }T

\ One depth deeper ?T is read-only, yet a star under isDefEqStuckEx.
: deeper-count ( t -- n ) false lf-mctx-depth{ made >r cands nip r> }lf-mctx-depth drop ;
T{ lv1 ?tv 0 ofnat deeper-count -> 23 }T

\ The priority sort is stable (lib/sort.fs, Lean's insertionSort):
\ candidates of equal priority keep getUnify's order, their ranks rising.
: pair-ok? ( v1 v2 -- flag )
  over lf-inst-priority over lf-inst-priority <> if 2drop true exit then
  it-rank swap it-rank > ;
: stable? ( addr n -- flag )
  true swap 1 ?do over i cells + dup cell- @ swap @ pair-ok? and loop nip ;
T{ lv1 ?tv add cands stable? -> true }T
T{ lv1 ?tv 0 ofnat cands stable? -> true }T

\ The candidates of Add Nat are in rank order: the two left out first.
T{ nat add cands drop dup @ invert elab-left-out@ drop nip swap cell+ @ invert elab-left-out@
   drop nip -> 0 1 }T

\ ---- Outcomes. A pi goal and a sort are refused; a goal that is no
\ class is error 110; a sort's key is other.
T{ nat nat add0 tpi lf-inst-candidates nip nip -> outcome-unsupported }T
T{ nat lf-inst-candidates nip nip lf-inst-error -> outcome-invalid 110 }T
: first-tag ( k n outcome -- tag outcome ) nip swap elab-key-tag swap ;
T{ l0 sort lf-dt-path first-tag -> elab-key-other outcome-ok }T
\ Exhausted: the budget spent before the first key.
T{ 0 lf-meta-budget! nat add lf-inst-unify nip nip lf-meta-default-budget lf-meta-budget!
   -> outcome-exhausted }T

\ ---- Keys: mkPath of an instance-implicit argument is a star, of a
\ numeral a literal, of a type its constant; the query's metavariable a
\ star under isDefEqStuckEx.
: keys-of ( t -- k n ) lf-dt-path made ;
: tags12 ( k n -- n tag2 tag1 )
  over 1+ elab-key-tag >r over 2 + elab-key-tag >r nip r> r> ;
T{ nat 0 ofnat keys-of tags12 -> 3 elab-key-lit elab-key-const }T
T{ nat add keys-of nip -> 2 }T
\ An arrow and its domain; a free variable; a nested Nat.succ of no
\ numeral is an offset, a star (isOffset).
: tag0 ( k n -- tag n ) swap elab-key-tag swap ;
: tag1 ( k n -- n tag ) swap 1+ elab-key-tag ;
T{ nat nat tpi keys-of tag0 -> elab-key-arrow 2 }T
T{ fx keys-of tag0 -> elab-key-fvar 1 }T
T{ succ succ fx app app keys-of tag1 -> 2 elab-key-star }T
T{ lv1 ?tv true lf-dt-nil lf-dt-key nip nip -> outcome-ok }T

\ The stuck signal (Main.lean:359-397): a recursor stuck on ?n, keyed
\ below the root under isDefEqStuckEx; without it, the recursor's key.
: rec-q ( -- t ) rec nat nat lam app zero app nat nat 0 bv lam lam app ?n app ;
: sub-key ( t -- outcome ) false lf-dt-nil lf-dt-key nip nip ;
T{ rec-q sub-key -> lf-meta-stuck }T
lf-defeq-elab lf-defeq-flags!
T{ rec-q sub-key -> outcome-ok }T
lf-defeq-elab lf-defeq-stuck or lf-defeq-flags!

\ ---- toNatLit?: literals, Nat.zero, Nat.succ and OfNat.ofNat.
T{ 5 num lf-dt-nat-lit -> 5 true outcome-ok }T
T{ zero lf-dt-nat-lit -> 0 true outcome-ok }T
T{ succ 4 num app lf-dt-nat-lit -> 5 true outcome-ok }T
T{ nat lf-dt-nat-lit -> 0 false outcome-ok }T
T{ succ fx app lf-dt-nat-lit -> 0 false outcome-ok }T

\ ---- Default instances, in rank order.
T{ s" OfNat" menv-name elab-decl-of drop lf-default-instances rot drop -> 1 outcome-ok }T
T{ s" HAdd" menv-name elab-decl-of drop lf-default-instances 2drop @ elab-default@ drop nip
   s" instHAdd" menv-name elab-decl-of drop = -> true }T

\ ---- Full: each heap request of a fresh root's build refused in turn.
\ The goal is made first: only the query meets the refusal.
: full-run ( t -- outcome ) lf-inst-reset lf-inst-candidates nip nip ;
: full-try ( k -- flag )
  nat add swap heap-refusals ! full-run 0 heap-refusals ! dup ok? swap outcome-full = or ;
: full-all ( -- flag ) true 40 1 do i full-try and loop ;
T{ nat add full-run -> outcome-ok }T
T{ full-all -> true }T
T{ depth-ok? -> true }T

bye
