\ Unit tests of the instance table and its keys (plans FE1e2 and FE1e3;
\ src/front/discr-keys.fs, src/front/instances.fs) over the Init slice
\ tests/front/whnf-slice.ndjson and its elaboration data (20 instances,
\ 476 left out, 18 classes, 8 default instances): every instance's class
\ and keys recomputed equal to the data's (§4); the first-use pass;
\ each heap request and each budget refused in turn, the same query then
\ answering in full (no part of a tree or check kept, each instance
\ counted once); isClass? at every
\ head; getUnify and getInstances on S1's problems, in pinned Lean's
\ order (its lists in tests/front/synth-tried.lean's trace, here by name
\ and rank); the outcomes: unsupported (a pi goal, a definition at a key,
\ a star root, a local instance, a string literal), invalid (no class, a
\ dead context view with no stale error code, a root arity other than
\ the type's, values short of their ranks), stuck (a reducible head or a recursor with a
\ metavariable under isDefEqStuckEx), exhausted (the budget) and full;
\ the keys of numerals, offsets, projections and an implicit or
\ strict-implicit literal; a root only left-out values have;
\ default instances by rank with their gaps; and that no check leaves a
\ depth or a mark open. Every T{ }T checks the data stack's depth.
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

\ ---- The first-use pass (§4 "When"): every root key and class, the
\ default instances' classes; no instance is final before its root is
\ queried, none verified; a left-out value or a number beyond never.
T{ lf-inst-classes lf-inst-classes lf-inst-checked# lf-inst-unverified#
   -> outcome-ok outcome-ok 0 0 }T
T{ s" instAddNat" inst-named lf-inst-verified? -1 lf-inst-verified?
   100000 lf-inst-verified?
   -> false false false }T

\ ---- Resources, on a fresh table: each heap request refused in turn
\ answers full or ok, and the same query then answers in full (OfNat ?T
\ 0: 23 candidates; no part of a tree is kept), until a run meets no
\ refusal; each budget from 0 answers exhausted or ok, and Add Nat then
\ has its three candidates with instAddNat verified (no check's
\ exhaustion is kept as unverified). The goal is made before the
\ refusal: only the query meets it.
lf-defeq-elab lf-defeq-stuck or lf-defeq-flags!
: full-goal ( -- t ) lv1 ?tv 0 ofnat ;
\ Every run starts with the table's slabs shrunk, so that each of its
\ heap requests comes again.
: shrink ( slab -- ) dup slab-clear slab-trim drop ;
: fresh ( -- )
  lf-inst-reset it-roots shrink it-nodes shrink it-vals shrink it-ranked shrink
  it-stack shrink it-out shrink it-status shrink it-dstatus shrink
  dk-cells shrink dk-args shrink dk-kinds shrink ;
: refused ( k -- outcome fired? )
  full-goal swap fresh heap-refusals ! lf-inst-candidates nip nip
  heap-refusals @ 0= 0 heap-refusals ! ;
: requery-ok? ( -- flag ) full-goal lf-inst-candidates ok? swap 23 = and nip ;
: full-or-ok? ( outcome -- flag ) dup ok? swap outcome-full = or ;
\ A failed build keeps no node and no value cell: no root's tree is
\ built, or the slabs hold one (each run starts with them empty).
: unbuilt? ( r -- flag ) it-root@ tr-node @ 0< ;
: no-cells? ( -- flag ) it-nodes slab-count it-vals slab-count or 0= ;
: nothing-kept? ( -- flag ) it-roots slab-count ['] unbuilt? all? 0= no-cells? or ;
\ Answered, nothing of a failure kept; then in full, instOfNatNat (OfNat's
\ one instance) the one check counted.
: one-checked? ( -- flag ) lf-inst-checked# 1 = ;
: refusal-ok? ( k -- flag fired? )
  refused swap full-or-ok? nothing-kept? and requery-ok? and one-checked? and swap ;
: refusals-ok? ( -- flag )   \ k = 1, 2, ... until a run meets no refusal
  true 500 1 do i refusal-ok? -rot and swap 0= if leave then loop ;
T{ refusals-ok? 500 refused nip -> true false }T
: budget-run ( k -- outcome )
  nat add swap lf-inst-reset lf-meta-budget! lf-inst-candidates nip nip
  lf-meta-default-budget lf-meta-budget! ;
: add-nat-ok? ( -- flag )
  nat add lf-inst-candidates ok? swap 3 = and nip
  s" instAddNat" inst-named lf-inst-verified? and ;
\ instAddNat, Add's one instance, the one check counted: none that ran
\ out of budget counts.
: budget-ok? ( k -- flag )
  budget-run dup ok? swap outcome-exhausted = or add-nat-ok? and one-checked? and ;
: budgets-ok? ( -- flag ) true 60 0 do i budget-ok? and loop ;
T{ budgets-ok? 0 budget-run 60 budget-run -> true outcome-exhausted outcome-ok }T
lf-meta-default lf-defeq-flags!

\ ---- isClass?
T{ nat add0 lf-class? -> s" Add" menv-name elab-decl-of drop true outcome-ok }T
T{ nat lf-class? -> false outcome-ok }T
T{ nat nat tpi lf-class? -> false outcome-ok }T
T{ nat nat add0 tpi lf-class? -> s" Add" menv-name elab-decl-of drop true outcome-ok }T
T{ 0 bv lf-class? -> false outcome-ok }T
\ isClassQuick?'s other heads: a definition the transparency unfolds is
\ undefined (unsupported; not at reducible, id being no reducible one);
\ a let, a projection and a lambda head undefined; a lambda, a free
\ variable, a literal and a Sort none; an assigned metavariable by its
\ value's head (a constant: its class; a lambda: undefined); an
\ unassigned one none.
: id-nat ( -- t ) lv1 1 s" id" cn nat app ;
: cproj ( e i -- t ) >r s" Add" menv-name r> lf-proj-of made ;
: ?add ( -- mvar )
  nat mv-natural lf-mvar-new made dup l0 1 s" Add" cn lf-mvar-assign made ;
: add-class ( -- class ) s" Add" menv-name elab-decl-of drop ;
T{ id-nat lf-class? id-nat ' lf-class? lf-tr-reducible lf-meta-at
   -> false outcome-unsupported false outcome-ok }T
T{ nat zero 0 bv let lf-class? fp 0 proj lf-class? nat 0 bv lam nat app lf-class?
   -> false outcome-unsupported false outcome-unsupported false outcome-unsupported }T
T{ nat 0 bv lam lf-class? fx lf-class? 5 num lf-class? lv1 sort lf-class?
   -> false outcome-ok false outcome-ok false outcome-ok false outcome-ok }T
T{ ?add nat app lf-class? ?add lf-class?
   -> add-class true outcome-ok add-class true outcome-ok }T
T{ ?f nat app lf-class? ?n nat app lf-class? ?n lf-class?
   -> false outcome-unsupported false outcome-ok false outcome-ok }T
\ An application of a free variable is none; a let made without a
\ dependency is undefined; a constant no declaration has is none (Lean's
\ getConstTemp? finds nothing).
: ghost-name ( -- name ) 0 s" NoSuchConstant" lf-name-str drop ;
: ghost ( -- t )
  ghost-name lf-name-generation @ lv-pairs 0 lf-cref-new must lf-cterm-new must drop ;
: nondep-let ( type value body -- t ) rot swap lam 1 lf-let-make must ;
T{ fx nat app lf-class? nat zero 0 bv nondep-let lf-class? ghost lf-class?
   -> false outcome-ok false outcome-unsupported false outcome-ok }T
\ The two checks' verdicts on a body: isClass? that cannot tell is passed
\ on; a body of no class, or of another, refuses (error 112); a default
\ instance whose conclusion's head is no constant, or one the data's
\ stage lacks, refuses (error 116).
T{ id-nat 0 it-class-verdict nat 0 it-class-verdict lf-inst-error
   -> outcome-unsupported outcome-invalid 112 }T
\ A root key of another arity than the body's: filed under another root
\ (Add Nat Nat for instAddNat, whose root key is Add of one argument).
T{ nat add0 nat app s" instAddNat" inst-named it-class-verdict lf-inst-error
   -> outcome-invalid 115 }T
T{ fx 0 it-default-verdict ghost 0 it-default-verdict lf-inst-error
   -> outcome-invalid outcome-invalid 116 }T
\ forallMetaTelescopeReducing enters a pi that whnf makes (a let's body:
\ zeta), and stops at a type whnf leaves.
: let-pi ( -- t ) lv1 sort nat 0 bv 1 bv tpi let ;
T{ let-pi lf-inst-telescope swap lf-term-tag@ -> outcome-ok lf-tag-constant }T

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
\ Verified once their root was queried: instAddNat, not instMulNat (Mul
\ never queried).
T{ s" instAddNat" inst-named lf-inst-verified? s" instMulNat" inst-named lf-inst-verified?
   -> true false }T
\ A star root (a bare metavariable goal) is unsupported; a root no value
\ has answers no values at once.
T{ ?n lf-inst-unify nip nip nat lf-inst-unify rot drop
   -> outcome-unsupported 0 outcome-ok }T
\ A root only left-out values have is a root: Nonempty Nat finds the two
\ whose key below the root is a star (instNonemptyOfInhabited, rank 0,
\ and instNonemptyOfMonad, rank 1).
: nonempty-nat ( -- t ) lv1 1 s" Nonempty" cn nat app ;
T{ nonempty-nat lf-inst-unify rot dup @ invert elab-left-out@ drop nip
   swap cell+ @ invert elab-left-out@ drop nip -> 2 outcome-ok 0 1 }T
\ A local instance of the class in the context is unsupported (FE1E
\ §2.7); a context view that is not live is invalid, never read as none.
: add-local ( -- view )
  lf-mctx-view dup nat add0 lf-lctx-local made 0 0 lf-local-new made
  s" Add" menv-name lf-local-instance made lf-view-push made lf-mctx-view! ;
T{ add-local nat add lf-inst-candidates nip nip swap lf-mctx-view!
   -> outcome-unsupported }T
T{ lf-mctx-view 999999 lf-mctx-view! nat add lf-inst-candidates nip nip swap lf-mctx-view!
   -> outcome-invalid }T
T{ nat add cands nip -> 3 }T
\ getInstances: a goal whose whnf is a pi is unsupported, and one whose
\ class isClass? cannot tell.
T{ let-pi lf-inst-candidates nip nip id-nat lf-inst-candidates nip nip
   fp 0 proj lf-inst-candidates nip nip
   -> outcome-unsupported outcome-unsupported outcome-unsupported }T
\ A root's node refused (its slab shrunk and filled, each heap request
\ of the build refused in turn): full or ok, then the same query in full.
: fill-nodes ( -- )
  begin it-nodes slab-count it-nodes slab-capacity < while 1 it-nodes slab-claim 2drop
  repeat ;
: mul-nat ( -- t ) l0 1 s" Mul" cn nat app ;
variable mul-n
mul-nat cands nip mul-n !
: filled ( k -- outcome fired? )
  mul-nat swap fresh fill-nodes heap-refusals ! lf-inst-candidates nip nip
  heap-refusals @ 0= 0 heap-refusals ! ;
: mul-ok? ( -- flag ) mul-nat lf-inst-candidates ok? swap mul-n @ = and nip ;
: filled-ok? ( -- flag )
  true 500 1 do i filled swap full-or-ok? mul-ok? and rot and swap 0= if leave then loop ;
T{ filled-ok? 500 filled nip mul-n @ 1 > -> true false true }T

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
  true swap 1 ?do over i cells + dup 1 cells - @ swap @ pair-ok? and loop nip ;
T{ lv1 ?tv add cands stable? -> true }T
T{ lv1 ?tv 0 ofnat cands stable? -> true }T

\ The candidates of Add Nat are in rank order: the two left out first.
T{ nat add cands drop dup @ invert elab-left-out@ drop nip swap cell+ @ invert elab-left-out@
   drop nip -> 0 1 }T

\ ---- Outcomes. A pi goal and a sort are refused; a goal that is no
\ class is error 110; a sort's key is other.
T{ nat nat add0 tpi lf-inst-candidates nip nip -> outcome-unsupported }T
T{ nat lf-inst-candidates nip nip lf-inst-error -> outcome-invalid 110 }T
\ Each query starts with no code: an invalid from below the table (a
\ context view that is not live) leaves 0, not the last query's 110.
T{ lf-mctx-view 999999 lf-mctx-view! nat add lf-inst-candidates nip nip swap lf-mctx-view!
   lf-inst-error -> outcome-invalid 0 }T
\ A root's values fill its ranks, else invalid (a gap the reader
\ refuses; it would read as left-out 0): checked on the last root built.
T{ it-ranked slab-count dup 1- outcome-ok it-gapless swap outcome-ok it-gapless
   5 outcome-full it-gapless -> outcome-invalid outcome-ok outcome-full }T
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

\ ---- The keys of numerals, offsets and projections; ignoreArg.
\ A literal under an implicit binder is no type: a star (@Eq {5} 0 0:
\ pinned Lean's keys are Eq, *, 0, 0).
: tags4 ( k n -- t0 t1 t2 t3 )
  drop dup elab-key-tag swap 1+ dup elab-key-tag swap 1+ dup elab-key-tag swap 1+
  elab-key-tag ;
T{ lv1 1 s" Eq" cn 5 num app 0 num app 0 num app keys-of tags4
   -> elab-key-const elab-key-star elab-key-lit elab-key-lit }T
\ ignoreArg: a literal and a term that is no type are ignored under a
\ strict-implicit binder too (no constant of the slice has one: the
\ binder kind given directly); under an explicit one kept, being no
\ proof.
T{ 5 num lf-binder-strict dk-ignore? fx lf-binder-strict dk-ignore?
   5 num lf-binder-default dk-ignore?
   -> true outcome-ok true outcome-ok false outcome-ok }T
\ getUnifyKeyArgs: a numeral below the root is a literal key; at the
\ root, its constant.
: key-tag ( t root? -- tag ) lf-dt-nil lf-dt-key drop drop elab-key-tag ;
T{ zero false key-tag zero true key-tag -> elab-key-lit elab-key-const }T
\ OfNat.ofNat Nat 3 _ is the numeral 3.
: ofnat-lit ( u -- t )
  >r l0 1 s" OfNat.ofNat" cn nat app r@ num app 0 s" instOfNatNat" cn r> num app app ;
T{ 3 ofnat-lit lf-dt-nat-lit -> 3 true outcome-ok }T
\ isOffset under mkPath: Nat.add, Add.add and HAdd.hAdd of a numeral at
\ Nat are stars; at another type, or of no numeral, their constant.
: inst-hadd ( -- t ) l0 1 s" instHAdd" cn nat app 0 s" instAddNat" cn app ;
: nat-add ( a b -- t ) >r 0 s" Nat.add" cn swap app r> app ;
: add-add ( type a b -- t ) >r >r l0 1 s" Add.add" cn swap app 0 s" instAddNat" cn app
  r> app r> app ;
: hadd-add ( a b -- t )
  >r >r l0 l0 l0 3 s" HAdd.hAdd" cn nat app nat app nat app inst-hadd app r> app r> app ;
T{ fx 2 num nat-add add0 keys-of tag1 nat fx 2 num add-add add0 keys-of tag1
   -> 2 elab-key-star 2 elab-key-star }T
T{ fx 2 num hadd-add add0 keys-of tag1 fx fz nat-add add0 keys-of tag1
   -> 2 elab-key-star 4 elab-key-const }T
T{ nat nat tpi fx 2 num add-add add0 keys-of tag1 nip -> elab-key-const }T
\ A projection: its key, its structure first on the todo list, a class's
\ too under getUnifyKeyArgs; under mkPath a class's structure is no_index,
\ but getFunInfoNArgs infers the projection's type there: unsupported
\ until FE1c's inferType has projections.
T{ fp 0 proj true lf-dt-nil lf-dt-key drop lf-dt-first fp = swap elab-key-tag
   -> true elab-key-proj }T
T{ fx 0 cproj true lf-dt-nil lf-dt-key drop nip lf-dt-first fx = -> true }T
T{ fx 0 cproj lf-dt-path nip nip -> outcome-unsupported }T
\ Unsupported: a string literal (S5); a definition reduceDT would
\ unfold (GE.ge, reducible: plan S2's delta).
: str-hi ( -- t ) s" hi" lf-str-new made drop ;
: ge-nat ( -- t ) l0 1 s" GE.ge" cn nat app 0 s" instLENat" cn app fx app fz app ;
T{ str-hi lf-dt-path nip nip ge-nat lf-dt-path nip nip
   -> outcome-unsupported outcome-unsupported }T
\ A reducible definition with a metavariable (Decidable.isTrue) never
\ reaches getUnifyKeyArgs' stuck test: reduceDT would unfold it, which is
\ unsupported until plan S2's delta.
lf-defeq-elab lf-defeq-stuck or lf-defeq-flags!
T{ 0 s" Decidable.isTrue" cn ?q app fx app sub-key -> outcome-unsupported }T

\ Literals beyond a cell, and a sum beyond one, are unsupported (S5),
\ as a numeral, at the root, below it in a path or a query.
: big ( -- t ) s" 18446744073709551616" lf-hterm-decimal must drop ;
T{ big lf-dt-nat-lit succ big app lf-dt-nat-lit succ -1 num app lf-dt-nat-lit
   -> -1 false outcome-unsupported -1 false outcome-unsupported
      -1 false outcome-unsupported }T
T{ big lf-dt-path nip nip succ big app add0 lf-dt-path nip nip succ big app sub-key
   -> outcome-unsupported outcome-unsupported outcome-unsupported }T
\ The budget spent before a literal's or a projection's key: exhausted.
: no-budget ( t -- outcome )
  0 lf-meta-budget! true lf-dt-nil lf-dt-key nip nip
  lf-meta-default-budget lf-meta-budget! ;
T{ 5 num no-budget fp 0 proj no-budget -> outcome-exhausted outcome-exhausted }T
\ A constant or a projection's structure the data's stage lacks: invalid,
\ as a key, as a path and at getUnifyKeyArgs' stuck test.
: ghost-proj ( -- t ) fx ghost-name 0 lf-proj-of made ;
T{ ghost true lf-dt-nil lf-dt-key nip nip ghost lf-dt-path nip nip
   ghost-proj true lf-dt-nil lf-dt-key nip nip
   -> outcome-invalid outcome-invalid outcome-invalid }T
T{ ghost ?n app sub-key -> outcome-invalid }T
\ ignoreArg reads getFunInfoNArgs: an argument beyond the parameters it
\ found is kept unless a proof (@id (Nat -> Nat) s x: Add, id, arrow, Nat,
\ s, x); where inferType or whnfD cannot tell (a projection, a type that
\ is a reducible definition) the path is unsupported.
: id3 ( -- t ) lv1 1 s" id" cn nat nat tpi app fs app fx app ;
: ge-local ( -- fvar ) ge-nat lf-lctx-local made ;
T{ id3 add0 keys-of nip -> 6 }T
: eq3 ( a b c -- t ) >r >r >r lv1 1 s" Eq" cn r> app r> app r> app ;
: ge-eq ( -- t ) ge-local dup dup eq3 ;
T{ fp 0 proj fx fx eq3 lf-dt-path nip nip ge-eq lf-dt-path nip nip
   -> outcome-unsupported outcome-unsupported }T
: id-twice ( a -- t ) lv1 1 s" id" cn over app swap app ;
T{ lv1 1 s" id" cn fp 0 proj app fx app add0 lf-dt-path nip nip
   ge-local id-twice add0 lf-dt-path nip nip
   fp 0 proj add0 lf-dt-path nip nip
   -> outcome-unsupported outcome-unsupported outcome-unsupported }T
\ reduceDT: strict eta (fun x => s x is s), a lambda that is no eta form
\ is other; whnfCore that cannot tell (a matcher, S3) is unsupported.
T{ sfun keys-of tag0 nat 0 bv lam keys-of tag0 -> elab-key-fvar 1 elab-key-other 1 }T
T{ 0 s" Nat.add.match_1" cn fk app lf-dt-path nip nip -> outcome-unsupported }T
\ isOffset: Add.add of no numeral is its constant; at a type whnf cannot
\ tell (Lean.SyntaxNodeKind, a reducible definition: S2) unsupported; a
\ numeral below the root (Nat.succ Nat.zero) a literal.
T{ nat fx fz add-add add0 keys-of tag1 nip -> elab-key-const }T
T{ 0 s" Lean.SyntaxNodeKind" cn fx 2 num add-add add0 lf-dt-path nip nip
   -> outcome-unsupported }T
T{ succ zero app add0 keys-of tag1 nip -> elab-key-lit }T
\ getUnifyKeyArgs without isDefEqStuckEx: a read-only metavariable (one
\ depth deeper) is other.
lf-defeq-elab lf-defeq-flags!
: deeper-key ( -- tag )
  false lf-mctx-depth{ made >r ?n true key-tag r> }lf-mctx-depth drop ;
T{ deeper-key ?n true key-tag -> elab-key-other elab-key-star }T
lf-defeq-elab lf-defeq-stuck or lf-defeq-flags!

\ The keys' own room: each heap request of a path refused in turn, the
\ todo cells shrunk first (an arrow's domain, a projection's structure
\ pushed), and a literal's text with the key texts filled: full, never
\ another answer, and nothing kept.
: path-refused ( t k -- outcome fired? )
  dk-cells shrink heap-refusals ! lf-dt-path nip nip
  heap-refusals @ 0= 0 heap-refusals ! ;
: answered? ( outcome -- flag ) dup full-or-ok? swap outcome-unsupported = or ;
: path-refusals-ok? ( t -- flag )
  true 100 1 do over i path-refused swap answered? rot and swap 0= if leave then
  loop nip ;
T{ nat nat tpi path-refusals-ok? fx 0 cproj path-refusals-ok? -> true true }T
: fill-texts ( -- )
  begin elab-texts slab-count elab-texts slab-capacity <
  while 1 elab-texts slab-claim 2drop repeat ;
: text-refused ( k -- outcome fired? )
  lf-dt-mark 2>r >r fill-texts heap-refusals ! 5 num true lf-dt-nil lf-dt-key nip nip
  heap-refusals @ 0= 0 heap-refusals ! r> 2r> lf-dt-release ;
: text-refusals-ok? ( -- flag )
  true 100 1 do i text-refused swap full-or-ok? rot and swap 0= if leave then loop ;
T{ elab-keys# text-refusals-ok? elab-keys# rot - -> true 0 }T

\ ---- lf-meta-at runs a word at a transparency and gives the configured
\ one back; whnfD is whnf at default whatever the mode (instHAdd unfolds
\ there: unsupported, S2).
T{ ' lf-defeq-mode lf-tr-all lf-meta-at lf-defeq-mode -> lf-tr-all lf-tr-default }T
T{ inst-hadd ' lf-meta-whnf-d lf-tr-reducible lf-meta-at nip lf-defeq-mode
   -> outcome-unsupported lf-tr-default }T
\ A THROW out of the word: lf-meta-at and lf-meta-with give the configured
\ transparency and flags back and pass the THROW on (review s1-synth-b L3).
: throw-77 ( -- ) 77 throw ;
: meta-at-throw ( -- ior ) ['] throw-77 lf-tr-all ['] lf-meta-at catch nip nip ;
: meta-with-throw ( -- ior )
  ['] throw-77 lf-defeq-opaque lf-tr-all ['] lf-meta-with catch nip nip nip ;
: same-config? ( flags mode -- flag ) lf-meta-config d= ;
: config-kept? ( xt -- ior flag ) lf-meta-config rot execute -rot same-config? ;
T{ ' meta-at-throw config-kept? ' meta-with-throw config-kept? -> 77 true 77 true }T
\ forallMetaTelescopeReducing's metavariables: synthetic for an
\ instance-implicit binder of the declared type (Decidable.decide's
\ [h : Decidable p]), natural for another, a store pi or none.
T{ s" Decidable.decide" menv-decl lf-menv-type dup it-mv-kind
   swap lf-term-second@ it-mv-kind -1 it-mv-kind nat nat tpi it-mv-kind
   -> mv-natural mv-synthetic mv-natural mv-natural }T

\ ---- Default instances, in rank order.
T{ s" OfNat" menv-name elab-decl-of drop lf-default-instances rot drop -> 1 outcome-ok }T
T{ s" HAdd" menv-name elab-decl-of drop lf-default-instances 2drop @ elab-default@ drop nip
   s" instHAdd" menv-name elab-decl-of drop = -> true }T
\ Pow's rank 0 is a gap (its default instance is not in the slice),
\ rank 1 instPowNat; one whose check could not finish is a gap too.
: class-defaults ( c-addr u -- addr n outcome )
  menv-name elab-decl-of drop lf-default-instances ;
: pow-defaults ( -- addr n outcome ) s" Pow" class-defaults ;
: default-named? ( j c-addr u -- flag )
  rot elab-default@ drop nip elab-decl-name -rot names= ;
T{ pow-defaults rot dup @ lf-default-gap? swap cell+ @ s" instPowNat" default-named?
   -> 2 outcome-ok true true }T
: hadd-defaults ( -- addr n outcome ) s" HAdd" class-defaults ;
T{ it-unverified 0 it-dstatus slab-at ! hadd-defaults rot @ lf-default-gap?
   it-verified 0 it-dstatus slab-at ! -> 1 outcome-ok true }T
\ No room for the answer: full; then in full.
T{ it-defaults shrink 1 heap-refusals ! pow-defaults nip nip 0 heap-refusals !
   pow-defaults rot drop -> outcome-full 2 outcome-ok }T

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
