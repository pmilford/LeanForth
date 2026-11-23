\ Unit tests of case patterns, slice E1 (plan row TB2, piece E; design
\ docs/design/TACTIC_PATTERNS.md) over decide's slice of Init in an
\ authoring run, by the classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ fvar-subst.fs; revert.fs's lf-goal-revert-kept; goal.fs's
\ lf-goal-intro-names and lf-goal-intro-kept; meta-induction.fs's
\ lf-recursor-info, lf-target-arity and lf-goal-induction; cases.fs's
\ lf-goal-cases; generalize.fs's lf-goal-generalize, each called on goals
\ built here; pattern-syntax.fs's reader and rcases.fs's walk through
\ LeanForth text (tests/support/tactic-text.fs):
\ 1. outcomes: each word's result; the reader's refusals 472, 473, 474,
\    458, 72; rcases' 470 and 471; each case not ported (99, unsupported);
\ 2. malformed input: an assigned goal, a kept run shorter than asked,
\    two free variables to revert-kept;
\ 3. records: every cell of a recursor's information, of a subgoal, of a
\    substitution, and the reader's arguments and spans;
\ 4. interfaces: tags (one minor premise: the parent's), the
\    inaccessible flag kept, an anonymous name made a, the order;
\ 5. resources: every heap allocation refused in turn through the
\    words' text (tests/support/meta-sweeps.fs): the answer or full;
\ 6. state: a refused goal left unassigned.
\ The terms are checked node for node with pinned Lean by check.py.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
include ../../../support/heap-watch.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/decide-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/decide-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" batch-g test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
: authored ( code -- n ) dup lf-author-throw = if drop lf-author-code lf-tac-forget then ;
: code2 ( x y xt -- code ) catch dup if nip nip then authored ;
: code4 ( w x y z xt -- code ) catch dup if >r 2drop 2drop r> then authored ;
: code3 ( x y z xt -- code ) catch dup if >r 2drop drop r> then authored ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: local+ ( type c-addr u flags -- fvar )
  >r lfa-intern swap lf-lctx-local made tuck swap r> lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: binder ( type c-addr u -- fvar ) 0 local+ ;
: anon+ ( type flags -- fvar )
  >r 0 swap lf-lctx-local made tuck swap r> lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: tagged ( type -- goal ) goal dup s" t" lfa-intern lf-mvar-tag! made ;
: decl ( c-addr u -- d ) lfa-intern lf-menv-find made ;
: nm ( c-addr u -- name ) lfa-intern ;
: run1 ( x -- run ) 0 swap lf-run+ ;
: run2 ( x y -- run ) >r run1 r> lf-run+ ;
: view# ( goal -- n ) lf-goal-view lf-view-count ;
: local-at ( goal i -- local ) swap lf-goal-view swap lf-view-local ;
: named? ( goal i c-addr u -- flag ) 2>r local-at lf-local-name 2r> nm lf-name-same? ;
: hidden? ( goal i -- flag ) local-at lf-local-inaccessible? ;
: open? ( goal -- flag ) lf-goal-assigned? 0= ;
: or-of ( p q -- t ) s" Or" 2swap 2 lf-mk-app-m ;
: and-of ( p q -- t ) s" And" 2swap 2 lf-mk-app-m ;
: tag? ( goal c-addr u -- flag ) rot lf-goal-tag -rot nm lf-name-same? ;
: eqv? ( a b -- flag ) lf-meta-eqv made ;

fresh
nat s" a" binder constant fa
nat s" b" binder constant fb
nat s" c" binder constant fc
fa fb lf-mk-eq constant ab
fb fa lf-mk-eq constant ba
fb fc lf-mk-eq constant bc

\ ---- 1. fvar-subst.fs: insert, get, erase, apply, append.
T{ 0 fa fb lf-fsubst-insert dup run-count swap 0 run@ dup 0 run@ swap 1 run@ -> 1 fa fb }T
\ get: a key's term; any other free variable itself.
0 fa fb lf-fsubst-insert constant s1
T{ s1 fa lf-fsubst-get s1 fc lf-fsubst-get 0 fa lf-fsubst-get -> fb fc fa }T
\ insert keeps the first term of a key; a new key's term replaces it in the others.
T{ s1 fa fc lf-fsubst-insert s1 = -> true }T
0 fc fa lf-fsubst-insert fa fb lf-fsubst-insert constant s2
T{ s2 fc lf-fsubst-get s2 fa lf-fsubst-get s2 run-count -> fb fb 2 }T
\ apply: each key replaced (a = b with a to b gives b = b); the empty one nothing.
T{ s1 ab lf-fsubst-apply fb fb lf-mk-eq eqv? 0 ab lf-fsubst-apply ab = -> true true }T
T{ fa fb fc lf-replace-fvar fa = ab fa fc lf-replace-fvar fc fb lf-mk-eq eqv? -> true true }T
\ erase: the pair gone, the others kept; an absent key changes nothing.
T{ s2 fc lf-fsubst-erase dup run-count swap fc lf-fsubst-get s1 fb lf-fsubst-erase run-count
   -> 1 fc 1 }T
\ append: fs1 then fs2, applying fs1's terms through fs2 (a to c, then c to b).
T{ 0 fa fc lf-fsubst-insert 0 fc fb lf-fsubst-insert lf-fsubst-append dup fa lf-fsubst-get
   swap fc lf-fsubst-get -> fb fb }T
T{ 0 s1 lf-fsubst-append s1 = s1 0 lf-fsubst-append run-count -> true 1 }T

\ ---- 2. revert-kept and intro-kept: names and the inaccessible flag.
fresh
nat s" a" binder constant ra
nat s" b" binder constant rb
ra rb lf-mk-eq s" h" lf-local-inaccessible local+ constant rh
ra rb lf-mk-eq tagged constant g1
g1 rb run1 lf-goal-revert-kept constant kept1 constant g1'
T{ kept1 run-count kept1 0 run@ lf-local-fvar kept1 1 run@ lf-local-fvar -> 2 rb rh }T
T{ kept1 1 run@ lf-local-inaccessible? kept1 0 run@ lf-local-inaccessible? g1' view# -> true false 1 }T
T{ g1 rb run1 ' lf-goal-revert-kept code2 -> thrown-invalid }T   \ assigned now
T{ ra rb lf-mk-eq tagged 0 lf-goal-revert-kept nip -> 0 }T
T{ ra rb lf-mk-eq tagged ra rb run2 ' lf-goal-revert-kept code2 -> thrown-unsupported }T
\ intro-kept: b, then h hidden as it was; an anonymous binder a, hidden.
g1' kept1 2 lf-goal-intro-kept constant xs1 constant g1''
T{ xs1 run-count g1'' view# g1'' 1 s" b" named? g1'' 2 s" h" named? -> 2 3 true true }T
T{ g1'' 1 hidden? g1'' 2 hidden? g1'' lf-goal-type ra xs1 0 run@ lf-mk-eq eqv? -> false true true }T
T{ g1' kept1 0 lf-goal-intro-kept nip -> 0 }T
T{ ra rb lf-mk-eq tagged rb run1 lf-goal-revert-kept 3 ' lf-goal-intro-kept code3
   -> thrown-invalid }T   \ kept shorter than n
fresh
nat s" a" binder constant za
nat lf-local-inaccessible anon+ constant zx
za za lf-mk-eq goal zx run1 lf-goal-revert-kept constant kz constant gz
T{ gz kz 1 lf-goal-intro-kept drop dup 1 s" a" named? swap 1 hidden? -> true true }T
\ intro-names: a name for each binder in turn; 0 and past the names the
\ binder's own, hidden.
fresh
nat s" a" binder constant na
nat s" b" binder constant nb
na nb lf-mk-eq s" h" binder constant nh
na nb lf-mk-eq goal nb run1 lf-goal-revert-kept drop constant gn
T{ gn s" x" nm run1 2 lf-goal-intro-names drop dup 1 s" x" named? over 1 hidden? rot 2 hidden?
   -> true false true }T
T{ gn 0 0 lf-goal-intro-names nip -> 0 }T

\ ---- 3. lf-recursor-info: from the declaration's type.
: info. ( info -- args params major indices minors levels# )
  dup lf-rinfo-args over lf-rinfo-params 2 pick lf-rinfo-major 3 pick lf-rinfo-indices
  4 pick lf-rinfo-minors 5 pick lf-rinfo-levels# 6 roll drop ;
s" And.casesOn" decl lf-recursor-info constant i-and
T{ i-and info. i-and lf-rinfo-decl s" And.casesOn" decl = -> 5 2 3 0 1 1 true }T
T{ i-and lf-rinfo-type s" And" nm lf-name-same? i-and 0 lf-rinfo-level -> true -1 }T
s" Nat.casesAuxOn" decl lf-recursor-info constant i-aux
T{ i-aux info. i-aux 0 lf-rinfo-level -> 4 0 1 0 2 1 -1 }T
\ Exists eliminates into Prop: its one level is Exists's own, index 0.
s" Exists.casesOn" decl lf-recursor-info constant i-ex
T{ i-ex info. i-ex 0 lf-rinfo-level -> 5 2 3 0 1 1 0 }T
s" Or.casesOn" decl lf-recursor-info constant i-or
T{ i-or info. -> 6 2 3 0 2 0 }T
\ Eq.casesOn has an index (E4's); a theorem is no recursor: 99.
T{ s" Eq.casesOn" decl lf-recursor-info lf-rinfo-indices -> 1 }T
: info-code ( d -- code ) ['] lf-recursor-info catch dup if nip then authored ;
T{ s" Eq.refl" decl info-code -> 99 }T
\ getTargetArity: pis, and the body of a redex's function.
T{ ab lf-target-arity ab ab lf-term-pi lf-made! lf-target-arity -> 0 1 }T
T{ ab ab lf-term-pi lf-made! nat swap lf-term-lam lf-made! fa lf-mk-app lf-target-arity -> 1 }T

\ ---- 4. lf-goal-induction and lf-goal-cases.
fresh
nat s" a" binder constant ia
nat s" b" binder constant ib
ia ib lf-mk-eq ib ia lf-mk-eq and-of s" h" binder constant ih
ib ia lf-mk-eq tagged constant gi
gi ih s" And.casesOn" decl 0 lf-goal-induction constant subs-and
\ One minor premise: the parent's tag; the fields hidden; h cleared.
: sub@ ( subs i k -- x ) swap 4 * + run@ ;
T{ subs-and run-count subs-and 0 3 sub@ subs-and 0 1 sub@ run-count -> 4 0 2 }T
subs-and 0 0 sub@ constant gi1
T{ gi1 s" t" tag? gi1 view# gi1 2 hidden? gi1 3 hidden? gi open? -> true 4 true true false }T
T{ subs-and 0 2 sub@ ih lf-fsubst-get lf-meta-fvar? -> true }T
T{ gi ih s" And.casesOn" decl 0 ' lf-goal-induction code4 -> thrown-invalid }T
\ Two minor premises (Or): tags t.inl and t.inr; cases puts the
\ constructors and maps h to each one applied.
ia ib lf-mk-eq ib ia lf-mk-eq or-of s" k" binder constant ik
ib ia lf-mk-eq tagged constant go
go ik s" x" nm run1 run1 false lf-goal-cases constant subs-or
T{ subs-or run-count subs-or 0 0 sub@ s" t.inl" tag? subs-or 1 0 sub@ s" t.inr" tag? -> 8 true true }T
T{ subs-or 0 3 sub@ s" Or.inl" nm lf-name-same? subs-or 1 3 sub@ s" Or.inr" nm lf-name-same?
   -> true true }T
T{ subs-or 0 0 sub@ dup view# 1- s" x" named? subs-or 1 0 sub@ dup view# 1- hidden? -> true true }T
T{ subs-or 0 2 sub@ ik lf-fsubst-get lf-meta-head s" Or.inl" lf-meta-const-named? -> true }T
\ Nat with nat-aux?: Nat.casesAuxOn (0 and n + 1); without it Nat.casesOn.
fresh
nat s" n" binder constant cn
cn cn lf-mk-eq goal constant gc
gc cn 0 true lf-goal-cases constant subs-nat
T{ subs-nat run-count subs-nat 0 0 sub@ lf-goal-type lf-meta-args2 nip s" Nat.zero" lf-meta-const-named? -> 8 false }T
T{ gc lf-instantiate! lf-meta-head s" Nat.casesAuxOn" lf-meta-const-named? -> false }T
cn cn lf-mk-eq goal cn 0 false lf-goal-cases drop
T{ subs-nat 1 3 sub@ s" Nat.succ" nm lf-name-same? -> true }T
\ An indexed family (Eq) and no inductive type: 99, the goal left open.
fresh
nat s" a" binder constant qa
nat s" b" binder constant qb
qa qb lf-mk-eq s" e" binder constant qe
s" Not" lf-mk-const0 qa qb lf-mk-eq lf-mk-app s" n" binder constant qn
qb qa lf-mk-eq goal constant ge
T{ ge qe 0 true ' lf-goal-cases code4 ge open? -> 99 true }T
T{ ge qn 0 true ' lf-goal-cases code4 ge open? -> 99 true }T
\ A dependent reverted and introduced again in each goal, mapped by the
\ substitution: e : a = b depends on b.
qa qb lf-mk-eq goal qb 0 true lf-goal-cases constant subs-dep
T{ subs-dep 1 2 sub@ qe lf-fsubst-get dup lf-meta-fvar? swap qe = -> true false }T
T{ subs-dep 1 0 sub@ dup view# 2 - s" e" named? subs-dep 1 0 sub@ view# -> true 4 }T

\ ---- 5. lf-goal-generalize: a name given, else a hidden x.
fresh
nat s" a" binder constant ga
nat s" b" binder constant gb
ga gb lf-mk-eq goal constant gq
gq ga run1 s" y" nm lf-run+ lf-goal-generalize constant gq' constant ys
T{ ys run-count gq' dup view# 1- s" y" named? gq' dup view# 1- hidden? gq open? -> 1 true false false }T
T{ gq' lf-goal-type ys 0 run@ gb lf-mk-eq eqv? -> true }T
ga gb lf-mk-eq goal ga run1 0 lf-run+ lf-goal-generalize nip constant gq2
T{ gq2 dup view# 1- hidden? gq2 dup view# 1- s" x" named? -> true true }T
T{ gq ga run1 0 lf-run+ ' lf-goal-generalize code2 -> thrown-invalid }T   \ assigned

\ ---- 6. The reader (pattern-syntax.fs) and the walk through text.
: st ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = b a = ∧ explicit: h b a =" ;
: so ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = b a = ∨ explicit: h b a = a b = ∨" ;
T{ st s" ' h by-obtain[ << x y >> ] ' y by-exact" tactic-ran -> 0 }T
\ The arguments: the target, x, y, the tuple (span 3).
: arg@ ( k -- x span ) 0 lf-tactic-step tac-first @ 1+ + dup lf-tactic-arg drop swap lf-tactic-arg-span ;
T{ 1 lf-tactic-step tac-count @ -> 4 }T
: args1 ( k -- x span ) 1 lf-tactic-step tac-first @ + dup lf-tactic-arg drop swap lf-tactic-arg-span ;
T{ 1 args1 nip 2 args1 nip 3 args1 -> 1 1 pat-tuple 3 }T
T{ so s" ' h by-rcases[ x | y ] ' Or.inr ' x $ by-exact ' Or.inl ' y $ by-exact" tactic-ran -> 0 }T
T{ 3 args1 -> pat-alts 3 }T
T{ so s\" ' h by-rcases[ x\n | y ] ' Or.inr ' x $ by-exact ' Or.inl ' y $ by-exact" tactic-ran
   -> 0 }T
T{ st s" ' h by-obtain[ << - _ rfl >> ]" tactic-ran 1 args1 2 args1 3 args1
   -> 99 pat-clear 1 0 1 pat-rfl 1 }T
\ Refusals: 472 (a bar first, twice, before a closer), 473 (the other
\ closer; ] with a tuple open), 474 (two elements, none), 458 (a word
\ that is no item), 72 (@).
T{ st s" ' h by-obtain[ | x ]" tactic-ran st s" ' h by-obtain[ x | | y ]" tactic-ran
   st s" ' h by-obtain[ << x | >> ]" tactic-ran -> 472 472 472 }T
T{ st s" ' h by-obtain[ << x ⟩ ]" tactic-ran st s" ' h by-obtain[ << x ]" tactic-ran
   st s" ' h by-obtain[ x >> ]" tactic-ran -> 473 473 473 }T
T{ st s" ' h by-rcases[ x y ]" tactic-ran st s" ' h by-rcases[ ]" tactic-ran -> 474 474 }T
T{ st s" ' h by-obtain[ x by-rfl ]" tactic-ran st s" ' h by-obtain[ @x ]" tactic-ran -> 458 72 }T
T{ st s" ' h by-obtain[ << ⟨ x y ⟩ >> ] ' x ' y $ by-exact" tactic-ran 0= -> false }T
lf-tac-forget
\ 471: a type that is no inductive one (a pi through whnfD).
: sn ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = Not explicit: h a a =" ;
T{ sn s" ' h by-rcases[ << x >> ]" tactic-ran dup 471 = swap 136 = or -> true }T
lf-tac-forget

\ ---- 7. Resources: the words through their text with every heap
\ allocation refused in turn: the answer or full.
: frames-anew ( -- )
  lfa-brackets sweep-slab-anew pat-frames sweep-slab-anew rcs-frames sweep-slab-anew
  mid-frames sweep-slab-anew mcs-frames sweep-slab-anew mri-frames sweep-slab-anew
  mgz-frames sweep-slab-anew mtk-frames sweep-slab-anew fsi-frames sweep-slab-anew
  frp-cells sweep-slab-anew mrv-frames sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
: full-code? ( code -- flag ) dup if lf-author-outcome outcome-full = then ;
: text-full ( c-addr u c-addr' u' -- code outcome )
  tactic-ran dup full-code? if drop -1 outcome-full else outcome-ok then ;
: p-obtain ( x -- code outcome ) drop st s" ' h by-obtain[ << x y >> ] ' y by-exact" text-full ;
: p-rcases ( x -- code outcome )
  drop so s" ' h by-rcases[ x | y ] ' Or.inr ' x $ by-exact ' Or.inl ' y $ by-exact" text-full ;
: p-nat ( x -- code outcome )
  drop s" Nat explicit: a Nat explicit: b a b = explicit: k a b =" s" ' b by-rcases[ _ | d ] by-assumption by-assumption" text-full ;
: p-term ( x -- code outcome )
  drop s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k b a ="
  s" ' And.intro ' h $ ' k $ by-obtain[ << p q >> ] ' q by-exact" text-full ;
T{ 0 ' p-obtain heap-sweep swept? 0 ' p-rcases heap-sweep swept? -> true true }T
T{ 0 ' p-nat heap-sweep swept? 0 ' p-term heap-sweep swept? -> true true }T
lf-tac-forget
.( batch-g test.fs: all tests passed) cr
