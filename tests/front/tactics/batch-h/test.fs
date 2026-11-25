\ Unit tests of case patterns, slice E2a (plan row TB2, piece E; design
\ docs/design/TACTIC_PATTERNS.md) over decide's slice of Init in an
\ authoring run.
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
: made ( x outcome -- x ) ok? 0= abort" batch-h test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
lf-meta-throw-base outcome-rejected - constant thrown-rejected
: authored ( code -- n ) dup lf-author-throw = if drop lf-author-code lf-tac-forget then ;
: code2 ( x y xt -- code ) catch dup if nip nip then authored ;
: code3 ( x y z xt -- code ) catch dup if >r 2drop drop r> then authored ;
: code4 ( w x y z xt -- code ) catch dup if >r 2drop 2drop r> then authored ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: local+ ( type c-addr u flags -- fvar )
  >r lfa-intern swap lf-lctx-local made tuck swap r> lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: binder ( type c-addr u -- fvar ) 0 local+ ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: nm ( c-addr u -- name ) lfa-intern ;
: run1 ( x -- run ) 0 swap lf-run+ ;
: view# ( goal -- n ) lf-goal-view lf-view-count ;
: local-at ( goal i -- local ) swap lf-goal-view swap lf-view-local ;
: named? ( goal i c-addr u -- flag ) 2>r local-at lf-local-name 2r> nm lf-name-same? ;
: hidden? ( goal i -- flag ) local-at lf-local-inaccessible? ;
: open? ( goal -- flag ) lf-goal-assigned? 0= ;
: eqv? ( a b -- flag ) lf-meta-eqv made ;
: bool-true ( -- t ) s" Bool.true" lf-mk-const0 ;
: heq-of ( a b -- t ) s" HEq" 2swap 2 lf-mk-app-m ;
: nsucc ( a -- t ) s" Nat.succ" lf-mk-const0 swap lf-mk-app ;
create xs 2 cells allot
: lam1 ( e x -- e' ) xs ! xs 1 lf-mk-lambda-fvars ;

\ ---- 1. app-builder.fs: mkEqOfHEq, mkEqNDRec, mkEqRec, each called on
\ terms built here (outcomes, malformed input).
fresh
nat s" a" binder constant fa
nat s" b" binder constant fb
fa fb lf-mk-eq s" h" binder constant fh
fb fa lf-mk-eq s" k" binder constant fk
fa fb heq-of s" q" binder constant fq
fa bool-true heq-of s" r" binder constant fr
fa fb lf-mk-eq constant ab
fb fa lf-mk-eq constant ba
\ eq_of_heq q : a = b; an equation, or two types not defeq: rejected.
T{ fq lf-mk-eq-of-heq lf-infer! ab eqv? -> true }T
T{ fh ' lf-mk-eq-of-heq catch nip fr ' lf-mk-eq-of-heq catch nip -> thrown-rejected thrown-rejected }T
\ Eq.ndrec (fun x => x = a) (Eq.refl a) h : b = a; a major Eq.refl gives the minor.
fb fa lf-mk-eq fb lam1 constant mot1
fa lf-mk-eq-refl constant rfa
T{ mot1 rfa fh lf-mk-eq-ndrec lf-infer! ba eqv? -> true }T
T{ mot1 rfa rfa lf-mk-eq-ndrec rfa = -> true }T
\ A major that is no equation, a motive whose body is no type: rejected; a
\ motive that is no lambda: not supported yet.
T{ mot1 rfa fq ' lf-mk-eq-ndrec code3 -> thrown-rejected }T
T{ fb fb lam1 rfa fh ' lf-mk-eq-ndrec code3 -> thrown-rejected }T
T{ fa rfa fh ' lf-mk-eq-ndrec code3 -> thrown-unsupported }T
T{ mot1 rfa fh ' lf-mk-eq-rec code3 -> thrown-unsupported }T   \ one binder only

\ ---- 2. meta-tactic/subst.fs called on goals built here.
: g-ab ( -- goal ) fa fb lf-mk-eq goal ;
: g-true ( -- goal ) s" True" lf-mk-const0 goal ;
: fl ( -- flags ) lf-subst-symm lf-subst-skip or ;
\ substCore: b eliminated (symm), k and q reverted and back; fs: k, q, b, h.
T{ g-ab fh 0 fl lf-goal-subst-core open? swap run-count -> true 4 }T
\ No skip asked: True's goal still gets Eq.ndrec, fs b and h.
T{ g-true fh 0 lf-subst-symm lf-goal-subst-core dup lf-goal-type g-true lf-goal-type eqv?
   swap open? rot run-count -> true true 4 }T
\ Errors: no equation (475), the side no variable (477, both forms); an
\ assigned goal is a fault (invalid).
T{ g-ab fq 0 fl ' lf-goal-subst-core code4 -> 475 }T
fa nsucc fb lf-mk-eq s" h2" binder constant fh2
fa fb nsucc lf-mk-eq s" h3" binder constant fh3
T{ g-ab fh2 0 0 ' lf-goal-subst-core code4 g-ab fh3 0 fl ' lf-goal-subst-core code4
   -> 477 477 }T
g-ab constant g-used
g-used fh 0 fl lf-goal-subst-core 2drop
T{ g-used fh 0 fl ' lf-goal-subst-core code4 -> thrown-invalid }T
\ heqToEq: an equation and an HEq of two types come back as they were;
\ q : HEq a b becomes a = b under q's name.
T{ g-ab dup fh lf-goal-heq-to-eq rot = swap fh = -> true true }T
T{ g-ab dup fr lf-goal-heq-to-eq rot = swap fr = -> true true }T
g-ab fq lf-goal-heq-to-eq constant gq constant fq'
T{ fq' lf-fvar-type ab eqv? gq dup view# 1- s" q" named? gq open? -> true true true }T
\ subst of an HEq becomes substEq; of a variable, substVar.
T{ g-ab fq lf-goal-subst open? g-ab fb lf-goal-subst open? -> true true }T
\ substEq takes the right side first: h : a = b maps b to a.
T{ g-ab fh 0 lf-goal-subst-eq drop fb lf-fsubst-get fa = -> true }T
\ Skip: nothing else reverted, True free of b and h: fs as given, no term.
fresh
nat s" a" binder constant ka
nat s" b" binder constant kb
ka kb lf-mk-eq s" h" binder constant kh
T{ g-true kh 0 fl lf-goal-subst-core open? swap -> true 0 }T
\ subst_vars in context order: a before its equation h is eliminated
\ first (b stays), where h first would eliminate b.
kb kb lf-mk-eq s" k" binder drop
ka kb lf-mk-eq s" h2" binder drop
T{ ka kb lf-mk-eq goal lf-goal-subst-vars lf-goal-view dup kb lf-view-has? swap ka lf-view-has?
   -> true false }T
\ subst_vars: no equation at all gives the goal itself.
fresh
nat s" a" binder constant va
T{ va va lf-mk-eq goal dup lf-goal-subst-vars = -> true }T
\ substVar passes an implementation detail over (none left: 479).
nat s" c" binder constant fc
fc va lf-mk-eq s" d" lf-local-impl-detail local+ drop
T{ fc fc lf-mk-eq goal fc ' lf-goal-subst-var code2 -> 479 }T

\ ---- 3. The tactics through their text: by-subst, by-subst[ ],
\ by-subst-vars, rfl in a pattern, by-rintro[ ] (each case, each error).
: sab ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a =" ;
T{ sab s" ' h by-subst by-rfl" tactic-ran sab s" ' b by-subst by-rfl" tactic-ran
   sab s" ' a by-subst by-rfl" tactic-ran -> 0 0 0 }T
: ssucc ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a ' Nat.succ b $ = explicit: h a ' Nat.succ b $ =" ;
T{ ssucc s" ' h by-subst by-rfl" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b b a = explicit: k a b = explicit: h a b ="
   s" ' h by-subst ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = explicit: h ' h ' h =" s" ' h by-subst by-rfl"
   tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a ' Nat.succ b $ = explicit: h ' h ' h ="
   s" ' h by-subst by-rfl" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b ' HEq a $ b $ explicit: h b a =" s" ' h by-subst by-rfl"
   tactic-ran -> 0 }T
\ The reduced paths: the right side (id m), the left (id n).
T{ s" Nat explicit: n Nat explicit: m n ' id m $ = explicit: h m n =" s" ' h by-subst by-rfl"
   tactic-ran -> 0 }T
T{ s" Nat explicit: n Nat explicit: m ' id n $ ' Nat.succ m $ = explicit: h n ' Nat.succ m $ ="
   s" ' h by-subst by-rfl" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h1 b c = explicit: h2 c a ="
   s" by-subst[ h1 h2 ] by-rfl" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = explicit: h True explicit: p True"
   s" ' h by-subst ' p by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = b a = ∧ explicit: h b a ="
   s" ' h by-obtain[ << hab _ >> ] ' hab by-subst by-assumption" tactic-ran -> 0 }T
\ Errors: occurs (476), no equation (479, also an HEq of two types),
\ neither side a variable (478), a name no local has (455); a let (99)
\ and a have (93, revert refuses it) not supported yet.
T{ s" Nat explicit: a a a = explicit: h True" s" ' h by-subst" tactic-ran -> 476 }T
T{ s" Nat explicit: a a a =" s" ' a by-subst" tactic-ran -> 479 }T
T{ s" Nat explicit: a ' HEq a $ Bool.true $ explicit: h True" s" ' h by-subst" tactic-ran
   -> 479 }T
T{ s" Nat.zero Nat.zero = explicit: h False" s" ' h by-subst" tactic-ran -> 478 }T
T{ sab s" by-subst[ zz ]" tactic-ran -> 455 }T
T{ sab s" a b = ' h by-let: k ' k by-subst" tactic-ran sab s" a b = ' h by-have: k ' k by-subst"
   tactic-ran -> 99 93 }T
lf-tac-forget
\ subst_vars: two equations; a variable before its equation (substVar
\ first, h.symm); a let in the context (480, caught: the next tried); a
\ have whose revert is refused (93, never caught).
T{ s" Nat explicit: a Nat explicit: b Nat explicit: c a b = explicit: h1 c b = explicit: h2 c a ="
   s" by-subst-vars by-rfl" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b b b = explicit: k a b = explicit: h a b ="
   s" by-subst-vars by-rfl" tactic-ran -> 0 }T
T{ s" Nat explicit: a a a =" s" Nat Nat.zero by-let: k by-subst-vars by-rfl" tactic-ran -> 0 }T
T{ sab s" a b = ' h by-have: k by-subst-vars by-rfl" tactic-ran -> 93 }T
lf-tac-forget
\ rfl in a pattern: in each alternative; a cleared field rfl eliminates
\ (both cleared at once, tryToSkip); a field that is no equation (478).
T{ s" Nat explicit: a Nat explicit: b a b = b a = ∨ explicit: h b a ="
   s" ' h by-rcases[ rfl | rfl ] by-rfl by-rfl" tactic-ran -> 0 }T
T{ s" ' Eq Nat.zero $ Exists explicit: h True" s" ' h by-obtain[ << - rfl >> ] by-trivial"
   tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = True ∧ explicit: h b a ="
   s" ' h by-obtain[ << - rfl >> ]" tactic-ran -> 478 }T
lf-tac-forget
\ rintro: a name, alternatives then a name, a tuple, rfl, Nat, _ (hidden:
\ assumption finds it), - (cleared: assumption fails, 381); none (481);
\ no binder left (94); the grouping (a | b c is two items: 94, Lean's).
: sri ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b =" ;
T{ sri s" by-revert[ h ] by-rintro[ k ] ' k by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = b a = ∨ explicit: h a a = explicit: k b a = a b = ∨"
   s" by-revert[ h k ] by-rintro[ h1 | h2 k ] ' Or.inr ' h1 $ by-exact ' Or.inl ' h2 $ by-exact"
   tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = b a = ∧ explicit: h b a ="
   s" by-revert[ h ] by-rintro[ << hab hba >> ] ' hba by-exact" tactic-ran -> 0 }T
T{ sab s" by-revert[ h ] by-rintro[ rfl ] by-rfl" tactic-ran -> 0 }T
T{ s" Nat explicit: n n n = explicit: h n n =" s" ' n by-revert by-rintro[ _ | m h ] by-rfl by-rfl"
   tactic-ran -> 0 }T
T{ sri s" by-revert[ h ] by-rintro[ _ ] by-assumption" tactic-ran
   sri s" by-revert[ h ] by-rintro[ - ] by-assumption" tactic-ran -> 0 381 }T
T{ sri s" by-rintro[ ]" tactic-ran sri s" by-rintro[ x ]" tactic-ran -> 481 94 }T
\ - then rfl: the cleared variable becomes Nat.zero, no longer a free
\ variable, so finish passes it over (the goal depends on it: no skip).
T{ s" Nat explicit: x ' Nat.zero x = explicit: h x x =" s" ' x by-revert by-rintro[ - rfl ] by-rfl"
   tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b a b = b a = a a = ∧ ∨ explicit: h b a = explicit: k b a ="
   s" by-revert[ h k ] by-rintro[ x | y z ] by-intro: d ' d by-exact by-intro: d ' d by-exact"
   tactic-ran -> 94 }T
lf-tac-forget

\ ---- 4. Resources: every heap allocation refused in turn, through the
\ words called directly and through their text: the answer or full.
: frames-anew ( -- )
  lfa-brackets sweep-slab-anew pat-frames sweep-slab-anew rcs-frames sweep-slab-anew
  mid-frames sweep-slab-anew mcs-frames sweep-slab-anew mri-frames sweep-slab-anew
  mgz-frames sweep-slab-anew mtk-frames sweep-slab-anew fsi-frames sweep-slab-anew
  frp-cells sweep-slab-anew mrv-frames sweep-slab-anew msc-frames sweep-slab-anew
  mse-frames sweep-slab-anew abr-frames sweep-slab-anew mat-cells sweep-slab-anew
  mti-frames sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
fresh
nat s" a" binder constant sa
nat s" b" binder constant sb
sb sa lf-mk-eq s" k" binder constant sk
sa sb lf-mk-eq s" h" binder constant sh0
sa sb heq-of s" q" binder constant sq
: s-ab ( -- goal ) sa sb lf-mk-eq goal ;
: typed1 ( goal outcome -- t outcome ) dup ok? if >r lf-goal-type r> then ;
: typed ( fs goal outcome -- t outcome ) >r nip r> typed1 ;
: d-core ( x -- t outcome ) drop s-ab sh0 0 fl ['] lf-goal-subst-core 4 2 lf-meta-catch typed ;
: d-eq ( x -- t outcome ) drop s-ab sh0 0 ['] lf-goal-subst-eq 3 2 lf-meta-catch typed ;
: d-heq ( x -- t outcome ) drop s-ab sq ['] lf-goal-heq-to-eq 2 2 lf-meta-catch typed ;
: d-var ( x -- t outcome ) drop s-ab sb ['] lf-goal-subst-var 2 1 lf-meta-catch typed1 ;
: d-subst ( x -- t outcome ) drop s-ab sq ['] lf-goal-subst 2 1 lf-meta-catch typed1 ;
: d-vars ( x -- t outcome ) drop s-ab ['] lf-goal-subst-vars 1 1 lf-meta-catch typed1 ;
T{ 0 ' d-core heap-sweep swept? 0 ' d-eq heap-sweep swept? 0 ' d-heq heap-sweep swept?
   -> true true true }T
T{ 0 ' d-var heap-sweep swept? 0 ' d-subst heap-sweep swept? 0 ' d-vars heap-sweep swept?
   -> true true true }T
: full-code? ( code -- flag ) dup if lf-author-outcome outcome-full = then ;
: text-full ( c-addr u c-addr' u' -- code outcome )
  tactic-ran dup full-code? if drop -1 outcome-full else outcome-ok then ;
: p-rec ( x -- code outcome ) drop
  s" Nat explicit: a Nat explicit: b a ' Nat.succ b $ = explicit: h ' h ' h ="
  s" ' h by-subst by-rfl" text-full ;
: p-reduced ( x -- code outcome )
  drop s" Nat explicit: n Nat explicit: m n ' id m $ = explicit: h m n ="
  s" ' h by-subst by-rfl" text-full ;
: p-rintro ( x -- code outcome )
  drop s" Nat explicit: a Nat explicit: b a b = b a = ∨ explicit: h b a ="
  s" by-revert[ h ] by-rintro[ rfl | rfl ] by-rfl by-rfl" text-full ;
T{ 0 ' p-rec heap-sweep swept? 0 ' p-reduced heap-sweep swept? 0 ' p-rintro heap-sweep swept?
   -> true true true }T
lf-tac-forget
.( batch-h test.fs: all tests passed) cr
