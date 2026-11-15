\ Unit tests of the front end's whnfCore and getStuckMVar? (plan FE1c;
\ src/front/whnf.fs) over the Init slice, with the variables of
\ tests/front/whnf-cases.fs: every step (beta, zeta, metavariable and let
\ variable heads, iota) with its result; every outcome -- ok, unsupported
\ (definition, projection, quotient and K-like heads, literal and
\ non-inert major premises), invalid (no term, a loose bound variable, a
\ malformed let), exhausted (the fuel), full (a refused allocation) --
\ and that a failed call leaves nothing that changes the next one.
\ Every T{ }T checks the data stack's depth. tests/front/check_whnf.py
\ compares the results with pinned Lean's.
include ../support/tester.fs
include ../support/heap-watch.fs
require ./whnf-cases.fs

\ Terms equal node for node (test only: recursion on the host stack).
: leaf= ( t1 t2 -- flag )
  over lf-term-first@ over lf-term-first@ = >r lf-term-second@ swap lf-term-second@ = r> and ;
: same? ( t1 t2 -- flag )
  2dup = if 2drop true exit then
  over lf-term-tag@ over lf-term-tag@ <> if 2drop false exit then
  over lf-term-tag@ lf-term-binary-tag? 0= if leaf= exit then
  over lf-term-first@ over lf-term-first@ recurse 0= if 2drop false exit then
  lf-term-second@ swap lf-term-second@ recurse ;
: whnf= ( term expected -- flag outcome ) >r lf-whnf-core r> swap >r same? r> ;
: same-out ( a b outcome -- flag outcome ) >r same? r> ;
: tag-out ( t outcome -- tag outcome ) >r lf-term-tag@ r> ;
: recm ( major -- t ) >r rec fm app fz app fs app r> app ;

\ ---- Full: the first call's first allocation (its spine's slab)
\ refused; the same call again works.
T{ 1 heap-refusals ! fk succ swap app recm lf-whnf-core heap-refusals @ -> -1 outcome-full 0 }T
T{ fk succ swap app recm lf-whnf-core nip -> outcome-ok }T

\ ---- Iota: Nat.rec on Nat.succ k and Nat.zero, extra arguments, stuck.
T{ fk succ swap app recm  fs fk app fk recm app whnf= -> true outcome-ok }T
T{ zero recm fz whnf= -> true outcome-ok }T
T{ zero recm fx app  fz fx app whnf= -> true outcome-ok }T
T{ fk recm dup whnf= -> true outcome-ok }T
T{ rec fm app fz app fs app dup whnf= -> true outcome-ok }T
T{ ?n recm dup whnf= -> true outcome-ok }T
\ Beta, zeta, heads.
T{ nat 0 bv lam fk app fk whnf= -> true outcome-ok }T
T{ nat fk fs 0 bv app let fs fk app whnf= -> true outcome-ok }T
T{ ?f fk app fs fk app whnf= ?h fk app dup whnf= -> true outcome-ok true outcome-ok }T
T{ fg fk app fs fk app whnf= fg sfun whnf= -> true outcome-ok true outcome-ok }T
T{ succ fk app dup whnf= -> true outcome-ok }T
\ A have (Lean's ldecl with nondep := true; plan FE1g-1): its value is
\ hidden, so whnf leaves the variable and its application as they are
\ (Lean's whnfEasyCases unfolds only a let with nondep := false).
nat sfun lf-lctx-have made constant fh
T{ fh lf-fvar-let? fh lf-fvar-nondep? fg lf-fvar-let? fg lf-fvar-nondep? -> false true true false }T
T{ fh lf-fvar-value fg lf-fvar-value fk lf-fvar-value fk lf-fvar-nondep? -> sfun sfun -1 false }T
T{ nat zero lf-lctx-have made lf-fvar-value -> zero }T
T{ fh dup whnf= fh fk app dup whnf= -> true outcome-ok true outcome-ok }T

\ ---- Frames: the major premise and a projection's structure are
\ reduced first (a let, a beta step, an assigned metavariable, an inner
\ recursor), then the step resumes.
: pair ( a b -- t ) >r >r l0 l0 2 s" Prod.mk" cn nat app nat app r> app r> app ;
T{ fa fb pair 0 proj fa whnf= fa fb pair 1 proj fb whnf= -> true outcome-ok true outcome-ok }T
T{ fp 0 proj dup whnf= fa fb pair 2 proj dup whnf= -> true outcome-ok true outcome-ok }T
T{ sfun fb pair 0 proj fk app fs fk app whnf= -> true outcome-ok }T
T{ nat fk succ 0 bv app let recm  fs fk app fk recm app whnf= -> true outcome-ok }T
T{ nat 0 bv lam fk app recm dup whnf= -> true outcome-ok }T
T{ rec fm app fz succ swap app app fs app zero app recm  fs fz app fz recm app whnf=
   -> true outcome-ok }T
T{ fk succ swap app 0 proj fk whnf= -> true outcome-ok }T
\ The structure or major premise is reduced by whnf (S2 merge A): what it
\ cannot decide is unsupported (reduceNat? of Nat.add (a, b)); a
\ definition it leaves (Nat.add alone has a `_sunfold`, so it stays)
\ leaves the projection or the recursor as they are.
T{ 0 s" Nat.add" cn fa fb pair app 0 proj lf-whnf-core -> -1 outcome-unsupported }T
T{ 0 s" Nat.add" cn 0 proj dup whnf= -> true outcome-ok }T
T{ 0 s" Nat.add" cn recm dup whnf= -> true outcome-ok }T

\ ---- A definition that the data says is no matcher and no auxiliary
\ recursor stays, as Lean's whnfCore leaves it (S1 merge B: whnfCore asks
\ the facts; without them it is unsupported, below).
T{ 0 s" Nat.add" cn fk app fk app dup whnf= -> true outcome-ok }T
\ ---- Unsupported: a quotient's lift, a K-like recursor, a structure's
\ eta, a Nat.succ that whnf may fold.
: quot ( -- t ) lv1 lv1 2 s" Quot.lift" cn nat app fx app nat app fs app fb app ;
T{ quot lv1 1 s" Quot.mk" cn nat app fx app fa app app lf-whnf-core
   -> -1 outcome-unsupported }T
T{ lv1 lv1 2 s" Eq.rec" cn nat app fa app fm app fx app fa app fk app lf-whnf-core
   -> -1 outcome-unsupported }T
: prod-rec ( -- t ) lv1 l0 l0 3 s" Prod.rec" cn nat app nat app fm app fs app ;
T{ prod-rec fp app lf-whnf-core -> -1 outcome-unsupported }T
T{ fk succ swap app succ swap app recm lf-whnf-core -> -1 outcome-unsupported }T

\ ---- Invalid: no term, a loose bound variable, a malformed let.
T{ -1 lf-whnf-core 0 bv lf-whnf-core -> -1 outcome-invalid -1 outcome-invalid }T
T{ fk fs 0 lf-let-make must lf-whnf-core -> -1 outcome-invalid }T
T{ 0 bv fk app lf-whnf-core -> -1 outcome-invalid }T

\ ---- Fuel: each step spends one; none left is exhausted.
: twice ( -- t ) nat 0 bv lam  nat 0 bv lam fk app app ;
T{ 2 lf-whnf-fuel! twice lf-whnf-core -> -1 outcome-exhausted }T
T{ 3 lf-whnf-fuel! twice fk whnf= -> true outcome-ok }T
T{ 0 lf-whnf-fuel! twice fk whnf= -> true outcome-ok }T

\ ---- getStuckMVar?.
T{ ?n lf-whnf-stuck -> ?n true outcome-ok }T
T{ ?n recm lf-whnf-stuck ?h fk app lf-whnf-stuck -> ?n true outcome-ok ?h true outcome-ok }T
T{ fk recm lf-whnf-stuck fs fk app lf-whnf-stuck -> false outcome-ok false outcome-ok }T
T{ ?n succ swap app recm lf-whnf-stuck -> false outcome-ok }T
T{ 0 s" Nat.add" cn fk app fk app lf-whnf-stuck -> false outcome-ok }T
\ With a metavariable, a definition that is no projection function has no
\ stuck one (getProjectionFnInfo? none; branch s2-tactics).
T{ 0 s" Nat.add" cn ?n app fk app lf-whnf-stuck -> false outcome-ok }T
T{ ?f lf-whnf-stuck fp s" Prod" menv-name 0 lf-proj-of made lf-whnf-stuck
   -> false outcome-unsupported false outcome-unsupported }T
T{ -1 lf-whnf-stuck fk lf-whnf-stuck -> false outcome-invalid false outcome-ok }T
\ A class's projection function (Add.add, getProjectionFnInfo? fromClass;
\ WHNF.lean:345-370): stuck on a plain metavariable instance; with the
\ instance known, on the first explicit argument that is a plain
\ metavariable (issue 1408), a parameter's too (OfNat.ofNat's n), none
\ when only an implicit one holds one; an explicit argument holding one
\ under a head Lean answers none for (a constructor, a local) is passed,
\ under another (a recursor, a class projection, S.toP, a projection) or
\ one past the type's binders unsupported (not ported); a
\ projection function of no class (Array.toList) none; a definition
\ named S.toP (an auxiliary parent projection, not in the data)
\ unsupported.
: add-of ( alpha inst a b -- t ) >r >r >r >r l0 1 s" Add.add" cn r> app r> app r> app r> app ;
0 s" instAddNat" cn constant inst-add
: ofnat-of ( n inst -- t ) >r >r l0 1 s" OfNat.ofNat" cn nat app r> app r> app ;
T{ nat ?q fk fk add-of lf-whnf-stuck -> ?q true outcome-ok }T
T{ nat inst-add fk ?n add-of lf-whnf-stuck -> ?n true outcome-ok }T
T{ nat inst-add ?n ?h add-of lf-whnf-stuck -> ?n true outcome-ok }T
T{ ?n inst-add fk fk add-of lf-whnf-stuck -> false outcome-ok }T
T{ nat inst-add succ ?n app ?h add-of lf-whnf-stuck -> ?h true outcome-ok }T
T{ nat inst-add succ ?n app fk add-of lf-whnf-stuck -> false outcome-ok }T
T{ nat inst-add ?n recm fk add-of lf-whnf-stuck -> false outcome-unsupported }T
T{ nat inst-add nat inst-add ?n fk add-of fk add-of lf-whnf-stuck -> false outcome-unsupported }T
\ An explicit argument whose head is a metavariable is not passed as none
\ (review s2-tactics re-check M2).
T{ nat inst-add ?f fk app fk add-of lf-whnf-stuck -> false outcome-unsupported }T
T{ nat inst-add 0 s" List.toByteArray" cn ?n app fk add-of lf-whnf-stuck
   -> false outcome-unsupported }T
T{ nat inst-add ?q 0 proj fk add-of lf-whnf-stuck -> false outcome-unsupported }T
T{ nat inst-add fk ?n app ?h add-of lf-whnf-stuck -> ?h true outcome-ok }T
T{ nat inst-add fk fk add-of ?n app lf-whnf-stuck -> false outcome-unsupported }T
T{ ?n 0 s" instOfNatNat" cn fk app ofnat-of lf-whnf-stuck -> ?n true outcome-ok }T
T{ l0 1 s" Array.toList" cn nat app ?n app lf-whnf-stuck -> false outcome-ok }T
T{ 0 s" List.toByteArray" cn ?n app lf-whnf-stuck -> false outcome-unsupported }T
T{ 0 s" List.toByteArray" cn fk app lf-whnf-stuck -> false outcome-ok }T
\ A K-like recursor is never stuck (isRecStuck?).
: eq-rec ( major -- t ) >r lv1 lv1 2 s" Eq.rec" cn nat app fa app fm app fx app fa app r> app ;
T{ ?h eq-rec lf-whnf-stuck ?h eq-rec lf-whnf-core -> false outcome-ok -1 outcome-unsupported }T

\ ---- A delayed-assigned metavariable at the head: unsupported (Lean's
\ whnfDelayedAssigned? is not ported).
nat mv-natural lf-mvar-new made constant ?d
0 fx lf-delay-fvar made drop  0 ?d ?n 1 lf-mvar-delay made drop
T{ ?d fk app lf-whnf-core ?d lf-whnf-stuck -> -1 outcome-unsupported false outcome-unsupported }T
T{ ?d fk app recm lf-whnf-core -> -1 outcome-unsupported }T

\ ---- More heads: a let, a pi (done), a constant no declaration has
\ (Lean's find? none: done); leaves alone.
: unknown ( -- t ) 0 s" motive" menv-part lf-name-generation @ lv-pairs 0 lf-cref-new must
  lf-cterm-new must drop ;
T{ nat fs 0 bv let fk app fs fk app whnf= -> true outcome-ok }T
T{ nat nat lf-term-pi must fk app dup whnf= unknown fk app dup whnf=
   -> true outcome-ok true outcome-ok }T
T{ ?f sfun whnf= fk dup whnf= -> true outcome-ok true outcome-ok }T
\ More major premises: another type's constructor (no rule), a wrong
\ number of levels (Lean's failK), a structure's constructor applied to
\ exactly its parameters and fields.
T{ fa fb pair recm dup whnf= -> true outcome-ok }T
T{ 0 s" Nat.rec" cn fm app fz app fs app zero app dup whnf= -> true outcome-ok }T
T{ prod-rec fa fb pair app fs fa app fb app whnf= -> true outcome-ok }T
\ More of getStuckMVar?: a constant no declaration has, a quotient's
\ lift, a constructor at the head, a Nat.succ whnf may fold.
T{ unknown fk app lf-whnf-stuck succ fk app lf-whnf-stuck -> false outcome-ok false outcome-ok }T

\ ---- Review fe1c-2 L1: a projection of a literal (toCtorIfLit:
\ unsupported) or of a constant no declaration has (whnf leaves it, as
\ Lean's getUnfoldableConstNoEx? does: the projection stays, S2), Nat.succ
\ alone as a major premise (fewer arguments than the rule's fields: the
\ rule's right side takes none), a malformed let whose binder is an
\ application, and a recursor of a nested block (Lean.Syntax.rec, three
\ motives).
: three ( -- t ) s" 3" lf-hterm-decimal must drop ;
T{ three 0 proj lf-whnf-core unknown 0 proj dup whnf=
   -> -1 outcome-unsupported true outcome-ok }T
T{ succ recm  nat fs 0 bv app rec fm app fz app fs app 0 bv app app lam whnf=
   -> true outcome-ok }T
T{ fk fs fk app 0 lf-let-make must lf-whnf-core -> -1 outcome-invalid }T
: syntax-rec ( n -- t ) >r lv1 1 s" Lean.Syntax.rec" cn r> 0 ?do fk app loop ;
T{ 11 syntax-rec lf-whnf-core 10 syntax-rec dup whnf= -> -1 outcome-unsupported true outcome-ok }T
T{ quot fa app lf-whnf-stuck -> false outcome-unsupported }T
T{ ?n succ swap app succ swap app recm lf-whnf-stuck -> false outcome-unsupported }T
\ A projection of a metavariable, alone or applied, is stuck on it (review
\ fe1c-2 M1); of anything else it would need whnf.
T{ ?q 0 proj fk app lf-whnf-stuck ?q 0 proj lf-whnf-stuck -> ?q true outcome-ok ?q true outcome-ok }T
T{ fa fb pair 0 proj fk app lf-whnf-stuck -> false outcome-unsupported }T
\ A major premise whose head is no constant is never read as one (review
\ M2): a lambda; a free variable whose number is Nat.succ's reference's.
T{ nat 0 bv lam recm lf-whnf-stuck -> false outcome-ok }T
variable want
: fvar-at ( n -- fvar ) want ! begin nat lf-lctx-local made dup lf-term-first@ want @ < while
  drop repeat ;
succ lf-term-first@ fvar-at constant ftwin
T{ ftwin lf-term-first@ succ lf-term-first@ = -> true }T
T{ ftwin zero app recm lf-whnf-stuck -> false outcome-ok }T

\ ---- whnf (lf-meta-whnf, S1 appendix D) in the fed environment, with the
\ slice's format 2 facts: what whnfCore leaves, a definition that is no
\ matcher and no auxiliary recursor included, unless reduceNat? or
\ unfoldDefinition? would act (unsupported, never a guess: smart
\ unfolding is S2); at the configured transparency.
: meta-whnf= ( term expected -- flag outcome ) >r lf-meta-whnf r> swap same-out ;
: nlit ( u -- t ) lf-hterm-cell must drop ;
: inst-hadd ( -- t ) l0 1 s" instHAdd" cn nat app 0 s" instAddNat" cn app ;
: hadd-kx ( -- t ) l0 l0 l0 3 s" HAdd.hAdd" cn nat app nat app nat app inst-hadd app fk app fx app ;
: in-mode ( term mode -- e' outcome )
  lf-defeq-mode >r lf-defeq-mode! lf-meta-whnf r> lf-defeq-mode! ;
\ Sorts, binders, literals, an inert head stay; a beta step is taken.
T{ nat nat tpi dup meta-whnf= lv1 sort dup meta-whnf= 2 nlit dup meta-whnf=
   -> true outcome-ok true outcome-ok true outcome-ok }T
T{ fk fx app dup meta-whnf= nat fs 0 bv app lam fk app fs fk app meta-whnf=
   -> true outcome-ok true outcome-ok }T
\ An instance (instance-reducible): unfolded at default to its structure
\ (S2 merge A), left at reducible (whnfR); whnfCore alone leaves it (no
\ matcher, no auxiliary recursor: S1 merge B).
: hadd-mk ( -- t ) l0 l0 l0 3 s" HAdd.mk" cn nat app nat app nat app
  nat nat l0 1 s" Add.add" cn nat app 0 s" instAddNat" cn app 1 bv app 0 bv app lam lam app ;
T{ inst-hadd hadd-mk meta-whnf= inst-hadd lf-meta-whnf-r nip inst-hadd dup lf-whnf-core same-out
   -> true outcome-ok outcome-ok true outcome-ok }T
T{ inst-hadd dup lf-meta-whnf-r drop same? lf-defeq-mode -> true lf-tr-default }T
\ A projection function (semireducible in the data): unfolded at default,
\ left at reducible; a matcher, an auxiliary recursor, Nat operations
\ reduceNat? might fold; Nat.succ of a variable stays.
T{ hadd-kx lf-meta-whnf hadd-kx dup lf-meta-whnf-r drop same?
   -> -1 outcome-unsupported true }T
T{ 0 s" Nat.add.match_1" cn fk app lf-meta-whnf -> -1 outcome-unsupported }T
T{ lv1 1 s" Nat.casesOn" cn fk app lf-meta-whnf -> -1 outcome-unsupported }T
\ (Nat.add k x: reduceNat? gets no value for an operand that holds a free
\ variable, Lean's withNatValue, and reducible leaves Nat.add; s2-tactics.)
T{ 0 s" Nat.add" cn fk app fx app dup lf-meta-whnf-r drop same? -> true }T
T{ succ 2 nlit app lf-meta-whnf succ fk app dup meta-whnf=
   -> -1 outcome-unsupported true outcome-ok }T
\ unfoldDefinition? by transparency: Nat.add alone stays (it has a
\ `_sunfold`: a constant then never unfolds, WHNF.lean:918); Nat.div
\ (irreducible) unfolds only at all, to its value; a theorem never (S2
\ merge A: getUnfoldableConst? gives none for one); at instances a
\ projection function applied (unfoldProjInst?), not alone.
T{ 0 s" Nat.add" cn dup meta-whnf= 0 s" Nat.add" cn lf-tr-reducible in-mode nip
   -> true outcome-ok outcome-ok }T
: nat-div ( -- t ) 0 s" Nat.div" cn ;
T{ nat-div dup meta-whnf= nat-div lf-tr-all in-mode tag-out
   -> true outcome-ok lf-tag-lam outcome-ok }T
T{ 0 s" Nat.zero_add" cn dup meta-whnf= 0 s" Nat.zero_add" cn dup lf-tr-all in-mode same-out
   -> true outcome-ok true outcome-ok }T
T{ hadd-kx lf-tr-instances in-mode l0 l0 l0 3 s" HAdd.hAdd" cn lf-tr-instances in-mode nip
   -> -1 outcome-unsupported outcome-ok }T
\ At instances, an application of a definition that is no projection and
\ that the transparency does not unfold stays (three arguments: no Nat
\ operation reduceNat? reads).
T{ 0 s" Nat.div" cn fk app fx app fk app dup lf-tr-instances in-mode drop same?
   -> true }T
\ Without the facts (no data read against the stage) a definition's head
\ is unsupported, as in whnfCore.
0 lf-menv-stage!
T{ inst-hadd lf-meta-whnf-r -> -1 outcome-unsupported }T
T{ 0 s" Nat.add" cn fk app fk app lf-whnf-core -> -1 outcome-unsupported }T
menv-lib lf-menv-stage!
\ The budget: none left is exhausted, nothing spent then.
T{ 0 lf-meta-budget! nat lf-meta-whnf lf-meta-budget lf-meta-default-budget lf-meta-budget!
   -> -1 outcome-exhausted 0 }T
\ whnfForall: a pi from whnf, else the term itself; a failure passes on.
T{ nat nat tpi fk app lf-meta-whnf-forall nat lf-meta-whnf-forall hadd-kx lf-meta-whnf-forall
   -> nat nat tpi fk app lf-whnf-core drop outcome-ok nat outcome-ok -1 outcome-unsupported }T
T{ nat nat nat tpi lam fk app lf-meta-whnf-forall swap nat nat tpi same? -> outcome-ok true }T
\ A constant no declaration has stays (getUnfoldableConstNoEx?); applied,
\ it is invalid (Lean: unknown constant); a type whnf cannot decide
\ passes its failure on through instantiateForall, one that is no pi is
\ invalid.
T{ unknown dup meta-whnf= unknown fk app lf-meta-whnf -> true outcome-ok -1 outcome-invalid }T
T{ hadd-kx fx 1 rxs lf-meta-instantiate-forall inst-hadd fx 1 rxs lf-meta-instantiate-forall
   -> -1 outcome-unsupported -1 outcome-invalid }T
\ instantiateForall: (a : Sort 1) -> a with Nat is Nat; (fun _ => Nat ->
\ Nat) k, a pi only after whnf, with x is Nat; one parameter too many is
\ invalid (Lean throws); none leaves the term.
T{ lv1 sort 0 bv tpi nat 1 rxs lf-meta-instantiate-forall -> nat outcome-ok }T
T{ nat nat nat tpi lam fk app fx 1 rxs lf-meta-instantiate-forall -> nat outcome-ok }T
T{ nat nat tpi fk fx 2 rxs lf-meta-instantiate-forall nat 0 rxs lf-meta-instantiate-forall
   -> -1 outcome-invalid nat outcome-ok }T
\ A negative count is invalid: nothing read, no whnf step spent (review
\ s1-meta-a L4).
T{ lf-meta-budget nat fk 1 rxs drop -1 lf-meta-instantiate-forall rot lf-meta-budget -
   -> -1 outcome-invalid 0 }T

\ ---- unfoldDefinition? (lf-meta-unfold, S2 merge A; check_unfold.py
\ compares the same terms with pinned Lean). Made: outParam Nat is Nat,
\ the transparency unfolds it (reducible) or not (none); none: Nat.add
\ alone (a `_sunfold`), a matcher, a theorem, a lambda, a constant no
\ declaration has (getUnfoldableConstNoEx?), one universe argument too
\ many (deltaDefinition's count).
: outp ( t -- t' ) >r lv1 1 s" outParam" cn r> app ;
: unf ( t mode -- e' flag outcome ) ['] lf-meta-unfold at-mode ;
: stays ( t mode -- flag' outcome same? ) over >r unf rot r> same? ;
: add-kx ( -- t ) l0 1 s" Add.add" cn nat app 0 s" instAddNat" cn app fk app fx app ;
T{ nat outp lf-tr-default unf nat outp lf-tr-reducible unf -> nat true outcome-ok nat true outcome-ok }T
T{ nat outp lf-tr-none stays 0 s" Nat.add" cn lf-tr-default stays
   -> false outcome-ok true false outcome-ok true }T
: match1 ( -- t ) lv1 1 s" Nat.add.match_1" cn fk app ;
T{ match1 lf-tr-default stays 0 s" Nat.zero_add" cn lf-tr-all stays
   -> false outcome-ok true false outcome-ok true }T
T{ nat fk lam lf-tr-default stays unknown lf-tr-default stays lv1 lv1 2 s" outParam" cn nat app
   lf-tr-default stays -> false outcome-ok true false outcome-ok true false outcome-ok true }T
\ Unsupported: Nat.add applied has a `_sunfold` (the smart path, merge B);
\ without the facts (no data read against the stage) any definition.
T{ 0 s" Nat.add" cn fk app fx app lf-meta-unfold -> -1 false outcome-unsupported }T
0 lf-menv-stage!
T{ nat outp lf-meta-unfold -> -1 false outcome-unsupported }T
menv-lib lf-menv-stage!
\ Invalid: no term; an application of a constant no declaration has
\ (Lean: unknown constant). Exhausted: no budget left. Full: the first
\ allocation refused; the same call again works.
T{ -1 lf-meta-unfold unknown fk app lf-meta-unfold -> -1 false outcome-invalid -1 false outcome-invalid }T
T{ 0 lf-meta-budget! nat outp lf-meta-unfold lf-meta-default-budget lf-meta-budget!
   -> -1 false outcome-exhausted }T
T{ 1 heap-refusals ! hadd-kx lf-tr-instances unf -rot 2drop heap-refusals @ -> outcome-full 0 }T
T{ hadd-kx lf-tr-instances unf rot add-kx same? -> true outcome-ok true }T
\ Class fields (unfoldProjInstWhenInstances?): HAdd.hAdd at instances
\ becomes Add.add (its instance's field, whnf of instHAdd at instances);
\ at reducible nothing; at default the projection itself; with a
\ structure no constructor (k) at instances nothing, at default k.1 k x.
T{ hadd-kx lf-tr-instances unf rot add-kx same? hadd-kx lf-tr-reducible stays
   -> true outcome-ok true false outcome-ok true }T
: hadd-kkx ( -- t ) l0 l0 l0 3 s" HAdd.hAdd" cn nat app nat app nat app fk app fk app fx app ;
: k1kx ( -- t ) fk s" HAdd" menv-name 0 lf-proj-of made fk app fx app ;
T{ hadd-kkx lf-tr-instances stays hadd-kkx lf-tr-default unf rot k1kx same?
   -> false outcome-ok true true outcome-ok true }T
\ unfoldProjInst? gives none when its result has no projection at the
\ head (the instance argument missing: a lambda) and for universe
\ arguments other than the declaration's parameters (check_unfold.py
\ compares both with pinned Lean; review s2-unfold-a).
: hadd-nnn ( -- t ) l0 l0 l0 3 s" HAdd.hAdd" cn nat app nat app nat app ;
: hadd-2kx ( -- t ) l0 l0 2 s" HAdd.hAdd" cn nat app nat app nat app inst-hadd app fk app fx app ;
T{ hadd-nnn lf-tr-instances stays hadd-2kx lf-tr-instances stays
   -> false outcome-ok true false outcome-ok true }T
\ A structure projection (Prod.fst, reducible, no class's): at reducible
\ unfoldDefault leaves its projection (no class field to reduce).
: fst-ab ( -- t ) l0 l0 2 s" Prod.fst" cn nat app nat app fa fb pair app ;
T{ fst-ab lf-tr-reducible unf rot fa fb pair 0 proj same? -> true outcome-ok true }T
\ The transparency on entry is back after every call, a failed one too.
T{ lf-tr-instances lf-defeq-mode! hadd-kx lf-meta-unfold 2drop drop lf-defeq-mode
   0 s" Nat.add" cn fk app fx app lf-meta-unfold 2drop drop lf-defeq-mode lf-tr-default lf-defeq-mode!
   -> lf-tr-instances lf-tr-instances }T

\ ---- whnfCore's parts by whnf (S2 merge A): a projection's structure
\ (instHAdd Nat instAddNat unfolds to its constructor at default, not at
\ reducible); whnfCoreAtDefEq's by whnfAtMostI (id unfolds at default
\ and implicit, not at instances); a recursor's major premise (id Nat Nat.zero is
\ Nat.zero); a literal major premise (toCtorIfLit) unsupported.
: add-lam ( -- t ) nat nat l0 1 s" Add.add" cn nat app 0 s" instAddNat" cn app 1 bv app 0 bv app lam lam ;
T{ inst-hadd 0 proj add-lam whnf= inst-hadd 0 proj dup lf-tr-reducible ' lf-whnf-core at-mode
   same-out -> true outcome-ok true outcome-ok }T
: id-ab ( -- t ) lv1 1 s" id" cn l0 l0 2 s" Prod" cn nat app nat app app fa fb pair app 0 proj ;
T{ id-ab fa whnf= id-ab dup lf-whnf-core-at-defeq same-out lf-defeq-mode
   -> true outcome-ok true outcome-ok lf-tr-default }T
\ At implicit transparency too (id is implicit-reducible: whnf at
\ implicit would unfold it, whnfAtMostI does not; review s2-unfold-a H1).
T{ id-ab dup lf-tr-implicit ' lf-whnf-core-at-defeq at-mode same-out -> true outcome-ok }T
\ A part that fails (Nat.add k x by whnfAtMostI: reduceNat?'s guard) still
\ gives the caller its transparency back.
T{ 0 s" Nat.add" cn fk app fx app 0 proj lf-whnf-core-at-defeq nip lf-defeq-mode
   -> outcome-unsupported lf-tr-default }T
T{ lv1 1 s" id" cn nat app zero app recm fz whnf= 5 nlit recm lf-whnf-core
   -> true outcome-ok -1 outcome-unsupported }T
\ whnf goes on after an unfolding: outParam Nat is Nat; instHAdd's
\ projection applied reaches Add.add's field, Nat.add k x, where
\ reduceNat?'s guard answers unsupported (merge B).
T{ nat outp nat meta-whnf= hadd-kx lf-meta-whnf -> true outcome-ok -1 outcome-unsupported }T

\ ---- isWFRec (reduceRec, WHNF.lean:229): Acc.rec and WellFounded.rec
\ reduce their major premise at transparency all when the configured one
\ is default (wc-wf-bump, before the major premise's frame runs); any
\ other recursor, or another transparency, keeps it. The slice has
\ neither recursor: their names are added to the context's tier.
: tier-str ( prefix c-addr u -- n ) lf-name-tier name-str ok? must ;
0 s" Acc" tier-str s" rec" tier-str drop  0 s" WellFounded" tier-str s" rec" tier-str drop
: bumped ( c-addr u mode -- mode' )
  lf-defeq-mode >r lf-defeq-mode! 0 -rot cn wc wc-head ! wc-wf-bump lf-defeq-mode
  r> lf-defeq-mode! ;
T{ s" Acc.rec" lf-tr-default bumped s" WellFounded.rec" lf-tr-default bumped
   s" Nat.rec" lf-tr-default bumped -> lf-tr-all lf-tr-all lf-tr-default }T
T{ s" Acc.rec" lf-tr-reducible bumped s" WellFounded.rec" lf-tr-instances bumped
   s" Acc.rec" lf-tr-all bumped lf-defeq-mode -> lf-tr-reducible lf-tr-instances lf-tr-all
   lf-tr-default }T

\ ---- Stale leaves: after the contexts are emptied, every metavariable
\ and free variable made before is invalid.
lf-mctx-reset
T{ ?n lf-whnf-core ?n fk app lf-whnf-core ?n lf-whnf-stuck
   -> -1 outcome-invalid -1 outcome-invalid false outcome-invalid }T
lf-lctx-reset
T{ fk lf-whnf-core fk fa app lf-whnf-core -> -1 outcome-invalid -1 outcome-invalid }T
\ The fed input as loading left it: everything above wrote only above
\ its marks (S1 §1, trust point 3).
T{ lf-input-intact? -> true }T

bye
