\ Lean's whnf with delta, in a check of the checked environment
\ (src/kernel/whnf.fs; ADR 0014 Q4, Q5; plan task 4.2.2c): the rows
\ whnf.* of tests/reference/definitional-equality.tsv as Lean's
\ Kernel.whnf answers them -- a definition unfolds, an @[irreducible] one
\ too (the attribute is the elaborator's; the export gives it a regular
\ hint), a theorem unfolds (ADR 0014 G5), an opaque declaration stays --
\ and its other cases: universe arguments substituted, the arguments
\ applied again and beta-reduced, a chain of definitions, an axiom, a
\ constant of the check's own block, K7, the whnf of ensure_sort and
\ ensure_pi (rows sort.* and pi.*; their verdicts against pinned Lean in
\ make test-definitional-equality-differential).
\ Each case's last declaration is the probe: while it is checked, its
\ value is put in whnf on a job's frames, and the result is kept; the
\ declaration before it, when the case gives one, holds the expected
\ term as its value. Test-only; nothing here accepts a theorem.
include ../support/tester.fs
require ../support/first-checker-driver.fs

variable probe-node  variable probe-outcome  variable probe-same  variable probe-diag
\ The value of declaration d.
: value-of ( d -- node ) lf-input-decl lf-idecl-value @ ;
\ Whether the result equals the expected term, by Lean's ==, compared
\ before the check's scratch is rolled back.
: probe-compare ( -- )
  probe-outcome @ ok? fc-last 0> and 0= if exit then
  probe-node @ fc-last 1- value-of 100000 lf-expr-equal ok? and probe-same ! ;
: probe-whnf ( -- )
  100000 lf-minfer-start-env lf-env-limit value-of lf-minfer-frames lf-whnf-on
  probe-outcome ! probe-node ! lf-diag-code@ probe-diag ! probe-compare ;
: probing ( -- ) lf-env-limit fc-last = if probe-whnf then lf-check-declaration ;
: probe-run ( -- )
  -1 probe-node ! outcome-invalid probe-outcome ! false probe-same !
  lf-input-end ok? must 64 lf-env-new ok? must dup lf-env-use ok? must
  ['] probing ['] fc-no-maker lf-env-run ok? must lf-env-free ok? must ;
\ Review rvCACHE L2: in a check, the caches on, inference refuses a node
\ made during its job (no source node) as invalid, even when a source node
\ of the same skeleton, the probe's value Sort 0, already has a cached type.
\ With sharing on the store would give the source node back (compact-store
\ plan step S4), so the fresh node is made with it off.
variable fresh-out
: fresh-sort ( -- node )
  false lf-term-sharing! 0 lf-term-symbolic-sort must true lf-term-sharing! ;
: probe-fresh ( -- )
  100000 lf-minfer-start-env lf-env-limit value-of lf-minfer-walk nip probe-outcome !
  fresh-sort lf-minfer-walk nip fresh-out ! ;
: fresh-probing ( -- ) lf-env-limit fc-last = if probe-fresh then lf-check-declaration ;
: fresh-run ( -- )
  outcome-invalid probe-outcome ! outcome-ok fresh-out !
  lf-input-end ok? must 64 lf-env-new ok? must dup lf-env-use ok? must
  ['] fresh-probing ['] fc-no-maker lf-env-run ok? must lf-env-free ok? must ;
\ The probe's result: whether it unfolded (another node), and whether it
\ equals the expected term.
: unfolds? ( -- flag outcome ) probe-node @ fc-last value-of <> probe-outcome @ ;
: expected? ( -- flag outcome ) probe-same @ probe-outcome @ ;

\ whnf.definition: def dqDefW (A : Prop) : Prop := A → A unfolds to its
\ value, the stored node itself (no universe arguments: no copy).
fc-case whnf-definition
fc-decl before def safe dqDefW 0 TYPE P S z S z VALUE L S z P V 0 V 1
fc-decl check def safe probe 0 TYPE P S z S z VALUE C dqDefW 0
T{ probe-run probe-node @ 0 value-of = probe-outcome @ -> true outcome-ok }T
\ whnf.theorem: theorem dqThmW : ∀ A : Prop, A → A := fun _ h => h.
fc-case whnf-theorem
fc-decl before thm safe dqThmW 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
fc-decl check thm safe probe 0 TYPE P S z P V 0 V 1 VALUE C dqThmW 0
T{ probe-run probe-node @ 0 value-of = probe-outcome @ -> true outcome-ok }T
\ whnf.opaque: Lean's whnf leaves it (opaque declarations never unfold,
\ plan task 4.2.6): is_delta refuses the kind (lf-whnf-valued?).
fc-case whnf-opaque
fc-decl before opq safe dqOpaqueW 0 TYPE P S z S z VALUE L S z P V 0 V 1
fc-decl check def safe probe 0 TYPE P S z S z VALUE C dqOpaqueW 0
T{ probe-run unfolds? -> false outcome-ok }T
create a-decl /lf-idecl allot
a-decl /lf-idecl erase  lf-kind-opaque a-decl lf-idecl-kind !
T{ a-decl 0 lf-whnf-valued? -> false }T
lf-kind-definition a-decl lf-idecl-kind !
T{ a-decl 0 lf-whnf-valued? a-decl 1 lf-whnf-valued? -> true false }T
lf-kind-theorem a-decl lf-idecl-kind !
T{ a-decl 0 lf-whnf-valued? -> true }T
\ An axiom never unfolds (plan task 5.3.1).
fc-case whnf-axiom
fc-decl before ax safe dqAx 0 TYPE P S z S z VALUE none
fc-decl check def safe probe 0 TYPE P S z S z VALUE C dqAx 0
T{ probe-run unfolds? -> false outcome-ok }T

\ The arguments applied again, then beta: dqDefW Prop is Prop → Prop.
fc-case whnf-applied
fc-decl before def safe dqDefW 0 TYPE P S z S z VALUE L S z P V 0 V 1
fc-decl before def safe expected 0 TYPE S s z VALUE P S z S z
fc-decl check def safe probe 0 TYPE S s z VALUE A C dqDefW 0 S z
T{ probe-run expected? -> true outcome-ok }T
\ Universe arguments for the parameters (instantiate_value_lparams):
\ dqLift.{u} (A : Sort u) : Sort u := A, at universe 1, is fun A : Sort 1 => A.
fc-case whnf-universe
fc-decl before def safe dqLift 1 u TYPE P S p u S p u VALUE L S p u V 0
fc-decl before def safe expected 0 TYPE P S s z S s z VALUE L S s z V 0
fc-decl check def safe probe 0 TYPE P S s z S s z VALUE C dqLift 1 s z
T{ probe-run expected? -> true outcome-ok }T
\ A chain: dqC1 A := dqC0 A, dqC0 A := A → A; dqC1 Prop unfolds both.
fc-case whnf-chain
fc-decl before def safe dqC0 0 TYPE P S z S z VALUE L S z P V 0 V 1
fc-decl before def safe dqC1 0 TYPE P S z S z VALUE L S z A C dqC0 0 V 0
fc-decl before def safe expected 0 TYPE S s z VALUE P S z S z
fc-decl check def safe probe 0 TYPE S s z VALUE A C dqC1 0 S z
T{ probe-run expected? -> true outcome-ok }T
\ A head that does not unfold stays (an application of a variable).
fc-case whnf-stays
fc-decl check def safe probe 0 TYPE P S s z S s z VALUE L S s z V 0
T{ probe-run unfolds? -> false outcome-ok }T
\ A constant Lean's environment does not hold (N1) is no delta target:
\ whnf leaves it, and the lookup's note is put back (no failure: the
\ diagnostic stays clear; the probe's own check then rejects it, N1).
fc-case whnf-absent
fc-decl check def safe probe 0 TYPE S s z VALUE C absent 0
T{ probe-run unfolds? probe-diag @ -> false outcome-ok lf-diag-none }T
fc-case fresh-node
fc-decl check def safe probe 0 TYPE S s z VALUE S z
T{ fresh-run probe-outcome @ fresh-out @ -> outcome-ok outcome-invalid }T

\ ensure_sort and ensure_pi through whnf, with the rows' verdicts:
\ sort.after-unfolding (A : dqProp, accepted), sort.not-after-unfolding
\ (A : dqPropFn, typeExpected: S2), pi.after-unfolding (f : dqPropFn,
\ accepted), pi.not-after-unfolding (f : dqProp, funExpected: F1).
variable the-env
: check-last ( -- outcome code )
  lf-input-end ok? must 64 lf-env-new ok? must dup the-env ! lf-env-use ok? must
  ['] lf-check-declaration ['] fc-no-maker lf-env-run ok? must
  lf-diag-code@ lf-env-view ok? must fc-last lf-env-outcome swap
  the-env @ lf-env-free ok? must ;
fc-case sort-after-unfolding
fc-decl before def safe dqProp 0 TYPE S s z VALUE S z
fc-decl check thm safe t16 0 TYPE P C dqProp 0 P V 0 V 1 VALUE L C dqProp 0 L V 0 V 0
T{ check-last -> outcome-ok lf-diag-none }T
fc-case sort-not-after-unfolding
fc-decl before def safe dqPropFn 0 TYPE S s z VALUE P S z S z
fc-decl check thm safe t17 0 TYPE P C dqPropFn 0 P V 0 V 1 VALUE L C dqPropFn 0 L V 0 V 0
T{ check-last -> outcome-rejected lf-diag-domain-type }T
fc-case pi-after-unfolding
fc-decl before def safe dqPropFn 0 TYPE S s z VALUE P S z S z
fc-decl check thm safe t18 0 TYPE P C dqPropFn 0 P S z P A V 1 V 0 A V 2 V 1 VALUE L C dqPropFn 0 L S z L A V 1 V 0 V 0
T{ check-last -> outcome-ok lf-diag-none }T
fc-case pi-not-after-unfolding
fc-decl before def safe dqProp 0 TYPE S s z VALUE S z
fc-decl check thm safe t19 0 TYPE P C dqProp 0 P S z P A V 1 V 0 A V 2 V 1 VALUE L C dqProp 0 L S z L A V 1 V 0 V 0
T{ check-last -> outcome-rejected lf-diag-function-expected }T

\ Let terms (core/let-terms.fs; plan task 4.2.3). Zeta: let x : Sort 1 :=
\ Sort 0; x is Sort 0; a let at the head of an application is reduced
\ first, then beta: (let f : Sort 1 -> Sort 1 := fun X => X; f) Sort 0 is
\ Sort 0.
fc-case zeta
fc-decl before def safe expect 0 TYPE S s z VALUE S z
fc-decl check def safe probe 0 TYPE S s z VALUE E 0 S s z S z V 0
T{ probe-run expected? -> true outcome-ok }T
fc-case zeta-head
fc-decl before def safe expect 0 TYPE S s z VALUE S z
fc-decl check def safe probe 0 TYPE S s z VALUE A E 0 P S s z S s z L S s z V 0 V 0 S z
T{ probe-run expected? -> true outcome-ok }T
\ Malformed let terms are invalid in whnf and in inference: a let whose
\ second child is a Pi (no lambda), of either flag; so is a projection
\ leaf alone. The audit refuses such lets, and a projection whose first
\ child is no projection leaf, but passes a well-formed one.
: sort0 ( -- node ) 0 fc-sort ;
: sort1 ( -- node ) lf-level-tag-succ 0 0 fc-level fc-sort ;
: pi00 ( -- node ) sort0 sort0 lf-tag-pi fc-binary ;
: bad-let ( -- node ) sort0 pi00 lf-tag-let fc-binary ;
: bad-let-nd ( -- node ) sort0 pi00 lf-tag-let-nondep fc-binary ;
: leaf ( -- node ) lf-tag-proj 0 0 lf-term-add must ;
: bad-proj ( -- node ) sort0 sort0 lf-tag-projection fc-binary ;
: good-proj ( -- node ) leaf sort0 lf-tag-projection fc-binary ;
: whnf-of ( node -- outcome ) 1000 lf-minfer-start-env lf-minfer-frames lf-whnf-on nip ;
: infer-of ( node -- outcome ) 1000 lf-minfer-start-env lf-minfer-walk nip ;
: audit-of ( node -- outcome ) dup lf-term-identity must 1000 lf-cterm-check ;
fc-case malformed-let
T{ bad-let whnf-of bad-let-nd whnf-of leaf whnf-of
   -> outcome-invalid outcome-invalid outcome-invalid }T
T{ bad-let infer-of bad-let-nd infer-of leaf infer-of
   -> outcome-invalid outcome-invalid outcome-invalid }T
T{ bad-let audit-of bad-let-nd audit-of bad-proj audit-of good-proj audit-of
   -> outcome-invalid outcome-invalid outcome-invalid outcome-ok }T
\ Inference (infer_let): the type of let x : Sort 1 := Sort 0; fun y : x
\ => y is the let term let x := Sort 0; x -> x (mk_pi keeps a variable
\ the type mentions); of let x : Sort 1 := Sort 0; Sort 0 it is Sort 1
\ (a dead let dropped). let x : Sort 0 := Sort 0; x is rejected
\ (letTypeMismatch), but inferred aside (infer-only, no check) as Sort 0.
\ == compares the nonDep flag.
: dep-let ( -- node ) 0 sort1 sort0 0 fc-bvar 0 fc-bvar lf-tag-lam fc-binary fc-let ;
: dead-let ( -- node ) 0 sort1 sort0 sort0 fc-let ;
: wrong-let ( -- node ) 0 sort0 sort0 0 fc-bvar fc-let ;
: type-of ( node -- type outcome ) 100000 lf-minfer-start-env lf-minfer-walk ;
: aside-of ( node -- type outcome )
  100000 lf-minfer-start-env true lf-minfer-aside ! lf-minfer-walk ;
: same? ( a b -- flag ) 1000 lf-expr-equal ok? and ;
fc-case let-inference
T{ dep-let type-of ok? swap dup lf-let? swap lf-let-type sort1 same? -> true true true }T
T{ dead-let type-of ok? swap sort1 same? -> true true }T
T{ wrong-let type-of nip lf-diag-code@ -> outcome-rejected lf-diag-let-value-apart }T
T{ wrong-let aside-of ok? swap sort0 same? -> true true }T
T{ 0 sort1 sort0 sort0 fc-let 1 sort1 sort0 sort0 fc-let same? dead-let dead-let same?
   -> false true }T
\ A let and a projection end a spine (Lean's get_app_fn stops at
\ Expr.letE and Expr.proj); their data words count both children at the
\ node's own depth: let x : Sort 1 := Sort 0; #1 and the projection of #0
\ each have the loose range 1 (the let's body sees one binder more).
: range-of ( node -- range ) lf-term-data@ must lf-data-loose ;
: outer-let ( -- node ) 0 sort1 sort0 1 fc-bvar fc-let ;
: var-proj ( -- node ) leaf 0 fc-bvar lf-tag-projection fc-binary ;
T{ dead-let sort0 lf-tag-app fc-binary lf-mhead-spine -> dead-let 1 }T
T{ var-proj sort0 lf-tag-app fc-binary lf-mhead-spine -> var-proj 1 }T
T{ outer-let range-of var-proj range-of dead-let range-of -> 1 1 0 }T

\ has_loose_bvars and has_fvar, as is_def_eq_core and lazy delta ask them,
\ read from the node's data word for no fuel (plan task 6.5.5; Lean's
\ cached node data, expr.h): #0 has a loose bound variable, which has_fvar
\ counts too (whnf.fs); a free variable applied to itself has a free
\ variable and no loose bound variable.
: scanned ( node xt -- flag outcome fuel )
  >r 100 lf-minfer-frames frame-fuel ! lf-minfer-frames r> execute
  lf-minfer-frames frame-fuel @ ;
lf-lctx-reset
0 lf-term-bvar drop constant wb0
wb0 lf-lctx-local drop constant wfx
wfx wfx lf-term-app drop constant wfxx
T{ wb0 ' lf-whnf-loose? scanned -> true outcome-ok 100 }T
T{ wb0 ' lf-whnf-free? scanned -> true outcome-ok 100 }T
T{ wfxx ' lf-whnf-loose? scanned -> false outcome-ok 100 }T
T{ wfxx ' lf-whnf-free? scanned -> true outcome-ok 100 }T

\ R3's scope guard (iota.fs, review rvIO M1): an open major premise counts as
\ scoped only on the inference job's frames AND with its loose range within
\ the scope's depth; any other (a bound variable no scope holds) is not.
1 lf-term-bvar drop constant wb1
: scoped-at ( node depth -- flag outcome )
  lf-minfer-context-depth ! lf-minfer-frames lf-iota-scoped?
  0 lf-minfer-context-depth ! ;
T{ wb0 0 scoped-at -> false outcome-ok }T
T{ wb0 1 scoped-at -> true outcome-ok }T
T{ wb1 1 scoped-at -> false outcome-ok }T
T{ wb1 2 scoped-at -> true outcome-ok }T
T{ wfxx 0 scoped-at -> true outcome-ok }T
bye
