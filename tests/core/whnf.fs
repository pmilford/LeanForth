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

variable probe-node  variable probe-outcome  variable probe-same
\ The value of declaration d.
: value-of ( d -- node ) lf-input-decl lf-idecl-value @ ;
\ Whether the result equals the expected term, by Lean's ==, compared
\ before the check's scratch is rolled back.
: probe-compare ( -- )
  probe-outcome @ ok? fc-last 0> and 0= if exit then
  probe-node @ fc-last 1- value-of 100000 lf-expr-equal ok? and probe-same ! ;
: probe-whnf ( -- )
  100000 lf-minfer-start-env lf-env-limit value-of lf-minfer-frames lf-whnf-on
  probe-outcome ! probe-node ! probe-compare ;
: probing ( -- ) lf-env-limit fc-last = if probe-whnf then lf-check-declaration ;
: probe-run ( -- )
  -1 probe-node ! outcome-invalid probe-outcome ! false probe-same !
  lf-input-end ok? must 64 lf-env-new ok? must dup lf-env-use ok? must
  ['] probing ['] fc-no-maker lf-env-run ok? must lf-env-free ok? must ;
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
\ whnf.opaque: Lean's whnf leaves it (opaque declarations never unfold);
\ LeanForth cannot hold an opaque declaration yet (U1: unsupported, plan
\ task 4.2.6), so a constant naming one is unsupported (K5): a temporary
\ gap, never a guess. is_delta itself refuses the kind (lf-whnf-valued?).
fc-case whnf-opaque
fc-decl before opq safe dqOpaqueW 0 TYPE P S z S z VALUE L S z P V 0 V 1
fc-decl check def safe probe 0 TYPE P S z S z VALUE C dqOpaqueW 0
T{ probe-run probe-node @ probe-outcome @ -> -1 outcome-unsupported }T
create a-decl /lf-idecl allot
a-decl /lf-idecl erase  lf-kind-opaque a-decl lf-idecl-kind !
T{ a-decl 0 lf-whnf-valued? -> false }T
lf-kind-definition a-decl lf-idecl-kind !
T{ a-decl 0 lf-whnf-valued? a-decl 1 lf-whnf-valued? -> true false }T
lf-kind-theorem a-decl lf-idecl-kind !
T{ a-decl 0 lf-whnf-valued? -> true }T
\ An axiom never unfolds; LeanForth holds none yet (U1): unsupported.
fc-case whnf-axiom
fc-decl before ax safe dqAx 0 TYPE P S z S z VALUE none
fc-decl check def safe probe 0 TYPE P S z S z VALUE C dqAx 0
T{ probe-run probe-outcome @ -> outcome-unsupported }T

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
bye
