/-
An explicit argument whose expected type is a pi (Lean 4.35.0
Elab/Term/TermElabM.lean, useImplicitLambda): Lean adds an implicit
lambda when the pi's binder is implicit or instance implicit, and none
when it is explicit or strict implicit. LeanForth reads the binder's kind
from the head's declared type (src/front/elab-app.fs, ea-no-lambda?):
explicit or strict implicit, the argument is elaborated as it is; any
other kind stops as not supported yet (error 133, an implicit lambda,
plan FE2), where Lean accepts.

tests/front/implicit-lambda.ndjson and its elaboration data are this
file's export by the pinned exporter (module IL):

  cp implicit-lambda.lean IL.lean && lean -o IL.olean IL.lean
  LEAN_PATH=. scripts/export.sh implicit-lambda.ndjson IL -- IL.z IL.impl IL.zs IL.strict
  LEAN_PATH=. scripts/export-elab.sh implicit-lambda.elab.ndjson implicit-lambda.ndjson IL

The two theorems after the namespace are the Lean twins of
tests/front/s2-lambda-impl.lf and s2-lambda-strict.lf (tests/front/check_s2.py):
Lean accepts both; LeanForth accepts t_strict and refuses t_impl with 133.
-/
namespace IL
theorem z {p : Prop} : p → p := fun h => h
/-- An explicit parameter whose type is a pi with an implicit binder. -/
theorem impl (_f : ∀ {p : Prop}, p → p) : True := True.intro
theorem zs ⦃p : Prop⦄ : p → p → p := fun h _ => h
/-- An explicit parameter whose type is a pi with a strict-implicit binder. -/
theorem strict (_f : ∀ ⦃p : Prop⦄, p → p → p) : True := True.intro
end IL

theorem t_impl : True := IL.impl IL.z
theorem t_strict : True := IL.strict IL.zs
