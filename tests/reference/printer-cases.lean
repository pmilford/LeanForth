/-
Lean's own printing of the term-printer cases (tests/present/print-cases.fs).
Each case builds the same expression the Forth test builds, binder names,
binder kinds and universe levels included, and prints it with `ppExpr`
under Lean's default options plus `pp.unicode.fun`. Output lines are
`case<TAB>text`; tests/present/printer-differential.py compares them with
tests/present/print-cases.golden. Nothing here is a theorem.
-/
import Lean
open Lean Meta

universe u

/-- The constant of `constant-fixture.lean`, with one implicit parameter. -/
def fixtureId {α : Sort u} (x : α) : α := x

namespace PrinterCases

def prp : Expr := mkSort Level.zero
def ty : Expr := mkSort Level.one
def bv (i : Nat) : Expr := mkBVar i
def lam (n : Name) (bi : BinderInfo) (t b : Expr) : Expr := mkLambda n bi t b
def pi (n : Name) (bi : BinderInfo) (t b : Expr) : Expr := mkForall n bi t b
def lu : Level := mkLevelParam `u
def lv : Level := mkLevelParam `v
def lw : Level := mkLevelParam `w
def ex := BinderInfo.default
def im := BinderInfo.implicit
def si := BinderInfo.strictImplicit
def ii := BinderInfo.instImplicit
/-- A hygienic binder name, as elaboration makes them: `inst._@.main._hyg.1`. -/
def hyg (n : Name) : Name := addMacroScope `main n 1

def out (name : String) (e : Expr) : MetaM Unit := do
  IO.println s!"{name}\t{← ppExpr e}"

end PrinterCases

open PrinterCases

set_option pp.unicode.fun true

-- Sorts and universe levels.
#eval out "prop" prp
#eval out "type" ty
#eval out "type-1" (mkSort (mkLevelSucc Level.one))
#eval out "sort-max" (mkSort (mkLevelMax lu lv))
#eval out "type-max" (mkSort (mkLevelMax (mkLevelSucc lu) (mkLevelSucc lv)))
#eval out "sort-imax" (mkSort (mkLevelIMax lu lv))
#eval out "type-succ" (mkSort (mkLevelSucc (mkLevelSucc lu)))
#eval out "type-max-succ" (mkSort (mkLevelSucc (mkLevelSucc (mkLevelMax lu lv))))
#eval out "sort-max-right" (mkSort (mkLevelMax lu (mkLevelMax lv lw)))
#eval out "sort-max-left" (mkSort (mkLevelMax (mkLevelMax lu lv) lw))
#eval out "sort-succ-max" (mkSort (mkLevelMax (mkLevelSucc lu) lv))

-- Binders: grouping, arrows, ∀, fun.
#eval out "identity-type" (pi `P im prp (pi `proof ex (bv 0) (bv 1)))
#eval out "identity-value" (lam `P im prp (lam `proof ex (bv 0) (bv 0)))
#eval out "composition-type"
  (pi `A im prp (pi `B im prp (pi `C im prp
    (pi `f ex (pi `x ex (bv 2) (bv 2)) (pi `g ex (pi `x ex (bv 2) (bv 2))
      (pi `value ex (bv 4) (bv 3)))))))
#eval out "composition-value"
  (lam `A im prp (lam `B im prp (lam `C im prp
    (lam `f ex (pi `x ex (bv 2) (bv 2)) (lam `g ex (pi `x ex (bv 2) (bv 2))
      (lam `value ex (bv 4) (mkApp (bv 1) (mkApp (bv 2) (bv 0)))))))))
#eval out "poly-type" (pi `α im (mkSort (mkLevelMax lu lv)) (pi `x ex (bv 0) (bv 1)))
#eval out "dep-explicit" (pi `α ex ty (pi `x ex (bv 0) (bv 1)))
#eval out "rfc-1834" (pi `x ex prp (pi `y ex prp (bv 1)))
#eval out "strict" (pi `x si prp (pi `h ex (bv 0) (bv 1)))
#eval out "inst-named" (pi `α im prp (pi `h ii (bv 0) (bv 1)))
#eval out "inst-anon" (pi `α im prp (pi (hyg `inst) ii (bv 0) (bv 1)))
#eval out "fun-inst-used" (lam `α im prp (lam `h ii (bv 0) (bv 0)))
#eval out "fun-inst-unused" (lam `α im prp (lam `h ii (bv 0) (lam `x ex (bv 1) (bv 0))))
#eval out "fun-strict" (lam `α si prp (lam `β si prp (bv 1)))
#eval out "nested-app"
  (lam `A im prp (lam `f ex (pi `x ex (bv 0) (bv 1)) (lam `x ex (bv 1)
    (mkApp (bv 1) (mkApp (bv 1) (bv 0))))))

-- Names restored without capture.
#eval out "shadow-fun" (lam `x ex prp (lam `x ex prp (bv 0)))
#eval out "capture-fun" (lam `x ex prp (lam `x ex prp (bv 1)))
#eval out "shadow-pi" (pi `x ex prp (pi `x ex prp (bv 0)))
#eval out "capture-pi" (pi `x ex prp (pi `x ex prp (bv 1)))
#eval out "capture-twice" (pi `x ex prp (pi `x ex prp (pi `x ex prp (mkApp (mkApp (bv 2) (bv 1)) (bv 0)))))
#eval out "capture-suffix"
  (lam `x ex prp (lam `x_1 ex prp (lam `x ex prp (mkApp (mkApp (bv 2) (bv 1)) (bv 0)))))
#eval out "hygienic-fun" (lam (hyg `a) ex prp (bv 0))
#eval out "anonymous-fun" (lam .anonymous ex prp (bv 0))
#eval out "name-shapes" (lam `x' ex prp (lam `x₁ ex prp (lam `h_2 ex prp (lam `a_b ex prp
  (lam `α' ex prp (lam `proof₁₂ ex prp (mkApp (mkApp (mkApp (mkApp (mkApp (bv 5) (bv 4)) (bv 3))
    (bv 2)) (bv 1)) (bv 0))))))))

-- Parentheses.
#eval out "fun-last-arg"
  (lam `g ex (pi `h ex (pi `x ex prp prp) prp) (mkApp (bv 0) (lam `x ex prp (bv 0))))
#eval out "fun-inner-arg"
  (lam `f ex (pi `h ex (pi `x ex prp prp) (pi `p ex prp prp)) (lam `p ex prp
    (mkApp (mkApp (bv 1) (lam `x ex prp (bv 0))) (bv 0))))
#eval out "beta-head" (lam `p ex prp (mkApp (lam `x ex prp (bv 0)) (bv 0)))
#eval out "fun-head-implicit"
  (lam `p ex prp (mkApp (mkApp (lam `a im prp (lam `b ex (bv 0) (bv 0))) (bv 0)) (bv 0)))
#eval out "forall-domain" (pi `h ex (pi `x ex prp (bv 0)) prp)
#eval out "arrow-domain" (pi `h ex (pi `x ex prp prp) prp)
#eval out "sort-arg" (lam `f ex (pi `x ex (mkSort (mkLevelSucc Level.one)) prp)
  (mkApp (bv 0) (mkSort Level.one)))
#eval out "type1-arg" (lam `f ex (pi `x ex (mkSort (mkLevelSucc (mkLevelSucc Level.one))) prp)
  (mkApp (bv 0) (mkSort (mkLevelSucc Level.one))))

-- Constants: hidden implicit arguments, @, universe arguments.
#eval out "const-implicit" (lam `P im prp (lam `h ex (bv 0)
  (mkApp (mkApp (mkConst ``fixtureId [Level.zero]) (bv 1)) (bv 0))))
#eval out "const-bare" (mkConst ``fixtureId [Level.one])
#eval out "const-partial" (mkApp (mkConst ``fixtureId [Level.one]) prp)
#eval out "const-unknown-levels" (lam `y ex prp (mkApp (mkConst `undeclaredC [lu]) (bv 0)))
#eval out "const-unknown" (lam `y ex prp (mkApp (mkConst `undeclaredK []) (bv 0)))
#eval out "const-dotted" (mkConst `My.name.space [])

set_option pp.universes true

#eval out "universes-implicit" (lam `P im prp (lam `h ex (bv 0)
  (mkApp (mkApp (mkConst ``fixtureId [Level.zero]) (bv 1)) (bv 0))))
#eval out "universes-list" (mkConst `undeclaredL [mkLevelMax lu lv, mkLevelSucc lu, Level.zero])
