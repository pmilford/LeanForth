import LeanForthFirstChecker
import LeanForthFirstCheckerTerms

/-!
# Deep terms: plan task 6.2.0, against the pinned Lean kernel

Mathlib's terms nest up to 1,221 deep, and Lean's kernel, which recurses
on the C++ stack, checks far deeper ones: every case below at depths 2,000
and 10,000 gets Lean's verdict here. Deeper, Lean depends on its stack: a
probe on 2026-11-04 found lambda and successor chains still accepted at
100,000, but the application chain refused with `deepRecursion` from
20,000 on (docs/project/BEYOND_LEAN.md). For n = 2,000 and 10,000:

* `lam`: `∀ (P : Prop), P → … → P` with n hypotheses, proved by
  `fun P h₁ … hₙ => h₁`: binders nest n deep (accepted); and the same proof
  returning `P` itself, which is no proof (declTypeMismatch; LeanForth's
  rules D4 down all n binders, then D2);
* `app`: `(fun x => x) ((fun x => x) (… h))`, n applications deep, at type
  `P` (accepted), and the same around `P` instead of `h`, a Prop where a
  proof of `P` is expected (appTypeMismatch; rule D2);
* `level`: `Sort (u + n) : Sort (u + n + 1)` (accepted), and the claim
  `Sort (u + n)` (declTypeMismatch).

Like `universe-scope-terms.lean`, each case is added with
`Kernel.Environment.addDeclCore` to a scratch copy of the kernel
environment, and the run fails unless Lean's verdict is the recorded one. It
prints one `EXPECT <id> <lean> <leanforth> <rule>` line per case, then every
case in the format of `first-checker-terms.lean`, for
`tests/core/lean-differential.py` (tables `depth` and `depth-fed` at 2,000,
`depth-deep-fed` at 10,000).
-/

open Lean FirstChecker

namespace Depth

def prop : Expr := .sort .zero

/-- `∀ P, P → … → P` (n hypotheses) and `fun P h₁ … hₙ => body`, where
body is h₁ or, wrong, P. -/
def lamType (n : Nat) : Expr :=
  let rec go : Nat → Expr
    | 0 => .bvar n
    | k+1 => .forallE `h (.bvar (n - k - 1)) (go k) .default
  .forallE `P prop (go n) .default
def lamValue (n : Nat) (wrong : Bool) : Expr :=
  let rec go : Nat → Expr
    | 0 => if wrong then .bvar n else .bvar (n - 1)
    | k+1 => .lam `h (.bvar (n - k - 1)) (go k) .default
  .lam `P prop (go n) .default
def lamDecl (n : Nat) (wrong : Bool) : Declaration :=
  thm (.mkSimple s!"lam{n}") (lamType n) (lamValue n wrong)

/-- `fun P h => (fun x => x) (… (fun x => x) leaf)`, leaf h or, wrong, P. -/
def appDecl (n : Nat) (wrong : Bool) : Declaration :=
  let idP := Expr.lam `x (.bvar 1) (.bvar 0) .default
  let rec go : Nat → Expr
    | 0 => if wrong then .bvar 1 else .bvar 0
    | k+1 => .app idP (go k)
  thm (.mkSimple s!"app{n}") (.forallE `P prop (.forallE `h (.bvar 0) (.bvar 1) .default) .default)
    (.lam `P prop (.lam `h (.bvar 0) (go n) .default) .default)

/-- `Sort (u + n)`, claimed at `Sort (u + n + 1)` or, wrong, `Sort (u + n)`. -/
def levelDecl (n : Nat) (wrong : Bool) : Declaration :=
  let rec go : Nat → Level
    | 0 => .param `u
    | k+1 => .succ (go k)
  defn (.mkSimple s!"lvl{n}") (.sort (if wrong then go n else .succ (go n))) (.sort (go n)) [`u]

def casesFor (n : Nat) : List Case :=
  [ { id := s!"depth{n}.lam", decl := lamDecl n false,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"{n} binders" },
    { id := s!"depth{n}.lam-wrong", decl := lamDecl n true,
      lean := "declTypeMismatch", leanforth := "rejected", rule := "D4",
      what := "the proof returns P, so its type ends in Prop: D4 down every binder, then D2" },
    { id := s!"depth{n}.app", decl := appDecl n false,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"{n} applications" },
    { id := s!"depth{n}.app-wrong", decl := appDecl n true,
      lean := "appTypeMismatch", leanforth := "rejected", rule := "D2",
      what := "the innermost argument is P, of type Prop, not P (D2)" },
    { id := s!"depth{n}.level", decl := levelDecl n false,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"a level {n} successors deep" },
    { id := s!"depth{n}.level-wrong", decl := levelDecl n true,
      lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
      what := "claimed one universe too low" } ]

def cases : List Case := casesFor 2000 ++ casesFor 10000

end Depth

open Depth in
run_cmd do
  let base := (← getEnv).toKernelEnv
  for c in Depth.cases do
    let got := verdict (base.addDeclCore 100000000 1000 c.decl none)
    unless got == c.lean do
      throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    IO.println s!"EXPECT {c.id} {got} {c.leanforth} {c.rule}"
  for c in Depth.cases do
    IO.println s!"CASE {c.id}"
    IO.println (declLine "check" c.decl)
