import LeanForthFirstChecker
import LeanForthFirstCheckerTerms

/-!
# Deep terms: plan task 6.2.0, against the pinned Lean kernel

Mathlib's terms nest up to 1,221 deep, and Lean's kernel checks far
deeper ones: every case below at depths 2,000 and 10,000 gets Lean's
verdict here, with `maxRecDepth` 1,000 as in every reference file. Deeper,
Lean counts its recursion: the application chain is refused with
`deepRecursion` from 16 * maxRecDepth - 1 (15,999 here, 8,191 at Lean's
default 512), lambda and successor chains are not counted
(`deep-recursion.lean`; docs/project/BEYOND_LEAN.md, BL-9). For n = 2,000
and 10,000:

* `lam`: `∀ (P : Prop), P → … → P` with n hypotheses, proved by
  `fun P h₁ … hₙ => h₁`: binders nest n deep (accepted); and the same proof
  returning `P` itself, which is no proof (declTypeMismatch; LeanForth's
  rules D4 down all n binders, then D2);
* `app`: `(fun x => x) ((fun x => x) (… h))`, n applications deep, at type
  `P` (accepted), and the same around `P` instead of `h`, a Prop where a
  proof of `P` is expected (appTypeMismatch; rule D2);
* `level`: `Sort (u + n) : Sort (u + n + 1)` (accepted), and the claim
  `Sort (u + n)` (declTypeMismatch).

At n = 2,000 only (review rvKC B-L5), three more shapes, each also wrong:
* `dom`: `T(n)`, where `T0 = Prop` and `T(k+1) = T(k) → Prop`, Pis nested
  in domain position, a definition of type `Type` (accepted), or `Prop`
  (declTypeMismatch);
* `spine`: `fun (P : Prop) (f : P → … → P) (x : P) => f x … x`, an
  application spine of n arguments in function position (accepted), or
  with `P` for the first `x` (appTypeMismatch);
* `maxsort`: `Sort (max u (… u)) : Sort (u+1)`, a Sort of a max chain n
  deep (accepted), or claimed at `Sort u` (declTypeMismatch).
Lean counts recursion for the first two (`deep-recursion.lean`), but far
below its limit here.

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

/-- `T(n)` with `T0 = Prop`, `T(k+1) = T(k) → Prop`, at `Type` or, wrong,
`Prop`. -/
def domDecl (n : Nat) (wrong : Bool) : Declaration :=
  let rec go : Nat → Expr
    | 0 => prop
    | k+1 => .forallE `x (go k) prop .default
  defn (.mkSimple s!"dom{n}") (.sort (if wrong then .zero else .succ .zero)) (go n)

/-- `fun P f x => f x … x` (n arguments), or, wrong, `f P x … x`. -/
def spineDecl (n : Nat) (wrong : Bool) : Declaration :=
  let rec arrows : Nat → Nat → Expr
    | k, 0 => .bvar k
    | k, j+1 => .forallE `a (.bvar k) (arrows (k+1) j) .default
  let fty := arrows 0 n
  let rec app : Nat → Expr
    | 0 => .bvar 1
    | k+1 => .app (app k) (if wrong && k == 0 then .bvar 2 else .bvar 0)
  thm (.mkSimple s!"spine{n}")
    (.forallE `P prop (.forallE `f fty (.forallE `x (.bvar 1) (.bvar 2) .default) .default) .default)
    (.lam `P prop (.lam `f fty (.lam `x (.bvar 1) (app n) .default) .default) .default)

/-- `Sort (max u (… u))` (n maxes) at `Sort (u+1)` or, wrong, `Sort u`. -/
def maxSortDecl (n : Nat) (wrong : Bool) : Declaration :=
  let u := Level.param `u
  let rec go : Nat → Level
    | 0 => u
    | k+1 => .max u (go k)
  defn (.mkSimple s!"maxsort{n}") (.sort (if wrong then u else .succ u)) (.sort (go n)) [`u]

def shapesFor (n : Nat) : List Case :=
  [ { id := s!"depth{n}.dom", decl := domDecl n false,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"Pis nested {n} deep in domain position" },
    { id := s!"depth{n}.dom-wrong", decl := domDecl n true,
      lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
      what := "claimed in Prop" },
    { id := s!"depth{n}.spine", decl := spineDecl n false,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"an application spine of {n} arguments" },
    { id := s!"depth{n}.spine-wrong", decl := spineDecl n true,
      lean := "appTypeMismatch", leanforth := "rejected", rule := "D2",
      what := "the first argument is P, a Prop" },
    { id := s!"depth{n}.maxsort", decl := maxSortDecl n false,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"a Sort of a max chain {n} deep" },
    { id := s!"depth{n}.maxsort-wrong", decl := maxSortDecl n true,
      lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
      what := "claimed one universe too low" } ]

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

def cases : List Case := casesFor 2000 ++ shapesFor 2000 ++ casesFor 10000

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
