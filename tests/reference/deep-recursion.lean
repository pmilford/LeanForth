import Lean

/-!
# Lean's `deepRecursion` is a counted recursion depth (BL-9, plan task 6.2.0)

Pinned Lean 4.35.0's kernel refuses a term whose checking recurses too deep
with `Kernel.Exception.deepRecursion`. The limit is not the thread's stack:
it is `addDeclCore`'s `maxRecDepth` argument (the `maxRecDepth` option,
default 512 in Lean's own `addDecl`), counted by `scope_rec_depth` in the
kernel's `infer_type_core`, `whnf_core` and `is_def_eq_core`
(`type_checker.cpp` 329, 469, 1133 at the referee commit). Measured on
2026-11-04: the chain `(fun x => x)` applied n deep to `h : P` is accepted
up to n = 16 * maxRecDepth - 2 and refused from 16 * maxRecDepth - 1, the
same with `lean --tstack=1048576` (1 GiB), `--tstack=8388608` and
`ulimit -s unlimited`, and the same in repeated runs; a lambda chain is
not counted (infer_lambda loops over a telescope). So LeanForth, which has
no such counter, gives Lean's verdict with a large enough `maxRecDepth`
(docs/project/BEYOND_LEAN.md, BL-9). The run fails unless every case gets
the recorded verdict; it prints one line per case.
-/

open Lean

def verdictOf : Except Kernel.Exception Kernel.Environment → String
  | .ok _ => "accepted"
  | .error .deepRecursion => "deepRecursion"
  | .error _ => "error"

/-- `fun P h => (fun x => x) (… (fun x => x) h)`, n applications deep. -/
def appChain (n : Nat) : Declaration :=
  let prop := Expr.sort .zero
  let idP := Expr.lam `x (.bvar 1) (.bvar 0) .default
  let rec body : Nat → Expr
    | 0 => .bvar 0
    | k+1 => .app idP (body k)
  .thmDecl { name := .mkSimple s!"app{n}", levelParams := [],
             type := .forallE `P prop (.forallE `h (.bvar 0) (.bvar 1) .default) .default,
             value := .lam `P prop (.lam `h (.bvar 0) (body n) .default) .default }

/-- `fun P h₁ … hₙ => h₁ : ∀ P, P → … → P`. -/
def lamChain (n : Nat) : Declaration :=
  let prop := Expr.sort .zero
  let rec ty : Nat → Expr
    | 0 => .bvar n
    | k+1 => .forallE `h (.bvar (n - k - 1)) (ty k) .default
  let rec val : Nat → Expr
    | 0 => .bvar (n - 1)
    | k+1 => .lam `h (.bvar (n - k - 1)) (val k) .default
  .thmDecl { name := .mkSimple s!"lam{n}", levelParams := [],
             type := .forallE `P prop (ty n) .default,
             value := .lam `P prop (val n) .default }

/-- (what, maxRecDepth, declaration, Lean's verdict) -/
def cases : List (String × Nat × Declaration × String) :=
  [ ("app 8190", 512, appChain 8190, "accepted"),
    ("app 8191", 512, appChain 8191, "deepRecursion"),
    ("app 15998", 1000, appChain 15998, "accepted"),
    ("app 15999", 1000, appChain 15999, "deepRecursion"),
    ("app 20000", 2000, appChain 20000, "accepted"),
    ("app 100000", 10000, appChain 100000, "accepted"),
    ("lam 10000", 512, lamChain 10000, "accepted") ]

run_cmd do
  let base := (← getEnv).toKernelEnv
  for (what, depth, decl, expected) in cases do
    let got := verdictOf (base.addDeclCore 100000000 depth.toUSize decl none)
    unless got == expected do
      throwError "{what} at maxRecDepth {depth}: Lean's verdict is {got}, expected {expected}"
    IO.println s!"{what} at maxRecDepth {depth}: {got}"
