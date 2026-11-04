import Lean

/-!
# Lean's `deepRecursion` is a counted recursion depth (BL-9, plan task 6.2.0)

Pinned Lean 4.35.0's kernel refuses a term whose checking recurses too deep
with `Kernel.Exception.deepRecursion`. The limit is not the thread's stack:
it is `addDeclCore`'s `maxRecDepth` argument (the `maxRecDepth` option,
default 512 in Lean's own `addDecl`), counted by `scope_rec_depth` in the
kernel's `infer_type_core`, `whnf_core` and `is_def_eq_core`
(`type_checker.cpp` 329, 469, 1133 at the referee commit). It counts
recursive calls, shape by shape, so no single depth bound reproduces it.
Measured on 2026-11-04, refused from (accepted one below):
* `(fun x => x)` applied n deep to `h : P`: 16 * maxRecDepth - 1 (1,599
  at maxRecDepth 100, 8,191 at 512, 15,999 at 1,000), the same with
  `lean --tstack=1048576` (1 GiB), `--tstack=8388608` and `ulimit -s
  unlimited`, and in repeated runs;
* an application spine `f x … x` (n arguments): 8,191 at 512;
* a Pi nested in domain position, `T(k+1) = T(k) → Prop`: 8,192 at 512;
* not counted at all: a lambda chain (infer_lambda loops over a
  telescope), accepted 10,000 deep at 512, and a Sort of a max chain
  `Sort (max u (… u))`, accepted 100,000 deep at 512.
LeanForth has no such counter and gives Lean's verdict with a large enough
`maxRecDepth`, a resource setting (owner, 2026-11-04;
docs/project/BEYOND_LEAN.md, BL-9). The run fails unless every case gets
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

/-- `T0 = Prop`, `T(k+1) = T(k) → Prop`, a definition of type `Type`: Pis
nested in domain position. -/
def domains (n : Nat) : Declaration :=
  let prop := Expr.sort .zero
  let rec go : Nat → Expr
    | 0 => prop
    | k+1 => .forallE `x (go k) prop .default
  .defnDecl { name := .mkSimple s!"dom{n}", levelParams := [], type := .sort (.succ .zero),
              value := go n, hints := .opaque, safety := .safe }

/-- `fun (P : Prop) (f : P → … → P) (x : P) => f x … x`, n arguments: an
application spine in function position. -/
def spine (n : Nat) : Declaration :=
  let prop := Expr.sort .zero
  let rec arrows : Nat → Nat → Expr
    | k, 0 => .bvar k
    | k, j+1 => .forallE `a (.bvar k) (arrows (k+1) j) .default
  let fty := arrows 0 n
  let rec app : Nat → Expr
    | 0 => .bvar 1
    | k+1 => .app (app k) (.bvar 0)
  .thmDecl { name := .mkSimple s!"spine{n}", levelParams := [],
             type := .forallE `P prop (.forallE `f fty (.forallE `x (.bvar 1) (.bvar 2) .default) .default) .default,
             value := .lam `P prop (.lam `f fty (.lam `x (.bvar 1) (app n) .default) .default) .default }

/-- `Sort (max u (max u … u)) : Sort (u+1)`, n maxes. -/
def maxSort (n : Nat) : Declaration :=
  let u := Level.param `u
  let rec go : Nat → Level
    | 0 => u
    | k+1 => .max u (go k)
  .defnDecl { name := .mkSimple s!"maxsort{n}", levelParams := [`u], type := .sort (.succ u),
              value := .sort (go n), hints := .opaque, safety := .safe }

/-- (what, maxRecDepth, declaration, Lean's verdict) -/
def cases : List (String × Nat × Declaration × String) :=
  [ ("app 1598", 100, appChain 1598, "accepted"),
    ("app 1599", 100, appChain 1599, "deepRecursion"),
    ("app 8190", 512, appChain 8190, "accepted"),
    ("app 8191", 512, appChain 8191, "deepRecursion"),
    ("app 15998", 1000, appChain 15998, "accepted"),
    ("app 15999", 1000, appChain 15999, "deepRecursion"),
    ("app 20000", 2000, appChain 20000, "accepted"),
    ("app 100000", 10000, appChain 100000, "accepted"),
    ("lam 10000", 512, lamChain 10000, "accepted"),
    ("spine 8190", 512, spine 8190, "accepted"),
    ("spine 8191", 512, spine 8191, "deepRecursion"),
    ("domains 8191", 512, domains 8191, "accepted"),
    ("domains 8192", 512, domains 8192, "deepRecursion"),
    ("max sort 100000", 512, maxSort 100000, "accepted") ]

run_cmd do
  let base := (← getEnv).toKernelEnv
  for (what, depth, decl, expected) in cases do
    let got := verdictOf (base.addDeclCore 100000000 depth.toUSize decl none)
    unless got == expected do
      throwError "{what} at maxRecDepth {depth}: Lean's verdict is {got}, expected {expected}"
    IO.println s!"{what} at maxRecDepth {depth}: {got}"
