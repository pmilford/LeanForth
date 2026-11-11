-- A shared statement instantiated at a universe argument (review rvPSE,
-- finding M1). tests/cli/sharing.lean's `sharedAnd`, 2^40 paths through
-- about 120 nodes, made universe-polymorphic, with the universe `u` at the
-- outer binder and in every leaf of the shared part:
-- * `sharedAndU.{u}`: `∀ (α : Sort u) (P : Prop) (h : P), T 40` with
--   `T 0 = ∀ (β : Sort u), P` and `T (k+1) = T k ∧ T k`, proved by
--   `And.intro (p k) (p k)` 40 times over, `p 0 = fun (β : Sort u) => h`;
-- * `useU := sharedAndU.{0}`, whose type is that statement at `u := 0`,
--   so inference instantiates the stored type's universe parameter
--   (instantiate_type_lparams with a nonempty list, instantiate.cpp
--   236-253): Lean's replace rebuilds each shared node once; LeanForth's
--   level substitution walked every path and ran out of fuel until agent
--   FX7 (2026-11-11).
-- Two wrong twins of `useU`, which Lean's kernel must reject with
-- declTypeMismatch (checked below, not added): the universe argument 1
-- instead of 0 (`sharedAndU.{1}`, whose outer binder is then `Sort 1`),
-- and the stated type's leaves `∀ (β : Sort 1), P` instead of `Sort 0`
-- (a mismatch only at the leaves, below the shared nodes).
-- tests/cli/test_leanforth.py checks LeanForth's verdicts on the export
-- and on the twins, written into copies of it; tests/cli/export-check.sh
-- rebuilds the export and its manifest and compares them with the
-- committed files.
import Lean
open Lean Elab Command

namespace SharingUniverse

def andType : Nat → Expr → Expr
  | 0, p => p
  | k+1, p => let t := andType k p; mkApp2 (.const ``And []) t t

def andProof : Nat → Expr → Expr → Expr
  | 0, _, h => h
  | k+1, p, h => let t := andType k p; let q := andProof k p h
    mkApp4 (.const ``And.intro []) t t q q

def prop : Expr := .sort .zero

-- `∀ (β : Sort v), P` under the binders α, P and h.
def leaf (v : Level) : Expr := .forallE `β (.sort v) (.bvar 2) .default

-- `∀ (α : Sort u) (P : Prop) (h : P), T 40` with the leaves `leaf v`.
def stmt (u v : Level) : Expr :=
  .forallE `α (.sort u) (.forallE `P prop (.forallE `h (.bvar 0)
    (andType 40 (leaf v)) .default) .default) .default

def thm (n : Name) (ls : List Name) (t v : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := ls, type := t, value := v, all := [n] }

def polyDecl : Declaration :=
  let u := Level.param `u
  thm `sharedAndU [`u] (stmt u u)
    (.lam `α (.sort u) (.lam `P prop (.lam `h (.bvar 0)
      (andProof 40 (leaf u) (.lam `β (.sort u) (.bvar 1) .default)) .default) .default)
      .default)

-- `useU` stated with the leaves at `v`, proved by `sharedAndU.{arg}`.
def useDecl (arg v : Level) : Declaration :=
  thm `useU [] (stmt .zero v) (.const `sharedAndU [arg])

def verdict : Except Kernel.Exception Kernel.Environment → String
  | .ok _ => "accepted"
  | .error (.declTypeMismatch ..) => "declTypeMismatch"
  | .error _ => "another exception"

end SharingUniverse

open SharingUniverse in
run_cmd do
  liftCoreM <| addDecl polyDecl
  let base := (← getEnv).toKernelEnv
  for (arg, v) in [(Level.one, Level.zero), (Level.zero, Level.one)] do
    let got := verdict (base.addDeclCore 100000000 1000 (useDecl arg v) none)
    unless got == "declTypeMismatch" do
      throwError "a wrong twin: Lean's verdict is {got}, expected declTypeMismatch"
  liftCoreM <| addDecl (useDecl .zero .zero)

#print axioms useU
