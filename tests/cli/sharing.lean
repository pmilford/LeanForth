-- Proofs whose terms share subterms along exponentially many paths, as
-- `omega` proofs do in Lean's `Init`. Lean's kernel keeps a node's data
-- (loose bound variables, free variables) in the node and caches each
-- substitution per shared node and offset (replace_fn.cpp), so it checks
-- them in time that grows with the nodes; LeanForth's audits and
-- substitutions did so once per path and ran out of fuel (agent EX,
-- 2026-11-10). Built with Lean's own `Expr` values, so the shared nodes
-- are one object each, and the export shares them too:
-- * `sharedAnd`: `∀ (P : Prop) (h : P), T 40` with `T 0 = P` and
--   `T (k+1) = T k ∧ T k`, proved by `And.intro (p k) (p k)` 40 times
--   over: 2^40 paths through about 120 nodes;
-- * `sharedBeta`: `∀ (h : True), True`, proved by `q 10`, where `q 0 = h`
--   and `q (k+1) = (fun y : True => q k) (q k)`: each `q k` is shared
--   under one more binder than its twin, so a bound variable in it names
--   `y` in one place and `h` in the other.
-- Each has a wrong twin, which Lean's kernel must reject with
-- appTypeMismatch (checked below, not added): the innermost proof `h` of
-- `sharedAnd` replaced by `P`, and `q 0` of `sharedBeta` replaced by
-- `True`. tests/cli/test_leanforth.py checks LeanForth's verdicts on the
-- export and on the twins, written into a copy of it.
-- tests/cli/export-check.sh rebuilds the export and its manifest and
-- compares them with the committed files.
import Lean
open Lean Elab Command

namespace Sharing

def andType : Nat → Expr → Expr
  | 0, p => p
  | k+1, p => let t := andType k p; mkApp2 (.const ``And []) t t

def andProof : Nat → Expr → Expr → Expr
  | 0, _, h => h
  | k+1, p, h => let t := andType k p; let q := andProof k p h
    mkApp4 (.const ``And.intro []) t t q q

def prop : Expr := .sort .zero
def trueE : Expr := .const ``True []

def thm (n : Name) (t v : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := t, value := v, all := [n] }

def andDecl (wrong : Bool) : Declaration :=
  thm `sharedAnd
    (.forallE `P prop (.forallE `h (.bvar 0) (andType 40 (.bvar 1)) .default) .default)
    (.lam `P prop (.lam `h (.bvar 0)
      (andProof 40 (.bvar 1) (if wrong then .bvar 1 else .bvar 0)) .default) .default)

def betaProof (wrong : Bool) : Nat → Expr
  | 0 => if wrong then trueE else .bvar 0
  | k+1 => let q := betaProof wrong k; .app (.lam `y trueE q .default) q

def betaDecl (wrong : Bool) : Declaration :=
  thm `sharedBeta (.forallE `h trueE trueE .default) (.lam `h trueE (betaProof wrong 10) .default)

def verdict : Except Kernel.Exception Kernel.Environment → String
  | .ok _ => "accepted"
  | .error (.appTypeMismatch ..) => "appTypeMismatch"
  | .error _ => "another exception"

end Sharing

open Sharing in
run_cmd do
  let base := (← getEnv).toKernelEnv
  for d in [andDecl true, betaDecl true] do
    let got := verdict (base.addDeclCore 100000000 1000 d none)
    unless got == "appTypeMismatch" do
      throwError "a wrong twin: Lean's verdict is {got}, expected appTypeMismatch"
  liftCoreM <| addDecl (andDecl false)
  liftCoreM <| addDecl (betaDecl false)

-- Both in one statement, whose axioms Lean lists.
theorem sharing : True := (fun _ _ => trivial) @sharedAnd @sharedBeta

#print axioms sharing
