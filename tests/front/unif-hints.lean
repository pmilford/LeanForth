/-
The unification hints of a library, with their keys (plan MF1, design
docs/design/MATHLIB_FRONT.md O7). Lean 4.35.0 keeps every `unif_hint` in
`unificationHintExtension`'s discrimination tree (Meta/UnificationHint.lean:37),
keyed by the hint's left-hand side; isDefEqOnFailure's tryUnificationHints
(:99) asks it with the failing side reduced at reducible transparency.
LeanForth's isDefEq does not read the hint table: a failure with a definition
at the head of either side answers unsupported (src/front/defeq.fs,
de-hints). So a hint is covered exactly when its root key is a constant
that is a definition.

Usage, with LEAN_PATH set to the library's .olean folders:

  lean --run tests/front/unif-hints.lean MODULE...

prints, per hint, its name, its root key and the root constant's kind,
sorted, then the number of hints and of those not keyed at a definition.
Its output for pinned Mathlib is docs/programming/ELABORATION_DATA.md's
list (section "Unification hints"), checked by tests/front/check_mathlib_slice.py.
-/
import Lean
open Lean Meta

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.defnInfo _) => "definition"
  | some (.thmInfo _) => "theorem"
  | some (.opaqueInfo _) => "opaque"
  | some (.axiomInfo _) => "postulate"
  | some (.inductInfo _) => "inductive"
  | some (.ctorInfo _) => "constructor"
  | some (.recInfo _) => "recursor"
  | some (.quotInfo _) => "quotient"
  | none => "none"

def keyText (env : Environment) : DiscrTree.Key → String × String
  | .const n a => (s!"{n}/{a}", kindOf env n)
  | k => (s!"{repr k}", "not a constant")

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let mods := args.toArray.map fun m => { module := m.toName : Import }
  let env ← importModules mods {} (loadExts := true)
  let tree := (unificationHintExtension.getState env).discrTree
  let rows := tree.root.foldl (init := #[]) fun acc k t =>
    let (key, kind) := keyText env k
    t.foldValues (init := acc) fun acc n => acc.push s!"{n} {key} {kind}"
  let rows := rows.qsort (· < ·)
  for r in rows do IO.println r
  let bad := rows.filter fun r => !(r.endsWith " definition")
  IO.println s!"{rows.size} hints, {bad.size} not keyed at a definition"
  return 0
