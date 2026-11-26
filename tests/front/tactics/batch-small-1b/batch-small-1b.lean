-- Pinned Lean twins of tests/front/tactics/batch-small-1b/*.lf (plan row TB2, small tactics 1:
-- iterate): tactic_check.py --lean writes batch-small-1b.golden from this file's terms, which
-- LeanForth's must equal node for node.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

theorem it_two (a b : Nat) (h : a = b) (k : b = a) : (a = b ∧ a = b) ∧ b = a := by
  iterate 2 constructor
  exact h
  exact h
  exact k
theorem it_zero (a b : Nat) (h : a = b) : a = b := by
  iterate 0 exact h
  exact h
theorem it_seq (a b : Nat) (h : a = b) : (a = b ∧ a = b) ∧ (a = b ∧ a = b) := by
  constructor
  iterate 2
    constructor
    exact h
    exact h
theorem it_nest (a b : Nat) (h : a = b) (k : b = a) : (a = b ∧ a = b) ∧ b = a := by
  iterate 2 iterate 1 constructor
  exact h
  exact h
  exact k

def pl (l : Level) : String := match l.toNat with
  | some n => toString n
  | none => "?l"

partial def sx : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .const n us => return n.toString ++ ".{" ++ String.intercalate "," (us.map pl) ++ "}"
  | .app f a => return s!"(app {← sx f} {← sx a})"
  | .lam _ t b _ => return s!"(lam {← sx t} {← sx b})"
  | .forallE _ t b _ => return s!"(pi {← sx t} {← sx b})"
  | .letE _ t v b nd => return s!"({if nd then "let-nd" else "let"} {← sx t} {← sx v} {← sx b})"
  | .sort l => return "Sort " ++ pl l
  | .lit (.natVal n) => return toString n
  | .mdata _ e => sx e
  | e => return s!"?? {e}"

def dump (n : Name) : MetaM Unit := do
  let some (.thmInfo i) := (← getEnv).find? n | IO.println s!"{n} ??"
  IO.println s!"{n} type {← sx i.type}"
  IO.println s!"{n} value {← sx i.value}"

#eval do
  for n in [``it_two, ``it_zero, ``it_seq, ``it_nest] do
    dump n
