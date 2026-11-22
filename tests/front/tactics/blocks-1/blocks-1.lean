-- The Lean twins of tests/front/tactics/blocks-1/*.lf (plan row TB2, blocks slice 1): each
-- theorem's type and value as S-expressions (batch-b.lean's printer), which tactic_check.py
-- compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and keeps in
-- blocks-1.golden.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

-- Braces (braces.lf): Lean's bullet · and its { }.
theorem br_and (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  · exact h
  · exact k
theorem br_two (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ (b = a ∧ a = b) := by
  constructor
  · exact h
  · constructor
    · exact k
    · exact h
theorem br_three (a b : Nat) (h : a = b) (k : b = a) :
    a = b ∧ (b = a ∧ (a = b ∧ b = a)) := by
  constructor
  { exact h }
  { constructor
    { exact k }
    { constructor
      { exact h }
      { exact k } } }
theorem br_names (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  · have x : a = b := h
    exact x
  · have x : b = a := k
    exact x
theorem br_ind (n : Nat) : n + 0 = n ∧ 0 + 0 = 0 := by
  induction n with
  | zero => { constructor; { rfl }; { rfl } }
  | succ m ih => { constructor; { rfl }; { rfl } }
theorem br_case (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  case right => · exact k
  case left => · exact h

-- have with a by block (have-by.lf).
theorem hb_symm (a b : Nat) (h : a = b) : b = a := by
  have k : b = a := by exact Eq.symm h
  exact k
theorem hb_inner (a b : Nat) (h : a = b) (k : b = a) : b = a ∧ a = b := by
  have j : a = b ∧ b = a := by
    constructor
    · have x : a = b := h
      exact x
    · exact k
  exact And.intro (And.right j) (And.left j)
theorem hb_twice (a b : Nat) (h : a = b) : a = b ∧ b = a := by
  constructor
  · have x : a = b := by exact h
    exact x
  · have y : b = a := by exact Eq.symm h
    have z : b = a := by exact y
    exact z

-- focus (focus.lf).
theorem fo_and (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  focus
    exact h
  exact k
theorem fo_open (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  focus
    have x : a = b := h
  exact x
  exact k
theorem fo_split (a b : Nat) (h : a = b) (k : b = a) : (a = b ∧ b = a) ∧ a = b := by
  constructor
  focus
    constructor
  exact h
  exact k
  exact h

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
  for n in [``br_and, ``br_two, ``br_three, ``br_names, ``br_ind, ``br_case, ``hb_symm,
      ``hb_inner, ``hb_twice, ``fo_and, ``fo_open, ``fo_split] do
    dump n
