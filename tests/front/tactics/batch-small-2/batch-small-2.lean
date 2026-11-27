-- Pinned Lean twins of tests/front/tactics/batch-small-2/*.lf (plan row 9.4.8z12, small
-- tactics 2: calc, with_reducible): tactic_check.py --lean writes batch-small-2.golden from
-- this file's terms, which LeanForth's must equal node for node. A calc whose last step is
-- the next tactic's goal ends with `;` here, so that Lean's parser does not read that tactic
-- as one more step.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

theorem cc_eq (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
    _ = c := h2
theorem cc_explicit (a b : Nat) (h1 : a = b + 0) (h2 : b = a) : a = a := by
  calc a = b + 0 := h1
    b = a := h2
theorem cc_one (a b : Nat) (h1 : a = b) : a = b := by
  calc a = b := h1
theorem cc_le (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  calc a ≤ b := h1
    _ ≤ c := h2
theorem cc_lt (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := by
  calc a < b := h1
    _ < c := h2
theorem cc_mix (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c < d) : a < d := by
  calc a = b := h1
    _ ≤ c := h2
    _ < d := h3
theorem cc_ltle (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  calc a < b := h1
    _ ≤ c := h2
theorem cc_leeq (a b c : Nat) (h1 : a ≤ b) (h2 : b = c) : a ≤ c := by
  calc a ≤ b := h1
    _ = c := h2
theorem cc_ext (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1;
  exact h2
theorem cc_ext_lt (a b c : Nat) (h1 : a = b) (h2 : b < c) : a < c := by
  calc a = b := h1;
  exact h2
theorem cc_hole (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := ?_
    _ = c := h2;
  exact h1
theorem cc_holes (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := ?_
    _ = c := ?_;
  case calc_2 => exact h2
  exact h1
theorem cc_num (a b : Nat) (h1 : a = b) (h2 : b = 1 + 1) : a = 1 + 1 := by
  calc a = b := h1
    _ = 1 + 1 := h2

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
  for n in [``cc_eq, ``cc_explicit, ``cc_one, ``cc_le, ``cc_lt, ``cc_mix, ``cc_ltle,
            ``cc_leeq, ``cc_ext, ``cc_ext_lt, ``cc_hole, ``cc_holes, ``cc_num] do
    dump n
