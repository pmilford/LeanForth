-- The Lean twins of tests/front/tactics/batch-h2/*.lf (plan row TB2, piece E, slice E2b:
-- by_contra with a pattern, contradiction on an empty type): each theorem's type and value as
-- S-expressions (batch-b.lean's printer), which tactic_check.py compares with LeanForth's
-- (tests/front/elab-dump.fs's decide-dump) and keeps in batch-h2.golden. Batteries'
-- by_contra_core and by_contra are copied from
-- .tools/mathlib/mathlib4/.lake/packages/batteries/Batteries/Tactic/Init.lean:43-60, as plain
-- `lean` loads no Batteries (batch-c.lean's copy).
import Lean
open Lean Meta Elab Tactic Parser.Tactic
set_option linter.unusedVariables false

macro "by_contra_core" : tactic => `(tactic| first
  | guard_target = Not _; change _ → False
  | refine @Decidable.byContradiction _ _ ?_
  | refine @Classical.byContradiction _ ?_)
syntax (name := byContra) "by_contra" (ppSpace colGt rcasesPatMed)? (" : " term)? : tactic
macro_rules
| `(tactic| by_contra $[$pat?]? $[: $ty?]?) => do
  let pat ← pat?.getDM `(rcasesPatMed| $(mkIdent `this):ident)
  `(tactic| (by_contra_core; rintro ($pat:rcasesPatMed) $[: $ty?]?))

-- by_contra with a pattern (by-contra.lf).
theorem bc_tuple (a b : Nat) (k : ¬b = a) : ¬(a = b ∧ b = a) := by
  by_contra ⟨hab, hba⟩
  contradiction
theorem bc_alts (a b : Nat) (h : ¬a = b) (k : ¬b = a) : ¬(a = b ∨ b = a) := by
  by_contra h1 | h2
  contradiction
  contradiction
theorem bc_rfl (a b : Nat) (h : ¬a = a) : ¬a = b := by
  by_contra rfl
  contradiction
theorem bc_rfl_word (a b : Nat) (h : ¬a = a) : ¬a = b := by
  by_contra rfl
  contradiction
theorem bc_name (a b : Nat) (h : a = b) : a = b := by
  by_contra k
  contradiction
theorem bc_clear (h : False) : ¬True := by
  by_contra -
  exact h
theorem bc_clear_word (h : False) : ¬True := by
  by_contra -
  exact h
theorem bc_anon_word (a b : Nat) (h : a = b) : a = b := by
  by_contra _
  contradiction
theorem bc_nest (a b : Nat) (h : ¬a = b) : ¬((a = b ∧ b = a) ∨ a = b) := by
  by_contra ⟨h1, _⟩ | h2
  contradiction
  contradiction

-- contradiction on an empty type (empty.lf).
theorem em_empty (a : Nat) (x : Empty) : a = Nat.succ a := by
  contradiction
theorem em_later (h : True) (x : Empty) : False := by
  contradiction
theorem em_dep (x : Empty) (h : x = x) : False := by
  contradiction

-- obtain through a substituted field (dvd.lf; the E1 review's probe p27).
theorem dv_obtain (h : Exists (Dvd.dvd (Nat.succ (Nat.succ Nat.zero)))) : True := by
  obtain ⟨_ | n, c, hc⟩ := h
  trivial
  trivial

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
  for n in [``bc_tuple, ``bc_alts, ``bc_rfl, ``bc_rfl_word, ``bc_name, ``bc_clear, ``bc_clear_word,
            ``bc_anon_word, ``bc_nest, ``em_empty, ``em_later, ``em_dep, ``dv_obtain] do
    dump n
