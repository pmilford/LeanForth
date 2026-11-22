-- The Lean twins of tests/front/tactics/batch-c/*.lf (plan row TB2, tactic batch 2b): each
-- theorem's type and value as S-expressions (batch-b.lean's printer), which tactic_check.py
-- compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and keeps in
-- batch-c.golden. Batteries' exacts, by_contra_core, by_contra and absurd are copied from
-- .tools/mathlib/mathlib4/.lake/packages/batteries/Batteries/Tactic/Init.lean:31-73, as plain
-- `lean` loads no Batteries.
import Lean
open Lean Meta Elab Tactic Parser.Tactic
set_option linter.unusedVariables false
set_option linter.unnecessaryRwa false

elab "exacts " "[" hs:term,* "]" : tactic => do
  for stx in hs.getElems do
    evalTactic (← `(tactic| exact $stx))
  evalTactic (← `(tactic| done))
macro "by_contra_core" : tactic => `(tactic| first
  | guard_target = Not _; change _ → False
  | refine @Decidable.byContradiction _ _ ?_
  | refine @Classical.byContradiction _ ?_)
syntax (name := byContra) "by_contra" (ppSpace colGt rcasesPatMed)? (" : " term)? : tactic
macro_rules
| `(tactic| by_contra $[$pat?]? $[: $ty?]?) => do
  let pat ← pat?.getDM `(rcasesPatMed| $(mkIdent `this):ident)
  `(tactic| (by_contra_core; rintro ($pat:rcasesPatMed) $[: $ty?]?))
macro "absurd " h:term : tactic =>
  `(tactic|
    first
    | refine @absurd _ _ ?_ $h
    | refine @absurd _ _ $h ?_)

-- rw [← r] and rewrite [← r].
theorem rs_hyp (a b : Nat) (h : a = b) : b + 0 = a := by
  rw [Nat.add_zero, ← h]
theorem rs_lemma (a b : Nat) (h : a + 0 = b) : a = b := by
  rw [← Nat.add_zero a]
  exact h
theorem rs_two (a b c : Nat) (h1 : a = b) (h2 : c = b) : a = c := by
  rw [h1, ← h2]
theorem rs_rewrite (a b c : Nat) (h : a = b) (h2 : c = a) (h3 : c ≤ c) : a ≤ b := by
  rewrite [← h, ← h2]
  exact h3
-- rwa.
theorem ra_basic (a b c : Nat) (h : a = b) (h2 : b = c) : a = c := by
  rwa [h]
theorem ra_rfl (a b : Nat) (h : a = b) : a = b := by
  rwa [h]
theorem ra_symm (a b c : Nat) (h : b = a) (h1 : c = a) (h2 : b = c) : a = c := by
  rwa [← h]
theorem ra_focus (a b c : Nat) (h : a = b) (h2 : b = c) (h3 : a = c) : a = c ∧ a = c := by
  apply And.intro
  rwa [h]
  exact h3
-- exacts.
theorem ex_two (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  exacts [h1, h2]
theorem ex_none (a b : Nat) (h : a ≤ b) : a ≤ b := by
  exact h
  exacts []
theorem ex_app (a : Nat) : a ≤ a := by
  exacts [Nat.le_refl a]
-- by_cases.
theorem bc_dec (a b : Nat) (h1 : a ≤ b) : a ≤ b := by
  by_cases h : a ≤ b
  exact h
  absurd h
  exact h1
theorem bc_tags (a b : Nat) (h1 : a = b) : a = b := by
  by_cases k : a = b
  case neg => absurd k; exact h1
  case pos => exact k
theorem bc_classical (hp : Nonempty Nat) : Nonempty Nat := by
  by_cases h : Nonempty Nat
  exact h
  absurd h
  exact hp
-- by_contra.
theorem bk_not (a b : Nat) (h : ¬a ≤ b) : ¬a ≤ b := by
  by_contra k
  absurd k
  assumption
theorem bk_dec (a b : Nat) (h : a ≤ b) : a ≤ b := by
  by_contra k
  absurd k
  exact h
theorem bk_classical (h : Nonempty Nat) : Nonempty Nat := by
  by_contra
  absurd this
  exact h
theorem bk_ne (a b : Nat) (h : a ≠ b) : a ≠ b := by
  by_contra_core
  intro k
  absurd k
  assumption
-- symm.
theorem sy_eq (a b : Nat) (h : a = b) : b = a := by
  symm
  exact h
theorem sy_iff (a b : Nat) (h : a ≤ b ↔ b ≤ a) : b ≤ a ↔ a ≤ b := by
  symm
  exact h
theorem sy_ne (a b : Nat) (h : a ≠ b) : b ≠ a := by
  symm
  assumption
theorem sy_and (a b : Nat) (h : a ≤ b ∧ b ≤ a) (h2 : b ≤ a ∨ a ≤ b) :
    (b ≤ a ∧ a ≤ b) ∧ (a ≤ b ∨ b ≤ a) := by
  apply And.intro
  symm
  exact h
  symm
  exact h2
theorem sy_heq (a b : Nat) (h : HEq a b) : HEq b a := by
  symm
  exact h
-- and_intros, next.
theorem ai_two (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  and_intros
  exact h1
  exact h2
theorem ai_nested (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) (h3 : a ≤ a) :
    a ≤ b ∧ b ≤ a ∧ a ≤ a := by
  and_intros
  exact h1
  exact h2
  exact h3
theorem ai_all (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : (a ≤ b ∧ b ≤ a) ∧ a ≤ b := by
  apply And.intro
  and_intros
  exact h1
  exact h2
  exact h1
theorem nx_basic (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  next => exact h1
  case _ => exact h2
theorem nx_name (a b : Nat) (h : a ≤ b) : a ≤ b := by
  revert h
  intro _
  next k => exact k
-- rwa on a ≤ c (accepted since tactic batch 3a).
theorem x_ra_le (a b c : Nat) (h : a = b) (h2 : b ≤ c) : a ≤ c := by
  rwa [h]

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
  for n in [``rs_hyp, ``rs_lemma, ``rs_two, ``rs_rewrite, ``ra_basic, ``ra_rfl, ``ra_symm,
      ``ra_focus, ``ex_two, ``ex_none, ``ex_app, ``bc_dec, ``bc_tags, ``bc_classical, ``bk_not,
      ``bk_dec, ``bk_classical, ``bk_ne, ``sy_eq, ``sy_iff, ``sy_ne, ``sy_and, ``sy_heq,
      ``ai_two, ``ai_nested, ``ai_all, ``nx_basic, ``nx_name, ``x_ra_le] do
    dump n
