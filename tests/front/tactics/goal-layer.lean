-- The Lean twins of tests/front/tactics/*/*.lf (slice a2-iii of
-- docs/design/TACTIC_PLUGINS.md; plan row TB1): each theorem's type and
-- value as S-expressions (the printer of tests/front/s2-proofs.lean),
-- which tests/front/tactics/tactic_check.py compares with LeanForth's
-- (tests/front/elab-dump.fs) and keeps in tests/front/tactics/goal-layer.golden.
import Lean
open Lean Meta
set_option linter.unusedVariables false

-- apply: a theorem, a hypothesis, implicit arguments left as goals in
-- Lean's order (non-dependent first). (A range of more than one argument
-- count needs a goal with a binder, which natural LeanForth cannot write
-- yet: tests/front/tactics/apply/test.fs reaches it.)
theorem ap_le_succ (n : Nat) : n ≤ n + 1 := by apply Nat.le_succ
theorem ap_le_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans
  apply h1
  apply h2
theorem ap_hyp (a b : Nat) (h : a ≤ b) : a ≤ b := by apply h
theorem ap_partial (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans h1
  exact h2
theorem ap_tag (n : Nat) : True ∧ True := by
  induction n with
  | zero => apply And.intro; constructor; constructor
  | succ k ih => apply And.intro; constructor; constructor
theorem ap_tag_trans (k a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  induction k with
  | zero => apply Nat.le_trans; apply h1; apply h2
  | succ j ih => apply Nat.le_trans; apply h1; apply h2
theorem ap_and (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  exact h1
  exact h2
-- exact on apply's goals, their types as stored (plan 9.4.8l J).
theorem ap_exact (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans
  exact h1
  exact h2
-- assumption: the newest hypothesis that fits, up to definitional equality.
theorem as_one (a b : Nat) (h : a ≤ b) : a ≤ b := by assumption
theorem as_newest (a b : Nat) (h1 : a ≤ b) (h2 : a ≤ b) : a ≤ b := by assumption
theorem as_defeq (a : Nat) (h : a ≤ a) : a ≤ a + 0 := by assumption
-- constructor: the first constructor that applies.
theorem co_and (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  constructor
  exact h1
  exact h2
theorem co_true : True := by constructor
theorem co_or (a : Nat) (h : a ≤ a) : a ≤ a ∨ a ≤ a + 1 := by
  constructor
  exact h
theorem co_le (n : Nat) : n ≤ n := by constructor
-- left and right (plan row TB1): nthConstructor's apply of the first or
-- the second constructor of a type that has two.
theorem le_or (a b : Nat) (h : a ≤ b) : a ≤ b ∨ b ≤ a := by
  left
  exact h
theorem le_le (a : Nat) : a ≤ a := by left
theorem ri_or (a b : Nat) (h : b ≤ a) : a ≤ b ∨ b ≤ a := by
  right
  exact h
theorem ri_le (a : Nat) : a ≤ a + 1 := by
  right
  left
-- exfalso: False.elim.{u} target ?g, the goal's tag kept.
theorem ex_exact (a b : Nat) (h : False) : a = b := by
  exfalso
  exact h
theorem ex_assumption (a b : Nat) (h : False) : a ≤ b := by
  exfalso
  assumption
theorem ex_tag (a b : Nat) (h : False) : a = b ∧ b = a := by
  apply And.intro
  exfalso
  exact h
  exfalso
  exact h
-- intros: every leading binder, none with a delta step first.
theorem is_or (a b : Nat) (h : a ≤ b ∨ a ≤ b) : a ≤ b := by
  apply Or.elim h
  intros
  assumption
  intros
  assumption
theorem is_none (a : Nat) (h : a ≤ a) : a ≤ a := by
  intros
  exact h
-- intro and intros on implicit and strict-implicit binders, each kept of
-- its kind (tests/front/tactics/intros/implicit.fs builds these goals,
-- which LeanForth text cannot state yet; their binder kinds are printed too).
theorem in_implicit : ∀ {x : Nat}, x = x := by
  intro x
  rfl
theorem in_strict : ∀ ⦃x : Nat⦄, x = x := by
  intro x
  rfl
theorem is_implicit : ∀ {x : Nat} ⦃y : Nat⦄ (z : Nat), y = y := by
  intros
  rfl
-- clear: a hypothesis or a variable nothing depends on.
theorem cl_hyp (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b := by
  clear h2
  exact h1
theorem cl_var (a b : Nat) (h : a ≤ a) : a ≤ a := by
  clear b
  exact h
-- decide (plan row S3, slice S3a): closed decidable facts about Nat and
-- Bool, Decidable.decide reduced to true by whnf (reduceNat? folding the
-- numbers); a hypothesis is allowed, only the goal must be closed.
theorem dc_add : 2 + 2 = 4 := by decide
theorem dc_lt : 10 < 20 := by decide
theorem dc_le : 3 ≤ 3 := by decide
theorem dc_mul : Nat.mul 12345 6789 = 83810205 := by decide
theorem dc_sub : 10 - 20 = 0 := by decide
theorem dc_div : 17 / 5 = 3 := by decide
theorem dc_mod : 100 % 7 = 2 := by decide
theorem dc_not : ¬ (2 + 2 = 5) := by decide
theorem dc_and : ¬ (7 = 8) ∧ 2 ≤ 2 := by decide
theorem dc_or : 1 = 0 ∨ 2 + 2 = 4 := by decide
theorem dc_true : True := by decide
theorem dc_bool : Bool.and true false = false := by decide
theorem dc_hyp (h : True) : 2 = 2 := by decide
theorem dc_gcd : Nat.gcd 1071 462 = 21 := by decide
theorem dc_pow : 2 ^ 10 = 1024 := by decide
theorem dc_word : 2 ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
-- Plan row S3, slice S3a-ops C1 (tests/front/tactics/decide/dc-ops.lf, dc-ops-init.lf):
-- Lean's operators, once instance keys unfold reducible definitions (DiscrTree's reduceDT).
theorem d_mul : 6 * 7 = 42 := by decide
theorem d_pythag : 3 * 3 + 4 * 4 = 5 * 5 := by decide
theorem d_gauss : 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by decide
theorem d_gt : 20 > 10 := by decide
theorem d_ge : 10 ≥ 10 := by decide
theorem d_ne : 3 ≠ 4 := by decide
theorem d_compare : 20 > 10 ∧ 10 ≥ 10 ∧ 3 ≠ 4 := by decide
theorem d_leap : 2024 % 4 = 0 ∧ 2024 % 100 ≠ 0 := by decide
theorem d_perfect : 1 + 2 + 4 + 7 + 14 = 28 := by decide
theorem d_mul_big : 12345 * 6789 = 83810205 := by decide
theorem d_divmod : 17 / 5 = 3 ∧ 17 % 5 = 2 := by decide
theorem d_mersenne : 2 ^ 11 - 1 = 23 * 89 := by decide
theorem d_euler : 2 ^ 32 + 1 = 641 * 6700417 := by decide
theorem d_taxicab : 1 ^ 3 + 12 ^ 3 = 1729 ∧ 9 ^ 3 + 10 ^ 3 = 1729 := by decide
theorem d_pow_cmp : 2 ^ 10 = 1024 ∧ 2 ^ 10 > 1000 := by decide
theorem x_dc_dvd : 3 ∣ 12 := by decide
-- Plan row S3, slice S3a-ops C2-C5 (tests/front/tactics/decide/dc-symbols.lf, dc-ascii.lf):
-- the talk's theorems with Lean's symbols, then in Lean's ASCII notation (Ne, Not where
-- Lean has none); check.py --init compares LeanForth's terms of both files with these.
theorem sy_mul : 6 * 7 = 42 := by decide
theorem sy_pythag : 3 * 3 + 4 * 4 = 5 * 5 := by decide
theorem sy_gauss : 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by decide
theorem sy_divmod : 17 / 5 = 3 ∧ 17 % 5 = 2 := by decide
theorem sy_gcd : Nat.gcd 1071 462 = 21 := by decide
theorem sy_compare : 20 > 10 ∧ 10 ≥ 10 ∧ 3 ≠ 4 := by decide
theorem sy_leap : 2024 % 4 = 0 ∧ 2024 % 100 ≠ 0 := by decide
theorem sy_mersenne : 2 ^ 11 - 1 = 23 * 89 := by decide
theorem sy_euler : 2 ^ 32 + 1 = 641 * 6700417 := by decide
theorem sy_taxicab : 1 ^ 3 + 12 ^ 3 = 1729 ∧ 9 ^ 3 + 10 ^ 3 = 1729 := by decide
theorem sy_not : ¬ (2 + 2 = 5) := by decide
theorem sy_or : 10 < 20 ∨ 20 < 10 := by decide
theorem sy_iff : 2 + 2 = 4 ↔ 3 ≤ 3 := by decide
theorem sy_pow_cmp : 2 ^ 10 = 1024 ∧ 2 ^ 10 > 1000 := by decide
theorem as_mul : 6 * 7 = 42 := by decide
theorem as_pythag : 3 * 3 + 4 * 4 = 5 * 5 := by decide
theorem as_gauss : 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by decide
theorem as_divmod : 17 / 5 = 3 /\ 17 % 5 = 2 := by decide
theorem as_gcd : Nat.gcd 1071 462 = 21 := by decide
theorem as_compare : 20 > 10 /\ 10 >= 10 /\ Ne 3 4 := by decide
theorem as_leap : 2024 % 4 = 0 /\ Ne (2024 % 100) 0 := by decide
theorem as_mersenne : 2 ^ 11 - 1 = 23 * 89 := by decide
theorem as_euler : 2 ^ 32 + 1 = 641 * 6700417 := by decide
theorem as_taxicab : 1 ^ 3 + 12 ^ 3 = 1729 /\ 9 ^ 3 + 10 ^ 3 = 1729 := by decide
theorem as_not : Not (2 + 2 = 5) := by decide
theorem as_or : 10 < 20 \/ 20 < 10 := by decide
theorem as_iff : 2 + 2 = 4 <-> 3 <= 3 := by decide
theorem as_pow_cmp : 2 ^ 10 = 1024 /\ 2 ^ 10 > 1000 := by decide
theorem x_sy_dvd : 3 ∣ 12 := by decide

def pl (l : Level) : String := match l.toNat with
  | some n => toString n
  | none => "?l"

partial def sx : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .const n us => return n.toString ++ ".{" ++ String.intercalate "," (us.map pl) ++ "}"
  | .app f a => return s!"(app {← sx f} {← sx a})"
  | .lam _ t b _ => return s!"(lam {← sx t} {← sx b})"
  | .forallE _ t b _ => return s!"(pi {← sx t} {← sx b})"
  | .sort l => return "Sort " ++ pl l
  | .lit (.natVal n) => return toString n
  -- mdata (the `borrowed` mark @& of Nat.mul's and Nat.gcd's arguments), which lean4export
  -- leaves out, so no LeanForth term has it: looked through, as check_whnf.py drops its <md>.
  | .mdata _ e => sx e
  | e => return s!"?? {e}"

def dump (n : Name) : MetaM Unit := do
  let some (.thmInfo i) := (← getEnv).find? n | IO.println s!"{n} ??"
  IO.println s!"{n} type {← sx i.type}"
  IO.println s!"{n} value {← sx i.value}"

def bk : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

partial def lams : Expr → List String
  | .lam _ _ b bi => bk bi :: lams b
  | _ => []

def dumpBinders (n : Name) : MetaM Unit := do
  let some (.thmInfo i) := (← getEnv).find? n | IO.println s!"{n} ??"
  IO.println s!"{n} binders{String.join ((lams i.value).map (" " ++ ·))}"

#eval do
  for n in [``ap_le_succ, ``ap_le_trans, ``ap_hyp, ``ap_partial, ``ap_tag, ``ap_tag_trans, ``ap_and, ``ap_exact, ``as_one, ``as_newest,
      ``as_defeq, ``co_and, ``co_true, ``co_or, ``co_le, ``le_or, ``le_le, ``ri_or, ``ri_le,
      ``ex_exact, ``ex_assumption, ``ex_tag, ``is_or, ``is_none, ``in_implicit, ``in_strict,
      ``is_implicit, ``cl_hyp, ``cl_var, ``dc_add, ``dc_lt, ``dc_le, ``dc_mul, ``dc_sub,
      ``dc_div, ``dc_mod, ``dc_not, ``dc_and, ``dc_or, ``dc_true, ``dc_bool, ``dc_hyp, ``dc_gcd,
      ``dc_pow, ``dc_word, ``d_mul, ``d_pythag, ``d_gauss, ``d_gt, ``d_ge, ``d_ne, ``d_compare,
      ``d_leap, ``d_perfect, ``d_mul_big, ``d_divmod, ``d_mersenne, ``d_euler, ``d_taxicab,
      ``d_pow_cmp, ``sy_mul, ``sy_pythag, ``sy_gauss, ``sy_divmod, ``sy_gcd, ``sy_compare,
      ``sy_leap, ``sy_mersenne, ``sy_euler, ``sy_taxicab, ``sy_not, ``sy_or, ``sy_iff,
      ``sy_pow_cmp, ``as_mul, ``as_pythag, ``as_gauss, ``as_divmod, ``as_gcd, ``as_compare,
      ``as_leap, ``as_mersenne, ``as_euler, ``as_taxicab, ``as_not, ``as_or, ``as_iff,
      ``as_pow_cmp] do
    dump n
  for n in [``in_implicit, ``in_strict, ``is_implicit] do
    dumpBinders n
