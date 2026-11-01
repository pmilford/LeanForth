/- A Lean reference for a small executable Forth-like stack language.
   This is not a LeanForth verifier, parser, compiler, or host semantics. -/

import Std.Tactic

namespace LeanForthProgramReference

abbrev Stack := List Int

inductive Op where
  | push (value : Int)
  | dup
  | add
  deriving Repr

-- Each operation is partial: an undersized data stack returns none. Integers
-- are mathematical and unbounded; this is not finite-cell host arithmetic.
def step : Op → Stack → Option Stack
  | .push n, s => some (n :: s)
  | .dup, x :: s => some (x :: x :: s)
  | .add, x :: y :: s => some ((y + x) :: s)
  | _, _ => none

def execute : List Op → Stack → Option Stack
  | [], s => some s
  | op :: rest, s => (step op s).bind (execute rest)

-- Minimum initial depth required by the remaining instructions. Subtraction
-- on Nat saturates at zero; DUP needs one item even if the suffix needs none.
def requiredDepth : List Op → Nat
  | [] => 0
  | .push _ :: rest => requiredDepth rest - 1
  | .dup :: rest => max 1 (requiredDepth rest - 1)
  | .add :: rest => max 2 (requiredDepth rest + 1)

-- Exactness includes soundness (sufficient depth prevents underflow) and
-- necessity (no smaller initial stack can execute this particular model).
theorem requiredDepth_iff_execution (code : List Op) (s : Stack) :
    requiredDepth code ≤ s.length ↔ ∃ result, execute code s = some result := by
  induction code generalizing s with
  | nil => simp [requiredDepth, execute]
  | cons op rest ih =>
    cases op with
    | push n =>
      simpa [requiredDepth, execute, step, List.length_cons] using
        (show requiredDepth rest - 1 ≤ s.length ↔
          ∃ result, execute rest (n :: s) = some result by
            rw [← ih]; simp only [List.length_cons]; omega)
    | dup =>
      cases s with
      | nil => simp [requiredDepth, execute, step]
      | cons x tail =>
        simp only [requiredDepth, execute, step, Option.bind_some, ← ih,
          List.length_cons, Nat.max_le]
        omega
    | add =>
      cases s with
      | nil => simp [requiredDepth, execute, step]
      | cons x tail =>
        cases tail with
        | nil =>
          have h := Nat.le_max_left 2 (requiredDepth rest + 1)
          simp [requiredDepth, execute, step]
          omega
        | cons y tail =>
          simp only [requiredDepth, execute, step, Option.bind_some, ← ih,
            List.length_cons, Nat.max_le]
          omega

example : requiredDepth [.dup, .add] = 1 := by decide
example : requiredDepth [.push 4, .add] = 1 := by decide
example : requiredDepth [.add, .push 4] = 2 := by decide
example : ¬ requiredDepth [.dup, .add] ≤ ([] : Stack).length := by decide

-- The reference weakest precondition requires successful execution; a proof
-- about it therefore includes absence of modeled stack underflow.
def wp : List Op → (Stack → Prop) → Stack → Prop
  | [], post, s => post s
  | op :: rest, post, s =>
      match step op s with
      | none => False
      | some next => wp rest post next

theorem wp_iff_execution (code : List Op) (post : Stack → Prop) (s : Stack) :
    wp code post s ↔ ∃ result, execute code s = some result ∧ post result := by
  induction code generalizing s with
  | nil => simp [wp, execute]
  | cons op rest ih =>
    simp only [wp, execute]
    cases h : step op s with
    | none => simp
    | some next => simpa [h] using ih next

-- A precondition guarantees successful execution and the postcondition exactly
-- when it implies wp. In particular, failed execution cannot satisfy it.
theorem wp_weakest (code : List Op) (pre post : Stack → Prop) :
    (∀ s, pre s → wp code post s) ↔
      (∀ s, pre s → ∃ result, execute code s = some result ∧ post result) := by
  constructor
  · intro h s hs
    exact (wp_iff_execution code post s).mp (h s hs)
  · intro h s hs
    exact (wp_iff_execution code post s).mpr (h s hs)

-- A stronger postcondition can be weakened without losing modeled safety.
theorem wp_mono (code : List Op) (strong weak : Stack → Prop)
    (h : ∀ s, strong s → weak s) (s : Stack) :
    wp code strong s → wp code weak s := by
  intro hw
  obtain ⟨result, hexec, hpost⟩ := (wp_iff_execution code strong s).mp hw
  exact (wp_iff_execution code weak s).mpr ⟨result, hexec, h result hpost⟩

-- A nontrivial symbolic example: duplicate the top mathematical integer and
-- add the copies while preserving any untouched stack suffix.
theorem duplicate_and_add (n : Int) (tail : Stack) :
    wp [.dup, .add] (fun out => out = (n + n) :: tail) (n :: tail) := by
  simp [wp, step]

-- Underflow is rejected, not mistaken for a vacuously correct execution.
theorem duplicate_empty_fails (post : Stack → Prop) : ¬ wp [.dup] post [] := by
  simp [wp, step]

-- Composition works for arbitrary modeled code and predicates, rather than
-- proving only a specific example. This supplies a reusable reference rule.
theorem wp_append (first second : List Op) (post : Stack → Prop) (s : Stack) :
    wp (first ++ second) post s ↔ wp first (wp second post) s := by
  induction first generalizing s with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.cons_append, wp]
    cases h : step op s <;> simp [ih]

end LeanForthProgramReference
