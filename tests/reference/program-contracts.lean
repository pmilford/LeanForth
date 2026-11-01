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

-- Two additions consume three inputs, preserving the rest of the stack.
theorem add_three (a b c : Int) (tail : Stack) :
    wp [.add, .add] (fun out => out = ((c + b) + a) :: tail)
      (b :: c :: a :: tail) := by
  simp [wp, step, Int.add_comm]

-- Bounds are explicit and independent of the backing function's totality.
-- A failed access returns none; it cannot produce a modified memory.
structure Memory where
  size : Nat
  cells : Nat → Int

def load (m : Memory) (address : Nat) : Option Int :=
  if address < m.size then some (m.cells address) else none

def store (m : Memory) (address : Nat) (value : Int) : Option Memory :=
  if address < m.size then
    some ⟨m.size, fun i => if i = address then value else m.cells i⟩
  else none

-- For every in-bounds address and value, a successful store reads back the
-- value and leaves every other address unchanged (the frame property).
theorem store_read_frame (m : Memory) (address : Nat) (value : Int)
    (h : address < m.size) :
    ∃ updated, store m address value = some updated ∧
      updated.size = m.size ∧ load updated address = some value ∧
      ∀ other, other ≠ address → updated.cells other = m.cells other := by
  refine ⟨⟨m.size, fun i => if i = address then value else m.cells i⟩, ?_⟩
  simp [store, load, h]
  intro other hne heq
  exact False.elim (hne heq)

-- The boundary itself and every address beyond it fail closed on both paths.
theorem out_of_bounds_access (m : Memory) (address : Nat) (value : Int)
    (h : m.size ≤ address) :
    load m address = none ∧ store m address value = none := by
  simp [load, store, Nat.not_lt.mpr h]

-- Read before writing. A failed source or destination access yields no
-- resulting memory; source and destination are allowed to be the same.
def copyCell (m : Memory) (source destination : Nat) : Option Memory :=
  (load m source).bind (store m destination)

theorem copyCell_success (m : Memory) (source destination : Nat)
    (hs : source < m.size) (hd : destination < m.size) :
    ∃ updated, copyCell m source destination = some updated ∧
      updated.size = m.size ∧
      load updated destination = load m source ∧
      ∀ other, other ≠ destination → updated.cells other = m.cells other := by
  obtain ⟨updated, hstore, hsize, hload, hframe⟩ :=
    store_read_frame m destination (m.cells source) hd
  refine ⟨updated, ?_, hsize, ?_, hframe⟩
  · simpa [copyCell, load, hs] using hstore
  · simpa [load, hs] using hload

theorem copyCell_source_out_of_bounds (m : Memory) (source destination : Nat)
    (h : m.size ≤ source) : copyCell m source destination = none := by
  simp [copyCell, load, Nat.not_lt.mpr h]

theorem copyCell_destination_out_of_bounds (m : Memory) (source destination : Nat)
    (h : m.size ≤ destination) : copyCell m source destination = none := by
  simp [copyCell, load, store, Nat.not_lt.mpr h]

-- Self-copy preserves every backing cell, including inaccessible ones.
theorem copyCell_self (m : Memory) (address : Nat) (h : address < m.size) :
    ∃ updated, copyCell m address address = some updated ∧
      updated.size = m.size ∧ ∀ i, updated.cells i = m.cells i := by
  obtain ⟨updated, hc, hsize, hread, hframe⟩ := copyCell_success m address address h h
  refine ⟨updated, hc, hsize, ?_⟩
  intro i
  by_cases hi : i = address
  · subst i
    simpa [load, h, hsize] using hread
  · exact hframe i hi

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
