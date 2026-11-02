/- Reference obligations for a modeled Forth-like word, not a proof about
   Forth source, finite-cell arithmetic, a compiler, or a runtime. The stack
   contains unbounded mathematical integers, with its top at the list head. -/
import «program-contracts»

namespace LeanForthProgramVerifiedObligations

open LeanForthProgramReference

-- A modeled DOUBLE word ( n -- n+n ), and an incorrect replacement that
-- adds one instead. Both are interpreted solely by program-contracts.step.
def doubleCode : List Op := [.dup, .add]
def brokenCode : List Op := [.push 1, .add]

def doublePost (n : Int) (tail : Stack) (out : Stack) : Prop :=
  out = (n + n) :: tail

-- The weakest precondition specializes to this concrete postcondition;
-- an empty stack cannot meet it because DUP underflows.
theorem double_wp (n : Int) (tail s : Stack) :
    wp doubleCode (doublePost n tail) s ↔
      ∃ x rest, s = x :: rest ∧ (x + x) :: rest = (n + n) :: tail := by
  cases s with
  | nil => simp [doubleCode, wp, step]
  | cons x rest =>
    simp [doubleCode, doublePost, wp, step]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨x, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, ⟨rfl, rfl⟩, h⟩
      exact ⟨h, rfl⟩

-- The stated precondition establishes the full obligation, including
-- successful modeled execution and preservation of the arbitrary suffix.
theorem double_obligation (n : Int) (tail : Stack) :
    ∀ s, s = n :: tail → wp doubleCode (doublePost n tail) s := by
  intro s h
  subst s
  simp [doubleCode, doublePost, wp, step]

-- Same contract, same legal input, but the broken word yields 3 instead of 4.
theorem broken_obligation_fails :
    ¬ (∀ s, s = (2 : Int) :: [] → wp brokenCode (doublePost 2 []) s) := by
  intro h
  have bad := h [2] rfl
  simp [brokenCode, doublePost, wp, step] at bad

-- Print the transitive logical assumptions when this reference is checked.
#print axioms double_wp
#print axioms double_obligation
#print axioms broken_obligation_fails

end LeanForthProgramVerifiedObligations
