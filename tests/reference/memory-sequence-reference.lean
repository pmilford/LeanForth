/- Abstract memory/stack execution only: no Forth runtime correspondence is claimed. -/
import «memory-copy-properties»
import «memory-swap-reference»

namespace LeanForthMemorySequenceReference

open LeanForthProgramReference (Memory load)
open LeanForthMemoryProgramReference (Item Op execute)
open LeanForthMemoryCopyReference (copyProgram copy_success)
open LeanForthMemoryCopyProperties (execute_append copy_failure_with_continuation)
open LeanForthMemorySwapReference (swapProgram swapped swap_success swap_reads
  swap_frame swap_out_of_bounds)

-- The source is on the stack; copy consumes it and swap preserves the tail.
def copyThenSwap (destination a b : Nat) : List Op :=
  copyProgram destination ++ swapProgram a b

-- All aliases are allowed. The swap reads the post-copy memory, so its
-- results are expressed in terms of that intermediate state.
theorem sequence_success (m : Memory) (source destination a b : Nat)
    (tail : List Item) (hs : source < m.size) (hd : destination < m.size)
    (ha : a < m.size) (hb : b < m.size) :
    ∃ copied final, execute (copyThenSwap destination a b)
        ⟨.address source :: tail, m⟩ = some ⟨tail, final⟩ ∧
      copied.size = m.size ∧ final.size = m.size ∧
      load copied destination = load m source ∧
      load final a = load copied b ∧ load final b = load copied a ∧
      ∀ i, i ≠ destination → i ≠ a → i ≠ b → final.cells i = m.cells i := by
  obtain ⟨copied, hc, hz, hr, hf⟩ := copy_success m source destination tail hs hd
  have ha' : a < copied.size := by simpa [hz] using ha
  have hb' : b < copied.size := by simpa [hz] using hb
  have reads := swap_reads copied a b ha' hb'
  refine ⟨copied, swapped copied a b, ?_, hz, ?_, hr, reads.1, reads.2, ?_⟩
  · simp [copyThenSwap, execute_append, hc, swap_success copied a b tail ha' hb']
  · simpa [swapped] using hz
  · intro i hid hia hib
    exact (swap_frame copied a b i hia hib).2.trans (hf i hid)

-- The copy's destination can be a swap operand: after copying source to a,
-- the final b contains the original source value, even when a = b.
theorem copied_value_reaches_b (m : Memory) (source a b : Nat)
    (tail : List Item) (hs : source < m.size) (ha : a < m.size)
    (hb : b < m.size) :
    ∃ final, execute (copyThenSwap a a b) ⟨.address source :: tail, m⟩ =
        some ⟨tail, final⟩ ∧ load final b = load m source := by
  obtain ⟨copied, final, he, _, _, hc, _, hb', _⟩ :=
    sequence_success m source a a b tail hs ha ha hb
  exact ⟨final, he, hb'.trans hc⟩

-- Any failed access stops the entire sequence and any later continuation.
theorem sequence_out_of_bounds (m : Memory) (source destination a b : Nat)
    (tail : List Item) (rest : List Op)
    (h : m.size ≤ source ∨ m.size ≤ destination ∨ m.size ≤ a ∨ m.size ≤ b) :
    execute (copyThenSwap destination a b ++ rest)
      ⟨.address source :: tail, m⟩ = none := by
  rcases h with hs | hd | ha | hb
  · simpa [copyThenSwap, List.append_assoc] using
      copy_failure_with_continuation m source destination tail (swapProgram a b ++ rest) (Or.inl hs)
  · simpa [copyThenSwap, List.append_assoc] using
      copy_failure_with_continuation m source destination tail (swapProgram a b ++ rest) (Or.inr hd)
  all_goals
    by_cases hs : source < m.size
    · by_cases hd : destination < m.size
      · obtain ⟨copied, hc, hz, _, _⟩ := copy_success m source destination tail hs hd
        rw [show copyThenSwap destination a b ++ rest =
          copyProgram destination ++ (swapProgram a b ++ rest) by simp [copyThenSwap, List.append_assoc]]
        rw [execute_append, hc]
        simp only [Option.bind_some]
        apply swap_out_of_bounds copied a b tail rest
        simp only [hz]
        first | exact Or.inl ha | exact Or.inr hb
      · simpa [copyThenSwap, List.append_assoc] using
          copy_failure_with_continuation m source destination tail (swapProgram a b ++ rest)
            (Or.inr (Nat.le_of_not_gt hd))
    · simpa [copyThenSwap, List.append_assoc] using
        copy_failure_with_continuation m source destination tail (swapProgram a b ++ rest)
          (Or.inl (Nat.le_of_not_gt hs))

-- For the supplied address stack shape, these four bounds are exactly the
-- conditions for obtaining any final state.
theorem sequence_succeeds_iff (m : Memory) (source destination a b : Nat)
    (tail : List Item) :
    (∃ result, execute (copyThenSwap destination a b)
      ⟨.address source :: tail, m⟩ = some result) ↔
      source < m.size ∧ destination < m.size ∧ a < m.size ∧ b < m.size := by
  constructor
  · intro ⟨result, hresult⟩
    by_cases hbounds : source < m.size ∧ destination < m.size ∧ a < m.size ∧ b < m.size
    · exact hbounds
    · have bad : m.size ≤ source ∨ m.size ≤ destination ∨ m.size ≤ a ∨ m.size ≤ b := by
        omega
      have hf := sequence_out_of_bounds m source destination a b tail [] bad
      simp only [List.append_nil] at hf
      rw [hresult] at hf
      contradiction
  · rintro ⟨hs, hd, ha, hb⟩
    obtain ⟨_, final, he, _⟩ := sequence_success m source destination a b tail hs hd ha hb
    exact ⟨_, he⟩

theorem sequence_wrong_tag (m : Memory) (v : Int) (destination a b : Nat)
    (tail : List Item) (rest : List Op) :
    execute (copyThenSwap destination a b ++ rest) ⟨.value v :: tail, m⟩ = none := by
  rfl

end LeanForthMemorySequenceReference
