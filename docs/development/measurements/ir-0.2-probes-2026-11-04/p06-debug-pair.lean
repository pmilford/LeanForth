-- IR 0.2 probe 6 (ADR 0019 Amendment 1): does the clamp proof survive a
-- debugging `dup .`? IR 0.1 has no output instruction, so `.` is written
-- here as what IR 0.2's stack semantics gives it, `prim .drop` (it takes
-- one cell and changes nothing else on the stacks). The proofs below are
-- clamp_returns and clamp_correct of tests/reference/program-ir.lean,
-- copied with only the names changed. debug-pair.sh inserts this text
-- into a copy of that file, at the end of its Part 3, and runs Lean.

-- `: lf-clamp 2dup > if 2drop drop false exit then >r max dup . r> min true ;`
def clampDebugBody : List Instr :=
  [.prim .twoDup, .prim .gt, .ifElse [.prim .twoDrop, .prim .drop, .prim .false, .exit] [],
   .prim .toR, .prim .max, .prim .dup, .prim .drop, .prim .fromR, .prim .min, .prim .true]

def clampDebugProgram : Program := [("lf-clamp", .word clampDebugBody)]

theorem lookup_clampDebug :
    lookup clampDebugProgram "lf-clamp" = some (.word clampDebugBody) := rfl

theorem clampDebug_returns (c : Cells) (fuel : Nat) (lower upper value : Int)
    (tail : List Int) :
    (run c clampDebugProgram fuel clampDebugBody ⟨upper :: lower :: value :: tail, []⟩).returned =
      some ((if lower > upper then [0] else [-1, clamp lower upper value]) ++ tail) := by
  simp only [clampDebugBody]
  ir_simp
  by_cases h : lower > upper
  · simp only [h, ↓reduceIte]
    simp [Result.returned]
  · simp only [h, ↓reduceIte]
    ir_simp
    simp only [Result.returned, clamp, List.cons_append, List.nil_append, Option.some.injEq,
      List.cons.injEq, true_and, and_true]
    repeat' split
    all_goals omega

theorem clampDebug_correct (c : Cells) (fuel : Nat) (lower upper value : Int)
    (tail rs : List Int) (enough : 1 ≤ fuel) :
    callWord c clampDebugProgram fuel "lf-clamp" ⟨upper :: lower :: value :: tail, rs⟩ =
      .next ⟨(if lower > upper then [0] else [-1, clamp lower upper value]) ++ tail, rs⟩ :=
  callWord_of_returns lookup_clampDebug (clampDebug_returns c _ lower upper value tail) enough

#print axioms clampDebug_correct
