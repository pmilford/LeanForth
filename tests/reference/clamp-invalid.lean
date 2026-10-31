def incorrectClamp (lower upper value : Int) : Int :=
  if value < lower then lower else if value > upper then value else value

example : incorrectClamp 0 10 11 ≤ 10 := by decide
