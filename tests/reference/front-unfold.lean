-- Lean source of tests/front/unfold-slice.ndjson (plan FE1a; review fe1ab L1):
-- two constants whose types are not visibly Pi types but become ones when
-- Lean's whnf unfolds them, so the natural reader cannot count their
-- explicit arguments without unfolding (error 73, until plan FE1c).
-- c's type is headed by a definition, d's by a lambda (a beta redex).
def F (α : Type) : Type := α → α
def c : F Nat := fun n => n
def d : (fun α : Type => α → α) Nat := fun n => n
