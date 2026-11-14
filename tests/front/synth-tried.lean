-- The candidates pinned Lean 4.35.0 tries for S1's instance problems
-- (docs/design/S1_INTERFACE.md §9, s1-synth's measurements), on Init
-- alone. Run: lean tests/front/synth-tried.lean, then read the
-- `[Meta.synthInstance.apply]` lines: each problem tries one candidate,
-- the last of its list, before its answer or its stuck exit (💥).
--   OfNat ?T 0       Lean.Grind.CommRing.OfCommSemiring.instOfNatQ  stuck
--   OfNat Nat 0      instOfNatNat                                    instOfNatNat 0
--   HAdd ?α ?β ?γ    String.instHAddCharRaw                          stuck
--   HAdd Nat Nat ?γ  instHAdd, then Add Nat: instAddNat              @instHAdd Nat instAddNat
--   Add ?α           Lean.Grind.CommRing.OfCommSemiring.instAddQ     stuck
--   Add Nat          instAddNat                                      instAddNat
set_option trace.Meta.synthInstance true
set_option pp.all true
#synth OfNat _ (nat_lit 0)
#synth OfNat Nat (nat_lit 0)
#synth HAdd _ _ _
#synth HAdd Nat Nat _
#synth Add _
#synth Add Nat
-- The same problems as the statement's elaboration meets them.
theorem t : 0 + 0 = 0 := by rfl
