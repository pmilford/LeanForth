import Lean
open Lean Meta

def modes : List TransparencyMode :=
  [.all, .default, .reducible, .instances, .none, .implicit]

def statusText : ReducibilityStatus → String
  | .reducible => "reducible" | .semireducible => "semireducible"
  | .irreducible => "irreducible" | .implicitReducible => "implicit_reducible"
  | .instanceReducible => "instance_reducible"

def kindText : ConstantInfo → String
  | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .axiomInfo _ => "ax" ++ "iom"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def bit (b : Bool) : String := if b then "1" else "0"

def unfoldCase (n : Name) : MetaM Unit := do
  let info ← getConstInfo n
  let mut s := s!"{n} {kindText info} {statusText (← getReducibilityStatus n)} "
  for m in modes do
    s := s ++ bit (← withTransparency m (getUnfoldableConst? n)).isSome
  s := s ++ " "
  for m in modes do
    s := s ++ bit (← withTransparency m (canUnfold info))
  let env ← getEnv
  s := s ++ " " ++ bit (← getMatcherInfo? n).isSome
  s := s ++ " " ++ bit (← getProjectionFnInfo? n).isSome
  s := s ++ " " ++ bit (isAuxRecursor env n)
  s := s ++ " " ++ bit (env.contains (mkSmartUnfoldingNameFor n))
  IO.println s

run_meta do
  unfoldCase `Nat.add
  unfoldCase `HAdd.hAdd
  unfoldCase `instHAdd
  unfoldCase `instAddNat
  unfoldCase `id
  unfoldCase `Function.comp
  unfoldCase `Nat.pred
  unfoldCase `OfNat.ofNat
  unfoldCase `instOfNatNat
  unfoldCase `Prod.fst
  unfoldCase `Prod.mk
  unfoldCase `Prod
  unfoldCase `Nat.casesOn
  unfoldCase `Nat.rec
  unfoldCase `Nat.div
  unfoldCase `Nat.zero_add
  unfoldCase `Classical.choice
  unfoldCase `Quot.lift
  unfoldCase `Quot
  unfoldCase `Quot.mk
  unfoldCase `Eq.ndrec
  unfoldCase `Nat.below
  unfoldCase `Nat.brecOn
  unfoldCase `Nat.add.match_1
  unfoldCase `Nat.add._f
  unfoldCase `outParam
  unfoldCase `Unit.unit
  unfoldCase `Unit
  unfoldCase `Nat
  unfoldCase `Nat.succ
  unfoldCase `Add.add
  unfoldCase `HAdd.mk
  unfoldCase `Eq.refl
  unfoldCase `Nat.mul
  unfoldCase `Nat.pow
  unfoldCase `Nat.lt
  unfoldCase `instLTNat
  unfoldCase `LT.lt
  unfoldCase `propext
