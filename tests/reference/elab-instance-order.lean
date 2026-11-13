/-
Pinned Lean's own candidate order for a set of instance problems over
Init (plan row FE1e1; docs/design/FE1E_APPLICATIONS.md §3.1, probe p6;
tests/front/elab-init.sh compares it with the ranks and priorities of the
elaboration data). For each goal it prints two lines:

  unify GOAL: NAME...      Lean's DiscrTree.getUnify on the instance tree,
                           in its order (which must be the data's ranks,
                           the values under the goal's root key in rank
                           order kept to these names)
  instances GOAL: NAME...  Meta.getInstances: the same after the stable
                           sort by priority and the erased filter (which
                           must be the data's priorities applied to that
                           order); Lean tries them from the last

The goals, in Lean notation: OfNat ?α 0, OfNat Nat 0, OfNat Nat 5,
HAdd Nat Nat Nat, HAdd Nat Nat ?γ, Add Nat, Add ?α, Mul Nat,
HMul Nat Nat ?γ, HPow Nat Nat Nat (in its tree instHPow (1000) comes
before Lean.Grind.Semiring.npow (100): only the priority sort makes Lean
try instHPow first), HPow Nat Nat ?γ, Sub Nat, LE Nat, LT Nat,
Inhabited Nat, BEq Nat, DecidableEq Nat (a Π type after unfolding),
Decidable (a = b) and Decidable (a ≤ b) for a b : Nat.

Usage: lean -DwarningAsError=true --run tests/reference/elab-instance-order.lean
-/
import Lean

open Lean Meta

def nat : Expr := mkConst ``Nat

/-- Names joined by spaces, each without Lean's «» escapes. -/
def plain (ns : Array (Option Name)) : String :=
  " ".intercalate (ns.map fun n => (n.getD .anonymous).toString (escape := false)).toList

def names (es : Array Expr) : String := plain (es.map (·.getAppFn.constName?))

def entryNames (es : Array InstanceEntry) : String := plain (es.map (·.globalName?))

/-- Lean's two orders for one goal, printed under its label. -/
def report (label : String) (goal : MetaM Expr) : MetaM (Array String) := do
  let type ← goal
  let unified ← forallTelescopeReducing type fun _ body => do
    let tree := (instanceExtension.getState (← getEnv)).discrTree
    withConfig (fun c => { c with isDefEqStuckEx := true }) <| tree.getUnify body
  let instances ← SynthInstance.getInstances type
  return #[s!"unify {label}: {entryNames unified}",
           s!"instances {label}: {names (instances.map (·.val))}"]

def typeMVar : MetaM Expr := do mkFreshExprMVar (mkSort (mkLevelSucc (← mkFreshLevelMVar)))

def app (c : Name) (us : List Level) (args : Array Expr) : Expr := mkAppN (mkConst c us) args

def goals : List (String × MetaM Expr) :=
  [("OfNat ?α 0", do return app ``OfNat [← mkFreshLevelMVar] #[← typeMVar, mkRawNatLit 0]),
   ("OfNat Nat 0", return app ``OfNat [0] #[nat, mkRawNatLit 0]),
   ("OfNat Nat 5", return app ``OfNat [0] #[nat, mkRawNatLit 5]),
   ("HAdd Nat Nat Nat", return app ``HAdd [0, 0, 0] #[nat, nat, nat]),
   ("HAdd Nat Nat ?γ", do return app ``HAdd [0, 0, ← mkFreshLevelMVar] #[nat, nat, ← typeMVar]),
   ("Add Nat", return app ``Add [0] #[nat]),
   ("Add ?α", do return app ``Add [← mkFreshLevelMVar] #[← typeMVar]),
   ("Mul Nat", return app ``Mul [0] #[nat]),
   ("HMul Nat Nat ?γ", do return app ``HMul [0, 0, ← mkFreshLevelMVar] #[nat, nat, ← typeMVar]),
   ("HPow Nat Nat Nat", return app ``HPow [0, 0, 0] #[nat, nat, nat]),
   ("HPow Nat Nat ?γ", do return app ``HPow [0, 0, ← mkFreshLevelMVar] #[nat, nat, ← typeMVar]),
   ("Sub Nat", return app ``Sub [0] #[nat]),
   ("LE Nat", return app ``LE [0] #[nat]),
   ("LT Nat", return app ``LT [0] #[nat]),
   ("Inhabited Nat", return app ``Inhabited [1] #[nat]),
   ("BEq Nat", return app ``BEq [0] #[nat]),
   ("DecidableEq Nat", return app ``DecidableEq [1] #[nat])]

/-- Decidable (a = b) and Decidable (a ≤ b) for local a b : Nat. -/
def localGoals : MetaM (Array String) :=
  withLocalDeclD `a nat fun a => withLocalDeclD `b nat fun b => do
    let eq := app ``Eq [1] #[nat, a, b]
    let le := app ``LE.le [0] #[nat, mkConst ``instLENat, a, b]
    return (← report "Decidable (a = b)" (return app ``Decidable [] #[eq]))
      ++ (← report "Decidable (a ≤ b)" (return app ``Decidable [] #[le]))

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<elab-instance-order>", fileMap := default,
                              maxHeartbeats := 0 }
  let run : MetaM (Array String) := do
    let mut lines := #[]
    for (label, goal) in goals do
      lines := lines ++ (← report label goal)
    return lines ++ (← localGoals)
  let (lines, _, _) ← (run.toIO ctx { env })
  for line in lines do
    IO.println line
  return 0
