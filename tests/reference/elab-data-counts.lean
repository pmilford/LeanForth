/-
Pinned Lean's own counts of the attributes of Init that LeanForth's
elaboration data holds (plan row FE1d; tests/front/elab-init.sh compares
them with scripts/export-elab.sh's records and with what LeanForth reads).
Found through Lean's public queries, one constant at a time, not through
the extensions' tables that scripts/export_elab.lean walks:
getInstancePriority? (an instance and its priority), getDefaultInstances
of each class, getReducibilityStatus, and getCustomEliminator? on a
variable of each type former (an inductive type or a definition of one:
Lean keys an eliminator by the head of its target's type); and samples:
the instances synthInstance finds for `Add Nat` and `OfNat Nat 0`, their
priorities and classes, the default instances of OfNat and HAdd, and the
eliminators of Nat.

Usage: lean -DwarningAsError=true --run tests/reference/elab-data-counts.lean
It prints one line per count or sample, sorted.
-/
import Lean

open Lean Meta

def statusName : ReducibilityStatus → String
  | .reducible => "reducible"
  | .semireducible => "semireducible"
  | .irreducible => "irreducible"
  | .implicitReducible => "implicit_reducible"
  | .instanceReducible => "instance_reducible"

/-- The class of an instance, as the head of its type's conclusion. -/
def classOf (name : Name) : MetaM String := do
  let info ← getConstInfo name
  forallTelescopeReducing info.type fun _ target => do
    return toString ((← isClass? target).getD .anonymous)

/-- The eliminator Lean's induction or cases tactic finds for a variable
of the inductive type `type` with its parameters and indices as variables. -/
def eliminatorFor (type : Name) (induction : Bool) : MetaM (Option Name) := do
  let info ← getConstInfo type
  let levels := info.levelParams.map Level.param
  forallTelescope info.type fun xs _ => do
    withLocalDeclD `x (mkAppN (mkConst type levels) xs) fun x =>
      getCustomEliminator? #[x] induction

def counts : MetaM (Array String) := do
  let env ← getEnv
  let mut instances := 0
  let mut defaults := 0
  let mut statuses : Std.HashMap String Nat := {}
  let mut eliminators := 0
  for (name, info) in env.constants.toList do
    if (← getInstancePriority? name).isSome then instances := instances + 1
    if isClass env name then defaults := defaults + (← getDefaultInstances name).length
    let status := statusName (← getReducibilityStatus name)
    statuses := statuses.insert status (statuses.getD status 0 + 1)
    if ← isTypeFormerType info.type then
      for induction in [true, false] do
        if (← eliminatorFor name induction).isSome then eliminators := eliminators + 1
  let mut lines := #[s!"instance {instances}", s!"default_instance {defaults}",
    s!"eliminator {eliminators}",
    s!"reducibility {env.constants.toList.length - statuses.getD "semireducible" 0}"]
  for (status, n) in statuses.toList do
    unless status == "semireducible" do lines := lines.push s!"status {status} {n}"
  return lines

def samples : MetaM (Array String) := do
  let nat := mkConst ``Nat
  let add ← synthInstance (mkApp (mkConst ``Add [0]) nat)
  let ofNat ← synthInstance (mkApp2 (mkConst ``OfNat [0]) nat (mkRawNatLit 0))
  let mut lines := #[]
  for inst in [add.getAppFn.constName!, ofNat.getAppFn.constName!] do
    let prio := (← getInstancePriority? inst).getD 0
    lines := lines.push s!"sample instance {inst} {← classOf inst} {prio}"
  for cls in [``OfNat, ``HAdd] do
    for (inst, prio) in ← getDefaultInstances cls do
      lines := lines.push s!"sample default {cls} {inst} {prio}"
  for induction in [true, false] do
    let elim := (← eliminatorFor ``Nat induction).getD .anonymous
    lines := lines.push s!"sample eliminator {if induction then "induction" else "cases"} Nat {elim}"
  return lines

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<elab-data-counts>", fileMap := default,
                              maxHeartbeats := 0 }
  let (lines, _, _) ← ((do return (← counts) ++ (← samples)) : MetaM _).toIO ctx { env }
  for line in lines.qsort (· < ·) do
    IO.println line
  return 0
