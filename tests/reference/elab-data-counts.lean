/-
Pinned Lean's own counts of the attributes of Init that LeanForth's
elaboration data holds (plan rows FE1d and FE1e1; tests/front/elab-init.sh
compares them with scripts/export-elab.sh's records and with what
LeanForth reads). Found through Lean's queries one constant at a time,
not through the walks of scripts/export_elab.lean: getInstancePriority?
(an instance and its priority) and getErasedInstances, isClass,
getDefaultInstances of each class, getReducibilityStatus,
getCustomEliminator? on a variable of each type former (an inductive type
or a definition of one: Lean keys an eliminator by the head of its
target's type), the tag predicates (hasTag of elab_as_elim and
elab_without_expected_type, isAuxRecursor, isNoConfusion,
isCasesOnRecursor, isRecOnRecursor, isBRecOnRecursor), getMatcherInfo?
and getProjectionFnInfo?; and samples: the instances synthInstance finds
for `Add Nat` and `OfNat Nat 0`, their priorities and classes, the keys
Lean's table of instances holds for six instances (a natural literal of
2^64, a string literal, a projection, arrows, other), the default
instances of OfNat and HAdd, HAdd's out-parameters, the tags of four
declarations, a matcher, a projection and the eliminators of Nat.

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

def plain (n : Name) : String := n.toString (escape := false)

/-- Each item after a space; numbers joined by commas. -/
def spaced (items : List String) : String := String.join (items.map (" " ++ ·))

def commas (ns : List Nat) : String := ",".intercalate (ns.map toString)

/-- The class of an instance, as the head of its type's conclusion. -/
def classOf (name : Name) : MetaM String := do
  let info ← getConstInfo name
  forallTelescopeReducing info.type fun _ target => do
    return plain ((← isClass? target).getD .anonymous)

/-- The eliminator Lean's induction or cases tactic finds for a variable
of the inductive type `type` with its parameters and indices as variables. -/
def eliminatorFor (type : Name) (induction : Bool) : MetaM (Option Name) := do
  let info ← getConstInfo type
  let levels := info.levelParams.map Level.param
  forallTelescope info.type fun xs _ => do
    withLocalDeclD `x (mkAppN (mkConst type levels) xs) fun x =>
      getCustomEliminator? #[x] induction

/-- The tags of a declaration, as the elaboration data names them. -/
def tagsOf (env : Environment) (name : Name) : List String :=
  [("elab_as_elim", Elab.Term.elabAsElim.hasTag env name),
   ("elab_without_expected_type", Elab.Term.elabWithoutExpectedTypeAttr.hasTag env name),
   ("aux_recursor", isAuxRecursor env name), ("no_confusion", isNoConfusion env name),
   ("cases_on", isCasesOnRecursor env name), ("rec_on", isRecOnRecursor env name),
   ("brec_on", isBRecOnRecursor env name)].filterMap fun (t, b) => if b then some t else none

def counts : MetaM (Array String) := do
  let env ← getEnv
  let mut instances := (← getErasedInstances).toList.length
  let mut classes := 0
  let mut defaults := 0
  let mut statuses : Std.HashMap String Nat := {}
  let mut eliminators := 0
  let mut tags := 0
  let mut matchers := 0
  let mut projections := 0
  for (name, info) in env.constants.toList do
    if (← getInstancePriority? name).isSome then instances := instances + 1
    if isClass env name then
      classes := classes + 1
      defaults := defaults + (← getDefaultInstances name).length
    let status := statusName (← getReducibilityStatus name)
    statuses := statuses.insert status (statuses.getD status 0 + 1)
    if ← isTypeFormerType info.type then
      for induction in [true, false] do
        if (← eliminatorFor name induction).isSome then eliminators := eliminators + 1
    tags := tags + (tagsOf env name).length
    if (← getMatcherInfo? name).isSome then matchers := matchers + 1
    if (← getProjectionFnInfo? name).isSome then projections := projections + 1
  let mut lines := #[s!"instance {instances}", s!"class {classes}",
    s!"default_instance {defaults}", s!"eliminator {eliminators}",
    s!"reducibility {env.constants.toList.length - statuses.getD "semireducible" 0}",
    s!"tag {tags}", s!"matcher {matchers}", s!"projection {projections}"]
  for (status, n) in statuses.toList do
    unless status == "semireducible" do lines := lines.push s!"status {status} {n}"
  return lines

/-- A key as the samples print it (tests/front/elab-init.fs prints the
same): a constant NAME/ARITY, a projection NAME#IDX/ARITY, a literal its
digits, a string literal in quotes, *, other, arrow. -/
def keyText : DiscrTree.Key → String
  | .const n a => s!"{plain n}/{a}"
  | .proj s i a => s!"{plain s}#{i}/{a}"
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s!"\"{s}\""
  | .star => "*"
  | .other => "other"
  | .arrow => "arrow"
  | .fvar f a => s!"fvar {plain f.name}/{a}"

def keySamples : MetaM (Array String) := do
  let table := (instanceExtension.getState (← getEnv)).instanceNames
  let mut lines := #[]
  for inst in [``instOfNatNat, ``Lean.Grind.instIsCharPUInt64OfNatNat,
               ``Lean.TSyntax.instCoeStrLitTerm, ``Decidable.predToBool, ``boolToProp,
               ``ShareCommon.instInhabitedState] do
    let keys := (table.find? inst).map (·.keys.toList.map keyText) |>.getD []
    lines := lines.push s!"sample keys {plain inst}:{spaced keys}"
  return lines

def samples : MetaM (Array String) := do
  let env ← getEnv
  let nat := mkConst ``Nat
  let add ← synthInstance (mkApp (mkConst ``Add [0]) nat)
  let ofNat ← synthInstance (mkApp2 (mkConst ``OfNat [0]) nat (mkRawNatLit 0))
  let mut lines := #[]
  for inst in [add.getAppFn.constName!, ofNat.getAppFn.constName!] do
    let prio := (← getInstancePriority? inst).getD 0
    lines := lines.push s!"sample instance {plain inst} {← classOf inst} {prio}"
  for cls in [``OfNat, ``HAdd] do
    for (inst, prio) in ← getDefaultInstances cls do
      lines := lines.push s!"sample default {plain cls} {plain inst} {prio}"
  for induction in [true, false] do
    let elim := (← eliminatorFor ``Nat induction).getD .anonymous
    lines := lines.push s!"sample eliminator {if induction then "induction" else "cases"} Nat {plain elim}"
  let params := (getOutParamPositions? env ``HAdd).getD #[]
  let levels := (getOutLevelParamPositions? env ``HAdd).getD #[]
  lines := lines.push s!"sample class HAdd {commas params.toList} {commas levels.toList}"
  for name in [``Nat.casesOn, ``Nat.brecOn, ``Nat.rec, ``Eq.ndrec] do
    lines := lines.push s!"sample tags {plain name}:{spaced (tagsOf env name)}"
  if let some m ← getMatcherInfo? ``Nat.add.match_1 then
    let alts := commas (m.altInfos.toList.map (·.numFields))
    let elim := (m.uElimPos?.map toString).getD "none"
    lines := lines.push s!"sample matcher Nat.add.match_1 {m.numParams} {m.numDiscrs} {elim} {alts}"
  if let some p ← getProjectionFnInfo? ``Add.add then
    lines := lines.push s!"sample projection Add.add {plain p.ctorName} {p.numParams} {p.i} {p.fromClass}"
  return lines ++ (← keySamples)

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
