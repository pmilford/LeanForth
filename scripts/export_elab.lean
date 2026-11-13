/-
LeanForth's elaboration-data exporter, its Lean part (plan rows FE1d and
FE1e1; ADR 0021 D10; docs/programming/ELABORATION_DATA.md). A development
tool, run with pinned Lean 4.35.0 when a library is exported (owner
decision of 2026-11-12, "Front-end syntax", answer 8); scripts/export-elab.sh
runs it and scripts/export_elab.py turns its output into the file LeanForth
reads (format version 2).

Usage: lean --run scripts/export_elab.lean MODULE...

It imports the modules and writes, on standard output, one JSON object per
line: first {"lean": {"githash": ..., "version": ...}, "modules": [...]}
and then every record of the attributes FE1 needs, as the environment
holds them after the import (global entries; nothing scoped is active):

  instance          every value of Lean's instance tree
                    (Meta.instanceExtension's discrimination tree): its
                    name, its class (the head of its type's conclusion, as
                    Meta.addInstance finds it with forallTelescopeReducing
                    and isClass?), priority, synthesis order, its keys as
                    the tree stores them, its rank (its place in a
                    depth-first walk of its root key's trie, children in
                    their stored order, values in theirs: the order of
                    DiscrTree.getUnify's result, probe p6 of
                    docs/design/FE1E_APPLICATIONS.md) and whether it is
                    erased (in the tree but never a candidate); the
                    finisher keeps it as an instance or an instance left out
  default_instance  a default instance (Meta.defaultInstanceExtension):
                    class, instance, priority and rank, its place in
                    getDefaultInstances of its class (most recent first)
  reducibility      a declaration whose status, getReducibilityStatusCore,
                    is not the default (semireducible): reducible,
                    irreducible, implicit_reducible or instance_reducible
  eliminator        an @[induction_eliminator] or @[cases_eliminator]
                    (Meta.customEliminatorExt): kind, the explicit target
                    types and the eliminator
  class             a class (classExtension): its name and the positions
                    of its out-parameters and out-level parameters
  tag               a declaration with one of the tags the application
                    elaborator reads: elab_as_elim, elab_without_expected_type
                    (tag attributes), cases_on, rec_on, brec_on (Lean's
                    isCasesOnRecursor, isRecOnRecursor, isBRecOnRecursor)

A name is a JSON array of its parts, strings and natural numbers, root
first (`Nat.add` is ["Nat","add"]). A key is "star", "other", "arrow",
{"const": NAME, "arity": N}, {"lit": N}, {"lit_str": S} or
{"proj": NAME, "idx": I, "arity": N}; an fvar key, which no global
instance has, stops the program. It also stops (exit status 1) when the
tree and Lean's table of instance names disagree: a value without a name,
an instance twice in the tree, a value whose first key is not its root,
a priority, synthesis order or key list that differs from the table's,
or a name of the table that is not in the tree. It prints records in no
particular order; the finisher sorts them. It reads no file and writes
nothing but standard output and standard error.
-/
import Lean

open Lean Meta

/-- A name as the array of its parts, root first. -/
partial def nameParts : Name → Array Json
  | .anonymous => #[]
  | .str p s => (nameParts p).push (Json.str s)
  | .num p k => (nameParts p).push (toJson k)

def nameJson (n : Name) : Json := Json.arr (nameParts n)

def record (kind : String) (fields : List (String × Json)) : Json :=
  Json.mkObj [(kind, Json.mkObj fields)]

/-- The class of an instance, found as `Meta.addInstance` checks it. -/
def instanceClass (name : Name) : MetaM Name := do
  let info ← getConstInfo name
  let cls? ← forallTelescopeReducing info.type fun _ target => isClass? target
  match cls? with
  | some cls => pure cls
  | none => throwError "instance {name}: its type's conclusion is not a class"

/-- A discrimination-tree key as JSON; an fvar key is an error. -/
def keyJson : DiscrTree.Key → MetaM Json
  | .star => pure "star"
  | .other => pure "other"
  | .arrow => pure "arrow"
  | .const n a => pure <| Json.mkObj [("const", nameJson n), ("arity", toJson a)]
  | .proj s i a => pure <| Json.mkObj [("proj", nameJson s), ("idx", toJson i), ("arity", toJson a)]
  | .lit (.natVal n) => pure <| Json.mkObj [("lit", toJson n)]
  | .lit (.strVal s) => pure <| Json.mkObj [("lit_str", Json.str s)]
  | .fvar f _ => throwError "an fvar key {f.name} in a global instance"

/-- The values of a trie depth first: a node's own values, then its
children's in their stored order (probe p6's walk). -/
partial def trieValues : DiscrTree.Trie InstanceEntry → Array InstanceEntry → Array InstanceEntry
  | .node vs cs, acc => cs.foldl (fun acc (_, c) => trieValues c acc) (acc ++ vs)

/-- The tree value at `rank` under `root` as a raw instance record, after
checking it against Lean's table of instance names. -/
def treeRecord (state : Instances) (root : DiscrTree.Key) (rank : Nat) (e : InstanceEntry) :
    MetaM (Name × Json) := do
  let some name := e.globalName? | throwError "an instance tree value without a name"
  unless e.keys[0]? == some root do throwError "instance {name}: its first key is not its root"
  let erased := state.erased.contains name
  unless erased do
    let some t := state.instanceNames.find? name | throwError "instance {name}: not in the table"
    unless t.priority == e.priority && t.synthOrder == e.synthOrder && t.keys == e.keys do
      throwError "instance {name}: the tree and the table differ"
  let cls ← instanceClass name
  return (name, record "instance"
    [("name", nameJson name), ("class", nameJson cls), ("priority", toJson e.priority),
     ("synth_order", toJson e.synthOrder), ("keys", Json.arr (← e.keys.mapM keyJson)),
     ("rank", toJson rank), ("erased", toJson erased)])

def instanceRecords : MetaM (Array Json) := do
  let state := instanceExtension.getState (← getEnv)
  let mut out := #[]
  let mut seen : NameSet := {}
  for (root, trie) in state.discrTree.root.toList do
    let values := trieValues trie #[]
    for h : rank in [0:values.size] do
      let (name, r) ← treeRecord state root rank values[rank]
      if seen.contains name then throwError "instance {name} is twice in the tree"
      seen := seen.insert name
      out := out.push r
  for (name, _) in state.instanceNames.toList do
    unless seen.contains name do throwError "instance {name} is not in the tree"
  return out

def defaultInstanceRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for (cls, insts) in (defaultInstanceExtension.getState env).defaultInstances.toList do
    for h : rank in [0:insts.length] do
      let (inst, prio) := insts[rank]
      out := out.push <| record "default_instance"
        [("class", nameJson cls), ("name", nameJson inst), ("priority", toJson prio),
         ("rank", toJson rank)]
  return out

def statusText : ReducibilityStatus → Option String
  | .reducible => some "reducible"
  | .semireducible => none
  | .irreducible => some "irreducible"
  | .implicitReducible => some "implicit_reducible"
  | .instanceReducible => some "instance_reducible"

def reducibilityRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for (name, _) in env.constants.toList do
    if let some status := statusText (getReducibilityStatusCore env name) then
      out := out.push <| record "reducibility"
        [("name", nameJson name), ("status", Json.str status)]
  return out

def eliminatorRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for ((induction, types), elim) in (customEliminatorExt.getState env).map.toList do
    out := out.push <| record "eliminator"
      [("kind", Json.str (if induction then "induction" else "cases")),
       ("types", Json.arr (types.map nameJson)), ("name", nameJson elim)]
  return out

def classRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for (name, outParams) in (classExtension.getState env).outParamMap.toList do
    let levels := (getOutLevelParamPositions? env name).getD #[]
    out := out.push <| record "class"
      [("name", nameJson name), ("out_params", toJson outParams),
       ("out_level_params", toJson levels)]
  return out

/-- The tags of a declaration that the application elaborator reads. -/
def tagsOf (env : Environment) (name : Name) : List String :=
  [("elab_as_elim", Elab.Term.elabAsElim.hasTag env name),
   ("elab_without_expected_type", Elab.Term.elabWithoutExpectedTypeAttr.hasTag env name),
   ("cases_on", isCasesOnRecursor env name), ("rec_on", isRecOnRecursor env name),
   ("brec_on", isBRecOnRecursor env name)].filterMap fun (t, b) => if b then some t else none

def tagRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for (name, _) in env.constants.toList do
    for tag in tagsOf env name do
      out := out.push <| record "tag" [("name", nameJson name), ("tag", Json.str tag)]
  return out

def allRecords : MetaM (Array Json) := do
  let env ← getEnv
  let insts ← instanceRecords
  return insts ++ defaultInstanceRecords env ++ reducibilityRecords env
    ++ eliminatorRecords env ++ classRecords env ++ tagRecords env

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lean --run scripts/export_elab.lean MODULE..."
    return 2
  let modules := args.toArray.map String.toName
  initSearchPath (← findSysroot)
  -- The extensions' states are made from the imported entries only with
  -- loadExts, which needs initializers enabled (Lean's own `lean` does so).
  unsafe enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m }) {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<export_elab>", fileMap := default,
                              maxHeartbeats := 0 }
  let (records, _, _) ← (allRecords.toIO ctx { env })
  let out ← IO.getStdout
  out.putStrLn <| Json.compress <| Json.mkObj
    [("lean", Json.mkObj [("githash", Json.str Lean.githash),
                          ("version", Json.str Lean.versionString)]),
     ("modules", Json.arr (modules.map fun m => Json.str m.toString))]
  for r in records do
    out.putStrLn r.compress
  return 0
