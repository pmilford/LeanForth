/-
LeanForth's elaboration-data exporter, its Lean part (plan row FE1d;
ADR 0021 D10; docs/programming/ELABORATION_DATA.md). A development tool,
run with pinned Lean 4.35.0 when a library is exported (owner decision of
2026-11-12, "Front-end syntax", answer 8); scripts/export-elab.sh runs it
and scripts/export_elab.py turns its output into the file LeanForth reads.

Usage: lean --run scripts/export_elab.lean MODULE...

It imports the modules and writes, on standard output, one JSON object per
line: first {"lean": {"githash": ..., "version": ...}, "modules": [...]}
and then every record of the attributes FE1 needs, as the environment
holds them after the import (global entries; nothing scoped is active):

  instance          an instance (Meta.instanceExtension): its name, its
                    class (the head of its type's conclusion, as
                    Meta.addInstance finds it with forallTelescopeReducing
                    and isClass?), its priority and its synthesis order
  default_instance  a default instance (Meta.defaultInstanceExtension):
                    class, instance and priority
  reducibility      a declaration whose status, getReducibilityStatusCore,
                    is not the default (semireducible): reducible,
                    irreducible, implicit_reducible or instance_reducible
  eliminator        an @[induction_eliminator] or @[cases_eliminator]
                    (Meta.customEliminatorExt): kind, the explicit target
                    types and the eliminator

A name is a JSON array of its parts, strings and natural numbers, root
first (`Nat.add` is ["Nat","add"]). It prints records in no particular
order; the finisher sorts them. It reads no file and writes nothing but
standard output and standard error.
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

def instanceRecords : MetaM (Array Json) := do
  let state := instanceExtension.getState (← getEnv)
  let mut out := #[]
  for (name, entry) in state.instanceNames.toList do
    unless state.erased.contains name do
      let cls ← instanceClass name
      out := out.push <| record "instance"
        [("name", nameJson name), ("class", nameJson cls),
         ("priority", toJson entry.priority), ("synth_order", toJson entry.synthOrder)]
  return out

def defaultInstanceRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for (cls, insts) in (defaultInstanceExtension.getState env).defaultInstances.toList do
    for (inst, prio) in insts do
      out := out.push <| record "default_instance"
        [("class", nameJson cls), ("name", nameJson inst), ("priority", toJson prio)]
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

def allRecords : MetaM (Array Json) := do
  let env ← getEnv
  let insts ← instanceRecords
  return insts ++ defaultInstanceRecords env ++ reducibilityRecords env ++ eliminatorRecords env

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
