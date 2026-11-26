/-
LeanForth's elaboration-data exporter, its simp part (plan row FE9, slices
SD-a and SD-b of docs/design/TACTIC_SIMP.md; docs/design/SIMP_DATA.md
section 3; docs/programming/ELABORATION_DATA.md, "Format 4"). A development
tool like scripts/export_elab.lean, kept apart from it (plan task SD-b.6)
so that the simp data's later kinds do not change the file whose digest
keys the Mathlib slice's cache (scripts/mathlib-slice.py).
scripts/export-elab.sh runs it for ELAB_FORMAT=4 or 4.1 beside
export_elab.lean and hands both outputs to scripts/export_elab.py.

Usage: lean --run scripts/export_simp.lean MODULE...

It imports the modules and writes, on standard output, one JSON object per
line: first {"lean": {"githash": ..., "version": ...}, "modules": [...],
"simp": true} and then these records, as the environment holds them after
the import:

  tag       a theorem with the defeq tag (defeqAttr, Lean/DefEqAttrib.lean:111:
            a theorem Lean holds to be proved by rfl, which simp's rfl flag
            and dsimp read, SimpTheorems.lean:212)
  congr     every @[congr] lemma (congrExtension,
            Meta/Tactic/Simp/SimpCongrTheorems.lean:49): its name, the
            function it is for, its hypotheses' positions among its
            binders, its priority and its rank, its place in its
            function's list (highest priority first, the newest first among
            equal ones, :39-47: the order simp tries)
  realized  (format 4.1) every congruence theorem Lean realized in the
            library, a theorem NAME.congr_simp (Meta/CongrTheorems.lean:
            405-446, made by mkCongrSimpCore? when a module's simp first
            needed it): its name, the function NAME, its kind
            "congr_simp" and its argument kinds as congrKindsExt holds them
            (0 fixed, 1 eq, 2 cast, 3 subsingletonInst: the numbering of
            src/front/congr-thms.fs), which simp's mkCongrSimp? compares
            with the kinds it computes before it uses the theorem
            (Simp/Types.lean:793)

A name is a JSON array of its parts, root first, as export_elab.lean
writes it. It stops (exit status 1) on a congruence lemma filed under
another function, a realized constant that is no theorem, one without
argument kinds, or an argument kind mkCongrSimpCore? never makes (heq,
fixedNoParam). It prints records in no particular order; the finisher
sorts them. It reads no file and writes nothing but standard output and
standard error.
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

/-- Every theorem with the defeq tag. -/
def defeqRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for (name, _) in env.constants.toList do
    if defeqAttr.hasTag env name then
      out := out.push <| record "tag" [("name", nameJson name), ("tag", Json.str "defeq")]
  return out

/-- The `@[congr]` lemmas, each with its rank: its place in its function's
list, highest priority first and the newest first among equal ones
(SimpCongrTheorems.lean:39-47), the order simp tries them in. -/
def congrRecords (env : Environment) : MetaM (Array Json) := do
  let mut out := #[]
  for (fn, list) in (congrExtension.getState env).lemmas.toList do
    let ts := list.toArray
    for h : rank in [0:ts.size] do
      let t := ts[rank]
      unless t.funName == fn do throwError "congr lemma {t.theoremName}: under another function"
      out := out.push <| record "congr"
        [("name", nameJson t.theoremName), ("fun", nameJson fn), ("hyps", toJson t.hypothesesPos),
         ("priority", toJson t.priority), ("rank", toJson rank)]
  return out

/-- An argument kind as the data writes it; mkCongrSimpCore? makes no other. -/
def kindNumber (name : Name) : CongrArgKind → MetaM Nat
  | .fixed => pure 0
  | .eq => pure 1
  | .cast => pure 2
  | .subsingletonInst => pure 3
  | k => throwError "{name}: argument kind {repr k}"

/-- Every realized NAME.congr_simp of the environment (format 4.1). -/
def realizedRecords (env : Environment) : MetaM (Array Json) := do
  let mut out := #[]
  for (name, info) in env.constants.toList do
    if let .str f s := name then
      if s == congrSimpSuffix then
        unless info matches .thmInfo _ do throwError "{name} is not a theorem"
        let some kinds := congrKindsExt.find? env name | throwError "{name}: no argument kinds"
        let kinds ← kinds.mapM (kindNumber name)
        out := out.push <| record "realized"
          [("name", nameJson name), ("fun", nameJson f), ("kind", Json.str "congr_simp"),
           ("arg_kinds", toJson kinds)]
  return out

def allRecords : MetaM (Array Json) := do
  let env ← getEnv
  return defeqRecords env ++ (← congrRecords env) ++ (← realizedRecords env)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lean --run scripts/export_simp.lean MODULE..."
    return 2
  let modules := args.toArray.map String.toName
  initSearchPath (← findSysroot)
  -- The extensions' states are made from the imported entries only with
  -- loadExts, which needs initializers enabled (Lean's own `lean` does so).
  unsafe enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m }) {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<export_simp>", fileMap := default,
                              maxHeartbeats := 0 }
  let (records, _, _) ← (allRecords.toIO ctx { env })
  let out ← IO.getStdout
  out.putStrLn <| Json.compress <| Json.mkObj
    [("lean", Json.mkObj [("githash", Json.str Lean.githash),
                          ("version", Json.str Lean.versionString)]),
     ("modules", Json.arr (modules.map fun m => Json.str m.toString)),
     ("simp", Json.bool true)]
  for r in records do
    out.putStrLn r.compress
  return 0
