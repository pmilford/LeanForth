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

/-! ## Format 4.1: the default simp set and its simprocs (simp group 4)

Ported by hand from branch simp-data-tool, commit 84b76124 (export_elab.lean
there), for the default set alone. -/

/-- A key as export_elab.lean's keyJson writes it (that file's digest keys
the Mathlib slice's cache, so it is not imported or changed here). -/
def keyJson : DiscrTree.Key → MetaM Json
  | .star => pure "star"
  | .other => pure "other"
  | .arrow => pure "arrow"
  | .const n a => pure <| Json.mkObj [("const", nameJson n), ("arity", toJson a)]
  | .proj s i a => pure <| Json.mkObj [("proj", nameJson s), ("idx", toJson i), ("arity", toJson a)]
  | .lit (.natVal n) => pure <| Json.mkObj [("lit", Json.str (toString n))]
  | .lit (.strVal s) => pure <| Json.mkObj [("lit_str", Json.str s)]
  | .fvar f _ => throwError "an fvar key {f.name} in a global simp set"

def keysJson (keys : Array DiscrTree.Key) : MetaM Json := do
  return Json.arr (← keys.mapM keyJson)

/-- The values of a trie depth first: a node's own values, then its
children's in their stored order (export_elab.lean's walk, probe p6). -/
partial def trieValues {α} : DiscrTree.Trie α → Array α → Array α
  | .node vs cs, acc => cs.foldl (fun acc (_, c) => trieValues c acc) (acc ++ vs)

/-- Every value of a tree with its root key and its rank, its place in
the depth-first walk of its root key's trie. -/
def rankedValues {α} (t : DiscrTree α) : Array (DiscrTree.Key × Nat × α) := Id.run do
  let mut out := #[]
  for (root, trie) in t.root.toList do
    let values := trieValues trie #[]
    for h : rank in [0:values.size] do
      out := out.push (root, rank, values[rank])
  return out

/-- A lemma of the default set, the value at `rank` under `root` of its
`post` (or pre) tree; it stops on what the format cannot say. -/
def simpRecord (s : SimpTheorems) (post : Bool) (root : DiscrTree.Key) (rank : Nat)
    (t : SimpTheorem) : MetaM Json := do
  let .decl origin _ inv := t.origin
    | throwError "the default simp set: a lemma whose origin is not a declaration"
  unless s.lemmaNames.contains t.origin do
    throwError "simp lemma {origin}: in the tree but not among the set's lemma names"
  unless t.levelParams.isEmpty do throwError "simp lemma {origin}: universe parameters of its own"
  let some proof := t.proof.constName?
    | throwError "simp lemma {origin}: its proof is not a constant"
  unless t.keys[0]? == some root do throwError "simp lemma {origin}: its first key is not its root"
  unless t.post == post do throwError "simp lemma {origin}: in the other phase's tree"
  return record "simp_lemma"
    [("set", nameJson `simp), ("origin", nameJson origin), ("inv", toJson inv),
     ("post", toJson post), ("proof", nameJson proof), ("priority", toJson t.priority),
     ("perm", toJson t.perm), ("rfl", toJson t.rfl), ("backward_rfl", toJson t.backwardRfl),
     ("keys", ← keysJson t.keys), ("rank", toJson rank)]

/-- The default set's records: the set (its simproc set), its lemmas of
both trees and its definitions to unfold. -/
def defaultSetRecords (env : Environment) : MetaM (Array Json) := do
  let s := simpExtension.getState env
  unless s.erased.toList.isEmpty do throwError "the default simp set: erased lemmas"
  let mut out := #[record "simp_set"
    [("name", nameJson `simp), ("simprocs", nameJson (Simp.simpAttrNameToSimprocAttrName `simp))]]
  for (tree, post) in [(s.pre, false), (s.post, true)] do
    for (root, rank, t) in rankedValues tree do
      out := out.push (← simpRecord s post root rank t)
  for n in s.toUnfold.toList do
    out := out.push <| record "simp_unfold" [("set", nameJson `simp), ("name", nameJson n)]
  return out

/-- The default simproc set's entries (simprocExtension, attribute
simprocAttr), each with its declaration's keys, its phase, its rank under
its root key and whether it is a dsimproc (no proof term). -/
def simprocRecords (env : Environment) : MetaM (Array Json) := do
  let s := Simp.simprocExtension.getState env
  unless s.erased.toList.isEmpty do throwError "the default simproc set: erased simprocs"
  let builtin ← Simp.builtinSimprocDeclsRef.get
  let mut out := #[]
  for (tree, post) in [(s.pre, false), (s.post, true)] do
    for (root, rank, e) in rankedValues tree do
      unless e.keys[0]? == some root && e.post == post && s.simprocNames.contains e.declName do
        throwError "simproc {e.declName}: not where the set's tree has it"
      let proofless ← match builtin.procs[e.declName]? with
        | some (.inr _) => pure true
        | some (.inl _) => pure false
        | none => match ((env.find? e.declName).map (·.type) : Option Expr) with
          | some (.const ``Simp.DSimproc _) => pure true
          | some (.const ``Simp.Simproc _) => pure false
          | _ => throwError "simproc {e.declName}: neither a Simproc nor a DSimproc"
      out := out.push <| record "simproc"
        [("name", nameJson e.declName), ("keys", ← keysJson e.keys), ("post", toJson post),
         ("rank", toJson rank), ("dsimproc", toJson proofless)]
  return out

def allRecords : MetaM (Array Json) := do
  let env ← getEnv
  return defeqRecords env ++ (← congrRecords env) ++ (← realizedRecords env)
    ++ (← defaultSetRecords env) ++ (← simprocRecords env)

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
