/-
LeanForth's elaboration-data exporter, its Lean part (plan rows FE1d and
FE1e1; ADR 0021 D10; docs/programming/ELABORATION_DATA.md). A development
tool, run with pinned Lean 4.35.0 when a library is exported (owner
decision of 2026-11-12, "Front-end syntax", answer 8); scripts/export-elab.sh
runs it and scripts/export_elab.py turns its output into the file LeanForth
reads (format version 3; with scripts/export_simp.lean's records, which
scripts/export-elab.sh adds for ELAB_FORMAT=4 or 4.1, format 4 or 4.1).

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
                    elaborator or Meta's whnf reads: elab_as_elim,
                    elab_without_expected_type (tag attributes),
                    aux_recursor (isAuxRecursor), no_confusion
                    (isNoConfusion), cases_on, rec_on, brec_on (Lean's
                    isCasesOnRecursor, isRecOnRecursor, isBRecOnRecursor),
                    match_pattern (hasMatchPatternAttribute)
  matcher           a matcher (Meta.getMatcherInfoCore?): numbers of
                    parameters and discriminants, the elimination
                    universe's position or null, each alternative's
                    numFields, numOverlaps and hasUnitThunk, and each
                    discriminant's `h :` name or null (its overlaps map,
                    which only the equation compiler's splitter reads, is
                    not written)
  projection        a projection function (getProjectionFnInfo?): the
                    constructor, the structure's parameters, the field's
                    index and whether the structure is a class
  sunfold           every smart-unfolding definition f._sunfold
                    (mkSmartUnfoldingNameFor, Meta/WHNF.lean:50): the
                    name f, f._sunfold's universe parameters, its value
                    as a table of levels and one of nodes, each entry
                    referring only to earlier ones (shared subterms
                    written once, the root last),
                    and f's structural recursion argument
                    (getStructuralRecArgPos?, Meta/WHNF.lean:46, which is
                    getStructuralRecArgPosImp?, Structural/Eqns.lean:191)
                    or null
  binder_kinds      every constant whose type has a leading Pi binder:
                    one text per such binder, its kind (0 default, 1
                    implicit, 2 strictImplicit, 3 instImplicit) and then
                    the kinds of its domain's leading Pi binders; the
                    finisher keeps those that differ from the export's

The simp data's records (the defeq tag, @[congr] lemmas, realized
congruence theorems: docs/design/SIMP_DATA.md section 3) are
scripts/export_simp.lean's (plan task SD-b.6).

A name is a JSON array of its parts, strings and natural numbers, root
first (`Nat.add` is ["Nat","add"]). A key is "star", "other", "arrow",
{"const": NAME, "arity": N}, {"lit": DIGITS} (the decimal digits as a
text, as lean4export writes natVal), {"lit_str": S} or
{"proj": NAME, "idx": I, "arity": N}; an fvar key, which no global
instance has, stops the program. A node is {"bvar": I}, {"sort": L},
{"const": NAME, "levels": [L...]} (L the place of a level in the record's
level table), {"app": [F, A]}, {"lam": BINDER} or
{"forall": BINDER} with BINDER {"name", "info", "type", "body"} (info
default, implicit, strict or inst), {"let": {"name", "type", "value",
"body", "non_dep"}}, {"lit": DIGITS}, {"str": S}, {"proj": {"struct",
"idx", "expr"}} or {"mdata": {"entries": [[KEY, VALUE]...], "expr"}}, the
numbers in it the indices of earlier nodes; a VALUE is {"bool": B},
{"nat": DIGITS}, {"string": S} or {"name": NAME}; a level of the table
is "zero", {"succ": L}, {"max": [L, L]}, {"imax": [L, L]} or {"param":
NAME}, each L the place of an earlier level. A
free variable, a metavariable, a level metavariable or another kind of
mdata value stops the program. It also stops (exit status 1) when the
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
  | .lit (.natVal n) => pure <| Json.mkObj [("lit", Json.str (toString n))]
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

/-- The tags of a declaration that the application elaborator and Meta's
whnf read. -/
def tagsOf (env : Environment) (name : Name) : List String :=
  [("elab_as_elim", Elab.Term.elabAsElim.hasTag env name),
   ("elab_without_expected_type", Elab.Term.elabWithoutExpectedTypeAttr.hasTag env name),
   ("aux_recursor", isAuxRecursor env name), ("no_confusion", isNoConfusion env name),
   ("cases_on", isCasesOnRecursor env name), ("rec_on", isRecOnRecursor env name),
   ("brec_on", isBRecOnRecursor env name),
   ("match_pattern", hasMatchPatternAttribute env name)].filterMap fun (t, b) =>
    if b then some t else none

def optJson : Option Nat → Json
  | some n => toJson n
  | none => Json.null

def matcherJson (name : Name) (m : Meta.MatcherInfo) : Json :=
  record "matcher"
    [("name", nameJson name), ("num_params", toJson m.numParams),
     ("num_discrs", toJson m.numDiscrs), ("u_elim_pos", optJson m.uElimPos?),
     ("alt_infos", Json.arr (m.altInfos.map fun a => Json.mkObj
        [("num_fields", toJson a.numFields), ("num_overlaps", toJson a.numOverlaps),
         ("has_unit_thunk", toJson a.hasUnitThunk)])),
     ("discr_names", Json.arr (m.discrInfos.map fun d => (d.hName?.map nameJson).getD Json.null))]

def projectionJson (name : Name) (p : ProjectionFunctionInfo) : Json :=
  record "projection"
    [("name", nameJson name), ("ctor", nameJson p.ctorName), ("num_params", toJson p.numParams),
     ("idx", toJson p.i), ("from_class", toJson p.fromClass)]

/-- Every constant's tags, matcher information and projection information. -/
def constantRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for (name, _) in env.constants.toList do
    for tag in tagsOf env name do
      out := out.push <| record "tag" [("name", nameJson name), ("tag", Json.str tag)]
    if let some m := Meta.getMatcherInfoCore? env name then
      out := out.push (matcherJson name m)
    if let some p := env.getProjectionFnInfo? name then
      out := out.push (projectionJson name p)
  return out

def binderText : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strict"
  | .instImplicit => "inst"

def dataValueJson : DataValue → MetaM Json
  | .ofBool b => pure <| Json.mkObj [("bool", toJson b)]
  | .ofNat n => pure <| Json.mkObj [("nat", Json.str (toString n))]
  | .ofString s => pure <| Json.mkObj [("string", Json.str s)]
  | .ofName n => pure <| Json.mkObj [("name", nameJson n)]
  | v => throwError "an mdata value {v} in a smart-unfolding body"

/-- A subterm as a key of the node table, compared by `Expr.equal`:
Lean's `Expr ==` ignores binder names and binder info, so two binders that
differ only there would share one node, which then carries the first one's
name and info (18 of Init's 389 bodies did, review s2-unfold-a M2). The
hash is Lean's, which ignores them too, so equal keys hash alike. -/
structure ExprKey where
  e : Expr

instance : BEq ExprKey := ⟨fun a b => a.e.equal b.e⟩
instance : Hashable ExprKey := ⟨fun a => a.e.hash⟩

/-- The tables of a term: each level and each subterm written once, after
its parts. -/
structure Nodes where
  levels : Array Json := #[]
  levelIndex : Std.HashMap Level Nat := {}
  nodes : Array Json := #[]
  index : Std.HashMap ExprKey Nat := {}

abbrev NodesM := StateT Nodes MetaM

/-- A universe level's place in the level table; a level metavariable is an error. -/
partial def levelOf (l : Level) : NodesM Nat := do
  if let some i := (← get).levelIndex[l]? then return i
  let entry ← match l with
    | .zero => pure (Json.str "zero")
    | .succ a => do pure <| Json.mkObj [("succ", toJson (← levelOf a))]
    | .max a b => do
      let a ← levelOf a; let b ← levelOf b
      pure <| Json.mkObj [("max", Json.arr #[toJson a, toJson b])]
    | .imax a b => do
      let a ← levelOf a; let b ← levelOf b
      pure <| Json.mkObj [("imax", Json.arr #[toJson a, toJson b])]
    | .param n => pure <| Json.mkObj [("param", nameJson n)]
    | .mvar _ => throwError "a level metavariable in a smart-unfolding body"
  let s ← get
  set { s with levels := s.levels.push entry, levelIndex := s.levelIndex.insert l s.levels.size }
  return s.levels.size

def binderJson (n : Name) (bi : BinderInfo) (ty body : Nat) : Json :=
  Json.mkObj [("name", nameJson n), ("info", Json.str (binderText bi)), ("type", toJson ty),
              ("body", toJson body)]

partial def nodeOf (e : Expr) : NodesM Nat := do
  if let some i := (← get).index[(⟨e⟩ : ExprKey)]? then return i
  let node ← match e with
    | .bvar i => pure <| Json.mkObj [("bvar", toJson i)]
    | .sort l => do pure <| Json.mkObj [("sort", toJson (← levelOf l))]
    | .const n ls => do
      let ls ← ls.toArray.mapM levelOf
      pure <| Json.mkObj [("const", nameJson n), ("levels", toJson ls)]
    | .app f a => do
      let f ← nodeOf f; let a ← nodeOf a
      pure <| Json.mkObj [("app", Json.arr #[toJson f, toJson a])]
    | .lam n ty b bi => do
      let ty ← nodeOf ty; let b ← nodeOf b
      pure <| Json.mkObj [("lam", binderJson n bi ty b)]
    | .forallE n ty b bi => do
      let ty ← nodeOf ty; let b ← nodeOf b
      pure <| Json.mkObj [("forall", binderJson n bi ty b)]
    | .letE n ty v b nonDep => do
      let ty ← nodeOf ty; let v ← nodeOf v; let b ← nodeOf b
      pure <| Json.mkObj [("let", Json.mkObj [("name", nameJson n), ("type", toJson ty),
        ("value", toJson v), ("body", toJson b), ("non_dep", toJson nonDep)])]
    | .lit (.natVal k) => pure <| Json.mkObj [("lit", Json.str (toString k))]
    | .lit (.strVal s) => pure <| Json.mkObj [("str", Json.str s)]
    | .proj s i x => do
      let x ← nodeOf x
      pure <| Json.mkObj [("proj", Json.mkObj [("struct", nameJson s), ("idx", toJson i),
        ("expr", toJson x)])]
    | .mdata m x => do
      let x ← nodeOf x
      let entries ← (m.entries.toArray.mapM fun (k, v) => do
        return Json.arr #[nameJson k, ← dataValueJson v] : MetaM (Array Json))
      pure <| Json.mkObj [("mdata", Json.mkObj [("entries", Json.arr entries), ("expr", toJson x)])]
    | .fvar _ | .mvar _ => throwError "a free variable or metavariable in a smart-unfolding body"
  let s ← get
  set { s with nodes := s.nodes.push node, index := s.index.insert ⟨e⟩ s.nodes.size }
  return s.nodes.size

/-- The record of f's smart-unfolding definition f._sunfold (a definition). -/
def sunfoldRecord (f : Name) (info : ConstantInfo) : MetaM Json := do
  let some value := info.value? | throwError "{info.name} has no value"
  let (root, table) ← (nodeOf value).run {}
  let recArg ← getStructuralRecArgPos? f
  return record "sunfold"
    [("name", nameJson f), ("level_params", Json.arr (info.levelParams.toArray.map nameJson)),
     ("levels", Json.arr table.levels), ("nodes", Json.arr table.nodes), ("value", toJson root),
     ("rec_arg", optJson recArg)]

/-- Every f._sunfold of the environment, as Lean's find? of
mkSmartUnfoldingNameFor f sees it: a definition. -/
def sunfoldRecords (env : Environment) : MetaM (Array Json) := do
  let mut out := #[]
  for (name, info) in env.constants.toList do
    if let .str f s := name then
      if s == smartUnfoldingSuffix then
        unless info matches .defnInfo _ do throwError "{name} is not a definition"
        out := out.push (← sunfoldRecord f info)
  return out

/-- A binder's kind as the data writes it, the place of Lean's BinderInfo
constructor: default 0, implicit 1, strictImplicit 2, instImplicit 3. -/
def binderDigit : BinderInfo → Char
  | .default => '0' | .implicit => '1' | .strictImplicit => '2' | .instImplicit => '3'

/-- The kinds of e's leading Pi binders (forallE nodes, nothing unfolded;
through metadata, which lean4export does not write and whnfCore steps
through). -/
partial def leadKinds : Expr → List Char
  | .forallE _ _ b bi => binderDigit bi :: leadKinds b
  | .mdata _ e => leadKinds e
  | _ => []

/-- One text per leading Pi binder of a type: its kind, then the kinds of
its domain's leading Pi binders (where the induction tactic reads an
alternative's fields). -/
partial def binderTexts : Expr → Array Json
  | .forallE _ d b bi => #[Json.str (String.ofList (binderDigit bi :: leadKinds d))] ++ binderTexts b
  | .mdata _ e => binderTexts e
  | _ => #[]

/-- Every constant's binder kinds, as its type holds them (format 3.2; plan
FE1c-bk): lean4export writes one node for expressions equal up to binder
kinds and names (Expr.eqv), so the finisher keeps the records whose kinds
differ from the export's. -/
def binderKindRecords (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for (name, info) in env.constants.toList do
    let texts := binderTexts info.type
    unless texts.isEmpty do
      out := out.push (record "binder_kinds" [("name", nameJson name), ("kinds", Json.arr texts)])
  return out

def allRecords : MetaM (Array Json) := do
  let env ← getEnv
  let insts ← instanceRecords
  return insts ++ defaultInstanceRecords env ++ reducibilityRecords env
    ++ eliminatorRecords env ++ classRecords env ++ constantRecords env
    ++ (← sunfoldRecords env) ++ binderKindRecords env

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
  out.putStrLn <| Json.compress <| Json.mkObj <|
    [("lean", Json.mkObj [("githash", Json.str Lean.githash),
                          ("version", Json.str Lean.versionString)]),
     ("modules", Json.arr (modules.map fun m => Json.str m.toString))]
  for r in records do
    out.putStrLn r.compress
  return 0
