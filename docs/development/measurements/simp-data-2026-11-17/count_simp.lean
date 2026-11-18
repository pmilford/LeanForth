/- Measurement for docs/design/SIMP_DATA.md: every simp set, simproc set and
congruence lemma of the imported environment, one JSON line each, in the
shape the proposed format-4 records would have.
Usage: lean --run count_simp.lean MODULE... -/
import Lean
open Lean Meta Simp

partial def nameParts : Name → Array Json
  | .anonymous => #[]
  | .str p s => (nameParts p).push (Json.str s)
  | .num p k => (nameParts p).push (toJson k)
def nameJson (n : Name) : Json := Json.arr (nameParts n)

def keyJson : DiscrTree.Key → Json
  | .star => "star"
  | .other => "other"
  | .arrow => "arrow"
  | .const n a => Json.mkObj [("const", nameJson n), ("arity", toJson a)]
  | .proj s i a => Json.mkObj [("proj", nameJson s), ("idx", toJson i), ("arity", toJson a)]
  | .lit (.natVal n) => Json.mkObj [("lit", Json.str (toString n))]
  | .lit (.strVal s) => Json.mkObj [("lit_str", Json.str s)]
  | .fvar f _ => Json.mkObj [("fvar", nameJson f.name)]

partial def trieValues {α} : DiscrTree.Trie α → Array α → Array α
  | .node vs cs, acc => cs.foldl (fun acc (_, c) => trieValues c acc) (acc ++ vs)

partial def trieNodes {α} : DiscrTree.Trie α → Nat
  | .node _ cs => cs.foldl (fun n (_, c) => n + trieNodes c) 1

/-- Values of a tree with their rank under their root, and the tree's node count. -/
def treeValues {α} (t : DiscrTree α) : Array (Nat × α) × Nat := Id.run do
  let mut out := #[]
  let mut nodes := 0
  for (_, trie) in t.root.toList do
    let vs := trieValues trie #[]
    nodes := nodes + trieNodes trie
    for h : r in [0:vs.size] do out := out.push (r, vs[r])
  return (out, nodes)

def originJson : Origin → Json × Bool
  | .decl n _ inv => (nameJson n, inv)
  | o => (Json.mkObj [("other", nameJson o.key)], false)

def simpRecord (set : Name) (rank : Nat) (t : SimpTheorem) : Json :=
  let (origin, inv) := originJson t.origin
  Json.mkObj [("simp", Json.mkObj [
    ("set", nameJson set), ("origin", origin), ("inv", toJson inv), ("post", toJson t.post),
    ("proof", match t.proof.constName? with | some n => nameJson n | none => Json.str "expr"),
    ("level_params", toJson t.levelParams.size),
    ("priority", toJson t.priority), ("perm", toJson t.perm), ("rfl", toJson t.rfl),
    ("backward_rfl", toJson t.backwardRfl), ("keys", Json.arr (t.keys.map keyJson)),
    ("rank", toJson rank)])]

def simpSetRecords (set : Name) (s : SimpTheorems) : Array Json := Id.run do
  let (pre, preN) := treeValues s.pre
  let (post, postN) := treeValues s.post
  let mut out := #[Json.mkObj [("simp_set", Json.mkObj [("set", nameJson set),
    ("pre", toJson pre.size), ("post", toJson post.size), ("pre_nodes", toJson preN),
    ("post_nodes", toJson postN), ("lemma_names", toJson s.lemmaNames.toList.length),
    ("to_unfold", toJson s.toUnfold.toList.length), ("erased", toJson s.erased.toList.length),
    ("to_unfold_thms", toJson s.toUnfoldThms.toList.length)])]]
  for (r, t) in pre ++ post do out := out.push (simpRecord set r t)
  for n in s.toUnfold.toList do
    out := out.push <| Json.mkObj [("unfold", Json.mkObj [("set", nameJson set), ("name", nameJson n),
      ("eqns", Json.arr ((s.toUnfoldThms.find? n).getD #[] |>.map nameJson))])]
  for o in s.erased.toList do
    out := out.push <| Json.mkObj [("erased", Json.mkObj [("set", nameJson set), ("origin", (originJson o).1)])]
  return out

def simprocSetRecords (set : Name) (s : Simprocs) : Array Json := Id.run do
  let (pre, _) := treeValues s.pre
  let (post, _) := treeValues s.post
  let mut out := #[Json.mkObj [("simproc_set", Json.mkObj [("set", nameJson set),
    ("pre", toJson pre.size), ("post", toJson post.size), ("erased", toJson s.erased.toList.length)])]]
  for (r, e) in pre ++ post do
    out := out.push <| Json.mkObj [("simproc", Json.mkObj [("set", nameJson set),
      ("name", nameJson e.declName), ("post", toJson e.post),
      ("dsimproc", toJson (match e.proc with | .inr _ => true | .inl _ => false)),
      ("keys", Json.arr (e.keys.map keyJson)), ("rank", toJson r)])]
  return out

def main (args : List String) : IO UInt32 := do
  let modules := args.toArray.map String.toName
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m }) {} (loadExts := true)
  let out ← IO.getStdout
  for (set, ext) in (← simpExtensionMapRef.get).toList do
    for r in simpSetRecords set (ext.getState env) do out.putStrLn r.compress
  for (set, ext) in (← simprocExtensionMapRef.get).toList do
    for r in simprocSetRecords set (ext.getState env) do out.putStrLn r.compress
  let decls := simprocDeclExt.getState env
  let imported := (List.range env.header.moduleNames.size).foldl
    (fun n i => n + (simprocDeclExt.getModuleEntries env i).size) 0
  out.putStrLn (Json.mkObj [("simproc_decls", Json.mkObj [("builtin", toJson decls.builtin.size),
    ("imported", toJson imported)])]).compress
  let (defeq, backward) := env.constants.toList.foldl (fun (a, b) (n, _) =>
    (a + if defeqAttr.hasTag env n then 1 else 0, b + if backwardDefeqAttr.hasTag env n then 1 else 0)) (0, 0)
  out.putStrLn (Json.mkObj [("defeq_tags", Json.mkObj [("defeq", toJson defeq),
    ("backward_defeq", toJson backward)])]).compress
  let congr := congrExtension.getState env
  for (_, ts) in congr.lemmas.toList do
    for t in ts do
      out.putStrLn (Json.mkObj [("congr", Json.mkObj [("name", nameJson t.theoremName),
        ("fun", nameJson t.funName), ("hyps", toJson t.hypothesesPos), ("priority", toJson t.priority)])]).compress
  return 0
