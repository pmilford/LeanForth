/- Measurement for docs/design/SIMP_DATA.md: Mathlib's norm_num extension
table (Mathlib.Meta.NormNum.normNumExt). Usage: lean --run count_normnum.lean Mathlib -/
import Mathlib.Tactic.NormNum.Core
open Lean Meta Mathlib.Meta.NormNum

partial def nameParts : Name → Array Json
  | .anonymous => #[]
  | .str p s => (nameParts p).push (Json.str s)
  | .num p k => (nameParts p).push (toJson k)
def nameJson (n : Name) : Json := Json.arr (nameParts n)
def keyJson : DiscrTree.Key → Json
  | .star => "star" | .other => "other" | .arrow => "arrow"
  | .const n a => Json.mkObj [("const", nameJson n), ("arity", toJson a)]
  | .proj s i a => Json.mkObj [("proj", nameJson s), ("idx", toJson i), ("arity", toJson a)]
  | .lit (.natVal n) => Json.mkObj [("lit", Json.str (toString n))]
  | .lit (.strVal s) => Json.mkObj [("lit_str", Json.str s)]
  | .fvar f _ => Json.mkObj [("fvar", nameJson f.name)]

partial def walk (keys : Array DiscrTree.Key) : DiscrTree.Trie NormNumExt → Array Json → Array Json
  | .node vs cs, acc =>
    let acc := vs.foldl (fun acc (v : NormNumExt) => acc.push <| Json.mkObj [("norm_num", Json.mkObj
      [("name", nameJson v.name), ("pre", toJson v.pre), ("post", toJson v.post),
       ("keys", Json.arr (keys.map keyJson))])]) acc
    cs.foldl (fun acc (k, c) => walk (keys.push k) c acc) acc

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules (args.toArray.map fun m => { module := m.toName }) {} (loadExts := true)
  let s := normNumExt.getState env
  let out ← IO.getStdout
  for (k, t) in s.tree.root.toList do
    for r in walk #[k] t #[] do out.putStrLn r.compress
  out.putStrLn (Json.mkObj [("erased", toJson s.erased.toList.length)]).compress
  return 0
