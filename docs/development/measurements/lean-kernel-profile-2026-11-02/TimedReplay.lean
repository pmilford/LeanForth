/-
Per-declaration timing of Lean's kernel (measurement script, not LeanForth code).

A copy of `Lean.Kernel.Environment.replay` (Lean 4.35.0, src/lean/Lean/Replay.lean,
which `leanchecker --fresh` uses) that times each kernel call separately.

Usage: lean --run TimedReplay.lean MODULE OUT.tsv [--diag] [--nocheck] [--dag] [--tags]
  --diag     enable kernel diagnostics; record delta-unfold counts per declaration
  --nocheck  use addDeclWithoutChecking (measures the non-checking overhead; not used
             for the 2026-11-02 measurements)
  --dag      count distinct (structurally equal) expression nodes per declaration
  --tags     mark proof styles by the constants a value uses (heuristic)
Output columns: name kind module ns unfolds distinct_unfolded top_unfolded top_count dag tags
For Mathlib modules set LEAN_PATH to the Mathlib build folders (run_profiled.sh --mathlib).
-/
import Lean
open Lean

namespace PF

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  out : IO.FS.Handle
  modOf : Name → String
  diag : Bool
  check : Bool
  dag : Bool
  tags : Bool

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  total : Nat := 0
  count : Nat := 0

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Distinct expression nodes (structural equality, cached hashes) reachable from `es`. -/
partial def dagSize (es : List Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut todo := es
  while true do
    match todo with
    | [] => break
    | e :: rest =>
      todo := rest
      if seen.contains e then continue
      seen := seen.insert e
      match e with
      | .app f a => todo := f :: a :: todo
      | .lam _ t b _ => todo := t :: b :: todo
      | .forallE _ t b _ => todo := t :: b :: todo
      | .letE _ t v b _ => todo := t :: v :: b :: todo
      | .mdata _ b => todo := b :: todo
      | .proj _ _ b => todo := b :: todo
      | _ => pure ()
  return seen.size

def declExprs (d : Declaration) : List Expr :=
  match d with
  | .defnDecl v => [v.type, v.value]
  | .thmDecl v => [v.type, v.value]
  | .opaqueDecl v => [v.type, v.value]
  | .axiomDecl v => [v.type]
  | .inductDecl _ _ ts _ => ts.flatMap fun t => t.type :: t.ctors.map (·.type)
  | _ => []

partial def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | .mdata _ b => stripLams b
  | e => e

/-- Proof-style markers from the constants a declaration's value uses (heuristic). -/
def tagsOf (d : Declaration) : String := Id.run do
  let (ty, val?) : Expr × Option Expr := match d with
    | .defnDecl v => (v.type, some v.value) | .thmDecl v => (v.type, some v.value)
    | .opaqueDecl v => (v.type, some v.value) | .axiomDecl v => (v.type, none)
    | _ => (.sort .zero, none)
  let some val := val? | return ""
  let cs := val.getUsedConstants
  let has (p : Name) : Bool := cs.any fun c => p.isPrefixOf c
  let mut tags : Array String := #[]
  if has `Lean.Omega then tags := tags.push "omega"
  if has `of_decide_eq_true || has `of_decide_eq_false then tags := tags.push "decide"
  if has `Lean.Grind then tags := tags.push "grind"
  if has `Std.Tactic.BVDecide then tags := tags.push "bv_decide"
  if has `Nat.Linear || has `Nat.SOM || has `Int.Linear then tags := tags.push "linear_arith"
  if has `Lean.ofReduceBool || has `Lean.ofReduceNat then tags := tags.push "native"
  if has `WellFounded.fix || has `WellFounded.Nat.fix then tags := tags.push "wf"
  if has `Lean.Data.AC then tags := tags.push "ac"
  let body := stripLams val
  let hd := (body.consumeMData.getAppFn).constName?
  if hd == some ``Eq.refl || hd == some ``rfl || hd == some ``HEq.refl || hd == some ``Iff.refl then
    tags := tags.push "rfl"
  let big := (Expr.find? (fun e => match e with
    | .lit (.natVal n) => n ≥ 2^64 | _ => false) val).isSome ||
    (Expr.find? (fun e => match e with | .lit (.natVal n) => n ≥ 2^64 | _ => false) ty).isSome
  if big then tags := tags.push "bignat"
  if (Expr.find? (fun e => e.isProj) val).isSome then tags := tags.push "proj"
  return ",".intercalate tags.toList

def declKind : Declaration → String
  | .defnDecl _ => "defn" | .thmDecl _ => "thm" | .opaqueDecl _ => "opaque"
  | .axiomDecl _ => "axiom" | .inductDecl .. => "induct" | .quotDecl => "quot"
  | _ => "other"

def addDecl (name : Name) (d : Declaration) : M Unit := do
  let ctx ← read
  let env0 := (← get).env
  let env1 := if ctx.diag then env0.resetDiag.enableDiag true else env0
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ =>
    if ctx.check then env1.addDeclCore 0 0 d (cancelTk? := none)
    else env1.addDeclWithoutChecking d
  let t1 ← IO.monoNanosNow
  match r with
  | .ok env =>
    let ns := t1 - t0
    let mut unf := 0
    let mut distinct := 0
    let mut top := Name.anonymous
    let mut topc := 0
    if ctx.diag then
      for (n, c) in env.getDiagnostics.unfoldCounter.toList do
        unf := unf + c
        distinct := distinct + 1
        if c > topc then
          top := n
          topc := c
    let dag := if ctx.dag then dagSize (declExprs d) else 0
    let tags := if ctx.tags then tagsOf d else ""
    ctx.out.putStrLn s!"{name}\t{declKind d}\t{ctx.modOf name}\t{ns}\t{unf}\t{distinct}\t{top}\t{topc}\t{dag}\t{tags}"
    let env := if ctx.diag then env.resetDiag.enableDiag false else env
    modify fun s => { s with env := env, total := s.total + ns, count := s.count + 1 }
  | .error ex =>
    throw <| .userError s!"kernel rejected {name}: {← (ex.toMessageData {}).toString}"

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      match ci with
      | .defnInfo info => addDecl name (Declaration.defnDecl info)
      | .thmInfo info =>
        if let some (.thmInfo info') := (← get).env.find? ci.name then
          if info.name == info'.name && info.type == info'.type &&
              info.levelParams == info'.levelParams && info.all == info'.all then
            return
        addDecl name (Declaration.thmDecl info)
      | .axiomInfo info => addDecl name (Declaration.axiomDecl info)
      | .opaqueInfo info => addDecl name (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let all ← info.all.mapM fun n => do pure ((← read).newConstants[n]!)
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do pure ((← read).newConstants[n]!))
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name, type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDecl name (Declaration.inductDecl info.levelParams info.numParams types false)
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        replayConstant `Eq
        addDecl name Declaration.quotDecl
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def checkPostponed : M Unit := do
  for c in (← get).postponedConstructors do
    match (← get).env.find? c, (← read).newConstants[c]? with
    | some (.ctorInfo i), some (.ctorInfo i') =>
      if !(i == i') then throw <| IO.userError s!"Invalid constructor {c}"
    | _, _ => throw <| IO.userError s!"No such constructor {c}"
  for c in (← get).postponedRecursors do
    match (← get).env.find? c, (← read).newConstants[c]? with
    | some (.recInfo i), some (.recInfo i') =>
      if !(i == i') then throw <| IO.userError s!"Invalid recursor {c}"
    | _, _ => throw <| IO.userError s!"No such recursor {c}"

end PF

open PF in
unsafe def main (args : List String) : IO UInt32 := do
  let (flags, args) := args.partition fun s => s.startsWith "--"
  let [modName, outPath] := args | throw <| IO.userError "usage: MODULE OUT.tsv [flags]"
  initSearchPath (← findSysroot)
  let t0 ← IO.monoNanosNow
  Lean.withImportModules #[{module := modName.toName}] {} fun env => do
    let t1 ← IO.monoNanosNow
    let consts := env.constants.map₁
    let modOf (n : Name) : String :=
      match env.getModuleIdxFor? n with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    IO.FS.withFile outPath .write fun h => do
      h.putStrLn "name\tkind\tmodule\tns\tunfolds\tdistinct_unfolded\ttop_unfolded\ttop_count\tdag\ttags"
      let mut remaining : NameSet := ∅
      for (n, ci) in consts.toList do
        if !ci.isUnsafe && !ci.isPartial then
          remaining := remaining.insert n
      let ctx : Context := { newConstants := consts, out := h, modOf,
                             diag := "--diag" ∈ flags, check := !("--nocheck" ∈ flags),
                             dag := "--dag" ∈ flags, tags := "--tags" ∈ flags }
      let env0 := (← mkEmptyEnvironment).toKernelEnv
      let t2 ← IO.monoNanosNow
      let (_, s) ← StateRefT'.run (s := { env := env0, remaining }) do
        ReaderT.run (r := ctx) do
          for n in remaining do replayConstant n
          checkPostponed
      let t3 ← IO.monoNanosNow
      IO.eprintln s!"constants {consts.size} kernel_calls {s.count} kernel_ns {s.total} \
        import_ns {t1 - t0} setup_ns {t2 - t1} replay_ns {t3 - t2}"
  return 0
