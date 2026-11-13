import Lean
open Lean Meta

partial def pl (ms : List (LMVarId × String)) (l : Level) : String :=
  let k := l.getOffset
  let base : Option String := match l.getLevelOffset with
    | .zero => none
    | .param n => some n.toString
    | .mvar id => some ((ms.lookup id).getD "?_")
    | .max x y => some s!"(max {pl ms x} {pl ms y})"
    | _ => some "??"
  match base with
  | none => toString k
  | some s => if k == 0 then s else s!"{s}+{k}"

def levelCase (ms : List (LMVarId × String)) (l r : Level) : MetaM Unit := do
  let res ← isLevelDefEqAux l r
  let ans := if (← getPostponed).size > 0 then "postponed" else toString res
  let vs ← ms.mapM fun (id, n) => do
    return s!" {n}={pl ms (← instantiateLevelMVars (mkLevelMVar id))}"
  IO.println (ans ++ String.join vs)

partial def sx : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .sort .zero => return "Prop"
  | .fvar id => return (← id.getUserName).toString
  | .mvar _ => return "?m"
  | .app f a => return s!"(app {← sx f} {← sx a})"
  | .lam _ t b _ => return s!"(lam {← sx t} {← sx b})"
  | .forallE _ t b _ => return s!"(pi {← sx t} {← sx b})"
  | e => return s!"?? {e}"

run_meta do
  withNewMCtxDepth do
    levelCase [] (mkLevelParam `u) (mkLevelParam `u)

run_meta do
  withNewMCtxDepth do
    levelCase [] (Nat.repeat mkLevelSucc 0 Level.zero) (Nat.repeat mkLevelSucc 1 Level.zero)

run_meta do
  withNewMCtxDepth do
    levelCase [] (Nat.repeat mkLevelSucc 1 (mkLevelParam `u)) (mkLevelParam `u)

run_meta do
  withNewMCtxDepth do
    levelCase [] (mkLevelParam `u) (mkLevelParam `v)

run_meta do
  withNewMCtxDepth do
    levelCase [] (Nat.repeat mkLevelSucc 3 (mkLevelParam `u)) (Nat.repeat mkLevelSucc 3 (mkLevelParam `u))

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] ma (Nat.repeat mkLevelSucc 1 Level.zero)

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] (Nat.repeat mkLevelSucc 1 ma) (Nat.repeat mkLevelSucc 2 Level.zero)

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    let mb ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a"), (mb.mvarId!, "b")] (Nat.repeat mkLevelSucc 1 ma) mb

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] ma (Nat.repeat mkLevelSucc 2 (mkLevelParam `u))

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] ma (Nat.repeat mkLevelSucc 1 ma)

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] (Nat.repeat mkLevelSucc 1 (mkLevelParam `u)) (Nat.repeat mkLevelSucc 2 ma)

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] (Nat.repeat mkLevelSucc 0 Level.zero) ma

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] (Nat.repeat mkLevelSucc 1 ma) (mkLevelParam `v)

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] (Nat.repeat mkLevelSucc 0 Level.zero) (Nat.repeat mkLevelSucc 1 ma)

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    let mb ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a"), (mb.mvarId!, "b")] ma mb

run_meta do
  let mr ← mkFreshLevelMVar
  withNewMCtxDepth do
    levelCase [(mr.mvarId!, "r")] mr (Nat.repeat mkLevelSucc 1 Level.zero)

run_meta do
  let mr ← mkFreshLevelMVar
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(mr.mvarId!, "r"), (ma.mvarId!, "a")] mr ma

run_meta do
  let mr ← mkFreshLevelMVar
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(mr.mvarId!, "r"), (ma.mvarId!, "a")] (Nat.repeat mkLevelSucc 1 ma) mr

run_meta do
  let mr ← mkFreshLevelMVar
  let ms ← mkFreshLevelMVar
  withNewMCtxDepth do
    levelCase [(mr.mvarId!, "r"), (ms.mvarId!, "s")] (Nat.repeat mkLevelSucc 1 mr) ms

run_meta do
  withNewMCtxDepth do
    levelCase [] (mkLevelMax (mkLevelParam `u) (mkLevelParam `v)) (mkLevelMax (mkLevelParam `u) (mkLevelParam `v))

run_meta do
  withNewMCtxDepth do
    levelCase [] (mkLevelMax (mkLevelParam `u) (mkLevelParam `v)) (mkLevelMax (mkLevelParam `v) (mkLevelParam `u))

run_meta do
  withNewMCtxDepth do
    let ma ← mkFreshLevelMVar
    levelCase [(ma.mvarId!, "a")] ma (mkLevelMax (mkLevelParam `u) (mkLevelParam `v))

run_meta do
  withLocalDeclD `x (mkSort Level.zero) fun x => do
  withLocalDeclD `y (mkSort Level.zero) fun y => do
    let m ← mkFreshExprMVar (mkSort Level.zero)
    IO.println (← sx (Expr.instantiate1 (mkBVar 0) x))
    IO.println (← sx (Expr.instantiate1 (mkBVar 1) x))
    IO.println (← sx (Expr.instantiate1 (mkLambda `a .default (mkSort Level.zero) (mkBVar 1)) x))
    IO.println (← sx (Expr.instantiate1 (mkLambda `a .default (mkSort Level.zero) (mkBVar 0)) x))
    IO.println (← sx (Expr.instantiate1 (mkApp (mkBVar 0) (mkBVar 0)) x))
    IO.println (← sx (Expr.instantiate1 (mkForall `a .default (mkSort Level.zero) (mkApp (mkBVar 1) (mkBVar 0))) y))
    IO.println (← sx (Expr.instantiate1 (mkLambda `a .default (mkSort Level.zero) (mkLambda `a .default (mkSort Level.zero) (mkApp (mkBVar 2) (mkBVar 1)))) x))
    IO.println (← sx (Expr.instantiate1 (mkApp (mkBVar 0) m) x))
    IO.println (← sx (Expr.instantiate1 (mkLambda `a .default (mkSort Level.zero) (mkBVar 2)) x))
    IO.println (← sx (Expr.instantiate1 (mkBVar 0) (mkApp x m)))
    IO.println (← sx (Expr.headBeta (mkApp (mkLambda `a .default (mkSort Level.zero) (mkBVar 0)) x)))
    IO.println (← sx (Expr.headBeta (mkApp (mkApp (mkLambda `a .default (mkSort Level.zero) (mkLambda `a .default (mkSort Level.zero) (mkApp (mkBVar 0) (mkBVar 1)))) x) y)))
    IO.println (← sx (Expr.headBeta (mkApp (mkApp (mkLambda `a .default (mkSort Level.zero) (mkBVar 0)) x) y)))
    IO.println (← sx (Expr.headBeta (mkApp x y)))
    IO.println (← sx (Expr.headBeta (mkApp (mkLambda `a .default (mkSort Level.zero) (mkLambda `a .default (mkSort Level.zero) (mkApp (mkBVar 0) (mkBVar 1)))) x)))
    IO.println (← sx (Expr.headBeta (mkApp (mkApp (mkLambda `a .default (mkSort Level.zero) (mkBVar 0)) (mkLambda `a .default (mkSort Level.zero) (mkBVar 0))) x)))
    IO.println (← sx (Expr.headBeta (mkSort Level.zero)))
