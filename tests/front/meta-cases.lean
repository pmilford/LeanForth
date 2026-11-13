import Lean
open Lean Meta

partial def pl (ms : List (LMVarId × String)) (l : Level) : String :=
  let k := l.getOffset
  let base : Option String := match l.getLevelOffset with
    | .zero => none
    | .param n => some n.toString
    | .mvar id => some ((ms.lookup id).getD "?_")
    | .max x y => some s!"(max {pl ms x} {pl ms y})"
    | .imax x y => some s!"(imax {pl ms x} {pl ms y})"
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
  | .sort l => return s!"Sort {pl [] l}"
  | .const _ us => return "C.{" ++ String.intercalate "," (us.map (pl [])) ++ "}"
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
    IO.println (← sx (Expr.abstract (mkApp x y) #[x]))
    IO.println (← sx (Expr.abstract (mkApp x y) #[x, y]))
    IO.println (← sx (Expr.abstract (mkApp x y) #[y, x]))
    IO.println (← sx (Expr.abstract (mkLambda `a .default (mkSort Level.zero) (mkApp x (mkBVar 0))) #[x]))
    IO.println (← sx (Expr.abstract (mkForall `a .default (mkSort Level.zero) (mkApp y (mkLambda `a .default (mkSort Level.zero) x))) #[x, y]))
    IO.println (← sx (Expr.abstract (mkApp m x) #[m]))
    IO.println (← sx (Expr.abstract (mkApp x y) #[x, x]))
    IO.println (← sx (Expr.abstract (mkApp x y) #[]))
    IO.println (← sx (Expr.abstract (mkLambda `a .default (mkSort Level.zero) (mkBVar 3)) #[x]))

run_meta do
  withLocalDeclD `x (mkSort Level.zero) fun x => do
  withLocalDeclD `y (mkSort Level.zero) fun y => do
    IO.println (pl [] (mkLevelMax' (mkLevelParam `u) (mkLevelParam `u)))
    IO.println (pl [] (mkLevelMax' (Nat.repeat mkLevelSucc 0 Level.zero) (mkLevelParam `u)))
    IO.println (pl [] (mkLevelMax' (mkLevelParam `u) (Nat.repeat mkLevelSucc 0 Level.zero)))
    IO.println (pl [] (mkLevelMax' (Nat.repeat mkLevelSucc 1 Level.zero) (Nat.repeat mkLevelSucc 2 Level.zero)))
    IO.println (pl [] (mkLevelMax' (Nat.repeat mkLevelSucc 2 (mkLevelParam `u)) (Nat.repeat mkLevelSucc 1 Level.zero)))
    IO.println (pl [] (mkLevelMax' (mkLevelMax (mkLevelParam `u) (mkLevelParam `v)) (mkLevelParam `u)))
    IO.println (pl [] (mkLevelMax' (mkLevelParam `v) (mkLevelMax (mkLevelParam `u) (mkLevelParam `v))))
    IO.println (pl [] (mkLevelMax' (Nat.repeat mkLevelSucc 1 (mkLevelParam `u)) (mkLevelParam `u)))
    IO.println (pl [] (mkLevelMax' (mkLevelParam `u) (Nat.repeat mkLevelSucc 1 (mkLevelParam `u))))
    IO.println (pl [] (mkLevelMax' (mkLevelParam `u) (mkLevelParam `v)))
    IO.println (pl [] (mkLevelMax' (Nat.repeat mkLevelSucc 1 (mkLevelParam `u)) (Nat.repeat mkLevelSucc 2 (mkLevelParam `v))))
    IO.println (pl [] (mkLevelIMax' (mkLevelParam `u) (Nat.repeat mkLevelSucc 1 Level.zero)))
    IO.println (pl [] (mkLevelIMax' (mkLevelParam `u) (Nat.repeat mkLevelSucc 0 Level.zero)))
    IO.println (pl [] (mkLevelIMax' (Nat.repeat mkLevelSucc 0 Level.zero) (mkLevelParam `u)))
    IO.println (pl [] (mkLevelIMax' (mkLevelParam `u) (mkLevelParam `u)))
    IO.println (pl [] (mkLevelIMax' (mkLevelParam `u) (mkLevelParam `v)))
    IO.println (pl [] (mkLevelIMax' (mkLevelParam `u) (mkLevelMax (mkLevelParam `v) (Nat.repeat mkLevelSucc 1 Level.zero))))
    IO.println (pl [] (mkLevelIMax' (mkLevelParam `u) (mkLevelIMax (mkLevelParam `v) (Nat.repeat mkLevelSucc 1 Level.zero))))
    IO.println (pl [] (mkLevelIMax' (Nat.repeat mkLevelSucc 1 Level.zero) (mkLevelIMax (mkLevelParam `u) (mkLevelParam `v))))
    IO.println (pl [] (Level.instantiateParams (Nat.repeat mkLevelSucc 1 (mkLevelParam `u)) [`u] [(Nat.repeat mkLevelSucc 2 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (mkLevelParam `v) [`u] [(Nat.repeat mkLevelSucc 1 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (mkLevelParam `u) [`u, `u] [(Nat.repeat mkLevelSucc 1 Level.zero), (Nat.repeat mkLevelSucc 2 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (mkLevelMax (Nat.repeat mkLevelSucc 1 Level.zero) (Nat.repeat mkLevelSucc 0 Level.zero)) [`u] [(Nat.repeat mkLevelSucc 1 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (Nat.repeat mkLevelSucc 2 (mkLevelParam `u)) [`u, `v] [(Nat.repeat mkLevelSucc 1 (mkLevelParam `v)), (Nat.repeat mkLevelSucc 0 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (mkLevelMax (mkLevelParam `u) (mkLevelParam `v)) [`u] [(Nat.repeat mkLevelSucc 1 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (mkLevelMax (mkLevelParam `u) (mkLevelParam `v)) [`u, `v] [(Nat.repeat mkLevelSucc 1 Level.zero), (Nat.repeat mkLevelSucc 2 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (mkLevelIMax (mkLevelParam `u) (mkLevelParam `v)) [`v] [(Nat.repeat mkLevelSucc 1 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (mkLevelIMax (mkLevelParam `u) (mkLevelParam `v)) [`u, `v] [(mkLevelParam `v), (Nat.repeat mkLevelSucc 0 Level.zero)]))
    IO.println (pl [] (Level.instantiateParams (mkLevelMax (mkLevelMax (mkLevelParam `u) (mkLevelParam `v)) (mkLevelParam `u)) [`v] [(mkLevelParam `u)]))
    IO.println (← sx (Expr.instantiateLevelParams (mkSort (mkLevelParam `u)) [`u] [(Nat.repeat mkLevelSucc 1 Level.zero)]))
    IO.println (← sx (Expr.instantiateLevelParams (mkConst `C [(mkLevelParam `u), (mkLevelParam `v)]) [`u, `v] [(Nat.repeat mkLevelSucc 1 Level.zero), (Nat.repeat mkLevelSucc 0 Level.zero)]))
    IO.println (← sx (Expr.instantiateLevelParams (mkLambda `a .default (mkSort (mkLevelParam `u)) (mkSort (Nat.repeat mkLevelSucc 1 (mkLevelParam `u)))) [`u] [(mkLevelParam `v)]))
    IO.println (← sx (Expr.instantiateLevelParams (mkForall `a .default (mkSort (mkLevelParam `v)) (mkApp (mkConst `C [(mkLevelParam `u), (mkLevelParam `v)]) (mkBVar 0))) [`v] [(Nat.repeat mkLevelSucc 1 (mkLevelParam `u))]))
    IO.println (← sx (Expr.instantiateLevelParams (mkApp x y) [`u] [(Nat.repeat mkLevelSucc 1 Level.zero)]))
    IO.println (← sx (Expr.instantiateLevelParams (mkConst `C [(Nat.repeat mkLevelSucc 0 Level.zero), (Nat.repeat mkLevelSucc 1 Level.zero)]) [`u] [(mkLevelParam `v)]))
    IO.println (← sx (Expr.instantiateLevelParams (mkSort (mkLevelMax (mkLevelParam `u) (mkLevelParam `v))) [`u] [(Nat.repeat mkLevelSucc 1 Level.zero)]))
    IO.println (← sx (Expr.instantiateLevelParams (mkSort (mkLevelIMax (mkLevelParam `u) (mkLevelParam `v))) [`v] [(Nat.repeat mkLevelSucc 0 Level.zero)]))
    IO.println (← sx (Expr.instantiateLevelParams (mkSort (mkLevelMax (mkLevelParam `u) (mkLevelParam `u))) [] []))
