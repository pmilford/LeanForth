import Lean
open Lean Meta

def pl (l : Level) : String := match l.toNat with
  | some n => toString n
  | none => "?l"

partial def sx : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .const n us => return n.toString ++ ".{" ++ String.intercalate "," (us.map pl) ++ "}"
  | .fvar id => return (← id.getUserName).toString
  | .mvar id => return "?" ++ (← id.getDecl).userName.toString
  | .app f a => return s!"(app {← sx f} {← sx a})"
  | .lam _ t b _ => return s!"(lam {← sx t} {← sx b})"
  | .forallE _ t b _ => return s!"(pi {← sx t} {← sx b})"
  | .letE _ t v b _ => return s!"(let {← sx t} {← sx v} {← sx b})"
  | .proj _ i e => return s!"(proj {i} {← sx e})"
  | .sort l => return "Sort " ++ pl l
  | .mdata _ e => return s!"<md>{← sx e}"
  | e => return s!"?? {e}"

def whnfCase (e : Expr) : MetaM Unit := do IO.println (← sx (← whnfCore e))

def inferCase (e : Expr) : MetaM Unit := do IO.println (← sx (← inferType e))

def stuckCase (e : Expr) : MetaM Unit := do
  match ← getStuckMVar? e with
  | some id => IO.println (← sx (mkMVar id))
  | none => IO.println "none"

def nat : Expr := mkConst ``Nat

run_meta do
  withLocalDeclD `m nat fun m => do
  withLocalDeclD `z nat fun z => do
  withLocalDeclD `s nat fun s => do
  withLocalDeclD `k nat fun k => do
  withLocalDeclD `x nat fun x => do
  withLocalDeclD `a nat fun a => do
  withLocalDeclD `b nat fun b => do
  withLocalDeclD `p (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) nat nat) fun p => do
  let sfun := mkLambda `y .default nat (mkApp s (mkBVar 0))
  withLetDecl `g nat sfun fun g => do
    let n ← mkFreshExprMVar nat (userName := `n)
    let h ← mkFreshExprMVar nat (userName := `h)
    let f ← mkFreshExprMVar nat (userName := `f)
    let q ← mkFreshExprMVar nat (userName := `q)
    f.mvarId!.assign sfun
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkApp (mkConst `Nat.succ []) k))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkConst `Nat.zero []))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) k)
    whnfCase (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s)
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkConst `Nat.zero [])) x)
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) n)
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkApp (mkConst `Nat.succ []) n))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkApp (mkConst `Nat.succ []) (mkApp (mkConst `Nat.succ []) k)))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.rec [(mkLevelSucc .zero), Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) m) s) (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.rec [(mkLevelSucc .zero), Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) m) s) p)
    whnfCase (mkApp (mkLambda `y .default (mkConst `Nat []) (mkBVar 0)) k)
    whnfCase (mkApp (mkApp (mkLambda `y .default (mkConst `Nat []) (mkLambda `y .default (mkConst `Nat []) (mkBVar 1))) a) b)
    whnfCase (mkLet `y (mkConst `Nat []) k (mkApp s (mkBVar 0)))
    whnfCase (mkApp (mkLet `y (mkConst `Nat []) s (mkBVar 0)) k)
    whnfCase (mkApp f k)
    whnfCase (mkApp h k)
    whnfCase (mkApp g k)
    whnfCase g
    whnfCase f
    whnfCase (mkApp (mkApp (mkConst `Nat.add []) k) k)
    whnfCase (mkApp (mkConst `Nat.succ []) k)
    whnfCase (mkApp (mkApp (mkConst `Classical.choice [(mkLevelSucc .zero)]) (mkConst `Nat [])) x)
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Eq.rec [(mkLevelSucc .zero), (mkLevelSucc .zero)]) (mkConst `Nat [])) a) m) x) a) (mkApp (mkApp (mkConst `Eq.refl [(mkLevelSucc .zero)]) (mkConst `Nat [])) a))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Quot.lift [(mkLevelSucc .zero), (mkLevelSucc .zero)]) (mkConst `Nat [])) x) (mkConst `Nat [])) s) b) (mkApp (mkApp (mkApp (mkConst `Quot.mk [(mkLevelSucc .zero)]) (mkConst `Nat [])) x) a))
    whnfCase (mkProj `Prod 0 (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b))
    whnfCase (mkProj `Prod 1 (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b))
    whnfCase (mkProj `Prod 0 p)
    whnfCase (mkProj `Prod 2 (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b))
    whnfCase (mkApp (mkProj `Prod 0 (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkLambda `y .default (mkConst `Nat []) (mkApp s (mkBVar 0)))) b)) k)
    whnfCase (mkProj `Prod 0 (mkApp (mkConst `Nat.succ []) k))
    whnfCase (mkProj `Prod 0 (mkApp (mkApp (mkConst `Nat.add []) k) k))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkLet `y (mkConst `Nat []) k (mkApp (mkConst `Nat.succ []) (mkBVar 0))))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkApp (mkLambda `y .default (mkConst `Nat []) (mkBVar 0)) k))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) (mkApp (mkConst `Nat.succ []) z)) s) (mkConst `Nat.zero [])))
    whnfCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkApp (mkApp (mkConst `Nat.add []) k) k))
    inferCase (mkConst `Nat.add [])
    inferCase (mkApp (mkConst `Nat.add []) k)
    inferCase (mkApp (mkApp (mkConst `Nat.add []) k) k)
    inferCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) k)
    inferCase k
    inferCase n
    inferCase g
    inferCase (mkConst `Nat [])
    inferCase (mkSort Level.zero)
    inferCase (mkApp (mkConst `Nat.succ []) k)
    inferCase (mkApp (mkApp (mkConst `Eq.refl [(mkLevelSucc .zero)]) (mkConst `Nat [])) a)
    inferCase (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero])
    inferCase (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) k)
    inferCase (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b)
    inferCase (mkConst `Quot.lift [(mkLevelSucc .zero), (mkLevelSucc .zero)])
    inferCase (mkLambda `y .default (mkConst `Nat []) (mkBVar 0))
    inferCase (mkLambda `y .default (mkConst `Nat []) (mkLambda `y .default (mkConst `Nat []) (mkBVar 1)))
    inferCase (mkLambda `y .default (mkConst `Nat []) (mkApp (mkApp (mkConst `Eq.refl [(mkLevelSucc .zero)]) (mkConst `Nat [])) (mkBVar 0)))
    inferCase (mkLambda `y .default (mkConst `Nat []) n)
    inferCase (mkLambda `y .default (mkConst `Nat []) (mkLambda `y .default (mkApp (mkApp (mkApp (mkConst `Eq [(mkLevelSucc .zero)]) (mkConst `Nat [])) (mkBVar 0)) (mkBVar 0)) (mkBVar 0)))
    inferCase (mkForall `y .default (mkConst `Nat []) (mkConst `Nat []))
    inferCase (mkForall `y .default (mkConst `Nat []) (mkApp (mkApp (mkApp (mkConst `Eq [(mkLevelSucc .zero)]) (mkConst `Nat [])) (mkBVar 0)) (mkBVar 0)))
    inferCase (mkForall `y .default (mkSort Level.zero) (mkSort Level.zero))
    inferCase (mkForall `y .default (mkSort (mkLevelSucc .zero)) (mkConst `Nat []))
    inferCase (mkForall `y .default (mkForall `y .default (mkConst `Nat []) (mkConst `Nat [])) (mkConst `Nat []))
    inferCase (mkProj `Prod 0 (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b))
    inferCase (mkLet `y (mkConst `Nat []) k (mkBVar 0))
    inferCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) (mkLambda `y .default (mkConst `Nat []) (mkConst `Nat []))) z) s) k)
    inferCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) (mkLambda `y .default (mkConst `Nat []) (mkApp (mkApp (mkApp (mkConst `Eq [(mkLevelSucc .zero)]) (mkConst `Nat [])) (mkBVar 0)) (mkBVar 0)))) z) s) k)
    inferCase (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) (mkLambda `y .default (mkConst `Nat []) (mkConst `Nat []))) z) s)
    stuckCase n
    stuckCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) n)
    stuckCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) k)
    stuckCase (mkApp h k)
    stuckCase (mkApp s k)
    stuckCase (mkApp (mkApp (mkConst `Nat.add []) n) k)
    stuckCase (mkApp (mkApp (mkConst `Nat.add []) k) k)
    stuckCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkApp (mkConst `Nat.succ []) n))
    stuckCase (mkProj `Prod 0 q)
    stuckCase (mkApp (mkProj `Prod 0 q) k)
    stuckCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [(mkLevelSucc .zero)]) m) z) s) (mkLambda `y .default (mkConst `Nat []) (mkBVar 0)))
    stuckCase (mkApp f k)
