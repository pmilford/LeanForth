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

def ibetaCase (e : Expr) (args : Array Expr) : MetaM Unit :=
  do IO.println (← sx (e.instantiateBetaRevRange 0 args.size args))

def stuckCase (e : Expr) : MetaM Unit := do
  match ← getStuckMVar? e with
  | some id => IO.println (← sx (mkMVar id))
  | none => IO.println "none"

def nat : Expr := mkConst ``Nat

def unfoldCase (m : TransparencyMode) (e : Expr) : MetaM Unit := do
  try
    match ← withTransparency m (unfoldDefinition? e) with
    | some e' => IO.println s!"1 {← sx e'}"
    | none => IO.println "0"
  catch _ => IO.println "error"

def mwhnfCase (m : TransparencyMode) (e : Expr) : MetaM Unit := do
  try IO.println (← sx (← withTransparency m (whnf e)))
  catch _ => IO.println "error"

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
    let _ := (m, z, s, k, x, a, b, p, g, n, h, f, q)
    unfoldCase .default (mkApp (mkConst `outParam [(mkLevelSucc .zero)]) (mkConst `Nat []))
    unfoldCase .reducible (mkApp (mkConst `outParam [(mkLevelSucc .zero)]) (mkConst `Nat []))
    unfoldCase .none (mkApp (mkConst `outParam [(mkLevelSucc .zero)]) (mkConst `Nat []))
    unfoldCase .default (mkConst `outParam [(mkLevelSucc .zero)])
    unfoldCase .all (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) x)
    unfoldCase .default (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) x)
    unfoldCase .reducible (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) x)
    unfoldCase .instances (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) x)
    unfoldCase .implicit (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) x)
    unfoldCase .instances (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat [])))
    unfoldCase .instances (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat []))
    unfoldCase .instances (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) x)
    unfoldCase .instances (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) k) k) x)
    unfoldCase .default (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) k) k) x)
    unfoldCase .reducible (mkApp (mkApp (mkApp (mkConst `Prod.fst [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b))
    unfoldCase .default (mkApp (mkConst `outParam [(mkLevelSucc .zero), (mkLevelSucc .zero)]) (mkConst `Nat []))
    unfoldCase .default (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))
    unfoldCase .reducible (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))
    unfoldCase .instances (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))
    unfoldCase .default (mkApp (mkApp (mkApp (mkApp (mkConst `Add.add [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat [])) k) x)
    unfoldCase .reducible (mkApp (mkApp (mkApp (mkApp (mkConst `Add.add [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat [])) k) x)
    unfoldCase .instances (mkApp (mkApp (mkApp (mkApp (mkConst `Add.add [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat [])) k) x)
    unfoldCase .default (mkConst `instAddNat [])
    unfoldCase .default (mkApp (mkApp (mkConst `Nat.add []) k) x)
    unfoldCase .default (mkConst `Nat.add [])
    unfoldCase .default (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) k)
    unfoldCase .all (mkConst `Nat.zero_add [])
    unfoldCase .default (mkConst `Nat.div [])
    unfoldCase .default (mkApp (mkApp (mkConst `id [(mkLevelSucc .zero)]) (mkConst `Nat [])) k)
    unfoldCase .reducible (mkApp (mkApp (mkConst `id [(mkLevelSucc .zero)]) (mkConst `Nat [])) k)
    unfoldCase .default k
    unfoldCase .default (mkLambda `y .default (mkConst `Nat []) (mkBVar 0))
    unfoldCase .default (mkConst `motive [])
    unfoldCase .default (mkApp (mkConst `motive []) k)
    mwhnfCase .default (mkApp (mkConst `outParam [(mkLevelSucc .zero)]) (mkConst `Nat []))
    mwhnfCase .default (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))
    mwhnfCase .reducible (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))
    mwhnfCase .instances (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))
    mwhnfCase .default (mkProj `Prod 0 (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat [])))
    mwhnfCase .default (mkApp (mkApp (mkConst `id [(mkLevelSucc .zero)]) (mkConst `Nat [])) k)
    mwhnfCase .default (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) x)
    mwhnfCase .instances (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) x)
    mwhnfCase .all (mkConst `Nat.zero_add [])
    mwhnfCase .default (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) m) k) (mkConst `Nat.zero [])) z) s)
    mwhnfCase .default (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) m) k) (mkApp (mkConst `Nat.succ []) x)) z) s)
    mwhnfCase .default (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) m) k) x) z) s)
    mwhnfCase .default (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) m) k) (mkConst `Nat.zero [])) z) s) a)
    mwhnfCase .all (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) m) k) (mkRawNatLit 2)) z) s)
    mwhnfCase .default (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) m) k) (mkConst `Nat.zero [])) z)
    mwhnfCase .default (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.casesOn [(mkLevelSucc .zero)]) m) (mkConst `Nat.zero [])) z) s)
    mwhnfCase .default (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.casesOn [(mkLevelSucc .zero)]) m) (mkApp (mkConst `Nat.succ []) k)) z) s)
    mwhnfCase .reducible (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) m) k) (mkConst `Nat.zero [])) z) s)
    mwhnfCase .instances (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.add.match_1 [(mkLevelSucc .zero)]) m) k) (mkConst `Nat.zero [])) z) s)
