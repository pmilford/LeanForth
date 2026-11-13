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
  | .lit (.natVal n) => return toString n
  | .mdata _ e => return s!"<md>{← sx e}"
  | e => return s!"?? {e}"

def answer (t s : Expr) (go : MetaM Bool) : MetaM Unit := do
  let saved ← saveState
  try
    if ← go then
      IO.println s!"true {← sx (← instantiateMVars t)} {← sx (← instantiateMVars s)}"
    else
      IO.println "false"
  catch _ => IO.println "error"
  saved.restore

def eqCase (t s : Expr) : MetaM Unit := answer t s (isDefEq t s)

def metaCase (t s : Expr) : MetaM Unit :=
  answer t s (withConfig (fun c => { c with foApprox := false, ctxApprox := false }) (isDefEq t s))

def deepCase (t s : Expr) : MetaM Unit := answer t s (withNewMCtxDepth (isDefEq t s))

def redCase (t s : Expr) : MetaM Unit := answer t s (withReducible (isDefEq t s))

def instCase (t s : Expr) : MetaM Unit :=
  answer t s (withTransparency .instances (isDefEq t s))

def implCase (t s : Expr) : MetaM Unit :=
  answer t s (withTransparency .implicit (isDefEq t s))

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
  let nat2 := mkForall `y .default nat nat
  let r ← mkFreshExprMVar nat (userName := `r)
  let t ← mkFreshExprMVar nat2 (userName := `t)
  let y ← mkFreshExprMVar (mkForall `y .default nat nat2) (userName := `y)
  let eqab := mkApp3 (mkConst ``Eq [Level.one]) nat a b
  withLocalDeclD `j nat fun j => do
  withLocalDeclD `e eqab fun e => do
  withLocalDeclD `c eqab fun c => do
  withLocalDeclD `u nat2 fun u => do
  withLocalDeclD `v (mkConst ``PUnit [Level.one]) fun v => do
  withLocalDeclD `w (mkConst ``PUnit [Level.one]) fun w => do
  withLocalDeclD `i (mkForall `y .default eqab nat) fun i => do
  let o ← mkFreshExprMVar nat (kind := .syntheticOpaque) (userName := `o)
  let _ := (m, z, k, x, p, g, n, h, q, r, t, y, j, e, c, u, v, w, i, o)
  eqCase k k
  eqCase k x
  eqCase (mkConst `Nat []) (mkConst `Nat [])
  eqCase (mkConst `Nat.zero []) (mkConst `Nat.succ [])
  eqCase (mkSort Level.zero) (mkSort Level.zero)
  eqCase (mkSort Level.zero) (mkSort Level.one)
  eqCase (mkRawNatLit 2) (mkRawNatLit 2)
  eqCase (mkRawNatLit 2) (mkRawNatLit 3)
  eqCase (mkConst `PUnit [Level.one]) (mkConst `PUnit [(mkLevelSucc Level.one)])
  eqCase (mkLambda `y .default (mkConst `Nat []) (mkBVar 0)) (mkLambda `y .default (mkConst `Nat []) (mkBVar 0))
  eqCase (mkLambda `y .default (mkConst `Nat []) (mkBVar 0)) (mkLambda `y .default (mkSort Level.zero) (mkBVar 0))
  eqCase (mkForall `y .default (mkConst `Nat []) (mkConst `Nat [])) (mkForall `y .default (mkConst `Nat []) (mkConst `Nat []))
  eqCase (mkForall `y .default (mkConst `Nat []) (mkConst `Nat [])) (mkForall `y .default (mkConst `Nat []) (mkSort Level.zero))
  eqCase (mkLambda `y .default (mkConst `Nat []) (mkApp (mkConst `Nat.succ []) (mkBVar 0))) (mkLambda `y .default (mkConst `Nat []) (mkApp (mkConst `Nat.succ []) n))
  eqCase (mkLambda `y .default (mkConst `Nat []) n) (mkLambda `y .default (mkConst `Nat []) k)
  eqCase (mkLambda `y .default (mkConst `Nat []) n) (mkLambda `y .default (mkConst `Nat []) (mkBVar 0))
  eqCase (mkLet `y (mkConst `Nat []) k x) x
  eqCase (mkLet `y (mkConst `Nat []) k (mkBVar 0)) k
  eqCase g (mkLambda `y .default (mkConst `Nat []) (mkApp s (mkBVar 0)))
  eqCase (mkLambda `y .default (mkConst `Nat []) (mkApp u (mkBVar 0))) u
  eqCase u (mkLambda `y .default (mkConst `Nat []) (mkApp u (mkBVar 0)))
  eqCase (mkLambda `y .default (mkConst `Nat []) (mkApp (mkConst `Nat.succ []) (mkBVar 0))) (mkConst `Nat.succ [])
  eqCase (mkLambda `y .default (mkConst `Nat []) (mkApp t (mkBVar 0))) u
  eqCase (mkLambda `y .default (mkConst `Nat []) (mkApp t (mkBVar 0))) (mkConst `Nat.succ [])
  eqCase (mkLambda `y .default (mkConst `Nat []) (mkApp t (mkBVar 0))) (mkLambda `y .default (mkConst `Nat []) (mkApp u (mkBVar 0)))
  eqCase e c
  eqCase e (mkApp (mkApp (mkConst `Eq.refl [Level.one]) (mkConst `Nat [])) a)
  eqCase n k
  eqCase k n
  eqCase n (mkApp (mkConst `Nat.succ []) k)
  eqCase n j
  eqCase r k
  eqCase r j
  eqCase n (mkApp (mkConst `Nat.succ []) n)
  eqCase n (mkConst `Nat [])
  eqCase t (mkConst `Nat.succ [])
  eqCase t u
  eqCase n h
  eqCase o k
  eqCase n o
  eqCase (mkApp t j) (mkApp (mkConst `Nat.succ []) j)
  eqCase (mkApp t j) (mkApp (mkConst `Nat.succ []) k)
  eqCase (mkApp t j) (mkApp u j)
  eqCase (mkApp t k) (mkApp (mkConst `Nat.succ []) k)
  metaCase (mkApp t k) (mkApp (mkConst `Nat.succ []) k)
  eqCase (mkApp (mkApp y k) k) (mkApp (mkApp (mkConst `Nat.add []) k) k)
  eqCase (mkApp (mkApp y j) j) (mkApp (mkApp (mkConst `Nat.add []) j) j)
  eqCase (mkApp (mkApp y j) k) (mkApp (mkApp (mkConst `Nat.add []) k) j)
  eqCase (mkApp t k) (mkApp t k)
  eqCase (mkApp t k) (mkApp t x)
  eqCase (mkApp t (mkRawNatLit 2)) (mkApp (mkConst `Nat.succ []) k)
  eqCase (mkApp t k) n
  eqCase n r
  eqCase r n
  eqCase n (mkRawNatLit 2)
  eqCase (mkApp u k) (mkApp u x)
  eqCase (mkApp u k) (mkApp u n)
  eqCase (mkApp u n) (mkApp (mkConst `Nat.succ []) k)
  eqCase (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b) (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) n)
  eqCase (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b) (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) b) a)
  eqCase p (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkProj `Prod 0 p)) (mkProj `Prod 1 p))
  eqCase (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b) p
  eqCase (mkProj `Prod 0 p) a
  eqCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [Level.one]) (mkLambda `y .default (mkConst `Nat []) (mkConst `Nat []))) z) (mkLambda `y .default (mkConst `Nat []) (mkLambda `y .default (mkConst `Nat []) (mkBVar 0)))) (mkConst `Nat.zero [])) z
  eqCase (mkApp (mkLambda `y .default (mkConst `Nat []) (mkApp (mkConst `Nat.succ []) (mkBVar 0))) k) (mkApp (mkConst `Nat.succ []) k)
  eqCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [Level.one]) (mkLambda `y .default (mkConst `Nat []) (mkConst `Nat []))) z) (mkLambda `y .default (mkConst `Nat []) (mkLambda `y .default (mkConst `Nat []) (mkBVar 0)))) n) k
  eqCase (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [Level.one]) m) z) s) (mkConst `Nat.zero [])) z
  eqCase n (mkApp (mkApp (mkApp (mkApp (mkConst `Nat.rec [Level.one]) (mkLambda `y .default (mkConst `Nat []) (mkConst `Nat []))) n) (mkLambda `y .default (mkConst `Nat []) (mkLambda `y .default (mkConst `Nat []) (mkBVar 0)))) (mkConst `Nat.zero []))
  eqCase (mkLambda `y .default (mkConst `Nat []) k) k
  eqCase v w
  eqCase v (mkConst `PUnit.unit [Level.one])
  eqCase (mkConst `PUnit.unit [Level.one]) w
  eqCase (mkApp (mkConst `Nat.succ []) h) (mkApp (mkConst `Nat.succ []) (mkApp (mkConst `Nat.succ []) k))
  eqCase (mkApp (mkConst `Nat.succ []) h) (mkApp (mkConst `Nat.succ []) (mkApp (mkConst `Nat.succ []) r))
  eqCase (mkApp (mkConst `Nat.succ []) (mkApp (mkConst `Nat.succ []) h)) (mkApp (mkConst `Nat.succ []) k)
  eqCase (mkApp (mkConst `Nat.succ []) k) (mkApp (mkConst `Nat.succ []) x)
  eqCase (mkApp (mkConst `Nat.succ []) h) (mkRawNatLit 3)
  eqCase (mkApp (mkConst `Nat.succ []) k) (mkRawNatLit 0)
  eqCase (mkRawNatLit 0) (mkConst `Nat.zero [])
  eqCase (mkRawNatLit 1) (mkConst `Nat.zero [])
  eqCase (mkRawNatLit 3) (mkApp (mkConst `Nat.succ []) (mkApp (mkConst `Nat.succ []) (mkApp (mkConst `Nat.succ []) (mkConst `Nat.zero []))))
  eqCase (mkApp (mkConst `Nat.succ []) h) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 0)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 0)))) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 1)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 1)))))
  eqCase (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 1)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 1)))) (mkApp (mkConst `Nat.succ []) k)
  deepCase n k
  deepCase (mkApp u n) (mkApp u k)
  redCase (mkConst `Nat.add []) (mkConst `Nat.mul [])
  eqCase (mkConst `Nat.add []) (mkConst `Nat.mul [])
  redCase (mkApp (mkApp (mkConst `Nat.add []) k) x) (mkApp (mkApp (mkConst `Nat.add []) k) x)
  redCase (mkApp (mkApp (mkConst `Nat.add []) k) x) (mkApp (mkApp (mkConst `Nat.add []) x) k)
  eqCase (mkApp (mkApp (mkConst `Nat.add []) k) x) (mkApp (mkApp (mkConst `Nat.add []) x) k)
  instCase (mkApp u k) (mkApp u x)
  instCase (mkApp (mkApp (mkConst `Nat.add []) k) x) (mkApp (mkApp (mkConst `Nat.add []) k) n)
  implCase (mkApp u n) (mkApp u k)
  redCase t (mkLambda `y .default (mkApp (mkApp (mkConst `id [(mkLevelSucc Level.one)]) (mkSort Level.one)) (mkConst `Nat [])) (mkBVar 0))
  redCase (mkConst `Nat.add []) k
  eqCase n (mkApp (mkApp (mkConst `Nat.add []) n) k)
  implCase (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) b) (mkApp (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a) n)
  instCase (mkConst `Nat.add []) k
  eqCase (mkApp (mkConst `Nat.succ []) h) (mkRawNatLit 9223372036854775808)
  eqCase (mkApp (mkConst `Nat.succ []) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) h) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 9223372036854775808)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 9223372036854775808))))) (mkRawNatLit 5)
  eqCase (mkApp (mkConst `Nat.succ []) h) (mkRawNatLit 18446744073709551615)
  eqCase (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904)))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904))))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904)))) (mkRawNatLit 13835058055282163712)
  eqCase (mkApp (mkConst `Nat.succ []) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) h) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904))))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904))))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904))))) (mkRawNatLit 13835058055282163713)
  eqCase (mkApp (mkConst `Nat.succ []) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) k) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) (mkConst `Nat [])) (mkApp (mkApp (mkConst `instHAdd [Level.zero]) (mkConst `Nat [])) (mkConst `instAddNat []))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904)))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904))))) (mkApp (mkApp (mkApp (mkConst `OfNat.ofNat [Level.zero]) (mkConst `Nat [])) (mkRawNatLit 4611686018427387904)) (mkApp (mkConst `instOfNatNat []) (mkRawNatLit 4611686018427387904)))))) (mkApp (mkConst `Nat.succ []) h)
  eqCase p (mkApp (mkApp (mkApp (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat [])) (mkConst `Nat [])) a)
  eqCase (mkApp i e) (mkApp i (mkProj `Prod 0 p))
