-- One shared source node read at different binder depths and scopes (review
-- rvS36 probes P1 and P2; ADR 0014 Amendments 3 and 4). LeanForth reads a
-- node once, whatever the depth: its inferred-type cache key (the node
-- closed with its scope), the replace memo's (node, offset, stamp) key, the
-- audit memo and the data-word shortcuts must keep the places apart.
-- * P1, 12 rows, 6 good and 6 bad twins (a stale key would accept the bad
--   ones): `@id #3 #2` at depth 4 and 6; `@id #1 #0` under two lets; `h.1`
--   as `Expr.proj` at depth 3 and 6; an argument closed twice then deeper; a
--   chain body naming only an outer binder; proof irrelevance through the
--   typer.
-- * P2, 7 rows: loose bound variables in a value or a type, and a shared node
--   in scope in one place and out of scope in another. Lean rejects m1, m2,
--   m3, m5 ("loose bound variables") and m6 (typeExpected), and accepts m4
--   and m4ok.
-- * P3 (agent PF), 6 rows: three arena perf ladders at n = 48 and bad twins.
-- * P4 (agent R5), 2 rows: proof irrelevance typing 48-argument spines aside;
--   Lean accepts spinegood and rejects spinebad (appTypeMismatch).
-- * P5 (agent CK, plan task 4.2.7d), 10 rows: Lean's infer-only typing
--   meeting an ill-typed term that beta reduction made; Lean rejects appbad,
--   lambad (funExpected), pibad (typeExpected) and projbad (invalidProj) and
--   accepts their good twins, lamgood and letgood.
-- Each row is a theorem or definition checked by pinned Lean's kernel
-- (`addDeclCore`, no axioms); the file prints a `row<TAB>id<TAB>verdict` line
-- per row and then each row's export. tests/cli/shared_depths.py, run by
-- tests/cli/export-check.sh, runs Lean on it and compares LeanForth's verdict
-- on every export with Lean's, with the audit memo on and off.
import Lean
import LeanExport.Basic
open Lean

namespace SharedDepths


def kverdict : Except Kernel.Exception Kernel.Environment → IO String
  | .ok _ => pure "accepted"
  | .error e => do
    let s ← (e.toMessageData {}).toString
    pure ("rejected: " ++ (s.replace "\n" " ").take 160)

/-- Check `ds` in order on `base`; the verdict of the last, or of the first failure. -/
def checkAll (base : Kernel.Environment) : List Declaration → IO (String × Kernel.Environment)
  | [] => pure ("accepted", base)
  | d :: ds => match base.addDeclCore 0 0 d none with
    | .ok e => if ds.isEmpty then pure ("accepted", e) else checkAll e ds
    | .error err => do
      let v ← kverdict (.error err)
      -- add the rest unchecked, for the export
      let e := (d :: ds).foldl (fun e d => match e.addDeclWithoutChecking d with
        | .ok e' => e' | .error _ => e) base
      pure (v, e)

def writeCase (env : Kernel.Environment) (id : String) (names : List Name) : IO Unit := do
  IO.println s!"ndjson-begin\t{id}"
  let lenv := Environment.ofKernelEnv env
  LeanExport.M.run lenv do
    LeanExport.initState lenv
    LeanExport.dumpMetadata
    for n in names do LeanExport.dumpConstant n
  IO.println "ndjson-end"


namespace P1

-- rvS36 P1: one source node read at two binder depths (hash-consed: one
-- node), where its type differs by depth; the inferred-type cache key (the
-- node closed with its scope, ADR 0014 Amendment 3) and the replace memo's
-- (node, offset, stamp) key must keep the two apart. Each good case has a
-- bad twin a stale key would accept.

def prop : Expr := .sort Level.zero
def thm (n : Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := ty, value := val, all := [n] }
def lam (n : Name) (t b : Expr) : Expr := .lam n t b .default
def pi (n : Name) (t b : Expr) : Expr := .forallE n t b .default
def andE (a b : Expr) : Expr := mkApp2 (mkConst ``And) a b
def andI (a b ha hb : Expr) : Expr := mkApp4 (mkConst ``And.intro) a b ha hb
def idE (t v : Expr) : Expr := mkApp2 (mkConst ``id [Level.one]) t v
def idP (t v : Expr) : Expr := mkApp2 (mkConst ``id [Level.zero]) t v
def letE (n : Name) (t v b : Expr) : Expr := .letE n t v b false
def b (i : Nat) : Expr := .bvar i

-- binders A : Prop, a : A, B : Prop, b : B
def abab (body : Expr) (mk : Name → Expr → Expr → Expr) : Expr :=
  mk `A prop (mk `a (b 0) (mk `B prop (mk `b (b 0) body)))

-- c1: N = @id #3 #2 is id A a at depth 4 and id B b at depth 6.
def n1 : Expr := idP (b 3) (b 2)
def c1v : Expr := abab (andI (b 3) (b 1) n1
  (mkApp2 (lam `y prop (lam `z (b 0) n1)) (mkConst ``True) (mkConst ``True.intro))) lam
def c1good : Expr := abab (andE (b 3) (b 1)) pi
def c1bad : Expr := abab (andE (b 3) (b 3)) pi

-- c2: N = @id #1 #0 is id B b at depth 4 and id X w under two lets.
def n2 : Expr := idP (b 1) (b 0)
def c2v : Expr := abab (andI (b 1) (b 3) n2 (letE `X prop (b 3) (letE `w (b 0) (b 3) n2))) lam
def c2good : Expr := abab (andE (b 1) (b 3)) pi
def c2bad : Expr := abab (andE (b 1) (b 1)) pi

-- c3: P = h.1 (Expr.proj) is A at depth 3 and C at depth 6.
def pr : Expr := .proj ``And 0 (b 0)
def abh (body : Expr) (mk : Name → Expr → Expr → Expr) : Expr :=
  mk `A prop (mk `B prop (mk `h (andE (b 1) (b 0)) body))
def inner (res : Expr) : Expr := pi `C prop (pi `D prop (pi `h2 (andE (b 1) (b 0)) res))
def c3v : Expr := abh (andI (b 2) (inner (b 2)) pr
  (lam `C prop (lam `D prop (lam `h2 (andE (b 1) (b 0)) pr)))) lam
def c3good : Expr := abh (andE (b 2) (inner (b 2))) pi
def c3bad : Expr := abh (andE (b 2) (inner (b 5))) pi

-- c4: an argument closed twice under one scope, then under a deeper one:
-- f X X with X = @id #3 #2, then the same X two binders deeper.
def c4v : Expr := abab (andI (andE (b 3) (b 3)) (b 1) (andI (b 3) (b 3) n1 n1)
  (mkApp2 (lam `y prop (lam `z (b 0) n1)) (mkConst ``True) (mkConst ``True.intro))) lam
def c4good : Expr := abab (andE (andE (b 3) (b 3)) (b 1)) pi
def c4bad : Expr := abab (andE (andE (b 3) (b 3)) (b 3)) pi

-- c5: a lambda chain whose inner body's type names only an outer binder
-- (abstract's data-word skip), its type compared with the declared one.
def c5v : Expr := abab (lam `y prop (lam `z (b 0) (b 4))) lam
def c5good : Expr := abab (pi `y prop (pi `z (b 0) (b 5))) pi
def c5bad : Expr := abab (pi `y prop (pi `z (b 0) (b 3))) pi

-- c6: proof irrelevance (the typer, infer-only cache) on h.1 read at two
-- depths: P (h.1) -> P (h2.1) needs both to prove the same Prop.
def c6ty (res : Expr) : Expr :=
  pi `A prop (pi `h (andE (b 0) (b 0)) (pi `C prop (pi `h2 (andE (b 0) (b 0))
    (pi `P (pi `x (b 3) prop) (pi `hp (mkApp (b 0) (.proj ``And 0 (b 3))) res)))))
def c6v : Expr :=
  lam `A prop (lam `h (andE (b 0) (b 0)) (lam `C prop (lam `h2 (andE (b 0) (b 0))
    (lam `P (pi `x (b 3) prop) (lam `hp (mkApp (b 0) (.proj ``And 0 (b 3))) (b 0))))))
def c6good : Expr := c6ty (mkApp (b 1) (.proj ``And 1 (b 4)))
-- bad: h2.1 : C, not A, so P (h2.1) is ill-typed (P : A -> Prop)
def c6bad : Expr := c6ty (mkApp (b 1) (.proj ``And 0 (b 2)))

run_cmd do
  let base := (← getEnv).toKernelEnv
  let cases : List (String × Expr × Expr) := [
    ("c1good", c1good, c1v), ("c1bad", c1bad, c1v),
    ("c2good", c2good, c2v), ("c2bad", c2bad, c2v),
    ("c3good", c3good, c3v), ("c3bad", c3bad, c3v),
    ("c4good", c4good, c4v), ("c4bad", c4bad, c4v),
    ("c5good", c5good, c5v), ("c5bad", c5bad, c5v),
    ("c6good", c6good, c6v), ("c6bad", c6bad, c6v)]
  let mut rows : Array String := #[]
  let mut outs : Array (String × Kernel.Environment × List Name) := #[]
  for (id, ty, v) in cases do
    let n := Name.mkSimple s!"RVS36_{id}"
    let d := thm n ty v
    let (verdict, e) ← liftM (checkAll base [d])
    rows := rows.push s!"row\t{id}\t{verdict}"
    outs := outs.push (id, e, [n])
  for r in rows do IO.println r
  for (id, e, ns) in outs do writeCase e id ns
end P1

namespace P2

-- rvS36 P2: malformed values (loose bound variables), some in a node
-- shared between an in-scope and an out-of-scope place, for V1's data-word
-- shortcut (ADR 0014 Amendment 4) and the audit memo.

def prop : Expr := .sort Level.zero
def thm (n : Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := ty, value := val, all := [n] }
def dfn (n : Name) (ty val : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .opaque,
              safety := .safe, all := [n] }
def lam (n : Name) (t b : Expr) : Expr := .lam n t b .default
def pi (n : Name) (t b : Expr) : Expr := .forallE n t b .default
def b (i : Nat) : Expr := .bvar i
def idP (t v : Expr) : Expr := mkApp2 (mkConst ``id [Level.zero]) t v

-- m1: fun A a => #2 (out of scope)
def m1 := thm `RVS36_m1 (pi `A prop (pi `a (b 0) (b 1))) (lam `A prop (lam `a (b 0) (b 2)))
-- m2: fun (x : #0) => #0, one shared #0, out of scope as the domain only
def m2 := dfn `RVS36_m2 (pi `x prop prop) (lam `x (b 0) (b 0))
-- m3: the type out of scope: ∀ (x : Prop), #1
def m3 := thm `RVS36_m3 (pi `x prop (b 1)) (lam `x prop (b 0))
-- m4: a shared open node N = @id #1 #0, in scope in the value's body and
-- out of scope in an argument at depth 1
def m4 := thm `RVS36_m4 (pi `A prop (pi `a (b 0) (b 1)))
  (lam `A prop (lam `a (b 0) (mkApp2 (lam `u prop (lam `v (b 0) (idP (b 3) (b 2)))) (b 1) (idP (b 1) (b 0)))))
def m4ok := thm `RVS36_m4ok (pi `A prop (pi `a (b 0) (b 1)))
  (lam `A prop (lam `a (b 0) (mkApp2 (lam `u prop (lam `v (b 0) (idP (b 3) (b 2)))) (b 1) (b 0))))

-- m5: N = @id #1 #0 in scope under fun a (depth 2), out of scope as the
-- argument at depth 1: (fun a => N) N
def m5 := thm `RVS36_m5 (pi `A prop (pi `a (b 0) (b 1)))
  (lam `A prop (mkApp (lam `a (b 0) (idP (b 1) (b 0))) (idP (b 1) (b 0))))
-- m6: the same in the declared type: ∀ (A : Prop), (∀ (a : A), id #1 #0 = …) -> N
def m6 := dfn `RVS36_m6 (pi `A prop (pi `h (pi `a (b 0) (idP (b 1) (b 0))) (idP (b 1) (b 0))))
  (lam `A prop (lam `h (pi `a (b 0) (idP (b 1) (b 0))) (b 0)))

run_cmd do
  let base := (← getEnv).toKernelEnv
  let cases : List (String × Declaration) := [("m1", m1), ("m2", m2), ("m3", m3), ("m4", m4), ("m4ok", m4ok), ("m5", m5), ("m6", m6)]
  let mut rows : Array String := #[]
  let mut outs : Array (String × Kernel.Environment × List Name) := #[]
  for (id, d) in cases do
    let (verdict, e) ← liftM (checkAll base [d])
    rows := rows.push s!"row\t{id}\t{verdict}"
    outs := outs.push (id, e, d.getNames)
  for r in rows do IO.println r
  for (id, e, ns) in outs do writeCase e id ns
end P2

namespace P3

-- Agent PF (plan task 6.5.5): small copies of three Lean Kernel Arena perf
-- tests, whose source nodes are read under every depth of a binder ladder.
-- * let: n lets, each body `x + (next let)`, over a sum naming every
--   binding (let-ladder); the bad twin's innermost value is `true`.
-- * beta: `(fun x => … ((fun x => x₁ + (… + (xₙ + 0))) 0) …) 0 = 0`
--   (beta-ladder); the bad twin claims `= 1`.
-- * app: n levels of `wrap2 L L`, one shared lambda L whose body is the next
--   level, over a sum naming every binder (app-lam); the bad twin adds
--   `True` to the sum.
-- `Nat.add x a` and `wrap2 L` have the body of a non-dependent Pi as their
-- type, which Lean's instantiate gives back without reading the argument
-- (instantiate.cpp 22): LeanForth no longer closes such an argument
-- (mixed-infer.fs, lf-minfer-put-closed). tests/cli/shared_depths.py also
-- bounds the fuel of the good rows.

def nat : Expr := mkConst ``Nat
def lit (k : Nat) : Expr := .lit (.natVal k)
def add (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.add) a b
def dfn (n : Name) (ty val : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .regular 0,
              safety := .safe, all := [n] }
def thm (n : Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := ty, value := val, all := [n] }

/-- x₁ + (x₂ + (… + (xₙ + last))) under n binders, x₁ the outermost. -/
def sumAll (n : Nat) (last : Expr) : Expr := Id.run do
  let mut b := last
  for i in [:n] do b := add (.bvar i) b
  return b

def letLadder (n : Nat) (bad : Bool) : Expr := Id.run do
  let mut body := sumAll n (lit 0)
  for k in [:n] do
    let v := if bad && k == 0 then mkConst ``Bool.true else lit 0
    body := .letE `x nat v (add (.bvar 0) body) false
  return body

def betaLadder (n : Nat) : Expr := Id.run do
  let mut e := sumAll n (lit 0)
  for _ in [:n] do e := .app (.lam `x nat e .default) (lit 0)
  return e

def wrap2 (f g : Nat → Nat) : Nat := Nat.add (f 0) (g 0)

def appLam (n : Nat) (bad : Bool) : Expr := Id.run do
  let mut body := sumAll n (if bad then mkConst ``True else lit 0)
  for _ in [:n] do
    let l := Expr.lam `x nat body .default
    body := mkApp2 (mkConst ``SharedDepths.P3.wrap2) l l
  return body

def eqNat (a b : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) nat a b
def reflNat (a : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) nat a

run_cmd do
  let base := (← getEnv).toKernelEnv
  let n := 48
  let cases : List (String × Declaration) := [
    ("letgood", dfn `PF_letgood nat (letLadder n false)),
    ("letbad", dfn `PF_letbad nat (letLadder n true)),
    ("betagood", thm `PF_betagood (eqNat (betaLadder n) (lit 0)) (reflNat (lit 0))),
    ("betabad", thm `PF_betabad (eqNat (betaLadder n) (lit 1)) (reflNat (lit 0))),
    ("appgood", dfn `PF_appgood nat (appLam n false)),
    ("appbad", dfn `PF_appbad nat (appLam n true))]
  let mut rows : Array String := #[]
  let mut outs : Array (String × Kernel.Environment × List Name) := #[]
  for (id, d) in cases do
    let (verdict, e) ← liftM (checkAll base [d])
    rows := rows.push s!"row\t{id}\t{verdict}"
    outs := outs.push (id, e, d.getNames)
  for r in rows do IO.println r
  for (id, e, ns) in outs do writeCase e id ns
end P3

namespace P4

-- Agent R5 (ADR 0014 Amendment 9): Lean's infer_app in infer-only mode
-- (type_checker.cpp 188-205) types an application `f a₁ … aₙ` from its head,
-- putting the arguments into f's Pi telescope by one instantiate_rev, not
-- one instantiate per argument. Proof irrelevance types `h 0 … 0` and
-- `h₂ 0 … 0` (n arguments, h h₂ : ∀ x₁ … xₙ, P x₁ … xₙ) that way when the
-- good row compares them. The bad twin's statement puts `h₂ 0 … 0 1`, a
-- proof of `P 0 … 0 1`, where a proof of `P 0 … 0` is expected
-- (appTypeMismatch). tests/cli/shared_depths.py bounds the good row's fuel.

def piN (n : Nat) (b : Expr) : Expr := Id.run do
  let mut e := b
  for _ in [:n] do e := .forallE `x P3.nat e .default
  return e

def lamN (n : Nat) (b : Expr) : Expr := Id.run do
  let mut e := b
  for _ in [:n] do e := .lam `x P3.nat e .default
  return e

/-- x₁ … xₙ under n binders: bound variables n-1 … 0. -/
def bvars (n : Nat) : Array Expr := (Array.range n).reverse.map (Expr.bvar ·)
def zeros (n : Nat) (last : Nat) : Array Expr :=
  ((List.replicate (n - 1) (P3.lit 0)) ++ [P3.lit last]).toArray
def eqProp (a b c : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.zero]) a b c
def reflProp (a b : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [Level.zero]) a b

run_cmd do
  let base := (← getEnv).toKernelEnv
  let n := 48
  let s := P3.sumAll n (P3.lit 0)
  let p (args : Array Expr) : Expr := mkAppN (mkConst `Spine.P) args
  let dP := P3.dfn `Spine.P (piN n (.sort .zero)) (lamN n (P3.eqNat s s))
  let hType := piN n (p (bvars n))
  let dh := P3.thm `Spine.h hType (lamN n (P3.reflNat s))
  let dh₂ := P3.thm `Spine.h₂ hType (lamN n (P3.reflNat s))
  let hz := mkAppN (mkConst `Spine.h) (zeros n 0)
  let good := P3.thm `Spine.good (eqProp (p (zeros n 0)) hz (mkAppN (mkConst `Spine.h₂) (zeros n 0)))
    (reflProp (p (zeros n 0)) hz)
  let bad := P3.thm `Spine.bad (eqProp (p (zeros n 0)) hz (mkAppN (mkConst `Spine.h₂) (zeros n 1)))
    (reflProp (p (zeros n 0)) hz)
  let cases : List (String × List Declaration) := [
    ("spinegood", [dP, dh, dh₂, good]), ("spinebad", [dP, dh, dh₂, bad])]
  let mut rows : Array String := #[]
  let mut outs : Array (String × Kernel.Environment × List Name) := #[]
  for (id, ds) in cases do
    let (verdict, e) ← liftM (checkAll base ds)
    rows := rows.push s!"row\t{id}\t{verdict}"
    outs := outs.push (id, e, (ds.getLast!).getNames)
  for r in rows do IO.println r
  for (id, e, ns) in outs do writeCase e id ns
end P4

namespace P5

-- Agent CK (plan task 4.2.7d; review rvKN 3; ADR 0014 Amendment 10): Lean's
-- infer-only typing (infer_type, the typer of is_def_eq's proof irrelevance)
-- meeting an ill-typed term made by reduction. F h, FT h, S h and PT h are
-- stuck for a variable h : True ∧ True (And.rec on a proof that is no
-- constructor; Lean eta-expands no proposition), and reduce for ⟨⟩; F h and
-- F ⟨⟩ are definitionally equal (the arguments by proof irrelevance). So
-- `(fun (f : F ⟨⟩) => f 0) x`, x : F h, is well typed, but its beta reduct
-- `x 0` is not: each row states `L = id L` by `Eq.refl L`, and is_def_eq
-- of L and id L puts L in whnf_core and types it (is_def_eq_proof_irrel).
-- * app: `x 0`: infer_app's ensure_pi on F h throws funExpected.
-- * pi: `x → Nat`, x : S h: infer_pi's ensure_sort on S h, typeExpected
--   (LeanForth took a Pi to be a type without typing it, and accepted).
-- * lam: `fun y => (fun (z : x 0) => y) (Q x)`: infer_lambda in infer-only
--   mode types no domain, so Lean accepts (LeanForth typed z's domain aside).
-- * lambad: `fun (a : x 0) => 0`: its type `(a : x 0) → Nat`, which is_prop
--   types (infer_pi), funExpected.
-- * let: `fun y => let z : x 0 := Q x; y`: infer_let types neither.
-- * proj: `x.1`, x : PT h: infer_proj's structure test, invalidProj.

noncomputable def F (p : True ∧ True) : Type :=
  @And.rec True True (fun _ => Type) (fun _ _ => Nat → Nat) p
noncomputable def FT (p : True ∧ True) : Type 1 :=
  @And.rec True True (fun _ => Type 1) (fun _ _ => Nat → Type) p
noncomputable def S (p : True ∧ True) : Type 1 :=
  @And.rec True True (fun _ => Type 1) (fun _ _ => Type) p
noncomputable def PT (p : True ∧ True) : Type :=
  @And.rec True True (fun _ => Type) (fun _ _ => Nat × Nat) p

def nat : Expr := mkConst ``Nat
def lit (n : Nat) : Expr := .lit (.natVal n)
def pi (n : Name) (t b : Expr) : Expr := .forallE n t b .default
def lam (n : Name) (t b : Expr) : Expr := .lam n t b .default
def b (i : Nat) : Expr := .bvar i
def andTT : Expr := mkApp2 (mkConst ``And) (mkConst ``True) (mkConst ``True)
def tt : Expr := mkApp4 (mkConst ``And.intro) (mkConst ``True) (mkConst ``True)
  (mkConst ``True.intro) (mkConst ``True.intro)
def app (f : Name) (a : Expr) : Expr := mkApp (mkConst f) a
def thm (n : Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := ty, value := val, all := [n] }
def l1 : Level := .succ .zero
def l2 : Level := .succ l1

/-- `∀ binders, L = id L` proved by `Eq.refl L`, at universe u for type T. -/
def same (n : Name) (binders : List (Name × Expr)) (u : Level) (T L : Expr) : Declaration :=
  let eq := mkApp3 (mkConst ``Eq [u]) T L (mkApp2 (mkConst ``id [u]) T L)
  let ty := binders.foldr (fun (bn, bt) e => pi bn bt e) eq
  let val := binders.foldr (fun (bn, bt) e => lam bn bt e) (mkApp2 (mkConst ``Eq.refl [u]) T L)
  thm n ty val

def appL : Expr := mkApp (lam `f (app ``F tt) (mkApp (b 0) (lit 0))) (b 0)
def piL : Expr := mkApp (lam `T (app ``S tt) (pi `a (b 0) nat)) (b 0)
def qT : Expr := pi `g (app ``FT tt) (mkApp (b 0) (lit 0))
def lamL : Expr :=
  mkApp (lam `f (app ``FT tt)
    (lam `y nat (mkApp (lam `z (mkApp (b 1) (lit 0)) (b 1)) (mkApp (b 2) (b 1))))) (b 1)
def lam2L : Expr := mkApp (lam `f (app ``FT tt) (lam `a (mkApp (b 0) (lit 0)) (lit 0))) (b 0)
def lam2T : Expr := pi `a (mkApp (lam `f (app ``FT tt) (mkApp (b 0) (lit 0))) (b 0)) nat
def letL : Expr :=
  mkApp (lam `f (app ``FT tt)
    (lam `y nat (.letE `z (mkApp (b 1) (lit 0)) (mkApp (b 2) (b 1)) (b 1) false))) (b 1)
def projL : Expr := mkApp (lam `f (app ``PT tt) (.proj ``Prod 0 (b 0))) (b 0)
def natNat : Expr := pi `n nat nat

/-- Row id: theorem InferOnly.id over h : True ∧ True, x (or y) : xt and more. -/
def row (id : String) (xt : Expr) (more : List (Name × Expr)) (u : Level) (T L : Expr) :
    String × Declaration :=
  (id, same (Name.mkStr `InferOnly id) ([(`h, andTT), (`x, xt)] ++ more) u T L)

run_cmd do
  let base := (← getEnv).toKernelEnv
  let h := b 0
  let cases : List (String × Declaration) := [
    row "appbad" (app ``F h) [] l1 nat appL, row "appgood" (app ``F tt) [] l1 nat appL,
    row "pibad" (app ``S h) [] l2 (.sort l1) piL, row "pigood" (app ``S tt) [] l2 (.sort l1) piL,
    row "lambad" (app ``FT h) [] l1 lam2T lam2L, row "lam2good" (app ``FT tt) [] l1 lam2T lam2L,
    row "lamgood" (app ``FT h) [(`Q, qT)] l1 natNat lamL,
    row "letgood" (app ``FT h) [(`Q, qT)] l1 natNat letL,
    row "projbad" (app ``PT h) [] l1 nat projL, row "projgood" (app ``PT tt) [] l1 nat projL]
  let mut rows : Array String := #[]
  let mut outs : Array (String × Kernel.Environment × List Name) := #[]
  for (id, d) in cases do
    let (verdict, e) ← liftM (checkAll base [d])
    rows := rows.push s!"row\t{id}\t{verdict}"
    outs := outs.push (id, e, d.getNames)
  -- p5all: the ten in one export (Lean's verdict: appbad's, the first
  -- failure), copied to tests/core/check-declaration-cases/infer-only.ndjson
  -- for test_leanforth.py's per-declaration test.
  let all := cases.map (·.2)
  let (verdict, e) ← liftM (checkAll base all)
  rows := rows.push s!"row\tp5all\t{verdict}"
  outs := outs.push ("p5all", e, all.flatMap (·.getNames))
  for r in rows do IO.println r
  for (id, e, ns) in outs do writeCase e id ns
end P5

end SharedDepths
