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

end SharedDepths
