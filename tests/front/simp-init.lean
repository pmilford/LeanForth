-- Init's one-line simp proofs re-run by pinned Lean 4.35.0: the Lean side of
-- the simp group 4 harness (.claude/work/briefs/simp-group-4-architect.md,
-- section 1 "Measurement"; result and method in
-- docs/development/measurements/simp-init-2026-11-26/README.md).
--
-- It imports Init alone (no Lean, no Std: the default simp set is Init's) and
-- lists every theorem of an Init module whose source text, found through
-- findDeclarationRanges?, ends in `:= by simp`, `:= by simp [..]` or
-- `:= by simp only [..]` on one line, after the first `:=` outside brackets
-- (the shapes docs/design/TACTIC_SIMP.md counted with grep; `[..]` holds no
-- `]`). For each one it introduces as many binders as the stored value has
-- leading lambdas, elaborates the tactic text with Lean's own mkSimpContext
-- in the theorem's namespace (plus the module's top-level `open`s), and runs
-- Simp.main on the target with the default methods, the discharger wrapped
-- by a counter (wellBehavedDischarge stays true, so the cache acts as in the
-- tactic). It then runs the same tactic again with `-iota -proj -zeta`: a
-- different result means reduceStep's projection, matcher/iota or let steps
-- were used. One NDJSON line per theorem goes to stdout.
--
-- Run by hand (no make target yet; the implementing group adds
-- reference-simp-init):
--   ulimit -u 500
--   $TOOLCHAIN/bin/lean --run tests/front/simp-init.lean > OUT.ndjson
--   python3 tests/front/simp_init_summary.py OUT.ndjson --export INIT.ndjson
-- where TOOLCHAIN is the pinned leanprover--lean4---v4.35.0 toolchain.
import Lean
open Lean Meta Elab Tactic

-- String helpers on character lists (4.35's String.drop returns a slice).
def sdrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
def stake (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
def sdropRight (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))
def strim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse
def has (m p : String) : Bool := (m.splitOn p).length > 1

def maxSx : Nat := 20000

partial def tsize (e : Expr) (cap : Nat) : StateM Nat Unit := do
  if (← get) ≥ cap then return
  modify (· + 1)
  match e with
  | .app f a => tsize f cap; tsize a cap
  | .lam _ t b _ | .forallE _ t b _ => tsize t cap; tsize b cap
  | .letE _ t v b _ => tsize t cap; tsize v cap; tsize b cap
  | .mdata _ b | .proj _ _ b => tsize b cap
  | _ => pure ()

def treeSize (e : Expr) (cap : Nat := 10000000) : Nat := ((tsize e cap).run 0).2

def pl (l : Level) : String := match l.toNat with
  | some n => toString n
  | none => toString l

-- tests/front/s2-proofs.lean's printer, with proj, let, mdata, string
-- literals and free variables added.
partial def sx : Expr → String
  | .bvar i => s!"#{i}"
  | .const n us => n.toString ++ ".{" ++ String.intercalate "," (us.map pl) ++ "}"
  | .app f a => s!"(app {sx f} {sx a})"
  | .lam _ t b _ => s!"(lam {sx t} {sx b})"
  | .forallE _ t b _ => s!"(pi {sx t} {sx b})"
  | .letE _ t v b _ => s!"(let {sx t} {sx v} {sx b})"
  | .sort l => "Sort " ++ pl l
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => (toJson s).compress
  | .proj s i b => s!"(proj {s} {i} {sx b})"
  | .mdata _ b => sx b
  | e => s!"?? {e}"

def family (n : Name) : String :=
  let s := n.toString (escape := false)
  let last := match n with | .str _ l => l | _ => s
  if [`reduceIte, `reduceDIte, `dreduceIte, `dreduceDIte].contains n then "core-ite"
  else if n == `reduceCtorEq then "ctor-eq"
  else match n.getRoot.toString (escape := false) with
  | "Nat" =>
    if (last.splitOn "Diff").length > 1 then "nat-diff"
    else if last == "reducePow" || last == "reduceDvd" then "nat-pow-dvd" else "nat-lit"
  | "Int" => "int" | "Fin" => "fin" | "Char" => "char" | "String" => "string"
  | "BitVec" => "bitvec" | "List" => "list" | "Array" => "array"
  | r => if ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32",
      "Int64", "ISize"].contains r then "uint-sint" else if s.startsWith "_private" then "private" else "other"

def binderConsts : List Name :=
  [``forall_congr, ``implies_congr, ``funext, ``forall_prop_domain_congr,
   ``implies_dep_congr_ctx, ``implies_congr_ctx, ``pi_congr, ``let_congr,
   ``let_val_congr, ``let_body_congr]
def castConsts : List Name :=
  [``cast, ``Eq.mpr, ``Eq.mp, ``Eq.rec, ``Eq.ndrec, ``HEq, ``Eq.recOn, ``Eq.casesOn]

def isEqLike (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ b => do
    let b ← instantiateMVars b
    return b.isAppOfArity ``Eq 3 || b.isAppOfArity ``Iff 2 || b.isAppOfArity ``HEq 4

-- The bracket items of `simp [..]`, split at top-level commas, classified.
def splitItems (s : String) : List String := Id.run do
  let mut out := #[]; let mut cur := ""; let mut d : Int := 0
  for c in s.toList do
    if c == '(' || c == '[' || c == '{' || c == '⟨' then d := d + 1
    if c == ')' || c == ']' || c == '}' || c == '⟩' then d := d - 1
    if c == ',' && d == 0 then out := out.push (strim cur); cur := "" else cur := cur.push c
  if strim cur != "" then out := out.push (strim cur)
  return out.toList

def classifyItem (item : String) : TacticM Json := do
  let mut t := item; let mut arrow := false; let mut erase := false
  if t.startsWith "←" then arrow := true; t := strim (sdrop t 1)
  else if t.startsWith "<-" then arrow := true; t := strim (sdrop t 2)
  if t.startsWith "-" then erase := true; t := strim (sdrop t 1)
  if t.startsWith "↓" || t.startsWith "↑" then t := strim (sdrop t 1)
  let mk (k : String) := Json.mkObj [("text", toJson (item)), ("kind", toJson (k)), ("arrow", toJson (arrow)), ("erase", toJson (erase))]
  if t == "*" then return mk "star"
  if t.any (fun c => c == ' ' || c == '(') then return mk "term"
  let id := t.toName
  if let some d := (← getLCtx).findFromUserName? id then
    return mk (if ← isEqLike d.type then "hyp-eq" else "hyp-other")
  match ← resolveGlobalName id with
  | (n, []) :: _ =>
    if ← Simp.isSimproc n then return mk "simproc"
    match (← getEnv).find? n with
    | some (.thmInfo i) => return mk (if ← isEqLike i.type then "thm-eq" else "thm-other")
    | some (.defnInfo _) => return mk "def"
    | some _ => return mk "other-const"
    | none => return mk "unresolved"
  | _ => return mk "unresolved"

def Lean.Expr.lambdaCount : Expr → Nat
  | .lam _ _ b _ => 1 + b.lambdaCount
  | .mdata _ b => b.lambdaCount
  | _ => 0

-- ---- The theorem as LeanForth natural-form text (simp group 4, pass 3: the
-- harness make reference-simp-init, tests/front/check_simp_init.py). The
-- introduced binders are v1 .. vk, the statement the goal's target in
-- postfix: Lean's notations as LeanForth's words (binop%, binrel% and the
-- logical connectives), a numeral as itself, any other constant applied to
-- its explicit arguments (`a1 .. an C`, or `' C a1 $ .. an $` when the
-- count is not its type's), the bracket items as `' NAME` (`<-` after a
-- reversed one). Anything else (a binder, fun, let or projection in the
-- statement, a sort, a raw or string literal, a private or escaped name,
-- universe parameters, a `*`, term, erased or ↓/↑ item) cannot be written:
-- lf_why names it. The statement LeanForth elaborates is compared with
-- Lean's (the dumped types), so a printing Lean's elaborator and
-- LeanForth's read differently is found, never counted.
abbrev LfM := ExceptT String MetaM

def lfOps : List (Name × Nat × String) :=
  [(``HAdd.hAdd, 6, "+"), (``HMul.hMul, 6, "*"), (``HSub.hSub, 6, "-"), (``HDiv.hDiv, 6, "/"),
   (``HMod.hMod, 6, "%"), (``HPow.hPow, 6, "^"), (``Eq, 3, "="), (``LE.le, 4, "≤"),
   (``LT.lt, 4, "<"), (``GE.ge, 4, "≥"), (``GT.gt, 4, ">"), (``Ne, 3, "≠"), (``And, 2, "∧"),
   (``Or, 2, "∨"), (``Iff, 2, "↔"), (``Dvd.dvd, 4, "∣")]

def lfName (n : Name) : LfM String := do
  if isPrivateName n then throwThe String "a private constant"
  if n.hasNum then throwThe String "a name with a numeric part"
  let s := n.toString (escape := true)
  if s.any (fun c => c == '«' || c == ' ' || c == '»') then throwThe String "a name that needs escaping"
  return s

-- The binder kinds of a type's syntactic telescope, and whether its body's
-- head may unfold to more binders (LeanForth then counts no arity).
partial def lfTele (env : Environment) : Expr → Array BinderInfo → Array BinderInfo × Bool
  | .forallE _ _ b bi, acc => lfTele env b (acc.push bi)
  | .mdata _ b, acc => lfTele env b acc
  | e, acc => (acc, match e.getAppFn with
      | .const c _ => match env.find? c with | some (.defnInfo _) => true | _ => false
      | .lam .. | .letE .. | .proj .. | .mdata .. => true
      | _ => false)

-- Numerals and arithmetic of numerals alone: nothing in it fixes a numeral's type.
partial def lfNumOnly (e : Expr) : Bool :=
  if e.isAppOfArity ``OfNat.ofNat 3 then true
  else if e.isAppOfArity ``Neg.neg 3 then lfNumOnly e.appArg!
  else if [``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow].any
      (e.isAppOfArity · 6) then lfNumOnly e.appFn!.appArg! && lfNumOnly e.appArg!
  else false

def lfJoin (xs : List String) : String := " ".intercalate (xs.filter (· != ""))

mutual
partial def lfTerm (names : FVarId → Option String) (e : Expr) : LfM String := do
  match e with
  | .fvar id => lfLocal names id #[]
  | .mdata _ b => lfTerm names b
  | .lit (.natVal _) => throwThe String "a raw natural literal"
  | .lit (.strVal _) => throwThe String "a string literal"
  | .sort _ => throwThe String "a sort (Prop, Type, Sort)"
  | .forallE .. => throwThe String "a binder (∀ or →) in the statement"
  | .lam .. => throwThe String "a fun in the statement"
  | .letE .. => throwThe String "a let in the statement"
  | .proj .. => throwThe String "a projection in the statement"
  | .const n _ => lfApp names n #[]
  | .app .. => match e.getAppFn with
    | .const n _ => lfApp names n e.getAppArgs
    | .fvar id => lfLocal names id e.getAppArgs
    | _ => throwThe String "an application of no constant or variable"
  | _ => throwThe String "a metavariable or loose variable"

partial def lfArgs (names : FVarId → Option String) (bis : Array BinderInfo) (args : Array Expr) :
    LfM (List String) := do
  let mut out := #[]
  for h : j in [0 : args.size] do
    if bis.getD j .default == .default then out := out.push (← lfTerm names args[j])
  return out.toList

-- A constant applied: a numeral, a notation, or its explicit arguments.
partial def lfApp (names : FVarId → Option String) (n : Name) (args : Array Expr) : LfM String := do
  if n == ``OfNat.ofNat && args.size == 3 then
    match args[1]! with
    | .lit (.natVal k) => if k < 1000000000 then return toString k
                          else throwThe String "a numeral of ten digits or more"
    | _ => throwThe String "OfNat.ofNat of no literal"
  if n == ``Not && args.size == 1 then return s!"{← lfTerm names args[0]!} ¬"
  for (op, ar, w) in lfOps do
    if n == op && args.size == ar then
      let (a, b) := (args[ar-2]!, args[ar-1]!)
      if !args[0]!.isConstOf ``Nat && lfNumOnly a && lfNumOnly b && ar > 2 then
        throwThe String "numerals of a type other than Nat no variable fixes (a type ascription)"
      return s!"{← lfTerm names a} {← lfTerm names b} {w}"
  let some ci := (← getEnv).find? n | throwThe String "an unknown constant"
  let (bis, unf) := lfTele (← getEnv) ci.type #[]
  let name ← lfName n
  let exps ← lfArgs names bis args
  let nexp := (bis.filter (· == .default)).size
  if !unf && args.size ≤ bis.size && exps.length == nexp then return lfJoin (exps ++ [name])
  return lfJoin ([s!"' {name}"] ++ exps.map (· ++ " $"))

-- A variable applied to its explicit arguments, as its type counts them.
partial def lfLocal (names : FVarId → Option String) (id : FVarId) (args : Array Expr) :
    LfM String := do
  let some s := names id | throwThe String "a free variable of no binder"
  let (bis, unf) := lfTele (← getEnv) (← instantiateMVars (← id.getType)) #[]
  let exps ← lfArgs names bis args
  if !unf && args.size == bis.size && exps.length == (bis.filter (· == .default)).size then
    return lfJoin (exps ++ [s])
  return lfJoin ([s!"' {s}"] ++ exps.map (· ++ " $"))
end

def lfBinderWord : BinderInfo → String
  | .default => "explicit:" | .implicit => "implicit:"
  | .strictImplicit => "strict-implicit:" | .instImplicit => "instance:"

-- A bracket item as `' NAME` or `' NAME <-`, resolved as classifyItem does.
def lfItem (names : FVarId → Option String) (item : String) : TacticM (Except String String) := do
  let mut t := item; let mut arrow := false
  if t.startsWith "←" then arrow := true; t := strim (sdrop t 1)
  else if t.startsWith "<-" then arrow := true; t := strim (sdrop t 2)
  if t.startsWith "-" then return .error "an erased item (-x)"
  if t.startsWith "↓" || t.startsWith "↑" then return .error "a pre or post item (↓, ↑)"
  if t == "*" then return .error "the item *"
  if t.any (fun c => c == ' ' || c == '(') then return .error "a term item"
  let tail := if arrow then " <-" else ""
  let id := t.toName
  if let some d := (← getLCtx).findFromUserName? id then
    match names d.fvarId with
    | some s => return .ok s!"' {s}{tail}"
    | none => return .error "an item naming no binder"
  match ← resolveGlobalName id with
  | (n, []) :: _ => match ← (lfName n).run with
    | .ok s => return .ok s!"' {s}{tail}"
    | .error w => return .error s!"an item: {w}"
  | _ => return .error "an unresolved item"

-- Postfix tokens as lines below 900 characters (a LeanForth line has fewer than 1024).
def lfLines (s : String) : List String := Id.run do
  let mut out := #[]; let mut cur := ""
  for w in s.splitOn " " do
    if cur.length + w.length + 1 > 900 then out := out.push cur; cur := w
    else cur := if cur == "" then w else cur ++ " " ++ w
  return (out.push cur).toList

-- The theorem's text, or why it cannot be written, in g's context after introNP.
def lfText (i : TheoremVal) (name tac : String) (fvars : Array FVarId) (g : MVarId) :
    TacticM (Except String String) := do
  if !i.levelParams.isEmpty then return .error "universe parameters"
  let names : FVarId → Option String := fun id =>
    (fvars.idxOf? id).map (fun j => s!"v{j + 1}")
  let mut lines := #[s!"theorem {name}"]
  for h : j in [0 : fvars.size] do
    let d ← fvars[j].getDecl
    if d.isLet then return .error "a let binder"
    match ← (lfTerm names (← instantiateMVars d.type)).run with
    | .ok s => lines := lines ++ ((lfLines s!"{s} {lfBinderWord d.binderInfo} v{j + 1}").map ("  " ++ ·)).toArray
    | .error w => return .error s!"binder type: {w}"
  match ← (lfTerm names (← instantiateMVars (← g.getType))).run with
  | .ok s => lines := lines ++ ((lfLines s).map ("  " ++ ·)).toArray
  | .error w => return .error s!"statement: {w}"
  let mut items := #[]
  if let [_, rest] := tac.splitOn "[" then
    for item in splitItems (sdropRight rest 1) do
      match ← lfItem names item with
      | .ok s => items := items.push s
      | .error w => return .error s!"bracket: {w}"
  let t := if tac == "simp" then "by-simp" else s!"by-simp[ {lfJoin items.toList} ]"
  return .ok ("\n".intercalate (lines ++ #[":= by", s!"  {t}", s!"end {name}"]).toList ++ "\n")

structure Run where
  closed : Bool
  why : String := ""
  value : Expr := default
  used : List (Origin × Nat) := []
  att : Nat := 0
  ok : Nat := 0
  items : Array Json := #[]
  lf : Except String String := .error "not made"

def countingDisch (att ok : IO.Ref Nat) : Simp.Discharge := fun e => do
  att.modify (· + 1)
  let r ← Simp.dischargeDefault? e
  if r.isSome then ok.modify (· + 1)
  return r

-- One run of `tac` on theorem `i`: intro, mkSimpContext, Simp.main, close.
def runSimp (i : TheoremVal) (tac : String) (withItems : Bool) (lfName : String := "") :
    TermElabM Run := do
  let stx ← match Parser.runParserCategory (← getEnv) `tactic tac with
    | .ok s => pure s | .error e => throwError "parse: {e}"
  let g0 ← mkFreshExprMVar i.type .syntheticOpaque
  let k := i.value.lambdaCount
  let (fvars, g) ← g0.mvarId!.introNP k
  let res ← IO.mkRef ({ closed := false } : Run)
  let att ← IO.mkRef 0; let ok ← IO.mkRef 0
  let _ ← Tactic.run g do
    g.withContext do
      let items ← if withItems then
        match tac.splitOn "[" with
        | [_, rest] => (splitItems (sdropRight rest 1)).toArray.mapM classifyItem
        | _ => pure #[]
        else pure #[]
      res.modify ({ · with items })
      if withItems then
        let lf ← lfText i lfName tac fvars g
        res.modify ({ · with lf })
      let r ← mkSimpContext stx (eraseLocal := false)
      let target ← instantiateMVars (← g.getType)
      let methods := Simp.mkMethods r.simprocs (countingDisch att ok) (wellBehavedDischarge := true)
      let (sr, stats) ← Simp.main target r.ctx {} methods
      let used := stats.usedTheorems.map.toList
      res.modify ({ · with used })
      if sr.expr.isTrue then
        g.assign (← match sr.proof? with
          | some p => mkOfEqTrue p | none => pure (mkConst ``True.intro))
        res.modify ({ · with closed := true })
      else
        res.modify ({ · with why := if sr.expr == target then "no-progress" else "unsolved" })
  let v ← instantiateMVars g0
  let r ← res.get
  if r.closed && v.hasMVar then return { r with closed := false, why := "mvars" }
  return { r with value := v, att := ← att.get, ok := ← ok.get }

def errClass (m : String) : String :=
  if has m "heartbeats" then "heartbeats"
  else if has m "maximum number of steps" then "max-steps"
  else if has m "maximum recursion depth" then "max-rec-depth"
  else if has m "unknown identifier" || has m "unknown constant" then "unknown-identifier"
  else if has m "ambiguous" then "ambiguous"
  else if has m "parse:" then "parse"
  else "error"

def runCore (env : Environment) (ns : Name) (opens : List OpenDecl) (x : TermElabM α) :
    IO (Except String α) := do
  let ctx : Core.Context := {
    fileName := "<simp-init>", fileMap := default, currNamespace := ns, openDecls := opens,
    maxHeartbeats := 200000 * 1000, maxRecDepth := defaultMaxRecDepth, initHeartbeats := ← IO.getNumHeartbeats,
    options := ({} : Options) }
  try
    let (a, _) ← ((x.run' {}).run' {} {}).toIO ctx { env }
    return .ok a
  catch e => return .error (toString e)

-- Source text between two positions (columns count code points).
def slice (ls : Array String) (a b : Position) : String := Id.run do
  if a.line == b.line then return stake (sdrop ls[a.line - 1]! a.column) (b.column - a.column)
  let mut s := sdrop ls[a.line - 1]! a.column
  for l in [a.line : b.line - 1] do s := s ++ "\n" ++ ls[l]!
  return s ++ "\n" ++ stake ls[b.line - 1]! b.column

-- The text after the first `:=` outside brackets, if any and if the text
-- before it has no `where` (a structure instance's field) or `|`.
def afterAssign (t : String) : Option String := Id.run do
  let cs := t.toList.toArray; let mut d : Int := 0
  for j in [0 : cs.size] do
    let c := cs[j]!
    if c == '(' || c == '[' || c == '{' || c == '⟨' || c == '⦃' then d := d + 1
    if c == ')' || c == ']' || c == '}' || c == '⟩' || c == '⦄' then d := d - 1
    if c == ':' && d == 0 && j + 1 < cs.size && cs[j+1]! == '=' then
      let sig := String.ofList (cs.toList.take j)
      if has sig " where" || has sig "where\n" || has sig "\n  |" then return none
      return some (String.ofList (cs.toList.drop (j + 2)))
  return none

-- `simp`, `simp [..]` or `simp only [..]` with its shape, or none.
def shapeOf (rest : String) : Option (String × String) :=
  if rest.any (· == '\n') || !rest.startsWith " by simp" then none else
  let tac := strim (sdrop rest 4)
  if tac == "simp" then some ("bare", tac)
  else if tac.startsWith "simp [" && tac.endsWith "]" && (sdropRight (sdrop tac 6) 1).all (· != ']') then
    some ("brackets", tac)
  else if tac.startsWith "simp only [" && tac.endsWith "]" && (sdropRight (sdrop tac 11) 1).all (· != ']') then
    some ("only", tac)
  else none

def opensBefore (env : Environment) (ls : Array String) (pos : Position) : List OpenDecl := Id.run do
  let mut out := #[]
  for j in [0 : pos.line] do
    let l := if j + 1 == pos.line then stake ls[j]! pos.column else ls[j]!
    if !l.startsWith "open " then continue
    let ws := (sdrop l 5).splitOn " " |>.filter (· != "")
    let inFlag := ws.getLast? == some "in"
    if inFlag && j + 2 < pos.line && j + 1 != pos.line then continue
    for w in ws do
      if w == "in" || w.startsWith "(" || w == "hiding" || w == "renaming" then break
      if w == "scoped" then continue
      let n := w.toName
      if env.isNamespace n then out := out.push (OpenDecl.simple n [])
  return out.toList

def oneTheorem (env : Environment) (mod : Name) (_ls : Array String) (n : Name) (i : TheoremVal)
    (line : Nat) (shape tac : String) (opens : List OpenDecl) (congrNames : NameSet) : IO Json := do
  let user := (privateToUserName? n).getD n
  let ns := user.getPrefix
  let env := env.setMainModule mod
  let base : List (String × Json) := [("name", toJson (n.toString (escape := false))), ("module", toJson mod.toString),
    ("line", toJson line), ("shape", toJson shape), ("tactic", toJson tac), ("lambdas", toJson i.value.lambdaCount)]
  let t0 ← IO.monoMsNow
  let lfOut (r : Run) : List (String × Json) := match r.lf with
    | .ok t => [("lf", toJson t), ("type", toJson (sx i.type))]
    | .error w => [("lf", Json.null), ("lf_why", toJson w)]
  match ← runCore env ns opens (runSimp i tac true "THEOREM") with
  | .error m => return Json.mkObj (base ++ [("closed", toJson false), ("why", toJson (errClass m)), ("msg", toJson (stake m 300)),
      ("ms", toJson ((← IO.monoMsNow) - t0))])
  | .ok r =>
    let ms := (← IO.monoMsNow) - t0
    if !r.closed then
      return Json.mkObj (base ++ [("closed", toJson false), ("why", toJson (r.why)), ("items", toJson r.items),
        ("discharge", Json.mkObj [("attempts", toJson (r.att)), ("ok", toJson (r.ok))]), ("ms", toJson (ms))]
        ++ lfOut r)
    let ordered := (r.used.toArray.qsort (fun a b => a.2 < b.2)).toList.map (·.1)
    let mut lemmas := #[]; let mut simprocs := #[]; let mut hyps := #[]
    for o in ordered do
      match o with
      | .decl d _ inv =>
        let isProc ← match ← runCore env ns opens (Simp.isSimproc d : TermElabM Bool) with
          | .ok b => pure b | .error _ => pure false
        if isProc then simprocs := simprocs.push (Json.mkObj [("name", toJson (d.eraseMacroScopes.toString (escape := false))),
          ("family", toJson (family d.eraseMacroScopes))])
        else lemmas := lemmas.push ((if inv then "←" else "") ++ d.toString (escape := false))
      | .fvar f => hyps := hyps.push f.name.toString
      | o => hyps := hyps.push (toString o.key)
    let v := r.value
    let cs := v.getUsedConstants
    let nm (xs : Array Name) := toJson (xs.map (·.toString (escape := false)))
    let funextNested := (v.find? fun s => s.isAppOf ``funext &&
      ((s.getAppArgs.back?.map (·.find? (·.isAppOf ``funext))).join).isSome).isSome
    -- the ablation: reduceStep's proj, iota/matcher and let steps off
    let abl ← match ← runCore env ns opens (runSimp i ("simp -iota -proj -zeta" ++ sdrop tac 4) false) with
      | .error m => pure s!"fails:{errClass m}"
      | .ok r2 => pure (if !r2.closed then s!"fails:{r2.why}" else if r2.value == v then "same" else "differs")
    let sz := treeSize v
    return Json.mkObj (base ++ [("closed", toJson true), ("lemmas", toJson lemmas), ("simprocs", toJson simprocs),
      ("hyps", toJson hyps), ("items", toJson r.items),
      ("discharge", Json.mkObj [("attempts", toJson (r.att)), ("ok", toJson (r.ok))]),
      ("binder", nm (cs.filter binderConsts.contains)), ("funext_nested", toJson funextNested),
      ("congr", nm (cs.filter congrNames.contains)),
      ("congr_simp", nm (cs.filter fun c => c.toString.endsWith "congr_simp")),
      ("helpers", nm (cs.filter fun c => match c with | .str _ s => s.startsWith "_simp_" | _ => false)),
      ("casts", nm (cs.filter castConsts.contains)),
      ("reduce_ablation", toJson (abl)), ("same_as_stored", toJson (v == i.value)),
      ("size", toJson (sz)), ("ms", toJson (ms)), ("term", if sz ≤ maxSx then toJson (sx v) else Json.null)]
      ++ lfOut r)

unsafe def main (args : List String) : IO Unit := do
  -- The running binary's toolchain, never a `lean` found on PATH (an elan
  -- proxy could download a toolchain).
  let some root := (← IO.appDir).parent | throw (IO.userError "no toolchain root")
  initSearchPath root
  enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let src := root / "src" / "lean"
  let only := args.head?  -- optional module-name prefix filter, for quick runs
  let congrNames : NameSet ← match ← runCore env .anonymous [] (do
      let c ← getSimpCongrTheorems
      return c.lemmas.fold (init := ({} : NameSet)) fun s _ l => l.foldl (·.insert ·.theoremName) s) with
    | .ok s => pure s | .error e => throw (IO.userError e)
  let stdout ← IO.getStdout
  let mut count := 0
  for h : idx in [0 : env.header.moduleNames.size] do
    let mod := env.header.moduleNames[idx]
    if mod.getRoot != `Init then continue
    if let some p := only then if !(mod.toString.startsWith p) then continue
    let path := mod.components.foldl (fun (p : System.FilePath) c => p / c.toString) src
    let path := path.addExtension "lean"
    let some text ← (do return some (← IO.FS.readFile path)) <|> pure none | continue
    let ls := (text.splitOn "\n").toArray
    let mut found := #[]
    for n in env.header.moduleData[idx]!.constNames do
      let some (.thmInfo i) := env.find? n | continue
      if ((privateToUserName? n).getD n).isInternal then continue
      let rs? ← match ← runCore env .anonymous [] (findDeclarationRanges? n : TermElabM _) with
        | .ok r => pure r | .error _ => pure none
      let some rs := rs? | continue
      let sel := slice ls rs.selectionRange.pos rs.selectionRange.endPos
      let last := match (privateToUserName? n).getD n with | .str _ s => s | _ => ""
      if !(sel == last || sel.endsWith ("." ++ last)) then continue
      let some rest := afterAssign (slice ls rs.selectionRange.endPos rs.range.endPos) | continue
      let some (shape, tac) := shapeOf rest | continue
      found := found.push (n, i, rs.range.endPos.line, shape, tac, opensBefore env ls rs.range.pos)
    for (n, i, line, shape, tac, opens) in found.qsort (fun a b => a.2.2.1 < b.2.2.1) do
      let j ← oneTheorem env mod ls n i line shape tac opens congrNames
      stdout.putStrLn j.compress
      stdout.flush
      count := count + 1
  IO.eprintln s!"simp-init: {count} theorems"
