import LeanForthFirstChecker

/-!
# The first checker's table cases as plain prefix text

Prints every case of `tests/reference/first-checker-expected.lean` (compiled
to the module `LeanForthFirstChecker` by `tests/core/lean-differential.py`):
the earlier declarations it needs and the declaration itself, exactly the
`Declaration` values that file adds to Lean's kernel. The LeanForth
differential (plan task 2.2.1, table `first-checker` in
`tests/core/lean-differential.py`) builds the same terms in LeanForth's
stores from this text, so the two sides cannot drift apart.

Format, one item per line:

* `CASE <id>`
* `DECL <role> <kind> <safety> <name> <n> <param>... TYPE <expr> VALUE <expr>`
  with role `before` or `check`, kind `thm`, `def`, `opq` or `ax`, safety
  `safe`, `unsafe` or `partial`, and value `none` for a statement without
  proof.

Expressions are prefix: `S <level>`, `V <index>`, `A <fn> <arg>`,
`L <domain> <body>` (lambda), `P <domain> <body>` (Pi),
`C <name> <n> <level>...`, `E <nonDep 0|1> <type> <value> <body>` (a `let`,
plan task 4.2.3), and `Xlit`, `Xmdata`, `Xproj`, `Xfvar`, `Xmvar` for the
forms the first checker does not support. Levels: `z`,
`s <level>`, `m <level> <level>`, `i <level> <level>`, `p <name>`. Binder
names and annotations are dropped: Lean's kernel ignores them.
-/

open Lean FirstChecker

def levelText : Level → String
  | .zero => "z"
  | .succ l => "s " ++ levelText l
  | .max a b => "m " ++ levelText a ++ " " ++ levelText b
  | .imax a b => "i " ++ levelText a ++ " " ++ levelText b
  | .param n => "p " ++ n.toString
  | .mvar _ => "?"

def exprText : Expr → String
  | .bvar i => s!"V {i}"
  | .sort l => "S " ++ levelText l
  | .const n ls => s!"C {n} {ls.length}" ++ String.join (ls.map (" " ++ levelText ·))
  | .app f a => "A " ++ exprText f ++ " " ++ exprText a
  | .lam _ t b _ => "L " ++ exprText t ++ " " ++ exprText b
  | .forallE _ t b _ => "P " ++ exprText t ++ " " ++ exprText b
  | .letE _ t v b nd => s!"E {if nd then 1 else 0} " ++ exprText t ++ " " ++ exprText v ++ " " ++
    exprText b
  | .lit .. => "Xlit"
  | .mdata .. => "Xmdata"
  | .proj .. => "Xproj"
  | .fvar .. => "Xfvar"
  | .mvar .. => "Xmvar"

def safetyText : DefinitionSafety → String
  | .safe => "safe"
  | .unsafe => "unsafe"
  | .partial => "partial"

def declText (role : String) (kind safety : String) (n : Name) (ps : List Name)
    (type : Expr) (value : Option Expr) : String :=
  s!"DECL {role} {kind} {safety} {n} {ps.length}" ++ String.join (ps.map (s!" {·}")) ++
    " TYPE " ++ exprText type ++ " VALUE " ++ (value.map exprText).getD "none"

def declLine (role : String) : Declaration → String
  | .thmDecl d => declText role "thm" "safe" d.name d.levelParams d.type d.value
  | .defnDecl d => declText role "def" (safetyText d.safety) d.name d.levelParams d.type d.value
  | .opaqueDecl d =>
    declText role "opq" (if d.isUnsafe then "unsafe" else "safe") d.name d.levelParams d.type
      d.value
  | .axiomDecl d =>
    declText role "ax" (if d.isUnsafe then "unsafe" else "safe") d.name d.levelParams d.type
      none
  | _ => s!"DECL {role} other"

run_cmd do
  for c in cases do
    IO.println s!"CASE {c.id}"
    for d in c.before do
      IO.println (declLine "before" d)
    IO.println (declLine "check" c.decl)
