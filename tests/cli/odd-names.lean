-- Names Lean writes with « », with a word of its syntax, or with characters a
-- line must never show raw (reviews F1 and F3 of fix-cli-present,
-- 2026-11-18). For each name N of oddParts: a definition N : Nat and a
-- theorem oddThmK : N = N, added with addDecl, since most of these names
-- cannot be typed as identifiers. Running the file prints one line per
-- name: K, Lean's Name.toString of N and Lean's ppExpr of the theorem's
-- statement, separated by tabs; tests/cli/odd-names.lean.out holds those
-- lines and tests/cli/test_leanforth.py (class OddNames) compares them with
-- what `leanforth check` and `leanforth print` show, with the differences
-- docs/user/COMMAND_LINE.md "Names" states. Exported with scripts/export.sh;
-- tests/cli/export-check.sh rebuilds the output, the export and its
-- manifest and compares them with the committed files.
import Lean
open Lean Meta Elab Command

def oddName (parts : List String) : Name := parts.foldl Name.mkStr .anonymous

def oddParts : List (List String) :=
  [["Foo", "a.b"], ["a\u202Eb"], ["Foo", "", "x"], ["Foo", "a«b»c"], ["fun"], ["Foo", "fun"],
   ["Prop"], ["Foo", "Prop"], ["by"], ["Type"], ["with space"], ["1x"],
   ["αβγ"], ["x y"], ["a_b}"], ["x₁"], ["x₊"], ["Foo", "a\\b"], ["λ"], ["Foo", "#x"],
   ["a", "b c", "d"], ["Foo", "12"]]

def oddStatement (n : Name) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) (mkConst n) (mkConst n)

def oddProof (n : Name) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkConst n)

def addOdd (k : Nat) (n : Name) : CoreM Unit := do
  addDecl (.defnDecl { name := n, levelParams := [], type := mkConst ``Nat,
                       value := mkConst ``Nat.zero, hints := .abbrev, safety := .safe })
  addDecl (.thmDecl { name := .mkSimple s!"oddThm{k}", levelParams := [],
                      type := oddStatement n, value := oddProof n })

run_cmd liftTermElabM do
  let mut k := 0
  for parts in oddParts do
    let n := oddName parts
    addOdd k n
    IO.println s!"{k}\t{n.toString}\t{← ppExpr (oddStatement n)}"
    k := k + 1
