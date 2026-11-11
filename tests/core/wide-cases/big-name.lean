import Lean
open Lean Elab Command
-- A declaration whose name has a numeric part of 2^32 (Lean's Name.num takes a Nat).
def bigName : Name := Name.num `Big 4294967296
def bigDecl : Declaration :=
  Declaration.defnDecl
    { name := bigName, levelParams := [], type := mkSort levelOne,
      value := mkSort levelZero, hints := ReducibilityHints.abbrev,
      safety := DefinitionSafety.safe }
run_cmd liftCoreM (addDecl bigDecl)
