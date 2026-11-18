-- How many namespaces `open N` can name in all of Mathlib (Lean's
-- namespacesExt, Lean/Namespace.lean): the set LeanForth's `open` would
-- need from the library (MATHLIB_FRONT.md section 2, obstacle 7).
import Mathlib
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut n := 0
  for _ in env.getNamespaces do n := n + 1
  IO.println s!"namespaces: {n}; Real: {env.isNamespace `Real}"
