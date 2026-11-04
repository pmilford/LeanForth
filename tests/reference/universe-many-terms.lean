import LeanForthFirstChecker
import LeanForthFirstCheckerTerms

/-!
# Many universe parameters: plan task 6.2.0, against the pinned Lean kernel

Lean has no fixed limit on a declaration's universe parameters, a
constant's universe arguments or the parameters a check knows, so
LeanForth has none either (plan task 6.2.0, brought forward by the owner on
2026-11-04). For n = 100, 300 and 1000 parameters `u_1 … u_n`, this file
builds, as `Declaration` values:

* `Big.{u_1…u_n} : Sort (max u_1 … u_n + 1) := Sort (max u_1 … u_n)`, the
  `max` a balanced tree (so its depth stays about log₂ n), and the same with
  the claim's `max` in reverse order, which normalize sorts back;
* uses `Big.{…}` with all n arguments, in order and reversed;
* failures: a use with n - 1 arguments (levelCount), a parameter list
  with u_1 twice (duplicateLevelParam), a claim one universe too high
  (declTypeMismatch), and a claim naming u_{n+1}, which is not a
  parameter (undefinedLevelParam).

Like `universe-scope-terms.lean`, each case is added with
`Kernel.Environment.addDeclCore` to a scratch copy of the kernel environment
after its earlier declarations, and the run fails unless Lean's verdict is
the recorded one. It prints one `EXPECT <id> <lean> <leanforth> <rule>` line
per case, then every case in the format of `first-checker-terms.lean`, for
`tests/core/lean-differential.py` (tables `universe-many` and
`universe-many-fed`). Reference observations, not a LeanForth checker.
-/

open Lean FirstChecker

namespace UniverseMany

/-- `u_1 … u_n`. -/
def names (n : Nat) : List Name := (List.range n).map fun i => Name.mkSimple s!"u_{i+1}"
def params (n : Nat) : List Level := (names n).map .param
/-- A balanced `max` of the levels. -/
partial def maxAll : List Level → Level
  | [] => .zero
  | [l] => l
  | ls => .max (maxAll (ls.take (ls.length / 2))) (maxAll (ls.drop (ls.length / 2)))
def s : Level → Level := .succ
def bigName (n : Nat) : Name := .mkSimple s!"Big{n}"
/-- `Big.{u_1…u_n} : Sort (claim + 1) := Sort (max u_1 … u_n)`. -/
def bigAt (n : Nat) (claim : Level) : Declaration :=
  defn (bigName n) (.sort (s claim)) (.sort (maxAll (params n))) (names n)
def big (n : Nat) : Declaration := bigAt n (maxAll (params n))
/-- `name.{ps} : Sort (claim + 1) := Big.{ls}`. -/
def use (n : Nat) (name : String) (ps : List Name) (claim : Level) (ls : List Level) :
    Declaration :=
  defn (.mkSimple s!"{name}{n}") (.sort (s claim)) (.const (bigName n) ls) ps

def casesFor (n : Nat) : List Case :=
  let ps := names n
  let ls := params n
  let top := maxAll ls
  [ { id := s!"many{n}.big", decl := big n,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"{n} universe parameters, their max a balanced tree" },
    { id := s!"many{n}.big-reversed", decl := bigAt n (maxAll ls.reverse),
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := "the claim's max in reverse order: normalize sorts it" },
    { id := s!"many{n}.use", before := [big n], decl := use n "Use" ps top ls,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"Big with all {n} universe arguments" },
    { id := s!"many{n}.use-reversed", before := [big n],
      decl := use n "UseR" ps top ls.reverse,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := "the arguments reversed: the same max after normalize" },
    { id := s!"many{n}.too-few", before := [big n], decl := use n "Few" ps top ls.tail,
      lean := "levelCount", leanforth := "rejected", rule := "L1",
      what := s!"{n - 1} arguments for {n} parameters" },
    { id := s!"many{n}.duplicate", decl := defn (.mkSimple s!"Dup{n}")
        (.sort (s top)) (.sort top) (ps ++ [Name.mkSimple "u_1"]),
      lean := "duplicateLevelParam", leanforth := "rejected", rule := "L3",
      what := "u_1 listed twice" },
    { id := s!"many{n}.too-high", decl := bigAt n (s top),
      lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
      what := "the claim one universe too high" },
    { id := s!"many{n}.undeclared", decl :=
        bigAt n (.max top (.param (.mkSimple s!"u_{n+1}"))),
      lean := "undefinedLevelParam", leanforth := "rejected", rule := "L2",
      what := s!"the claim names u_{n+1}, not a parameter" } ]

def cases : List Case := casesFor 100 ++ casesFor 300 ++ casesFor 1000

end UniverseMany

open UniverseMany in
run_cmd do
  let base := (← getEnv).toKernelEnv
  for c in UniverseMany.cases do
    let mut scratch := base
    for d in c.before do
      match scratch.addDeclCore 1000000 1000 d none with
      | .ok next => scratch := next
      | .error _ => throwError "{c.id}: Lean rejected a prerequisite"
    let got := verdict (scratch.addDeclCore 1000000 1000 c.decl none)
    unless got == c.lean do
      throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    IO.println s!"EXPECT {c.id} {got} {c.leanforth} {c.rule}"
  for c in UniverseMany.cases do
    IO.println s!"CASE {c.id}"
    for d in c.before do
      IO.println (declLine "before" d)
    IO.println (declLine "check" c.decl)
