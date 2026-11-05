import LeanForthFirstChecker
import LeanForthFirstCheckerTerms

/-!
# Many dependencies: plan task 6.2.0, against the pinned Lean kernel

Lean has no fixed limit on the constants one declaration uses, or on the
constants an environment holds, so LeanForth has none either since plan
task 6.2.0: a check's list of dependencies and the environment's
dependency pool grow with the heap. They held 16 per check and 65,536 per
environment before, and the drivers start the pool with room for 64. This
file builds, as `Declaration` values:

* `k_0 … k_(n-1) : Type := Prop` and `pair : Type → Type → Type := fun a b => a`;
* for n = 40 and 1,000, `use_n : Type := pair (pair k_0 k_1) (pair k_2 k_3) …`,
  every `k_i` once, in a balanced tree of `pair`s (so its depth stays about
  log₂ n), which depends on n + 1 earlier declarations (accepted); and the
  same claimed at `Prop` (declTypeMismatch, LeanForth's rule D1), which
  LeanForth decides only after it has recorded every dependency;
* `pool_0 … pool_65`, each the same tree over `k_0 … k_999` at `Type`:
  `pool_65` is checked after the 65 others, and its 1,001 dependencies
  bring the environment's pool to 66,066, past the old 65,536 (accepted).

Like `universe-many-terms.lean`, each case is added with
`Kernel.Environment.addDeclCore` to a scratch copy of the kernel environment
after its earlier declarations, and the run fails unless Lean's verdict is
the recorded one. It prints one `EXPECT <id> <lean> <leanforth> <rule>` line
per case, then every case in the format of `first-checker-terms.lean`, for
`tests/core/lean-differential.py` (tables `dependencies` and
`dependencies-fed`). Reference observations, not a LeanForth checker.
-/

open Lean FirstChecker

namespace Dependencies

def kName (i : Nat) : Name := .mkSimple s!"k_{i}"
/-- `k_i : Type := Prop`. -/
def k (i : Nat) : Declaration := defn (kName i) type prop
/-- `pair : Type → Type → Type := fun a b => a`. -/
def pair : Declaration :=
  defn `pair (.forallE `a type (.forallE `b type type .default) .default)
    (.lam `a type (.lam `b type (.bvar 1) .default) .default)
/-- The constants `k_i` for i in [lo, hi), joined by `pair` in a balanced tree. -/
partial def tree (lo hi : Nat) : Expr :=
  if hi - lo ≤ 1 then .const (kName lo) [] else
  let mid := (lo + hi) / 2
  mkAppN (.const `pair []) #[tree lo mid, tree mid hi]
def before (n : Nat) : List Declaration := pair :: (List.range n).map k
/-- `name : claim := tree 0 n`, every `k_i` below n once. -/
def use (name : String) (n : Nat) (claim : Expr) : Declaration :=
  defn (.mkSimple name) claim (tree 0 n)

def casesFor (n : Nat) : List Case :=
  [ { id := s!"deps{n}.use", before := before n, decl := use s!"use_{n}" n type,
      lean := "accepted", leanforth := "accepted", rule := "A1",
      what := s!"{n + 1} dependencies" },
    { id := s!"deps{n}.use-wrong", before := before n, decl := use s!"use_{n}" n prop,
      lean := "declTypeMismatch", leanforth := "rejected", rule := "D1",
      what := "claimed in Prop, decided after every dependency is recorded" } ]

/-- 66 declarations of 1,001 dependencies each; the last is the one checked. -/
def poolCase : Case :=
  { id := "pool66066.use",
    before := before 1000 ++ (List.range 65).map fun j => use s!"pool_{j}" 1000 type,
    decl := use "pool_65" 1000 type,
    lean := "accepted", leanforth := "accepted", rule := "A1",
    what := "the pool holds 66,066 dependencies once it is published" }

def cases : List Case := casesFor 40 ++ casesFor 1000 ++ [poolCase]

end Dependencies

open Dependencies in
run_cmd do
  let base := (← getEnv).toKernelEnv
  for c in Dependencies.cases do
    let mut scratch := base
    for d in c.before do
      match scratch.addDeclCore 100000000 1000 d none with
      | .ok next => scratch := next
      | .error _ => throwError "{c.id}: Lean rejected a prerequisite"
    let got := verdict (scratch.addDeclCore 100000000 1000 c.decl none)
    unless got == c.lean do
      throwError "{c.id}: Lean's verdict is {got}, expected {c.lean}"
    IO.println s!"EXPECT {c.id} {got} {c.leanforth} {c.rule}"
  -- Each case printed whole, in one write.
  for c in Dependencies.cases do
    let mut out := s!"CASE {c.id}\n"
    for d in c.before do
      out := out ++ declLine "before" d ++ "\n"
    IO.print (out ++ declLine "check" c.decl ++ "\n")
