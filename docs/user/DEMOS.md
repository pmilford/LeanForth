# Five small proofs, proved by Lean and re-checked

Five well-known results, each stated in mathematical notation, in Lean and in
LeanForth words. **Lean 4.35.0 proves each theorem; LeanForth re-checks the
proof terms in Lean's export** and rejects a deliberately wrong copy. You do
not need to know Lean or Forth to read the mathematics.

**What this page does and does not show.** LeanForth checks proofs that Lean
produced and exported. LeanForth text can be checked since 2026-11-12
([checking a file](LEANFORTH_SYNTAX.md#checking-a-file), plan 8.2.1c-d), but the demos below were
not written as LeanForth input. The "LeanForth words" below are the statement printed from
Lean's export as an `axiom` form with no proof; they show what is checked, are
not runnable input, and running them does not check anything.

**How to read the page.** Every statement is printed four times by
`leanforth print`:

- *in mathematics* (rendered LaTeX, and the same as plain Unicode text), with
  `ℕ` for the natural numbers, `·` for multiplication and exponents raised;
- *in Lean*, as Lean's own `#check` prints the theorem (the test compares the
  two character by character);
- *in LeanForth words*, the same type, printed from Lean's export, as postfix Forth words: names, `$` applies a
  function to the argument before it, `^` applies a constant to universe
  levels, `lit#` is a number literal ([LeanForth syntax](LEANFORTH_SYNTAX.md)).

Mathematics and Lean show only the arguments a person writes: the implicit
arguments and type-class instances that Lean fills in are hidden, as Lean's
own printer hides them, and `Nat.succ n` is shown as `n + 1`. The table that
decides this is the [notation table](TERM_PRINTER.md#notation-the-table-and-the-modes);
`leanforth print --kernel` prints the terms as the checker has them instead.

**Trust.** The printer is presentation code: nothing it prints is evidence
that anything was checked, and the checker never loads it. The verdict under
each statement is the checker's. Until an outside Lean expert has audited the
checker, every accepted result is *experimental, not independently audited*.
"accepted ... axioms: propext, Quot.sound" says which of Lean's standard axioms
the proof depends on; the two are on the allowlist.

**The wrong twin.** For each theorem, `tests/demos/wrong_twin.py` copies the
export and changes only the statement: the proof is attached to *P → P*
instead of *P*, where *P* is the original statement. The checker must say
`rejected: declared type mismatch`, and the test fails if it does not.

## 1. Addition does not care about order

**In words.** For all natural numbers m and n, m + n = n + m.

**The idea.** Induction on n. For n = 0 both sides are m. If the claim holds for k, then m + (k + 1) = (m + k) + 1 = (k + m) + 1 = (k + 1) + m, using the rules `Nat.add_succ` and `Nat.succ_add` that define addition one step at a time.

**In mathematics** (Unicode text, then rendered LaTeX):

```text
∀ (m n : ℕ), m + n = n + m
```

```math
\forall (m\ n : \mathbb{N}),\ m + n = n + m
```

**In Lean**, as pinned Lean 4.35.0 prints `#check @add_comm_by_induction`:

```text
add_comm_by_induction : ∀ (m n : Nat), m + n = n + m
```

**In LeanForth words** (the type of the theorem as `leanforth print` writes it from Lean's export; an `axiom` form with no proof, not runnable input):

```text
axiom add_comm_by_induction
  Nat explicit: m
  Nat explicit: n
  Eq 1 ^ Nat $ HAdd.hAdd 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $ instHAdd 0 ^ Nat $ instAddNat $ $ m
    $ n $ $ HAdd.hAdd 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $ instHAdd 0 ^ Nat $ instAddNat $ $ n $
    m $ $
end add_comm_by_induction
```

**The Lean proof** (`tests/demos/DemoAddComm.lean`; Lean compiled it, LeanForth did not read it):

```lean
/-- Addition of natural numbers is commutative: `m + n = n + m`, by induction on `n`.
    Demo 1 of docs/user/DEMOS.md. -/
theorem add_comm_by_induction (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => exact (Nat.zero_add m).symm ▸ rfl
  | succ k ih => rw [Nat.add_succ, ih, Nat.succ_add]
```

**The verdicts.** `leanforth check` of Lean's export of the theorem and the
declarations it needs:

```text
52 declarations: 52 accepted
accepted: 52 (experimental, not independently audited); axioms: none
```

and of the wrong twin (exit status 1, as for any rejection):

```text
add_comm_by_induction: rejected
  rejected: declared type mismatch (D1-D5); diagnostic 60 at check-declaration lf-check-declaration: 0 0
```

The checker's derivation log of this theorem: *1024 steps, incomplete: truncated at step 1025 (records).* The log of a proof this size is cut at the bound `leanforth print` keeps, so no proof outline is printed; the verdict is unaffected.

## 2. Gauss's sum

**In words.** Twice the sum 0 + 1 + ... + n is n (n + 1). Here `sumTo n` is that sum, defined by `sumTo 0 = 0` and `sumTo (k + 1) = sumTo k + (k + 1)`.

**The idea.** Induction on n. For n = 0 both sides are 0. For n = k + 1, twice the sum is 2 (sumTo k) + 2 (k + 1) = k (k + 1) + 2 (k + 1) = (k + 1) (k + 2), where the middle step is the claim for k.

**In mathematics** (Unicode text, then rendered LaTeX):

```text
∀ (n : ℕ), 2 · sumTo n = n · (n + 1)
```

```math
\forall (n : \mathbb{N}),\ 2 \cdot \mathsf{sumTo}\ n = n \cdot (n + 1)
```

**In Lean**, as pinned Lean 4.35.0 prints `#check @gauss_sum`:

```text
gauss_sum : ∀ (n : Nat), 2 * sumTo n = n * (n + 1)
```

**In LeanForth words** (the type of the theorem as `leanforth print` writes it from Lean's export; an `axiom` form with no proof, not runnable input):

```text
axiom gauss_sum
  Nat explicit: n
  Eq 1 ^ Nat $ HMul.hMul 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $ instHMul 0 ^ Nat $ instMulNat $ $
    OfNat.ofNat 0 ^ Nat $ 2 lit# $ instOfNatNat 2 lit# $ $ $ sumTo n $ $ $ HMul.hMul 0 ^ 0
    ^ 0 ^ Nat $ Nat $ Nat $ instHMul 0 ^ Nat $ instMulNat $ $ n $ HAdd.hAdd 0 ^ 0 ^ 0 ^
    Nat $ Nat $ Nat $ instHAdd 0 ^ Nat $ instAddNat $ $ n $ OfNat.ofNat 0 ^ Nat $ 1 lit# $
    instOfNatNat 1 lit# $ $ $ $ $
end gauss_sum
```

**The Lean proof** (`tests/demos/DemoGauss.lean`; Lean compiled it, LeanForth did not read it):

```lean
/-- `sumTo n = 0 + 1 + ... + n`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- Gauss's sum: twice `0 + 1 + ... + n` is `n (n + 1)`. Demo 2 of docs/user/DEMOS.md. -/
theorem gauss_sum (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show 2 * (sumTo k + (k + 1)) = (k + 1) * (k + 1 + 1)
    rw [Nat.mul_add, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
```

**The verdicts.** `leanforth check` of Lean's export of the theorem and the
declarations it needs:

```text
1442 declarations: 1442 accepted
accepted: 1442 (experimental, not independently audited); axioms: propext, Quot.sound (allowlisted); none NOT PROVED
```

and of the wrong twin (exit status 1, as for any rejection):

```text
gauss_sum: rejected
  rejected: declared type mismatch (D1-D5); diagnostic 60 at check-declaration lf-check-declaration: 0 0
```

The checker's derivation log of this theorem: *1024 steps, incomplete: truncated at step 1025 (records).* The log of a proof this size is cut at the bound `leanforth print` keeps, so no proof outline is printed; the verdict is unaffected.

## 3. The first n odd numbers add up to n squared

**In words.** 1 + 3 + 5 + ... + (2n - 1) = n². Here `sumOdd n` is that sum, defined by `sumOdd 0 = 0` and `sumOdd (k + 1) = sumOdd k + (2 k + 1)`.

**The idea.** Induction on n. For n = 0 both sides are 0. For n = k + 1: k² + (2 k + 1) = (k + 1)², by expanding the square.

**In mathematics** (Unicode text, then rendered LaTeX):

```text
∀ (n : ℕ), sumOdd n = n²
```

```math
\forall (n : \mathbb{N}),\ \mathsf{sumOdd}\ n = n^{2}
```

**In Lean**, as pinned Lean 4.35.0 prints `#check @odd_sum`:

```text
odd_sum : ∀ (n : Nat), sumOdd n = n ^ 2
```

**In LeanForth words** (the type of the theorem as `leanforth print` writes it from Lean's export; an `axiom` form with no proof, not runnable input):

```text
axiom odd_sum
  Nat explicit: n
  Eq 1 ^ Nat $ sumOdd n $ $ HPow.hPow 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $ instHPow 0 ^ 0 ^ Nat $
    Nat $ instPowNat 0 ^ Nat $ instNatPowNat $ $ $ n $ OfNat.ofNat 0 ^ Nat $ 2 lit# $
    instOfNatNat 2 lit# $ $ $ $
end odd_sum
```

**The Lean proof** (`tests/demos/DemoOddSum.lean`; Lean compiled it, LeanForth did not read it):

```lean
/-- `sumOdd n = 1 + 3 + ... + (2 n - 1)`. -/
def sumOdd : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)

/-- The sum of the first `n` odd numbers is `n²`. Demo 3 of docs/user/DEMOS.md. -/
theorem odd_sum (n : Nat) : sumOdd n = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumOdd k + (2 * k + 1) = (k + 1) ^ 2
    rw [ih, Nat.pow_two, Nat.pow_two]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
```

**The verdicts.** `leanforth check` of Lean's export of the theorem and the
declarations it needs:

```text
1445 declarations: 1445 accepted
accepted: 1445 (experimental, not independently audited); axioms: propext, Quot.sound (allowlisted); none NOT PROVED
```

and of the wrong twin (exit status 1, as for any rejection):

```text
odd_sum: rejected
  rejected: declared type mismatch (D1-D5); diagnostic 60 at check-declaration lf-check-declaration: 0 0
```

The checker's derivation log of this theorem: *1024 steps, incomplete: truncated at step 1025 (records).* The log of a proof this size is cut at the bound `leanforth print` keeps, so no proof outline is printed; the verdict is unaffected.

## 4. Cantor's theorem

**In words.** No function f from a type α to the predicates on α is onto: for every f there is a predicate g with f a = g for no a.

**The idea.** The diagonal predicate g x = "x is not in f x" differs from every f a at the point a. If g were f a, then f a a and its negation would be the same proposition, which is absurd.

**In mathematics** (Unicode text, then rendered LaTeX):

```text
∀ (α : Type), ¬(∃ f, ∀ (g : α → Prop), ∃ a, f a = g)
```

```math
\forall (\alpha : \mathrm{Type}),\ \neg (\exists f,\ \forall (g : \alpha \to \mathrm{Prop}),\ \exists a,\ f\ a = g)
```

**In Lean**, as pinned Lean 4.35.0 prints `#check @cantor`:

```text
cantor : ∀ (α : Type), ¬∃ f, ∀ (g : α → Prop), ∃ a, f a = g
```

**In LeanForth words** (the type of the theorem as `leanforth print` writes it from Lean's export; an `axiom` form with no proof, not runnable input):

```text
axiom cantor
  0 Type explicit: α
  Not Exists 1 ^ α α Prop -> -> $ α α Prop -> -> explicit: f α Prop -> explicit: g
    Exists 1 ^ α $ α explicit: a Eq 1 ^ α Prop -> $ f a $ $ g $ fun $ forall fun $ $
end cantor
```

**The Lean proof** (`tests/demos/DemoCantor.lean`; Lean compiled it, LeanForth did not read it):

```lean
/-- Cantor's theorem: no function from `α` to the predicates on `α` is onto.
    The diagonal predicate `fun x => ¬ f x x` is not any `f a`. Demo 4 of docs/user/DEMOS.md. -/
theorem cantor (α : Type) : ¬ ∃ f : α → α → Prop, ∀ g : α → Prop, ∃ a, f a = g :=
  fun ⟨f, h⟩ =>
    let ⟨a, ha⟩ := h (fun x => ¬ f x x)
    have e : f a a = ¬ f a a := congrFun ha a
    have n : ¬ f a a := fun p => (e ▸ p) p
    n (e ▸ n)
```

**The verdicts.** `leanforth check` of Lean's export of the theorem and the
declarations it needs:

```text
16 declarations: 16 accepted
accepted: 16 (experimental, not independently audited); axioms: none
```

and of the wrong twin (exit status 1, as for any rejection):

```text
cantor: rejected
  rejected: declared type mismatch (D1-D5); diagnostic 60 at check-declaration lf-check-declaration: 0 0
```

The checker's derivation log of this theorem: *756 steps, complete. The statement is a proposition: s72 (from s3).* No outline template covers an induction proof yet, so the steps are listed instead.

## 5. The square root of 2 is irrational

**In words.** There are no natural numbers a and b with b > 0 and a² = 2 b². That is: no fraction a / b squares to 2.

**The idea.** Strong induction on b. If a² = 2 b², then a² is even, so a is even, a = 2c, and 4 c² = 2 b², so b² = 2 c² and b is even too, b = 2d, with c² = 2 d². Since 0 < d < b, the smaller pair (c, d) repeats the situation, which cannot go on forever.

**In mathematics** (Unicode text, then rendered LaTeX):

```text
¬(∃ a b, b > 0 ∧ a² = 2 · b²)
```

```math
\neg (\exists a\ b,\ b > 0 \wedge a^{2} = 2 \cdot b^{2})
```

**In Lean**, as pinned Lean 4.35.0 prints `#check @sqrt2_irrational`:

```text
sqrt2_irrational : ¬∃ a b, b > 0 ∧ a ^ 2 = 2 * b ^ 2
```

**In LeanForth words** (the type of the theorem as `leanforth print` writes it from Lean's export; an `axiom` form with no proof, not runnable input):

```text
axiom sqrt2_irrational
  Not Exists 1 ^ Nat $ Nat explicit: a Exists 1 ^ Nat $ Nat explicit: b And GT.gt 0 ^ Nat
    $ instLTNat $ b $ OfNat.ofNat 0 ^ Nat $ 0 lit# $ instOfNatNat 0 lit# $ $ $ $ Eq 1 ^
    Nat $ HPow.hPow 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $ instHPow 0 ^ 0 ^ Nat $ Nat $ instPowNat
    0 ^ Nat $ instNatPowNat $ $ $ a $ OfNat.ofNat 0 ^ Nat $ 2 lit# $ instOfNatNat 2 lit# $
    $ $ $ HMul.hMul 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $ instHMul 0 ^ Nat $ instMulNat $ $
    OfNat.ofNat 0 ^ Nat $ 2 lit# $ instOfNatNat 2 lit# $ $ $ HPow.hPow 0 ^ 0 ^ 0 ^ Nat $
    Nat $ Nat $ instHPow 0 ^ 0 ^ Nat $ Nat $ instPowNat 0 ^ Nat $ instNatPowNat $ $ $ b $
    OfNat.ofNat 0 ^ Nat $ 2 lit# $ instOfNatNat 2 lit# $ $ $ $ $ $ fun $ fun $ $
end sqrt2_irrational
```

**The Lean proof** (`tests/demos/DemoSqrt2.lean`; Lean compiled it, LeanForth did not read it):

```lean
/-- A square that is even has an even root. -/
theorem even_of_sq (a : Nat) (h : (a * a) % 2 = 0) : a % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
  · exact h0
  · exfalso
    have : (a * a) % 2 = 1 := by rw [Nat.mul_mod, h1]
    omega

/-- Descent: if `a² = 2 b²` with `b > 0`, there is a smaller such `b`. -/
theorem no_sqrt2_descent : ∀ b : Nat, ∀ a : Nat, 0 < b → a ^ 2 ≠ 2 * b ^ 2 := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro a hb h
    rw [Nat.pow_two, Nat.pow_two] at h
    obtain ⟨c, hc⟩ : ∃ c, a = 2 * c := ⟨a / 2, by have := even_of_sq a (by omega); omega⟩
    subst hc
    have e : 2 * 2 * (c * c) = 2 * (b * b) := by rw [← Nat.mul_mul_mul_comm]; exact h
    obtain ⟨d, hd⟩ : ∃ d, b = 2 * d := ⟨b / 2, by have := even_of_sq b (by omega); omega⟩
    subst hd
    have e2 : 2 * 2 * (d * d) * 2 = 2 * 2 * (c * c) := by
      rw [e, ← Nat.mul_mul_mul_comm]; omega
    have e3 : c * c = 2 * (d * d) := by omega
    exact ih d (by omega) c (by omega) (by rw [Nat.pow_two, Nat.pow_two]; exact e3)

/-- The square root of 2 is irrational: there are no `a`, `b` with `b > 0` and `a² = 2 b²`.
    Demo 5 of docs/user/DEMOS.md. -/
theorem sqrt2_irrational : ¬ ∃ a b : Nat, b > 0 ∧ a ^ 2 = 2 * b ^ 2 :=
  fun ⟨a, b, hb, h⟩ => no_sqrt2_descent b a hb h
```

**The verdicts.** `leanforth check` of Lean's export of the theorem and the
declarations it needs:

```text
1591 declarations: 1591 accepted
accepted: 1591 (experimental, not independently audited); axioms: propext, Quot.sound (allowlisted); none NOT PROVED
```

and of the wrong twin (exit status 1, as for any rejection):

```text
sqrt2_irrational: rejected
  rejected: declared type mismatch (D1-D5); diagnostic 60 at check-declaration lf-check-declaration: 0 0
```

The checker's derivation log of this theorem: *1024 steps, incomplete: truncated at step 1025 (records).* The log of a proof this size is cut at the bound `leanforth print` keeps, so no proof outline is printed; the verdict is unaffected.

## What this does not show

- The proofs are Lean's; LeanForth reads Lean's export of them and checks the
  proof terms again. The words shown are the statement printed from the export, not
  input; LeanForth text is checked since 2026-11-12, but these demos were not
  written as LeanForth input ([plan](../project/PLAN_DRAFT.md), 8.2.1 and 8.6.11).
- The proof outline (reasons between proof lines, [PROOF_OUTLINE.md](PROOF_OUTLINE.md))
  has templates for small propositional proofs only. These proofs are induction
  and arithmetic; the checker's log of each is complete or cut at the bound
  shown, and `leanforth print` says so instead of printing a partial outline.
- Number theory beyond the core library (Mathlib's primes, real numbers)
  needs the full Mathlib export; these five use only Lean's core library.

## Reproduce

```text
make test-demos          # the page and the golden file agree (no Lean needed)
make reference-demos     # pinned Lean proves, exports, LeanForth checks and prints
python3 tests/demos/test_demos.py --write   # after a change: regenerate, review the diff
```
