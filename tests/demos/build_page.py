"""Build docs/user/DEMOS.md from tests/demos/demos.golden (plan task 8.6.6).

Usage: python3 tests/demos/build_page.py [--write | --check]   (from the repository root)

The page is made only from the golden file (what pinned Lean and LeanForth
printed, written by tests/demos/test_demos.py --write), the Lean sources of
tests/demos and the prose below, so every number, verdict and formula on it is
output of a run, not typed. --check (make test; no Lean needed) fails when the
committed page differs from this script's page; --write rewrites it.
"""
import pathlib
import sys

HERE = pathlib.Path("tests/demos")
GOLDEN = HERE / "demos.golden"
PAGE = pathlib.Path("docs/user/DEMOS.md")

DEMOS = [
    {"id": "AddComm", "module": "DemoAddComm", "theorem": "add_comm_by_induction",
     "title": "Addition does not care about order",
     "claim": "For all natural numbers m and n, m + n = n + m.",
     "idea": ("Induction on n. For n = 0 both sides are m. If the claim holds for k, then "
              "m + (k + 1) = (m + k) + 1 = (k + m) + 1 = (k + 1) + m, using the rules "
              "`Nat.add_succ` and `Nat.succ_add` that define addition one step at a time."),
     },
    {"id": "Gauss", "module": "DemoGauss", "theorem": "gauss_sum",
     "title": "Gauss's sum",
     "claim": ("Twice the sum 0 + 1 + ... + n is n (n + 1). Here `sumTo n` is that sum, "
               "defined by `sumTo 0 = 0` and `sumTo (k + 1) = sumTo k + (k + 1)`."),
     "idea": ("Induction on n. For n = 0 both sides are 0. For n = k + 1, twice the sum is "
              "2 (sumTo k) + 2 (k + 1) = k (k + 1) + 2 (k + 1) = (k + 1) (k + 2), "
              "where the middle step is the claim for k."),
     },
    {"id": "OddSum", "module": "DemoOddSum", "theorem": "odd_sum",
     "title": "The first n odd numbers add up to n squared",
     "claim": ("1 + 3 + 5 + ... + (2n - 1) = n². Here `sumOdd n` is that sum, defined by "
               "`sumOdd 0 = 0` and `sumOdd (k + 1) = sumOdd k + (2 k + 1)`."),
     "idea": ("Induction on n. For n = 0 both sides are 0. For n = k + 1: "
              "k² + (2 k + 1) = (k + 1)², by expanding the square."),
     },
    {"id": "Cantor", "module": "DemoCantor", "theorem": "cantor",
     "title": "Cantor's theorem",
     "claim": ("No function f from a type α to the predicates on α is onto: for every f "
               "there is a predicate g with f a = g for no a."),
     "idea": ("The diagonal predicate g x = \"x is not in f x\" differs from every f a at the "
              "point a. If g were f a, then f a a and its negation would be the same "
              "proposition, which is absurd."),
     },
    {"id": "Sqrt2", "module": "DemoSqrt2", "theorem": "sqrt2_irrational",
     "title": "The square root of 2 is irrational",
     "claim": ("There are no natural numbers a and b with b > 0 and a² = 2 b². "
               "That is: no fraction a / b squares to 2."),
     "idea": ("Strong induction on b. If a² = 2 b², then a² is even, so a is even, a = 2c, "
              "and 4 c² = 2 b², so b² = 2 c² and b is even too, b = 2d, with c² = 2 d². "
              "Since 0 < d < b, the smaller pair (c, d) repeats the situation, "
              "which cannot go on forever."),
     },
]

INTRO = """# Five small proofs, proved by Lean and re-checked

Five well-known results, each stated in mathematical notation, in Lean and in
LeanForth words. **Lean 4.35.0 proves each theorem; LeanForth re-checks the
proof terms in Lean's export** and rejects a deliberately wrong copy. You do
not need to know Lean or Forth to read the mathematics.

**What this page does and does not show.** LeanForth checks proofs that Lean
produced and exported. LeanForth text cannot yet be checked by LeanForth's
kernel (plan 8.2.1 and 8.6.11 are not built), so nothing here was proved from
LeanForth input. The "LeanForth words" below are the statement printed from
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

"""

OUTRO = """## What this does not show

- The proofs are Lean's; LeanForth reads Lean's export of them and checks the
  proof terms again. LeanForth text cannot yet be checked: the words shown are the
  statement printed from the export, not input, and LeanForth has proved nothing from
  its own input ([plan](../project/PLAN_DRAFT.md), 8.2.1 and 8.6.11).
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
"""


def sections(golden):
    """The golden file's sections: {id: {name: text}}."""
    found = {}
    for chunk in golden.split("== ")[1:]:
        ident, _, rest = chunk.partition("\n")
        parts = {}
        for piece in rest.split("-- ")[1:]:
            name, _, text = piece.partition("\n")
            parts[name] = text.rstrip("\n")
        found[ident] = parts
    return found


def field(printed, label):
    for line in printed.splitlines():
        if line.startswith(f"  {label}:"):
            return line.split(":", 1)[1].strip()
    raise KeyError(label)


def leanforth_words(printed):
    """The LeanForth form's block, without its indentation."""
    block, inside = [], False
    for line in printed.splitlines():
        if line.startswith("    axiom "):
            inside = True
        if inside:
            block.append(line[4:])
        if line.startswith("    end "):
            break
    return "\n".join(block)


def unquote(math):
    return math[1:-1] if math.startswith("$") and math.endswith("$") else math


def outline_note(log):
    """Why `leanforth print` has no proof outline for the demo, from its log line."""
    if "incomplete" in log:
        return ("The log of a proof this size is cut at the bound `leanforth print` keeps, so "
                "no proof outline is printed; the verdict is unaffected.")
    return "No outline template covers an induction proof yet, so the steps are listed instead."


def demo_section(number, demo, parts):
    printed = parts["print"]
    source = (HERE / f"{demo['module']}.lean").read_text(encoding="utf-8").rstrip("\n")
    log = field(printed, "Checker log")
    first_wrong = parts["wrong twin"].splitlines()
    return f"""## {number}. {demo['title']}

**In words.** {demo['claim']}

**The idea.** {demo['idea']}

**In mathematics** (Unicode text, then rendered LaTeX):

```text
{field(printed, "Statement in math text")}
```

```math
{unquote(field(printed, "Statement in mathematics"))}
```

**In Lean**, as pinned Lean 4.35.0 prints `#check @{demo['theorem']}`:

```text
{parts['lean']}
```

**In LeanForth words** (the type of the theorem as `leanforth print` writes it from Lean's export; an `axiom` form with no proof, not runnable input):

```text
{leanforth_words(printed)}
```

**The Lean proof** (`tests/demos/{demo['module']}.lean`; Lean compiled it, LeanForth did not read it):

```lean
{source}
```

**The verdicts.** `leanforth check` of Lean's export of the theorem and the
declarations it needs:

```text
{parts['check']}
```

and of the wrong twin (exit status {first_wrong[0]}, as for any rejection):

```text
{chr(10).join(first_wrong[1:])}
```

The checker's derivation log of this theorem: *{log}* {outline_note(log)}

"""


def page(golden_text):
    found = sections(golden_text)
    body = "".join(demo_section(number, demo, found[demo["id"]])
                   for number, demo in enumerate(DEMOS, 1))
    return INTRO + body + OUTRO


def main(argument):
    text = page(GOLDEN.read_text(encoding="utf-8"))
    if argument == "--write":
        PAGE.write_text(text, encoding="utf-8")
        print(f"wrote {PAGE}")
        return 0
    if PAGE.read_text(encoding="utf-8") != text:
        print(f"{PAGE} differs from tests/demos/build_page.py's page (run it with --write)")
        return 1
    print(f"{PAGE}: the page is what the golden file and the Lean sources make; {len(DEMOS)} demos")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "--check"))
