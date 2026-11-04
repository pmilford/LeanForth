# Two-mode program words: prototype, 2026-11-03

Evidence for [ADR 0019](../../../adr/0019-program-words-two-modes.md)
(proposed). **Throwaway code**: not reviewed, not part of `src/`, global
variables for brevity; it shows the design works, nothing more.

The same source file is loaded either with a LeanForth *correctness
vocabulary*, whose words emit IR 0.1 when Forth's interpreter runs them, or
with ordinary Forth to run it. After the owner's answers, the same was
done with a *mode shift* (Forth's own words, a third interpreter state)
and extended to defining words and loops in both designs.

## Run

From the repository root, on each Gforth:

```sh
bash docs/development/measurements/two-mode-prototype-2026-11-03/run.sh .tools/gforth/bin/gforth
```

`run-gforth-1.0.0.out` and `run-gforth-0.7.3.out` are the recorded outputs
(identical apart from the version line); `run.sh` exits 0 when every check
passes.

## Files

| File | What it is |
| --- | --- |
| `cv.fs` | The correctness vocabulary for IR 0.1 and its runner: isolation, the literal gap check, the file's own words, structure frames |
| `sym.fs` | Demo of the ADR's question 4(b): the same runner with a symbolic vocabulary |
| `ir-of.sh`, `sym-of.sh` | One source file in correctness mode (IR) or symbolic mode |
| `golden.sh` | The real `clamp.fs`, `examples.fs` and `all-primitives.fs` against `tests/program/ir/*.ir`, byte for byte |
| `run-mode.sh`, `run-mode.fs` | Run mode: the same files in plain Gforth, 19 calls checked |
| `reader_cases.py` | Replays the verdict, diagnostic and IR checks of `tests/program/ir-reader.fs` on the vocabulary |
| `adversarial.fs` | 86 hostile inputs: recognizer and number syntaxes, host words, forged structure, names, comments, a run while compiling |
| `roundtrip.py`, `awkward.ir` | IR → Forth text → correctness mode → IR, with awkward names; refusals of IR no Forth source can give |
| `ms.fs`, `ms-of.sh` | The mode shift, portable (ADR §9 (b2)): Forth's own words with verification semantics, keyed by identity, performed in a third interpreter state |
| `ms-gforth1.fs`, `g1-of.sh` | The mode shift on Gforth 1.0 only (§9 (b1)): Gforth's own interpreter in a third state (`translate-method:`) |
| `adversarial.sh`, `modes.sh` | The three designs side by side: golden IR, reader tests, hostile inputs, a redefined `MAX` |
| `v1.fs`, `v1-of.sh`, `v1.sh` | Defining words and loops (§10), given to both designs; draft IR v1 |
| `v1-demo.fs`, `v1-run.fs`, `v1-demo.ir`, `v1-adversarial.fs` | Their demo source, its run-mode checks, its draft IR v1, and 20 edge inputs |
| `run.sh` | All of the above, plus four planted faults in a copy of `cv.fs` |
| `p01-recognizers.fs`, `p02-scope.fs` | Probes: how each Gforth reads odd tokens when only one word list is visible (`gforth FILE`) |
| `p03-translations.fs`, `p04-recurse.fs` | Probes: Gforth 1.0's translation tokens; `RECURSE`'s execution token on each host |

Python here is test tooling only, as elsewhere in `tests/`.
