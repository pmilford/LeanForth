# IR 0.2 probes (2026-11-04)

Throwaway evidence for [ADR 0019 Amendment 1](../../../adr/0019-program-words-two-modes.md#amendment-1-proposed-ir-02-redefinition-output-words-and-sha-2):
what plain Gforth 1.0.0 and 0.7.3 do with redefined words, output words,
shifts and number prefixes, and two Lean checks of the proofs the
amendment plans. Nothing here is in `src/` or in `make test`; nothing of
IR 0.2 is implemented.

| File | What it shows |
| --- | --- |
| `p01-redefine.fs` | Early binding: words compiled before a redefinition keep the old version, later ones get the new; a definition is hidden until its `;`, so its own name inside it is the previous version (or undefined, −13); names fold case; constants; `RECURSE` in a redefinition; `SEARCH-WORDLIST` finds the newest of two headers and the older execution token still runs; `.` and `DUP` redefined |
| `p02-output.fs` | What `.`, `U.`, `CR`, `SPACE`, `SPACES` (also 0 and −2), `."`, `S" … " TYPE` and `.S` (0, 3 and 12 cells) print; `.` in `BASE` 16; the stack each leaves; a `#>` string after `.`; `.(` inside a definition |
| `p03-emit.fs` | The bytes `EMIT` writes for 65, 0, 9, 200, 255, 321, 955 and −1 (shown as numbers by `run.sh`) |
| `p04-shifts-literals.fs` | `LSHIFT` and `RSHIFT` by 0, 63, 64, 65, 127 and −1; how each host reads `$10`, `$-10`, `-$10`, `#-10`, `%-101`, `'a'`, 32-bit and 64-bit constants and Gforth's own forms (`1_000`, `0x10`); whether `-rot`, `.s` and the output words are host words |
| `p05-debug.fs` | The owner's case: `lf-clamp` with `dup .` added, and the real `lf-clamp` wrapped by a second version of its name that shows the stack before and after calling the first |
| `p06-debug-pair.lean`, `debug-pair.sh` | The clamp proof of `tests/reference/program-ir.lean`, copied unchanged, proves the clamp with `dup .` added (`.` written as its IR 0.2 stack effect, `prim .drop`); with `.` planted as doing nothing, Lean rejects it |
| `p07-rotr.lean` | `sha-rotr`'s arithmetic: or'ing the shifts and masking with 2^32 − 1 is FIPS 180-4's ROTR on every cell width of at least 32 bits (`rotr_masked`), and the instructions of `sha-rotr` and `sha-w32`, with `LSHIFT` as IR 0.2 would define it, leave ROTR on 64-bit cells (`rotr_cells64`); without the mask they do not (`unmasked_rotr_wrong`) |
| `p08-closed-stdout.sh` | `.` with standard output closed, and with a pipe whose reader has gone (one `.`, then 100,000) |

## Results

`run-gforth-1.0.0.out` and `run-gforth-0.7.3.out` hold the output of
`run.sh` on each host. Their standard output is identical except for
three number forms outside Forth-2012 (`-$10`: 1.0 refuses it, 0.7.3
reads −16; `1_000` and `$1_0`: 1.0 reads them, 0.7.3 refuses them);
Gforth's "redefined" warnings go to standard error on both, in different
layouts. `p08-closed-stdout.out` is the same on both hosts: with standard
output closed, `.` returns normally (THROW code 0, output lost); with a
broken pipe, one `.` returns normally (buffered) and 100,000 end in
THROW −2049. `lean.out` holds the two Lean checks: probe 6 accepted
(axioms `propext`, `Classical.choice`, `Quot.sound`) and, with the planted
fault, rejected (exit 1); probe 7 accepted, every theorem within the
three standard axioms.

## Reproduction

From the repository root:

```sh
D=docs/development/measurements/ir-0.2-probes-2026-11-04
bash $D/run.sh .tools/gforth/bin/gforth
bash $D/run.sh GFORTH_0_7_3_WRAPPER
bash $D/p08-closed-stdout.sh .tools/gforth/bin/gforth
bash $D/p08-closed-stdout.sh GFORTH_0_7_3_WRAPPER
LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
bash $D/debug-pair.sh $LEAN
bash $D/debug-pair.sh $LEAN fault
$LEAN -DwarningAsError=true $D/p07-rotr.lean
```

Hosts: Gforth 1.0.0 (`.tools/gforth`, amd64) and Gforth 0.7.3 (Ubuntu's
package, extracted locally, as CI uses); Lean 4.35.0; Linux under WSL2,
64-bit cells.
