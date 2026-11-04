# Re-export of `Init`, `Std` and Mathlib: measurements

Measured 2026-11-03 (local time, UTC-8) by a Claude Code agent for plan
task 3.2.4, on the machine of [the Mathlib measurements](../mathlib-2026-11-02/README.md).
The owner's question: *have we tested a LeanForth re-export of Mathlib,
followed by a re-import, and can we compare it byte for byte with Lean's
NDJSON?* The re-exporter and its format are described in
[NDJSON_READER.md, "Re-export"](../../NDJSON_READER.md#re-export).

## Result

All three exports come back **byte-identical**: the re-exported copy has
the original's SHA-256 and `cmp` finds no difference; the reader reads each
copy back into the same field-by-field dump as the original.

| Export (pinned Lean 4.35.0) | Lines | Bytes | Re-export, `gforth-fast` | Peak memory | SHA-256 of export and copy | SHA-256 of both dumps |
| --- | --- | --- | --- | --- | --- | --- |
| `Init` | 6,452,982 | 345,690,182 | 17.8 s (17.4 s user) | 14,856 KiB | `c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179` | `2ca3a7a21eed47855b810e295e9201ce2b4c3be5e2fea257b3d976e3f6c38e65` |
| `Std` | 10,193,568 | 562,170,995 | 29.2 s (28.8 s user) | 14,884 KiB | `bae74d695e165b8af16f34e66125de3177575e5c75d6b12e45982ea5a9afcbeb` | `76750d5ced59ec47e6724f7cfa454d757037a82dd460efc098e3ac4463cce14a` |
| all of Mathlib | 110,895,826 | 6,258,342,501 | 5 min 28.9 s (324.4 s user) | 20,104 KiB | `18448e5d228e385d75bf6bad5bd9208a8b561b5e395f372e85caa350211559c6` | `3cf988e8b53bc3c13944762728503a62022f3a2c663d3ff966e760f831ddd674` |

The export hashes are those recorded for the exports
([Mathlib](../mathlib-2026-11-02/README.md); `Init` and `Std` in
[NDJSON_READER.md](../../NDJSON_READER.md#measured-speed-and-memory)), and
the dumps of `Init` and Mathlib those recorded for the reader's
differentials against Python's `json` module.

## Machine and versions

AMD Ryzen 5 7600X (6 cores, 12 threads; 10 online to this WSL2 guest),
39 GiB memory, Linux 6.18.54.1-microsoft-standard-WSL2; Gforth 1.0.0
(`.tools/gforth/bin/gforth-fast`), Lean 4.35.0 (`eb6cafb7…`) with its
`leanexport` (lean4export 3.1.0); GNU coreutils `sha256sum` and diffutils
`cmp`. Single-threaded, one measurement at a time, the input in the page
cache; other agents' jobs ran on the machine at the same time, so wall
times may vary by a few percent.

## Commands

From the repository root. `Init` and `Std` were exported afresh with the
pinned toolchain (14.8 s, 0.99 GB and 27.1 s, 1.39 GB), into the
gitignored work folder `.claude/work/RX/`; their SHA-256 sums equal the
recorded ones. The Mathlib export is the owner's
`.tools/mathlib/mathlib.ndjson`, only read.

```sh
TC=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin
PATH="$TC:$PATH" "$TC/leanexport" Init >.claude/work/RX/Init.ndjson
PATH="$TC:$PATH" "$TC/leanexport" Std >.claude/work/RX/Std.ndjson
M=docs/development/measurements/reexport-2026-11-03/measure.sh
REIMPORT=1 $M Init .claude/work/RX/Init.ndjson .claude/work/RX
REIMPORT=1 $M Std .claude/work/RX/Std.ndjson .claude/work/RX
REIMPORT=1 TO=3600 $M Mathlib .tools/mathlib/mathlib.ndjson .claude/work/RX
```

[`measure.sh`](measure.sh) runs, for an export `EXPORT` and its copy
`OUT/NAME.copy.ndjson`:

```sh
/usr/bin/time -v .tools/gforth/bin/gforth-fast src/import/ndjson-emit.fs \
  -e 's" EXPORT" s" OUT/NAME.copy.ndjson" reexport bye'
sha256sum EXPORT OUT/NAME.copy.ndjson
cmp EXPORT OUT/NAME.copy.ndjson
/usr/bin/time -v .tools/gforth/bin/gforth-fast tests/core/ndjson-dump.fs \
  -e 's" EXPORT" dump-export bye' | sha256sum        # and the same for the copy
```

`scripts/ndjson-reexport.sh --reimport EXPORT COPY` does the same in one
command (`make reexport EXPORT=… COPY=…`), and reports the first differing
line and byte when there is one. The copies (6.26 GB for Mathlib; the disk
had 150 GB free) were deleted by name afterwards.

## Logs

RESULT_LOGS

## Earlier run

The first version of the re-exporter (before mdata's members were sorted,
before a failed line took its bytes back, and before every record went
through one dispatching handler) was measured the same way a quarter of
an hour earlier, with the same results: all three byte-identical, the same
SHA-256 sums and dumps; `Init` 20.7 s and 14,856 KiB, `Std` 33.9 s and
14,840 KiB, Mathlib 5 min 21.3 s (314.3 s user) and 20,196 KiB. The
differences in time are within what the machine's other work causes.

## What the numbers say

- Re-exporting takes about three times as long as reading alone: counting
  all of Mathlib with the same reader took 1 min 43 s to 1 min 49 s
  ([NDJSON_READER.md](../../NDJSON_READER.md#measured-speed-and-memory)),
  so writing takes about two thirds of a re-export. The JSON writer checks
  every call (state, room, UTF-8, the order of every key) and passes each
  piece of a line to its sink; it has not been tuned.
- Memory is flat: Gforth's image, the reader's line buffer and tape, and
  the output buffer, each grown to the longest line (Mathlib's is a
  2.7 MB string, which gives the larger peak).
- The dump, the reader alone writing every field as text, takes about
  half as long as the re-export.
