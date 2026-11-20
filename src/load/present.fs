\ Layer entry: presentation, on the general library (lib/) and Lean's data
\ model (core/), never the kernel: the term printer and its side table, and
\ the proof outline printed from the derivation log (untrusted output; the
\ checker loads only the log itself, src/core/derivation-log.fs).
\ src/main.fs loads it after src/load/program.fs.
require ../present/term-printer.fs
require ../present/log-check.fs
require ../present/proof-outline.fs
