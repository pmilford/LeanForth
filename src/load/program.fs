\ Layer entry: the verified-program track, on the general library (lib/)
\ alone: the example words, the stack-depth analyzer and the program IR's
\ interpreter. The IR 0.1 reader (program/ir-reader.fs) is the tests'
\ oracle only and is not loaded here (review R1, 2026-11-18): leanforth
\ verify reads Forth with program/verify.fs, which scripts/program_verify.py
\ loads. src/main.fs loads it after src/load/checker.fs.
require ../program/clamp.fs
require ../program/examples.fs
require ../program/program-depth.fs
require ../program/ir-run.fs
