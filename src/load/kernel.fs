\ Layer entry: the checker under development and what it stands on, the
\ general library (lib/) and Lean's data model (core/), and nothing else.
\ Its two top modules: the definition and theorem probe, which requires
\ inference, conversion, the rebuild passes, signatures, level algorithms
\ and the data model; and the first checker, check-declaration (plan task
\ 2.2.3), which requires the checked environment v0 (ADR 0012: the input
\ marks, write-once slots, snapshots and handles, and the single publisher)
\ and inference in environment mode.
\ A test of the kernel loads this file, not src/main.fs, so that a change
\ above the kernel (the front end, the command line) does not re-run it
\ (scripts/tested-tree.py; scripts/check-layers.py keeps the layering).
\ src/main.fs loads it first, through src/load/checker.fs. Loading leaves
\ both stacks empty and prints nothing.
require ../kernel/mixed-definition-probe.fs
require ../kernel/check-declaration.fs
