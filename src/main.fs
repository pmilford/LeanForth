\ LeanForth loader and command-line entry point. It requires only the top
\ modules, the ones no other module requires; each module requires its own
\ direct dependencies, so the whole data model, library and checker under
\ development load with them.
\ Usage: gforth src/main.fs   (paths resolve relative to this file), or,
\ as bin/leanforth runs it, gforth src/main.fs -e cli-main COMMAND ...
\ (src/cli/leanforth.fs, docs/user/COMMAND_LINE.md).
\ Nothing loaded here is verified: the checker in kernel/ is under
\ development and counts as trusted only once the owner declares it so after
\ the review gate in AGENTS.md.
\ Loading leaves both stacks empty and prints nothing; tests/smoke checks it.

\ The checker under development, through its outermost probe: definition
\ checking, which requires inference, conversion, the rebuild passes,
\ signatures, level algorithms and the Lean data model.
require ./kernel/mixed-definition-probe.fs

\ The first checker: check-declaration (plan task 2.2.3), which requires
\ the checked environment v0 (ADR 0012: the input marks, write-once slots,
\ snapshots and handles, and the single publisher) and inference in
\ environment mode.
require ./kernel/check-declaration.fs

\ Staging of decoded Lean exports into the term store, and the reader of
\ lean4export NDJSON files.
require ./import/load.fs
require ./import/ndjson.fs

\ Verified-program track: example words, the stack-depth analyzer, the
\ reader from restricted Forth source to the program IR and its interpreter.
require ./program/clamp.fs
require ./program/examples.fs
require ./program/program-depth.fs
require ./program/ir-reader.fs
require ./program/ir-run.fs

\ Presentation: the term printer and its side table (untrusted output).
require ./present/term-printer.fs

\ The command line: check, count, reexport, version, capabilities. It
\ loads the staging of exports into the checker's input, the counter, the
\ re-exporter and the manifest check.
require ./cli/leanforth.fs
