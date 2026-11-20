\ LeanForth loader and command-line entry point. It requires the layer
\ entries of src/load/ and the command line, the modules no other module
\ requires; each module requires its own direct dependencies, so the whole
\ data model, library and checker under development load with them.
\ Usage: gforth src/main.fs   (paths resolve relative to this file), or,
\ as bin/leanforth runs it, gforth src/main.fs -e cli-main COMMAND ...
\ (src/cli/leanforth.fs, docs/user/COMMAND_LINE.md).
\ Nothing loaded here is verified: the checker in kernel/ is under
\ development and counts as trusted only once the owner declares it so after
\ the review gate in AGENTS.md.
\ Loading leaves both stacks empty and prints nothing; tests/smoke checks it.
\ The entries load in this order, each after the layers below it, so every
\ definition comes in the same order as when this file listed the modules
\ itself; a test loads the smallest entry it needs, so that a change in a
\ higher layer does not re-run it (scripts/tested-tree.py), and
\ scripts/check-layers.py keeps each entry to its layers.

\ The checker: the kernel (src/load/kernel.fs), the importer
\ (src/load/import.fs) and the checked environment's snapshots.
require ./load/checker.fs

\ Verified-program track: example words, the stack-depth analyzer and the
\ program IR's interpreter.
require ./load/program.fs

\ Presentation: the term printer and its side table, and the proof outline
\ printed from the derivation log.
require ./load/present.fs

\ The front end (ADR 0021; untrusted, never loaded by the kernel): the Meta
\ layer, the elaborator and the tactics.
require ./load/front.fs

\ The command line: check, replay, print, count, reexport, version,
\ capabilities. It loads the staging of exports into the checker's input,
\ the counter, the re-exporter, the manifest check and print's proof
\ outlines (cli/print.fs), and the check of LeanForth text (cli/check-lf.fs).
require ./cli/print.fs
require ./cli/leanforth.fs
