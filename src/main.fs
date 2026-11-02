\ LeanForth loader. It requires only the top modules, the ones no other
\ module requires; each module requires its own direct dependencies, so the
\ whole data model, library and checker under development load with them.
\ Usage: gforth src/main.fs   (paths resolve relative to this file).
\ Nothing loaded here is verified: the checker in kernel/ is under
\ development and counts as trusted only once the owner declares it so after
\ the review gate in AGENTS.md. Later this file becomes the command-line
\ entry point.
\ Loading leaves both stacks empty and prints nothing; tests/smoke checks it.

\ The checker under development, through its outermost probe: definition
\ checking, which requires inference, conversion, the rebuild passes,
\ signatures, level algorithms and the Lean data model.
require ./kernel/mixed-definition-probe.fs

\ Staging of decoded Lean exports into the term store.
require ./import/load.fs

\ Verified-program track: example words and the stack-depth analyzer.
require ./program/clamp.fs
require ./program/examples.fs
require ./program/program-depth.fs
