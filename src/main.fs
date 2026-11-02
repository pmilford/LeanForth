\ LeanForth loader: includes every current module in dependency order.
\ Usage: gforth src/main.fs   (paths resolve relative to this file).
\ Nothing loaded here is a trusted checker. src/kernel/ stays empty until
\ code passes the review gate in AGENTS.md; superseded code in src/legacy/
\ is not loaded. Later this file becomes the command-line entry point.
\ Loading leaves both stacks empty and prints nothing; tests/smoke checks it.

\ Lean data model and operations: terms, names, universe levels, sessions
\ and handles, constant references, then the substitution, reduction,
\ comparison, conversion and inference passes built on them.
include ./core/terms.fs
include ./core/names.fs
include ./core/levels.fs
include ./core/level-scope.fs
include ./core/tagged-sort-boundary.fs
include ./core/symbolic-session.fs
include ./core/generation-handles.fs
include ./core/constant-references.fs
include ./core/constant-term-boundary.fs
include ./core/constant-term-scope.fs
include ./core/level-substitute.fs
include ./core/level-value.fs
include ./core/level-compare.fs
include ./core/mixed-level-substitute.fs
include ./core/mixed-signature-probe.fs
include ./core/mixed-signature-audit.fs
include ./core/mixed-shift.fs
include ./core/mixed-instantiate.fs
include ./core/mixed-beta.fs
include ./core/mixed-compare.fs
include ./core/mixed-convert.fs
include ./core/mixed-infer.fs
include ./core/mixed-definition-probe.fs

\ Staging of decoded Lean exports into the term arena.
include ./import/load.fs

\ Verified-program track: example words and the stack-depth analyzer.
include ./program/clamp.fs
include ./program/examples.fs
include ./program/program-depth.fs
