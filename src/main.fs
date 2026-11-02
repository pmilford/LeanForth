\ LeanForth loader: includes every current module in dependency order.
\ Usage: gforth src/main.fs   (paths resolve relative to this file).
\ Nothing loaded here is verified: the checker in kernel/ is under
\ development and counts as trusted only once the owner declares it so after
\ the review gate in AGENTS.md. Later this file becomes the command-line
\ entry point.
\ Loading leaves both stacks empty and prints nothing; tests/smoke checks it.

\ Lean data model: terms, names, universe levels and their scope, Sort
\ representation, sessions and stale-handle checks, constant references.
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

\ Checker under development: universe substitution, value and comparison;
\ candidate signatures; shift, instantiate, beta reduction, comparison,
\ conversion and type inference of mixed terms; the definition probe.
include ./kernel/level-substitute.fs
include ./kernel/level-value.fs
include ./kernel/level-compare.fs
include ./kernel/mixed-level-substitute.fs
include ./kernel/mixed-signature-probe.fs
include ./kernel/mixed-signature-audit.fs
include ./kernel/mixed-rebuild.fs
include ./kernel/mixed-shift.fs
include ./kernel/mixed-instantiate.fs
include ./kernel/mixed-beta.fs
include ./kernel/mixed-compare.fs
include ./kernel/mixed-convert.fs
include ./kernel/mixed-infer.fs
include ./kernel/mixed-definition-probe.fs

\ Staging of decoded Lean exports into the term store.
include ./import/load.fs

\ Verified-program track: example words and the stack-depth analyzer.
include ./program/clamp.fs
include ./program/examples.fs
include ./program/program-depth.fs
