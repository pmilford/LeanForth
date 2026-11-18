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

\ The importer stage (ADR 0016 C9 step 2): an export, checked against its
\ manifest, staged into a compact input tier (core/compact*.fs) with its
\ declarations; it declares no context member and allocates nothing while
\ loading. The feed (C9 step 3, plan task 3.2.2) makes a sealed stage the
\ checker's input in file order, its names read from the input tier.
require ./import/stage.fs
require ./import/feed.fs
\ The input tier saved to and loaded from a sectioned file (ADR 0020, plan
\ step SN2); a fresh check runs none of it.
require ./import/snapshot-tier.fs
\ The checked environment saved and loaded with it, its verdict version
\ (ADR 0020, plan step SN3); a fresh check without --save-snapshot runs
\ none of it.
require ./kernel/verdict-version.fs
require ./kernel/env-snapshot.fs
require ./kernel/env-import.fs

\ Verified-program track: example words, the stack-depth analyzer, the
\ reader from restricted Forth source to the program IR and its interpreter.
require ./program/clamp.fs
require ./program/examples.fs
require ./program/program-depth.fs
require ./program/ir-reader.fs
require ./program/ir-run.fs

\ Presentation: the term printer and its side table, and the proof outline
\ printed from the derivation log (untrusted output; the checker loads
\ only the log itself, src/core/derivation-log.fs).
require ./present/term-printer.fs
require ./present/log-check.fs
require ./present/proof-outline.fs

\ The front end (ADR 0021, plan FE1; untrusted, never loaded by the
\ kernel): the natural reader (front/reader.fs, which the command line
\ loads through cli/check-lf.fs), the metavariable context, and the first
\ pieces of the Meta layer (plan FE1c): level unification, bound-variable
\ instantiation and abstraction, level simplification and normalization,
\ universe-parameter instantiation, the view of the environment
\ (reducibility and unfolding under each transparency), whnfCore and the
\ first cases of type inference; the tactic framework's goals, each with
\ its own local context, the goal list and their text (plan FE1g-1); the
\ instance table and its discrimination-tree keys over the elaboration
\ data (plans FE1e2, FE1e3); unfolding one definition (unfoldDefinition?)
\ and lazy delta reduction in unification (isDefEqDelta, which sets
\ defeq.fs's hook: plan S2).
require ./front/level-map.fs
require ./front/mvars.fs
require ./front/meta-config.fs
require ./front/level-defeq.fs
require ./front/instantiate.fs
require ./front/level-simp.fs
require ./front/level-params.fs
require ./front/level-normalize.fs
require ./front/lib-decode.fs
require ./front/meta-env.fs
require ./front/term-find.fs
require ./front/unfold.fs
require ./front/whnf.fs
require ./front/beta-inst.fs
require ./front/infer.fs
require ./front/defeq-delta.fs
require ./front/goal-print.fs
require ./front/instances.fs
\ Instance search (plan FE1e5), which sets defeq.fs's synthesis hooks.
require ./front/synth.fs
\ The elaborator (plan S1, FE1e6-7): pending instance problems and default
\ instances, applications, terms, and the glue that elaborates natural
\ declarations, by-exact's terms and #check (front/elab-decl.fs sets the
\ reader's, the hand-over's and the tactics' hooks).
require ./front/elab-pending.fs
require ./front/elab-app.fs
require ./front/elab-term.fs
require ./front/elab-decl.fs
\ S2's tactics (branch s2-tactics): rewriting (kabstract, Meta.check) and
\ induction with its alternatives, rows of the runner.
require ./front/kabstract.fs
require ./front/meta-check.fs
require ./front/tactic-rewrite.fs
require ./front/tactic-induction.fs
\ The step log the runner keeps (branch s2-steps), written by check --steps.
require ./front/step-log.fs

\ The command line: check, replay, print, count, reexport, version,
\ capabilities. It loads the staging of exports into the checker's input,
\ the counter, the re-exporter, the manifest check and print's proof
\ outlines (cli/print.fs).
require ./cli/print.fs
require ./cli/leanforth.fs
