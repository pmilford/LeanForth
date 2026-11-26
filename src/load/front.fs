\ Layer entry: the front end (ADR 0021, plan FE1; untrusted, never loaded by
\ the kernel), on the general library, the data model, the presentation,
\ the authoring words and the importer stage's names, never the kernel or
\ the command line: the metavariable context and the Meta layer (plan
\ FE1c): level unification, bound-variable instantiation and abstraction,
\ level simplification and normalization, universe-parameter
\ instantiation, the view of the environment (reducibility and unfolding
\ under each transparency), whnfCore and the first cases of type
\ inference; the tactic framework's goals, each with its own local
\ context, the goal list and their text (plan FE1g-1); the instance table
\ and its discrimination-tree keys over the elaboration data (plans FE1e2,
\ FE1e3); unfolding one definition (unfoldDefinition?) and lazy delta
\ reduction in unification (isDefEqDelta, which sets defeq.fs's hook: plan
\ S2); and, through them, the natural reader (front/reader.fs). A test that
\ opens a library or hands declarations to the kernel also requires
\ src/load/checker.fs before this file and src/cli/check-lf.fs after it.
\ src/main.fs loads it after src/load/present.fs.
require ../front/level-map.fs
require ../front/mvars.fs
require ../front/meta-config.fs
require ../front/level-defeq.fs
require ../front/offset-walk.fs
require ../front/instantiate.fs
require ../front/level-simp.fs
require ../front/level-params.fs
require ../front/level-normalize.fs
require ../front/lib-decode.fs
require ../front/meta-env.fs
\ Simp's elaboration data (format 4's congr kind; plan FE9 slice SD-a;
\ format 4.1's default simp set, simp group 4).
require ../front/simp-data.fs
require ../front/simp-set-data.fs
require ../front/term-find.fs
require ../front/unfold.fs
require ../front/whnf.fs
require ../front/beta-inst.fs
require ../front/infer.fs
require ../front/defeq-delta.fs
require ../front/goal-print.fs
require ../front/instances.fs
\ Simp's congruence argument kinds (plan FE9 slice SL1a-1).
require ../front/congr-thms.fs
\ Instance search (plan FE1e5), which sets defeq.fs's synthesis hooks.
require ../front/synth.fs
\ The elaborator (plan S1, FE1e6-7): pending instance problems and default
\ instances, applications, terms, and the glue that elaborates natural
\ declarations, by-exact's terms and #check (front/elab-decl.fs sets the
\ reader's, the hand-over's and the tactics' hooks).
require ../front/elab-pending.fs
require ../front/elab-app.fs
require ../front/elab-term.fs
require ../front/elab-decl.fs
\ S2's rewriting's Meta words (branch s2-tactics; its tactics, induction
\ and case are files of front/tactics/ on the tactic library since plan
\ 9.4.8l I).
require ../front/kabstract.fs
require ../front/meta-check.fs
\ The step log the runner keeps (branch s2-steps), written by check --steps.
require ../front/step-log.fs
\ The tactics that register themselves (tactic plug-in design, slices
\ a2-ii and a2-iii): by-apply, by-assumption, by-constructor, on the
\ tactic library and its goal operations (front/meta-tactic/).
require ../front/tactics/all.fs
