\ The verdict version (ADR 0020 D3; plan task 6.2.5, step SN3): one
\ number naming the checker's rules, written into every checked-environment
\ snapshot (kernel/env-snapshot.fs) and compared when one is loaded: a
\ snapshot written under another verdict version is refused as stale
\ (unsupported), so a loaded verdict is always one this build's rules give.
\
\ What it covers: every field a snapshot stores for a declaration except
\ its diagnostic -- the outcome, the axiom bits, the dependencies, the
\ lookups and their answers (environment.fs, "Lookups"), the warnings,
\ recipe and shape, the skipped and added marks, and the fuel used.
\ Bump it for any change that could change one of them for any
\ declaration: a Lean rule or its order, the fuel model or what a step
\ costs, an audit that can refuse, the lookup rules (ADR 0012 E5) or what
\ a check looks up, the axiom allowlist, the block check's derived fields,
\ the importer's reading of an export. Keep it only for a change that
\ cannot change them by construction (printing, reports, the command line,
\ I/O, documentation, tests, a speed change that keeps every fuel count
\ and lookup), shown by the both-ways comparison of ADR 0020 D3 (identical
\ stored fields for every declaration of Init, the arena and a fixed
\ Mathlib prefix, between a fresh check with the change and a snapshot
\ written before it); the commit records that evidence and the review
\ checks it. A bump makes every older snapshot stale: write them again.
\
\ Changelog (newest last; each bump with its reason):
\   1  2026-11-11  the first snapshot format (step SN3): the rules of
\                  main at 233916d, with lookups recorded.
\   2  2026-11-11  plan step SN5: the lookups of names a check made beyond
\                  its input (a nested block's auxiliary types) are kept as
\                  those names (written after the tier's names), no longer
\                  as the one key 2^32 - 1; no outcome or fuel changes.
\   3  2026-11-11  agent PF (ADR 0014 Amendment 6): an application's
\                  argument is not closed for a Pi body without loose
\                  bound variables, so fuel counts fall (97 declarations
\                  of the pinned exports use less, none more); and the
\                  command line's default fuel per declaration is
\                  100,000,000 (owner, 2026-11-11), so a declaration
\                  that ran out at 20,000,000 may now be decided.
\   5  2026-11-11  agent R5 (ADR 0014 Amendment 8; 4 is agent PF's
\                  Amendment 7, branch pf-perf: renumber at merge if
\                  needed): infer-only inference types an application
\                  from its spine's head, as Lean's infer_app does, so
\                  fuel counts fall (the pinned exports: every report the
\                  same but for fuel, which only fell); no verdict.
\
\ [kernel] code: experimental, not through the review gate.
\ State: none.

5 constant lf-verdict-version
