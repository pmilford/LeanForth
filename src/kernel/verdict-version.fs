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
\
\ [kernel] code: experimental, not through the review gate.
\ State: none.

1 constant lf-verdict-version
