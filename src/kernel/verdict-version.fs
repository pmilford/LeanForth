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
\   4  2026-11-11  agent PF (ADR 0014 Amendment 7; review rvSN4 B1): a
\                  check's fuel no longer depends on the other records of
\                  the tier: each == class of input binders is one node,
\                  and in a check a node or level made before it is given
\                  for an equal one only once the check reached it. Fuel
\                  moves (Init: +0.34% in all, 48,397 declarations more,
\                  5 less), no verdict.
\   5  2026-11-11  agent R5 (ADR 0014 Amendment 9): infer-only inference types an application
\                  from its spine's head, as Lean's infer_app does, so
\                  fuel counts move, mostly down (the pinned exports:
\                  every report the same but for fuel, which only fell;
\                  Init: -0.99% in all, 31,418 declarations less, 27
\                  more); no verdict.
\   6  2026-11-11  agent NS: an inductive block's walks (the audit, T0,
\                  C1, the occurrence tests of the scope, positivity and
\                  the recursor) meet each shared node once, and B3 and
\                  the nested keys compare by Lean's == (each pair once),
\                  as Lean's for_each and expr_eq_fn do: blocks use less
\                  fuel (41 declarations of the pinned exports less, none
\                  more), so five Navier-Stokes structures that ran out at
\                  100,000,000 are decided; Init's verdicts are unchanged.
\   7  2026-11-12  agent FXK (review rvKN 1 and 2): C1 walks each (node,
\                  binder depth) pair once, as Lean's for_each with an
\                  offset (before, a node met again at an earlier depth
\                  was walked again with its subterm, up to exponentially
\                  often), and the occurrence walk inside the nested-
\                  occurrence walk no longer erases that walk's marks:
\                  blocks use less fuel (Init: one declaration 4 units
\                  less, none more, every other field the same; the
\                  pinned exports unchanged); no verdict.
\   8  2026-11-12  review MO: a nested block's translation, lowering and
\                  restoration keep each (node, offset) pair's result for
\                  the rest of their call, as Lean's replace does (before,
\                  every path was walked, up to exponentially often):
\                  nested blocks use less fuel (the pinned exports: 3
\                  declarations less, none more, every other field the
\                  same; Init: Lean.Syntax 2 units less, every other
\                  record the same); no verdict.
\
\ [kernel] code: experimental, not through the review gate.
\ State: none.

8 constant lf-verdict-version
