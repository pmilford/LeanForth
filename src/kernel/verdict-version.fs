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
\   9  2026-11-12  agent CK (plan task 4.2.7d; review rvKN 3; ADR 0014
\                  Amendment 10): inference aside types no lambda's
\                  domain, as Lean's infer-only infer_lambda; what Lean's
\                  infer-only typing throws (typeExpected, funExpected,
\                  invalidProj) rejects aside too (was unknown); and is_def_eq
\                  types a Pi with its typer where Lean's infer_type does
\                  (proof irrelevance, eta, unit-like types), as infer_pi may
\                  throw on an ill-typed Pi (was taken as a type: an export
\                  Lean rejects was accepted). Fuel moves (the pinned
\                  exports: unfold's impliesSelf 65 -> 68, every other
\                  report the same; Init: +0.03% in all, 5,873
\                  declarations more, 3,647 less, every other field the
\                  same); verdicts only on ill-typed reducts
\                  (tests/cli/shared-depths.lean P5).
\
\ The reach of each step (ADR 0020 Amendment 5; docs/design/
\ SNAPSHOT_COMPATIBILITY.md R1 and R3; plan step 6.2.5c1). A build takes
\ the results of a snapshot whose verdict version V is older than its own
\ but inside the window (lf-snapshot-window versions back) only for the
\ declarations outside the reach of every step V+1 to its own, and checks
\ the rest again (the carry pass, kernel/env-import.fs). Each step has an
\ entry in lf-verdict-steps: its version, its reach bits and a list of
\ names (0: none). A declaration is in a step's reach when any of the
\ step's bits holds for it, each decided from the snapshot alone:
\   reach-all            always
\   reach-kind-definition, -theorem, -opaque, -axiom, -quotient
\                        it is of that kind
\   reach-block-any      it is a member of an inductive block, or one of
\                        its lookups was answered by a member's slot or a
\                        generated recursor's holder
\   reach-block-nested   as reach-block-any, for blocks with auxiliary types
\   reach-block-mutual   as reach-block-any, for blocks of several types
\   reach-literal-nat, reach-literal-string, reach-projection, reach-let
\                        the construct is in its terms or in those of a
\                        declaration its lookups answered
\   reach-quotient       a lookup of the quotient's state, or answered by
\                        the quotient's slots
\   reach-scratch-names  a lookup key names a name beyond the input
\   reach-not-accepted   its saved outcome is not accepted
\   reach-names          a lookup key names one of the entry's names
\ The obligation on an entry (S-R): every check that can run code the step
\ changed satisfies the entry's predicate, judged from its declaration and
\ the slots its lookups answered. The bump commit argues it and records
\ that every field the step moved (the golden snapshots, all of Init)
\ lies inside the reach; the step's [kernel] review checks the argument.
\ reach-all is the default, and the only entry allowed for a change to the
\ lookup rules, the fuel model as a whole, the publisher, the importer's
\ reading of an export, or anything every check shares. Loading this file
\ stops (abort) when a step inside the window has no entry or an entry
\ has a bit outside reach-known.
\
\ [kernel] code: not through the review gate (AGENTS.md).
\ State: none.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
9 constant lf-verdict-version

\ The window: a snapshot's format or verdict version is read when at most
\ this many versions older than the build's (the owner, 2026-11-12).
2 constant lf-snapshot-window

\ The reach bits (the kinds' in the order of the export's kind numbers,
\ axiom first: env-import.fs computes them by a shift).
1 constant reach-all
2 constant reach-kind-axiom           4 constant reach-kind-definition
8 constant reach-kind-theorem         16 constant reach-kind-opaque
32 constant reach-kind-quotient       64 constant reach-block-any
128 constant reach-block-nested       256 constant reach-block-mutual
512 constant reach-literal-nat        1024 constant reach-literal-string
2048 constant reach-projection        4096 constant reach-let
8192 constant reach-quotient          16384 constant reach-scratch-names
32768 constant reach-not-accepted     65536 constant reach-names
131071 constant reach-known           \ every bit above

\ Each step's entry: version, reach bits, names (one entry to a line).
3 cells constant /lf-vstep
create lf-verdict-steps
  2 , reach-scratch-names , 0 ,
  3 , reach-all , 0 ,
  4 , reach-all , 0 ,
  5 , reach-all , 0 ,
  6 , reach-block-any , 0 ,
  7 , reach-block-any , 0 ,
  8 , reach-block-nested , 0 ,
  9 , reach-all , 0 ,
here lf-verdict-steps - /lf-vstep / constant lf-verdict-steps#
: lf-vstep-at ( i -- entry ) /lf-vstep * lf-verdict-steps + ;
: lf-vstep-version ( entry -- k ) @ ;
: lf-vstep-reach ( entry -- bits ) cell+ @ ;
: lf-vstep-names ( entry -- names|0 ) 2 cells + @ ;
\ Step k's entry, or 0 for none.
: lf-vstep-is? ( k i -- k flag ) lf-vstep-at lf-vstep-version over = ;
: lf-vstep-of ( k -- entry|0 )
  0 swap lf-verdict-steps# 0 ?do i lf-vstep-is? if nip i lf-vstep-at swap then loop drop ;
\ Step k's reach bits; reach-all for a step without an entry.
: lf-vstep-bits ( k -- bits ) lf-vstep-of ?dup if lf-vstep-reach else reach-all then ;
\ The reach of the steps after verdict version v up to this build's: their
\ bits joined (0 for this build's own version or a newer one).
: lf-verdict-reach ( v -- bits )
  0 swap 1+ lf-verdict-version 1+ tuck min ?do i lf-vstep-bits or loop ;
\ The oldest version a build of version current reads (at least 1).
: lf-window-oldest ( current -- oldest ) lf-snapshot-window - 1 max ;
\ Whether verdict version v is older than this build's, inside the window:
\ its results are carried where the steps since cannot reach.
: lf-verdict-carried? ( v -- flag )
  lf-verdict-version lf-window-oldest lf-verdict-version within ;

\ Loading stops when a step inside the window lacks an entry or an entry
\ holds a bit no evaluator knows.
: lf-vstep-known? ( i -- flag ) lf-vstep-at lf-vstep-reach reach-known invert and 0= ;
: lf-vsteps-known? ( -- flag ) true lf-verdict-steps# 0 ?do i lf-vstep-known? and loop ;
: lf-window-steps ( -- limit first ) lf-verdict-version 1+ dup 1- lf-window-oldest 1+ ;
: lf-window-covered? ( -- flag ) true lf-window-steps ?do i lf-vstep-of 0<> and loop ;
lf-vsteps-known? lf-window-covered? and 0= [if]
  .( verdict-version.fs: a step in the window has no reach entry, or an unknown bit) cr
  abort
[then]
base !   \ the BASE this file was loaded with
