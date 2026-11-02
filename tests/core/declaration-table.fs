\ Emit experimental statuses for the same closed declaration candidates as
\ declaration-table.lean. A zero status is not a checked theorem handle.
include ../../src/legacy/declaration-probe.fs
include ../support/term-cases.fs
decimal

\ Build the closed identity theorem and two altered declaration candidates.
: build-declaration-table ( -- )
  lf-term-reset
  0 lf-term-sort require-test-node drop
  0 lf-term-bvar require-test-node drop
  1 lf-term-bvar require-test-node drop
  1 2 lf-term-pi require-test-node drop
  0 3 lf-term-pi require-test-node drop
  1 1 lf-term-lam require-test-node drop
  0 5 lf-term-lam require-test-node drop
  1 2 lf-term-lam require-test-node drop
  0 7 lf-term-lam require-test-node drop
  1 lf-term-sort require-test-node drop ;

\ Print one case index and the corresponding untrusted status.
: emit-declaration-probe ( case type value -- )
  rot . 50000 lf-declaration-probe . cr ;
build-declaration-table
0 4 6 emit-declaration-probe
1 4 8 emit-declaration-probe
2 6 6 emit-declaration-probe
3 9 0 emit-declaration-probe
\ Lean accepts this declaration: its outer domain beta-reduces to Prop, but
\ our conservative comparison requires structurally identical binder domains.
lf-term-reset
0 lf-term-sort require-test-node drop
1 lf-term-sort require-test-node drop
0 lf-term-bvar require-test-node drop
1 lf-term-bvar require-test-node drop
1 2 lf-term-lam require-test-node drop
4 0 lf-term-app require-test-node drop
2 3 lf-term-pi require-test-node drop
5 6 lf-term-pi require-test-node drop
2 2 lf-term-lam require-test-node drop
0 8 lf-term-lam require-test-node drop
4 7 9 emit-declaration-probe
bye
