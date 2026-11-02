\ Untrusted helpers shared by the passes that rebuild mixed terms (shift,
\ instantiate and beta): visit results, the audit before allocation,
\ binary-node rebuilding and rollback. Structural transformation only; no
\ proof judgment. Load constant-term-boundary.fs and its dependencies
\ first.
\ State: none. Every word works on the frames record (lib/frame.fs) that
\ its pass passes on the stack.

\ Visit results. Each node occurrence costs one unit of fuel and one frame,
\ so the frames also bound the recursion depth. Leaf constants and
\ symbolic Sorts are kept with their original stamps; rebuilt nodes are
\ appended in post-order. A visit gives a node and ok, or -1 and the
\ failure.
: lf-rebuild-invalid ( -- -1 outcome ) outcome-invalid no-result ;
: lf-rebuild-exhausted ( -- -1 outcome ) outcome-exhausted no-result ;
: lf-rebuild-bad ( node frames -- -1 outcome ) 2drop lf-rebuild-invalid ;
: lf-rebuild-keep ( node frames -- node outcome ) drop outcome-ok ;
\ A visitor dispatches on the tag of its node; a node the store does not
\ hold gives tag 0, which no term has, so the default arm refuses it.
0 constant lf-rebuild-no-tag
: lf-rebuild-tag ( node frames flag -- node frames tag )
  if over lf-term-tag@ else lf-rebuild-no-tag then ;
\ A fresh node is ok; a failed allocation (full store, spent serial or an
\ invalid child) exhausts.
: lf-rebuild-allocated ( node true | false -- node outcome )
  if outcome-ok else lf-rebuild-exhausted then ;

\ Binary nodes, whose fields were read in this visit and are fetched again
\ unchecked. The second child of a lambda or Pi lies under one more binder,
\ which cannot be entered at context max-n; that is checked before the
\ first child is visited, so such a node spends no fuel on its children.
\ Every nested visit holds a few cells of the host's stacks, so the words
\ between two visits are kept few and flat (see mixed-beta.fs).
: lf-rebuild-binder? ( node -- flag ) lf-term-tag@ lf-tag-app <> ;
: lf-rebuild-stuck? ( node frames -- flag )
  frame-context @ max-n = swap lf-rebuild-binder? and ;
: lf-rebuild-build ( r1 node r2 -- result outcome )
  swap lf-term-tag@ lf-term-binary lf-rebuild-allocated ;
: lf-rebuild-descend ( node -- xt )
  lf-rebuild-binder? if ['] frame-under else ['] frame-call then ;
: lf-rebuild-join ( r1 node frames -- result outcome )
  >r dup lf-term-second@ over lf-rebuild-descend r> swap execute
  ok-keep2? if lf-rebuild-build then ;
\ Visit both children with the pass's frames record, then append the node.
: lf-rebuild-binary ( node frames -- result outcome )
  2dup lf-rebuild-stuck? if 2drop lf-rebuild-exhausted exit then
  over lf-term-first@ over frame-call ok-keep2? if -rot lf-rebuild-join then ;

\ Audit a whole root with the pass's fuel before anything is allocated. The
\ pass continues with the fuel the audit leaves, or zero after a failure.
\ lf-cterm-check gives only ok, invalid or exhausted (its contract), so the
\ outcome needs no narrowing.
: lf-rebuild-audit ( index identity frames -- outcome )
  >r r@ frame-fuel @ lf-cterm-check
  dup ok? if lf-cterm-fuel @ else 0 then r> frame-fuel ! ;

\ Run a pass on a root from the current term count, which stays on the
\ return stack meanwhile. Success gives a live result and its identity; any
\ failure, or a result without an identity, restores the count, discarding
\ every node the pass appended (allocation serials are never rewound), and
\ gives -1 0 and the outcome.
: lf-rebuild-none ( outcome -- -1 0 outcome ) -1 0 rot ;
: lf-rebuild-discard ( outcome start -- -1 0 outcome ) lf-term-count ! lf-rebuild-none ;
: lf-rebuild-identify ( result start -- index identity outcome )
  over lf-term-identity if nip outcome-ok exit then
  nip outcome-invalid swap lf-rebuild-discard ;
: lf-rebuild-finish ( result outcome start -- index identity outcome )
  over ok? if nip lf-rebuild-identify else rot drop lf-rebuild-discard then ;
: lf-rebuild-run ( root context frames -- index identity outcome )
  lf-term-count @ >r frame-run r> lf-rebuild-finish ;
