\ Untrusted mixed-term shift: add an amount to every bound variable at or
\ above a cutoff, rebuilding the term. Structural transformation only; no
\ proof judgment. Load constant-term-boundary.fs and its dependencies
\ first. Also defines the lf-rebuild-* words that the instantiate and beta
\ passes share: the audit before allocation, binary-node rebuilding and
\ rollback.
\ State: one frame record, lf-mshift-frames (fuel, nesting, the cutoff as
\ its context, the amount, the starting term count). Not re-entrant and
\ single-threaded: the instantiate pass shifts its replacement on this
\ record, so no shift may be running then. Exclude raw mutation, resets
\ and concurrent access during a call.

outcome-ok constant lf-mshift-ok
outcome-invalid constant lf-mshift-invalid
outcome-exhausted constant lf-mshift-exhausted
max-n constant lf-mshift-max
lf-term-capacity frames: lf-mshift-frames

\ Fuel left after a shift; mixed-infer continues with it.
: lf-mshift-fuel ( -- addr ) lf-mshift-frames frame-fuel ;
: lf-mshift-amount ( -- addr ) lf-mshift-frames frame-arg ;
: lf-mshift-cutoff ( -- cutoff ) lf-mshift-frames frame-context @ ;

\ Rebuilding passes (shift, instantiate, beta). Each node occurrence costs
\ one unit of fuel and one frame (frame.fs), so the frames also bound the
\ recursion depth. Leaf constants and symbolic Sorts are kept with their
\ original stamps; rebuilt nodes are appended in post-order. A visit gives
\ a node and ok, or -1 and the failure.
: lf-rebuild-invalid ( -- -1 outcome ) -1 outcome-invalid ;
: lf-rebuild-exhausted ( -- -1 outcome ) -1 outcome-exhausted ;
: lf-rebuild-keep ( node first second -- node outcome ) 2drop outcome-ok ;
: lf-rebuild-leaf? ( tag -- flag ) dup lf-tag-symbolic-sort = swap lf-tag-constant = or ;
\ A fresh node is ok; a failed allocation (full store, spent serial or an
\ invalid child) exhausts.
: lf-mshift-allocated ( node true | false -- node status )
  if outcome-ok else lf-rebuild-exhausted then ;
\ Go on with a child's result, or drop the two cells kept for the next
\ step and pass the child's failure up.
: lf-rebuild-then? ( x1 x2 result outcome -- x1 x2 result true | result outcome false )
  dup ok? if drop true else 2swap 2drop false then ;

\ Binary nodes. The second child of a lambda or Pi lies under one more
\ binder, which cannot be entered at depth lf-mshift-max; that is checked
\ before the first child is visited. The node was read in this visit, so
\ its fields are fetched again unchecked. Every nested visit holds a few
\ cells of the data and return stacks, so the visiting words are kept flat.
: lf-rebuild-binder? ( node -- flag ) lf-term-slot node-tag @ lf-tag-app <> ;
: lf-rebuild-stuck? ( node frames -- flag )
  frame-context @ lf-mshift-max = swap lf-rebuild-binder? and ;
: lf-rebuild-build ( r1 node r2 -- result outcome )
  swap lf-term-slot node-tag @ lf-term-binary lf-mshift-allocated ;
: lf-rebuild-join ( r1 node frames -- result outcome )
  over lf-rebuild-binder? >r over lf-term-slot node-second @ swap r>
  if frame-under else frame-call then lf-rebuild-then? if lf-rebuild-build then ;
\ Visit both children with the pass's frame record, then append the node.
: lf-rebuild-binary ( node frames -- result outcome )
  2dup lf-rebuild-stuck? if 2drop lf-rebuild-exhausted exit then
  over lf-term-slot node-first @ over frame-call
  lf-rebuild-then? if -rot lf-rebuild-join then ;

\ Audit a whole root with the pass's fuel before anything is allocated. The
\ pass continues with the fuel the audit leaves, or zero after a failure.
\ lf-cterm-check gives only ok, invalid or exhausted.
: lf-rebuild-audit ( index identity frames -- outcome )
  >r r@ frame-fuel @ lf-cterm-check
  dup ok? if lf-cterm-fuel @ else 0 then r> frame-fuel ! ;

\ Run a pass on a root from the current term count. Success gives a live
\ result and its identity; any failure, or a result without an identity,
\ restores the count, discarding every node the pass appended (allocation
\ serials are never rewound), and gives -1 0 and the outcome.
: lf-rebuild-none ( outcome -- -1 0 outcome ) -1 0 rot ;
: lf-rebuild-discard ( outcome start -- -1 0 outcome ) lf-term-count ! lf-rebuild-none ;
: lf-rebuild-identify ( result start -- index identity outcome )
  over lf-term-identity if nip outcome-ok exit then
  nip outcome-invalid swap lf-rebuild-discard ;
: lf-rebuild-finish ( result outcome start -- index identity outcome )
  over ok? if nip lf-rebuild-identify else rot drop lf-rebuild-discard then ;
: lf-rebuild-run ( root context xt frames -- index identity outcome )
  lf-term-count @ over frame-mark ! dup >r frame-run r> frame-mark @ lf-rebuild-finish ;

\ Visiting one node of the shift. The preaudit establishes tags, payloads
\ and backward edges; any tag other than a leaf or variable is rebuilt as a
\ binary node. A variable below the cutoff is kept; the others move up by
\ the amount, which exhausts past lf-mshift-max.
: lf-mshift-up ( index -- result outcome )
  dup lf-mshift-max lf-mshift-amount @ - > if drop lf-rebuild-exhausted
  else lf-mshift-amount @ + lf-term-bvar lf-mshift-allocated then ;
: lf-mshift-bvar ( node index -- result outcome )
  dup lf-mshift-cutoff < if drop outcome-ok else nip lf-mshift-up then ;
: lf-mshift-visit ( node -- result outcome )
  dup lf-term-read 0= if drop lf-rebuild-invalid exit then
  rot dup lf-tag-bvar = if 2drop lf-mshift-bvar exit then
  lf-rebuild-leaf? if lf-rebuild-keep else 2drop lf-mshift-frames lf-rebuild-binary then ;

\ Shift node from cutoff by the amount already in the record.
: lf-mshift-run ( node cutoff -- result outcome )
  ['] lf-mshift-visit lf-mshift-frames frame-run ;
\ Shift a node by amount from cutoff zero, from inside another pass whose
\ frame record lends its fuel and gets back what is left. Nothing is rolled
\ back here; the caller's pass does that.
: lf-mshift-inside ( node amount frames -- result outcome )
  >r lf-mshift-amount ! r@ frame-fuel @ lf-mshift-fuel ! 0 lf-mshift-run
  lf-mshift-fuel @ r> frame-fuel ! ;

\ Shift a live mixed root. Validation and traversal share fuel; invalid input
\ and resource exhaustion are distinct. On failure discard appended nodes,
\ but never rewind allocation serials. Negative fuel is invalid and leaves
\ lf-mshift-fuel unchanged; a negative cutoff or amount is invalid; a failed
\ audit leaves fuel at zero. Leaf constants and symbolic sorts are reused
\ with their original stamps. A zero shift returns the audited root without
\ allocating or traversing it.
: lf-mshift-refuse ( index identity cutoff amount -- -1 0 status )
  2drop 2drop outcome-invalid lf-rebuild-none ;
: lf-mshift-args? ( cutoff amount -- flag ) 0< swap 0< or 0= ;
: lf-mshift-copy ( index identity cutoff -- index identity status )
  lf-mshift-amount @ 0= if drop outcome-ok exit then
  nip ['] lf-mshift-visit lf-mshift-frames lf-rebuild-run ;
: lf-mshift-root ( index identity cutoff -- index identity status )
  >r 2dup lf-mshift-frames lf-rebuild-audit dup ok?
  if drop r> lf-mshift-copy else r> drop nip nip lf-rebuild-none then ;
: lf-mixed-shift ( index identity cutoff amount fuel -- index identity status )
  lf-mshift-frames frame-budget 0= if lf-mshift-refuse exit then
  2dup lf-mshift-args? if lf-mshift-amount ! lf-mshift-root else lf-mshift-refuse then ;
