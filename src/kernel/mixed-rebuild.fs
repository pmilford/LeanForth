\ Untrusted helpers shared by the passes that rebuild mixed terms (shift,
\ instantiate and beta): visit results, the audit before allocation,
\ binary-node rebuilding and rollback. Structural transformation only; no
\ proof judgment.
\ State: none. Every word works on the frames record (lib/frame.fs) that its
\ pass passes on the stack.

\ Visit results. Each node occurrence costs one unit of fuel and one frame
\ on the pass's explicit stack (lib/frame.fs), which grows with the
\ depth: no depth limit (plan task 6.2.0). Leaf constants and symbolic
\ Sorts are kept with their original stamps; rebuilt nodes are appended in
\ post-order. A visit gives a node and ok, or -1 and the failure. Every
\ visitor and continuation here is a step ( ... frames -- ... frames next
\ ), and a leaf's step returns with lf-rebuild-return.

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/terms.fs

: lf-rebuild-invalid ( -- -1 outcome ) outcome-invalid no-result ;
: lf-rebuild-full ( -- -1 outcome ) outcome-full no-result ;
: lf-rebuild-bad ( node frames -- -1 outcome ) 2drop lf-rebuild-invalid ;
: lf-rebuild-keep ( node frames -- node outcome ) drop outcome-ok ;
\ A visit's step that returns what xt ( node frames -- result outcome )
\ gives for its node.
: lf-rebuild-return ( node frames xt -- result outcome frames 0 )
  over >r execute r> 0 ;
: lf-rebuild-refuse ( node frames -- -1 outcome frames 0 ) ['] lf-rebuild-bad lf-rebuild-return ;
\ A visitor dispatches on the tag of its node; a node the store does not
\ hold gives tag 0, which no term has, so the default arm refuses it.
0 constant lf-rebuild-no-tag
: lf-rebuild-tag ( node frames flag -- node frames tag )
  if over lf-term-tag@ else lf-rebuild-no-tag then ;
\ A fresh node is ok; a failed allocation is full: the term store has no
\ free record or its identity serial is spent (the children are results
\ of earlier visits, so they are live).
: lf-rebuild-allocated ( node true | false -- node outcome )
  if outcome-ok else lf-rebuild-full then ;

\ Binary nodes, whose fields were read in this visit and are fetched again
\ unchecked. The second child of a lambda or Pi lies under one more binder,
\ which cannot be entered at context max-n (full); that is checked before
\ the first child is visited, so such a node spends no fuel on its children.
\ The check is independent of fuel (ADR 0008): a node whose own visit took
\ the last unit is still full there, not exhausted, and it is recorded as
\ a full binder context.
\ The node is kept on the pass's stack while its first child is visited,
\ the node and the first result while its second is: three steps, the
\ visit (lf-rebuild-first), then each child's continuation
\ (lf-rebuild-next, lf-rebuild-joined), shared with mixed-open.fs.
: lf-rebuild-binder? ( node -- flag ) lf-term-tag@ lf-tag-app <> ;
: lf-rebuild-stuck? ( node frames -- flag )
  frame-context @ max-n = swap lf-rebuild-binder? and ;
: lf-rebuild-site ( -- site ) c" mixed-rebuild lf-rebuild-binary" ;
: lf-rebuild-deep ( -- -1 outcome )
  max-n dup lf-rebuild-site lf-diag-binders-full lf-diag-note lf-rebuild-full ;
: lf-rebuild-build ( r1 node r2 -- result outcome )
  swap lf-term-tag@ lf-term-binary lf-rebuild-allocated ;
\ A failed child: its ( -1 outcome ) is the visit's, the n cells the
\ visit kept dropped.
: lf-rebuild-failed ( -1 outcome frames n -- -1 outcome frames 0 )
  0 ?do dup frame-restore drop loop 0 ;
\ The second child of a lambda or Pi is one binder deeper.
: lf-rebuild-descend ( node -- xt )
  lf-rebuild-binder? if ['] frame-under else ['] frame-call then ;
\ Keep the node and visit its first child, then cont.
: lf-rebuild-first ( node frames cont -- first frames next )
  >r over lf-term-first@ -rot tuck frame-save r> frame-call ;
\ After the first child: keep r1 too and visit the second child, then cont.
: lf-rebuild-next ( r1 outcome frames cont -- second frames next | -1 outcome frames 0 )
  >r over ok? 0= if r> drop 1 lf-rebuild-failed exit then nip
  dup frame-restore 2dup swap frame-save -rot tuck frame-save
  over lf-term-second@ -rot swap lf-rebuild-descend r> swap execute ;
\ After the second child: the node made from r1 and r2 by xt ( r1 node r2
\ -- result outcome ).
: lf-rebuild-joined ( r2 outcome frames xt -- result outcome frames 0 )
  >r over ok? 0= if r> drop 2 lf-rebuild-failed exit then nip
  >r r@ frame-restore r@ frame-restore rot r> r> swap >r execute r> 0 ;
\ A binary node: both children visited, then the node appended.
: lf-rebuild-built ( r2 outcome frames -- result outcome frames 0 )
  ['] lf-rebuild-build lf-rebuild-joined ;
: lf-rebuild-second ( r1 outcome frames -- second frames next | -1 outcome frames 0 )
  ['] lf-rebuild-built lf-rebuild-next ;
: lf-rebuild-binary ( node frames -- first frames next | -1 outcome frames 0 )
  2dup lf-rebuild-stuck? if nip >r lf-rebuild-deep r> 0 exit then
  ['] lf-rebuild-second lf-rebuild-first ;

\ Audit a whole root with the pass's fuel before anything is allocated. The
\ pass continues with the fuel the audit leaves, or zero after a failure.
\ lf-cterm-check gives only ok, invalid, exhausted or full (its contract),
\ so the outcome needs no narrowing.
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
