\ Runs: sequences of cells that never change (plan FE1g-1;
\ docs/design/FE1G_TACTICS.md §4.1), the front end's local contexts
\ (lctx-views.fs) and goal lists (goals.fs). Lean keeps both as persistent
\ values (a LocalContext's PersistentArray, a List MVarId), so a saved
\ state is a pointer and a goal's context changes without disturbing the
\ others'. Here a run is a handle: 0 the empty run, n > 0 the record n - 1
\ of rn-recs, which names a stretch of the slab rn-cells (its first cell
\ and its count). Cells are only appended, never changed, so runs share
\ cells and every operation makes a new run:
\ - lf-run-push ( run x -- run' outcome ): the run, then x. When the run
\   ends at the top of rn-cells, x is appended there; else the run is
\   first copied to the top (a run that another one extended stays).
\ - lf-run-take ( run n -- run' outcome ): its first n cells;
\   lf-run-after ( run n -- run' outcome ): the cells after them. Neither
\   copies; taking all, or none after, gives the run itself.
\ - lf-run-cat ( run1 run2 -- run outcome ): run1's cells, then run2's;
\   no copy when run2 begins where run1 ends.
\ - lf-run-count ( run -- n ), lf-run@ ( run i -- x ) (unchecked: a valid
\   run and 0 <= i < n), lf-run-valid? ( run -- flag ).
\ - lf-runs-reset ( -- ): every run is gone (lf-mctx-reset does it, with
\   a new declaration); lf-runs-epoch ( -- n ) changes with each reset.
\   Like a term index, a handle means nothing after a reset.
\ Outcomes: ok; invalid for a handle that names no run, or n outside 0 to
\ the count; full when a slab cannot grow (the heap refuses). A failure
\ makes no run (cells appended for it stay, unreachable). Untrusted.
\ General in itself (no Lean knowledge); kept in front/ because its slabs
\ are the front end's state in the checker context.
\ State: the slabs rn-cells and rn-recs, in the checker context (ADR 0009).

require ../lib/lib.fs

begin-structure /rn
  field: rn-first     \ its first cell in rn-cells
  field: rn-count     \ its number of cells
end-structure
1 cells context-slab: rn-cells
/rn context-slab: rn-recs
: lf-runs-reset ( -- ) rn-cells slab-clear rn-recs slab-clear ;
: lf-runs-epoch ( -- n ) rn-recs slab-generation ;

\ Reading. Unchecked but for lf-run-valid?: a run that names a record.
: rn-rec ( run -- addr ) 1- rn-recs slab-at ;
: lf-run-valid? ( run -- flag ) ?dup if 1- rn-recs slab-valid? else true then ;
: lf-run-count ( run -- n ) ?dup if rn-rec rn-count @ else 0 then ;
: rn-first@ ( run -- i ) ?dup if rn-rec rn-first @ else 0 then ;
: rn-end ( run -- i ) dup rn-first@ swap lf-run-count + ;
: rn-cell ( i -- addr ) rn-cells slab-at ;
: lf-run@ ( run i -- x ) swap rn-first@ + rn-cell @ ;

\ A new run of n cells from first; none is the empty run, no record.
: rn-made ( first n i -- run ) dup >r rn-recs slab-at tuck rn-count ! rn-first ! r> 1+ ;
: rn-new ( first n -- run outcome )
  dup 0= if 2drop 0 outcome-ok exit then
  1 rn-recs slab-claim ok-then? if rn-made outcome-ok else nip nip no-result then ;

\ Parts: a valid run and 0 <= n <= its count.
: rn-within? ( run n -- flag )
  over lf-run-valid? if swap lf-run-count 0 swap between? else 2drop false then ;
: lf-run-take ( run n -- run' outcome )
  2dup rn-within? 0= if 2drop -1 outcome-invalid exit then
  2dup swap lf-run-count = if drop outcome-ok else swap rn-first@ swap rn-new then ;
: rn-tail ( run n -- first n' ) over lf-run-count over - >r swap rn-first@ + r> ;
: lf-run-after ( run n -- run' outcome )
  2dup rn-within? 0= if 2drop -1 outcome-invalid exit then
  dup 0= if drop outcome-ok else rn-tail rn-new then ;

\ Copies. The run's cells copied to the top of rn-cells: where they begin.
: rn-move ( run i -- )
  swap dup rn-first@ rn-cell rot rn-cell rot lf-run-count cells move ;
: rn-copied ( run -- first outcome )
  dup lf-run-count rn-cells slab-claim ok-then? if tuck rn-move outcome-ok
  else nip no-result then ;
\ Where the run begins once it ends at the top: itself, or a copy.
: rn-top? ( run -- flag ) rn-end rn-cells slab-count = ;
: rn-at-top ( run -- first outcome )
  dup rn-top? if rn-first@ outcome-ok else rn-copied then ;

\ Pushing: x appended at the top, after the run's cells.
: rn-put ( x -- outcome )
  1 rn-cells slab-claim ok-then? if rn-cell ! outcome-ok else nip then ;
: rn-pushed ( x first n -- run outcome )
  rot rn-put ok-then2? if 1+ rn-new else no-result then ;
: rn-grown ( run x -- x first n outcome ) swap dup lf-run-count >r rn-at-top r> swap ;
: lf-run-push ( run x -- run' outcome )
  over lf-run-valid? 0= if 2drop -1 outcome-invalid exit then
  rn-grown ok-then3? if rn-pushed else no-result then ;

\ Joining: in place when run2 begins where run1 ends; else run1 at the
\ top and a copy of run2 after it.
: rn-both-valid? ( run1 run2 -- run1 run2 flag )
  2dup lf-run-valid? swap lf-run-valid? and ;
: rn-adjacent? ( run1 run2 -- flag ) rn-first@ swap rn-end = ;
: rn-total ( run1 run2 -- n ) lf-run-count swap lf-run-count + ;
: rn-sum ( run1 run2 -- first n ) over rn-first@ -rot rn-total ;
: rn-joined ( run1 run2 -- run outcome )
  2dup rn-total >r swap rn-at-top ok-then? 0= if nip r> drop no-result exit then
  swap rn-copied ok-then? if drop r> rn-new else nip r> drop no-result then ;
: rn-cat ( run1 run2 -- run outcome )
  2dup rn-adjacent? if rn-sum rn-new else rn-joined then ;
: lf-run-cat ( run1 run2 -- run outcome )
  rn-both-valid? 0= if 2drop -1 outcome-invalid exit then
  dup 0= if drop outcome-ok exit then over 0= if nip outcome-ok exit then rn-cat ;
