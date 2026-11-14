\ Runs: sequences of cells that never change, sharing their cells (a
\ persistent array of the simplest kind). A run is a handle, one cell: 0
\ is the empty run, n > 0 the record n - 1 of a slab of records, each of
\ which names a stretch (its first cell and its count) of one slab of
\ cells. Cells are only appended, never changed, so a run never changes
\ and every operation makes a new run; a saved run is just its handle.
\ LeanForth's front end keeps its local contexts and goal lists as runs
\ (src/front/lctx-views.fs, goals.fs), as Lean keeps them as persistent
\ values (a LocalContext's PersistentArray, a List MVarId).
\ - run-push ( run x -- run' outcome ): the run, then x. When the run ends
\   at the top of the cells, x is appended there; else the run is copied
\   to the top first (a run that another one extended stays as it was).
\ - run-take ( run n -- run' outcome ): its first n cells; run-after ( run
\   n -- run' outcome ): the cells after them. Neither copies; taking all,
\   or none after, gives the run itself.
\ - run-cat ( run1 run2 -- run outcome ): run1's cells, then run2's; no
\   copy when run2 begins where run1 ends.
\ - run-count ( run -- n ), run@ ( run i -- x ) (unchecked: a valid run,
\   0 <= i < n), run-valid? ( run -- flag ).
\ - run-each ( i*x run xt -- i*x outcome ): xt ( i*x x -- i*x outcome )
\   on each cell x of the run, in order, while it gives ok: ok, or the
\   first outcome that is not ok (no step after it). The values below x
\   are the steps' to read and replace, as outcome.fs's ok-each; a step
\   may make runs (the run it walks stays as it was).
\ - run-filter ( run xt -- run' outcome ): a new run of the cells x for
\   which xt ( x -- keep? ) is true, in order (the empty run when none),
\   the kept cells appended once and one record made; the test makes no
\   runs.
\ - runs-reset ( -- ): every run is gone (and its handle means nothing
\   afterwards); runs-epoch ( -- n ) changes with each reset, so a holder
\   of a run can tell; runs-cells ( -- n ) the cells in use.
\ Outcomes (outcome.fs): ok; invalid for a handle that names no run, or n
\ outside 0 to the count; full when a slab cannot grow (the heap refuses).
\ A failure makes no run (cells appended for it stay, unreachable).
\ Example:
\   0 7 run-push drop  dup 8 run-push drop   \ [7] and [7 8], one cell shared
\   over 9 run-push drop  rot drop           \ [7 9]: [7] copied to the top
\   run-cat drop  dup run-count .            \ [7 8 7 9]: 4
\   dup 2 run-after drop 0 run@ .            \ 7
\   : sum ( n x -- n' outcome ) + outcome-ok ;
\   : odd? ( x -- flag ) 1 and 0<> ;
\   0 over ' sum run-each drop .             \ 31
\   ' odd? run-filter drop run-count .       \ [7 7 9]: 3
\ State: two slabs (slab.fs) that are members of the checker context
\ (context.fs, ADR 0009), so each context has its own runs; one context
\ is single-threaded. Requires bounds.fs, outcome.fs, slab.fs, context.fs
\ and module.fs; helpers private in lf-lib-private (ADR 0010). Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./bounds.fs
require ./outcome.fs
require ./slab.fs
require ./context.fs
require ./module.fs

lf-lib-private module-open

begin-structure /rn
  field: rn-first     \ its first cell in rn-cells
  field: rn-count     \ its number of cells
end-structure
1 cells context-slab: rn-cells
/rn context-slab: rn-recs
lf-lib set-current
: runs-reset ( -- ) rn-cells slab-clear rn-recs slab-clear ;
: runs-epoch ( -- n ) rn-recs slab-generation ;
: runs-cells ( -- n ) rn-cells slab-count ;
lf-lib-private set-current

\ Reading. Unchecked but for run-valid?: a run that names a record.
: rn-rec ( run -- addr ) 1- rn-recs slab-at ;
lf-lib set-current
: run-valid? ( run -- flag ) ?dup if 1- rn-recs slab-valid? else true then ;
: run-count ( run -- n ) ?dup if rn-rec rn-count @ else 0 then ;
lf-lib-private set-current
: rn-first@ ( run -- i ) ?dup if rn-rec rn-first @ else 0 then ;
: rn-end ( run -- i ) dup rn-first@ swap run-count + ;
: rn-cell ( i -- addr ) rn-cells slab-at ;
lf-lib set-current
: run@ ( run i -- x ) swap rn-first@ + rn-cell @ ;
lf-lib-private set-current

\ A new run of n cells from first; none is the empty run, no record.
: rn-made ( first n i -- run ) dup >r rn-recs slab-at tuck rn-count ! rn-first ! r> 1+ ;
: rn-new ( first n -- run outcome )
  dup 0= if 2drop 0 outcome-ok exit then
  1 rn-recs slab-claim ok-then? if rn-made outcome-ok else nip nip no-result then ;

\ Parts: a valid run and 0 <= n <= its count.
: rn-within? ( run n -- flag )
  over run-valid? if swap run-count 0 swap between? else 2drop false then ;
: rn-tail ( run n -- first n' ) over run-count over - >r swap rn-first@ + r> ;
lf-lib set-current
: run-take ( run n -- run' outcome )
  2dup rn-within? 0= if 2drop -1 outcome-invalid exit then
  2dup swap run-count = if drop outcome-ok else swap rn-first@ swap rn-new then ;
: run-after ( run n -- run' outcome )
  2dup rn-within? 0= if 2drop -1 outcome-invalid exit then
  dup 0= if drop outcome-ok else rn-tail rn-new then ;
lf-lib-private set-current

\ Copies. The run's cells copied to the top of rn-cells: where they begin.
: rn-move ( run i -- )
  swap dup rn-first@ rn-cell rot rn-cell rot run-count cells move ;
: rn-copied ( run -- first outcome )
  dup run-count rn-cells slab-claim ok-then? if tuck rn-move outcome-ok
  else nip no-result then ;
\ Where the run begins once it ends at the top: itself, or a copy.
: rn-top? ( run -- flag ) rn-end rn-cells slab-count = ;
: rn-at-top ( run -- first outcome )
  dup rn-top? if rn-first@ outcome-ok else rn-copied then ;

\ Pushing: x appended at the top, after the run's cells.
: rn-put ( x -- outcome ) rn-cells slab-push ;
: rn-pushed ( x first n -- run outcome )
  rot rn-put ok-then2? if 1+ rn-new else no-result then ;
: rn-grown ( run x -- x first n outcome ) swap dup run-count >r rn-at-top r> swap ;
lf-lib set-current
: run-push ( run x -- run' outcome )
  over run-valid? 0= if 2drop -1 outcome-invalid exit then
  rn-grown ok-then3? if rn-pushed else no-result then ;
lf-lib-private set-current

\ Joining: in place when run2 begins where run1 ends; else run1 at the
\ top and a copy of run2 after it.
: rn-both-valid? ( run1 run2 -- run1 run2 flag )
  2dup run-valid? swap run-valid? and ;
: rn-adjacent? ( run1 run2 -- flag ) rn-first@ swap rn-end = ;
: rn-total ( run1 run2 -- n ) run-count swap run-count + ;
: rn-sum ( run1 run2 -- first n ) over rn-first@ -rot rn-total ;
: rn-joined ( run1 run2 -- run outcome )
  2dup rn-total >r swap rn-at-top ok-then? 0= if nip r> drop no-result exit then
  swap rn-copied ok-then? if drop r> rn-new else nip r> drop no-result then ;
: rn-cat ( run1 run2 -- run outcome )
  2dup rn-adjacent? if rn-sum rn-new else rn-joined then ;
lf-lib set-current
: run-cat ( run1 run2 -- run outcome )
  rn-both-valid? 0= if 2drop -1 outcome-invalid exit then
  dup 0= if drop outcome-ok exit then over 0= if nip outcome-ok exit then rn-cat ;
lf-lib-private set-current

\ Walking a run: its cells' numbers in rn-cells, end and first, as ?DO
\ takes them. Cells are only appended, so the numbers stay valid while a
\ step makes runs; the xt is the index of an outer loop run once, read
\ with J (outcome.fs's ok-each), so a step sees only its own values.
: rn-span ( run -- end first ) dup rn-end swap rn-first@ ;
: rn-step ( i*x x xt -- i*x true | i*x outcome false )
  execute dup ok? if drop true else false then ;
lf-lib set-current
\ The step xt ( i*x x -- i*x outcome ) on each cell, in order, to the
\ first failure (the header); invalid for a handle that names no run.
: run-each ( i*x run xt -- i*x outcome )
  over run-valid? 0= if 2drop outcome-invalid exit then
  dup 1+ swap ?do rn-span ?do i rn-cell @ j rn-step 0= if unloop unloop exit then
  loop loop outcome-ok ;
lf-lib-private set-current
\ A filter appends the cells it keeps at the top of rn-cells, from cell
\ number first on, and makes one run of them at the end.
: rn-kept ( first xt x -- first xt outcome )
  2dup swap execute if rn-put else drop outcome-ok then ;
: rn-from ( first -- run outcome ) rn-cells slab-count over - rn-new ;
lf-lib set-current
\ A new run of the cells the test xt ( x -- keep? ) keeps, in order; -1
\ and the outcome when none is made (invalid, or full). The test makes
\ no runs (its cells would join the new run's).
: run-filter ( run xt -- run' outcome )
  rn-cells slab-count -rot swap ['] rn-kept run-each nip
  ok-then? if rn-from else no-result then ;
lf-lib-private set-current

module-close
base !   \ the BASE this file was loaded with
