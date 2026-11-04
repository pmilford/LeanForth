\ A deterministic, CPU-bound test job whose whole state lives in the
\ current context, for tests/lib/task.fs and task-bench.fs. Each round
\ builds a random DAG in a context store, one node per step, and walks it
\ with a plain and a paired walk record; after the last round a recursive
\ pass nests dag-depth visits deep on the host's stacks. A checksum folds in every visit,
\ outcome and fuel left. Load after src/lib/task.fs.

48 constant dag-nodes        \ nodes per DAG; node k > 1 has two earlier children
2000 constant dag-fuel       \ visits per walk
500 constant dag-depth       \ nesting of the recursive pass
0 constant dag-leaf
1 constant dag-pair

begin-structure /dag-state
  field: dag-seed        \ random generator state
  field: dag-rounds      \ rounds left; 0 when the job is finished
  field: dag-built       \ nodes built in this round
  field: dag-sum         \ checksum
  field: dag-visits      \ visits so far
  field: dag-oks         \ walks that ended ok rather than exhausted or full
  field: dag-every       \ yield after every this many visits; 0 never
  field: dag-rp          \ return-stack pointer when the recursive pass began
  field: dag-deep        \ return-stack cells the recursive pass used
  field: dag-depth0      \ data-stack depth when the recursive pass began
  field: dag-data        \ data-stack cells the recursive pass used
end-structure

dag-nodes /node 0 context-store: dag-store
dag-nodes 2* context-walk: dag-walker
dag-nodes 2* context-walk2: dag-pairs
/dag-state context-record: dag-state

\ The seed's cell; a planted fault redirects it to a shared variable.
: dag-own-seed ( -- addr ) dag-state dag-seed ;
defer dag-seed-cell  ' dag-own-seed is dag-seed-cell
: dag-rnd ( n -- r )
  dag-seed-cell dup @ 1103515245 * 12345 + dup rot ! 16 rshift 32767 and swap mod ;
: dag-mix ( x -- ) dag-state dag-sum dup @ 31 * rot + swap ! ;

\ Building: node k is a leaf for k < 2, else a pair of one of the three
\ nodes before it and any earlier node, so most walks run out of fuel.
: dag-near ( k -- index ) dup 1- swap 3 min dag-rnd - ;
: dag-node ( k -- tag first second )
  dup 2 < if drop dag-leaf 0 0 else dag-pair over dag-near rot dag-rnd then ;
: dag-add ( -- )
  dag-state dag-built @ dag-node dag-store node-new 0= abort" dag: store full" drop
  1 dag-state dag-built +! ;

\ Walking, with a checksum of every visit and a yield every dag-every visits.
: dag-due? ( -- flag )
  dag-state dag-every @ ?dup if dag-state dag-visits @ swap mod 0= else false then ;
: dag-note ( x -- ) dag-mix 1 dag-state dag-visits +! dag-due? if task-yield then ;
: dag-dispatch ( first second walk tag -- outcome )
  case dag-leaf of 2drop drop outcome-ok endof
    dag-pair of walk-children endof walk-bad-tag endcase ;
: dag-dispatch2 ( first second walk tag -- outcome )
  case dag-leaf of 2drop drop outcome-ok endof
    dag-pair of dup walk-context @ 1+ swap walk-children-at endof walk-bad-tag endcase ;
: dag-visit ( walk -- outcome )
  dup walk-node @ dag-note dag-store ['] dag-dispatch walk-visit ;
: dag-visit2 ( walk -- outcome )
  dup walk-node @ over walk-context @ + dag-note dag-store ['] dag-dispatch2 walk-visit ;
: dag-budget ( walk -- ) dag-fuel swap walk-budget drop ;
: dag-count ( outcome -- outcome ) dup ok? if 1 dag-state dag-oks +! then ;
: dag-result ( outcome walk -- ) swap dag-count dag-mix walk-fuel @ dag-mix ;
: dag-root ( -- index ) dag-nodes 1- ;
: dag-walk ( -- )
  dag-walker dag-budget dag-root ['] dag-visit dag-walker walk-run dag-walker dag-result ;
: dag-walk2 ( -- )
  dag-pairs dag-budget dag-root 0 ['] dag-visit2 dag-pairs walk-run-pair
  dag-pairs dag-result ;

\ The recursive pass: visit x recurses x deeper on the host's stacks,
\ holding two data-stack and two return-stack cells per level; the
\ deepest visit records how many cells of each the pass uses.
: dag-most ( n addr -- ) dup @ rot max swap ! ;
: dag-measure ( -- )
  dag-state dag-rp @ rp@ - 1 cells / dag-state dag-deep dag-most
  depth dag-state dag-depth0 @ - dag-state dag-data dag-most ;
: dag-sink ( x -- result )
  dup 0= if drop dag-measure 1000 dag-rnd exit then
  dup >r dup dup 1- recurse 31 * + nip r> drop ;
: dag-recurse ( -- )
  rp@ dag-state dag-rp ! depth dag-state dag-depth0 !
  dag-depth dag-sink dag-mix outcome-ok dag-mix ;

\ Steps. dag-start ( seed rounds every -- ) begins a job in the current
\ context; dag-step does one step and tells whether more remain.
: dag-start ( seed rounds every -- )
  dag-state dup /dag-state erase tuck dag-every ! tuck dag-rounds ! drop
  dag-seed-cell ! dag-store store-clear ;
: dag-building? ( -- flag ) dag-state dag-built @ dag-nodes < ;
: dag-round-done ( -- more? )
  -1 dag-state dag-rounds +! dag-state dag-rounds @ 0>
  dup if dag-store store-clear 0 dag-state dag-built ! else dag-recurse then ;
: dag-step ( -- more? )
  dag-state dag-rounds @ 0> 0= if false exit then
  dag-building? if dag-add true else dag-walk dag-walk2 dag-round-done then ;
: dag-run ( -- ) begin dag-step 0= until ;
: dag-results ( -- sum visits ) dag-state dag-sum @ dag-state dag-visits @ ;
