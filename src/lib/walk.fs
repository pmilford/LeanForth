\ Bounded depth-first walks over DAG nodes. A walk record holds the fuel
\ left, the node being visited, one cell for the visitor's own use (such as
\ a mode), and a bounded work stack. Every word here takes the record's
\ address, so separate records give independent walks: this module has no
\ global state, and a task or process with its own records can walk in
\ parallel with others. A module that owns one walk record is still not
\ re-entrant itself: its check must not run again while that record is in
\ use. Requires: store.fs (store-zeroed,), node.fs, outcome.fs.
\
\ walk-run pushes a root, then repeatedly spends one unit of fuel, pops a
\ node into walk-node and calls the visitor ( walk -- outcome ), which reads
\ that node and pushes its children. It stops at the first outcome that is
\ not ok, with exhausted when fuel reaches zero or the stack is full, or
\ with ok when the stack empties. A visitor result outside the outcome
\ vocabulary counts as invalid. A node shared by several parents is
\ visited, and charged, once per path.

begin-structure walk-header
  field: walk-fuel       \ visits left
  field: walk-node       \ node being visited
  field: walk-arg        \ one cell for the visitor
  field: walk-pending    \ items on the work stack
  field: walk-capacity   \ maximum items
end-structure

: walk-stack ( walk -- addr ) walk-header + ;
: walk-bytes ( capacity -- u ) cells walk-header + ;
\ Defining word: name ( -- walk ), zeroed, with room for capacity items. A
\ capacity below 1 aborts the definition.
: walk: ( capacity "name" -- )
  dup 0> 0= abort" walk: bad capacity" create dup walk-bytes store-zeroed, walk-capacity ! ;

\ Set the budget for a walk; a negative fuel is refused and stores nothing.
: walk-budget ( fuel walk -- flag ) over 0< if 2drop false else walk-fuel ! true then ;

\ The work stack. A push fails, changing nothing, when the stack is full or
\ its count or capacity is out of range; signed comparisons only.
: walk-room? ( walk -- flag ) dup walk-pending @ swap walk-capacity @ over > swap 0< 0= and ;
: walk-top ( walk -- addr ) dup walk-pending @ cells swap walk-stack + ;
: walk-push ( index walk -- flag )
  dup walk-room? if tuck walk-top ! 1 swap walk-pending +! true else 2drop false then ;
\ Unchecked: 0 < pending <= capacity (walk-loop only pops a nonempty stack).
: walk-pop ( walk -- index ) -1 over walk-pending +! walk-top @ ;

\ Pushing children from a visitor. walk-child and walk-children require an
\ earlier node than the one being visited, which rules out cycles and
\ forward edges; walk-push-outcome and walk-push2 do not check, for inputs
\ whose shape an earlier pass validated.
: walk-push-outcome ( index walk -- outcome ) walk-push if outcome-ok else outcome-exhausted then ;
: walk-push2 ( first second walk -- outcome )
  rot over walk-push if walk-push-outcome else 2drop outcome-exhausted then ;
: walk-child? ( index walk -- flag ) walk-node @ 0 swap within ;
: walk-child ( index walk -- outcome )
  2dup walk-child? if walk-push-outcome else 2drop outcome-invalid then ;
: walk-children ( first second walk -- outcome )
  >r 2dup r@ walk-child? swap r@ walk-child? and
  if r> walk-push2 else 2drop r> drop outcome-invalid then ;
\ Visiting: read the current node of a store of tagged nodes, then dispatch
\ on its tag with ( first second walk tag -- outcome ); an unreadable node is
\ invalid. The default arm of a dispatch CASE reports an unknown tag.
: walk-read ( walk store -- first second walk tag true | false )
  over walk-node @ swap node-read if 2swap true else drop false then ;
: walk-visit ( walk store xt -- outcome ) >r walk-read if r> execute else r> drop outcome-invalid then ;
: walk-bad-tag ( first second walk tag -- outcome tag ) >r drop 2drop outcome-invalid r> ;

\ The loop.
: walk-spend? ( walk -- flag ) walk-fuel dup @ 0= if drop false else -1 swap +! true then ;
: walk-take ( walk -- ) dup walk-pop swap walk-node ! ;
: walk-step ( xt walk -- outcome )
  dup walk-spend? if dup walk-take swap execute outcome-sane else 2drop outcome-exhausted then ;
: walk-loop ( xt walk -- outcome )
  begin dup walk-pending @ 0> while
    2dup walk-step dup ok? 0= if nip nip exit then drop
  repeat 2drop outcome-ok ;
: walk-start ( root walk -- flag ) 0 over walk-pending ! walk-push ;
: walk-run ( root xt walk -- outcome )
  rot over walk-start if walk-loop else 2drop outcome-exhausted then ;
