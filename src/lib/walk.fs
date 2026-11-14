\ Bounded depth-first walks over DAG nodes. A walk record holds the fuel
\ left, the node being visited, one cell for the visitor's own use (such as
\ a mode), and a bounded work stack. Every word here takes the record's
\ address, so separate records give independent walks: this module has no
\ global state, and a task or process with its own records can walk in
\ parallel with others. A module that owns one walk record is still not
\ re-entrant itself: its check must not run again while that record is in
\ use. A record is made in the dictionary by walk: or walk2:, or at run time
\ in memory the caller provides by walk-init or walk2-init, with the same
\ layout.
\
\ walk-run pushes a root, then repeatedly spends one unit of fuel, pops a
\ node into walk-node and calls the visitor ( walk -- outcome ), which reads
\ that node and pushes its children. It stops at the first outcome that is
\ not ok, with exhausted when fuel reaches zero, full when the work stack
\ has no room for a push, or ok when the stack empties. Room for a push is
\ checked where the push happens, independently of fuel: a visit that took
\ the last unit of fuel and then finds no room for a child is full, not
\ exhausted (ADR 0008). A root that cannot be pushed means a corrupted
\ record (walk-start empties the stack and every record holds an item),
\ which is invalid. A visitor result outside the outcome vocabulary counts
\ as invalid. A node shared by several parents is visited, and charged,
\ once per path.
\ In a paired walk (walk2:) each item is a node plus one context cell, such
\ as the number of binders around that node; walk-take puts the context in
\ walk-context, and walk-run-pair and walk-push-pair take both cells.
\ A growable walk (walk-growable; plan task 6.2.0) has no fixed depth: a
\ push its work stack has no room for moves the stack to a heap block at
\ least twice as large, so it is full only when the heap refuses (and
\ for a corrupted count). walk-free gives the block back and returns the
\ walk to its first room, empty; until then the block keeps its largest
\ size. Every checker context's walks are growable (lib/context.fs frees
\ their blocks with the context).

require ./bounds.fs
require ./node.fs
require ./outcome.fs
require ./portability.fs

begin-structure walk-header
  field: walk-fuel       \ visits left
  field: walk-node       \ node being visited
  field: walk-context    \ its context cell, in a paired walk
  field: walk-arg        \ one cell for the visitor
  field: walk-pending    \ cells on the work stack
  field: walk-capacity   \ maximum cells
  field: walk-width      \ cells per item: 1, or 2 in a paired walk
  field: walk-heap       \ a growable walk's stack once it outgrew its room, or 0
  field: walk-grows      \ true for a growable walk
  field: walk-room       \ the cells of the record's own stack
end-structure

: walk-stack ( walk -- addr ) dup walk-heap @ ?dup if nip exit then walk-header + ;
: walk-bytes ( cells -- u ) cells walk-header + ;
: walk-paired? ( walk -- flag ) walk-width @ 2 = ;

\ Making a walk record with room for capacity items of one cell (walk-size,
\ walk-init, walk:) or of a node and its context (walk2-size, walk2-init,
\ walk2:). A capacity must be at least 1 and small enough for the size to
\ fit in a cell. walk-init and walk2-init zero walk-size or walk2-size
\ bytes at walk, or for a bad capacity give false and write nothing. The
\ defining words make name ( -- walk ) in the dictionary and abort on a bad
\ capacity.
\ Unchecked: width is 1 or 2.
: walk-span ( capacity width -- u ) * walk-bytes ;
: walk-plan? ( capacity width -- flag ) cells max-n walk-header - swap / 1 swap between? ;
: walk-format ( capacity width walk -- )
  >r tuck * r@ over walk-bytes erase dup r@ walk-capacity ! r@ walk-room ! r> walk-width ! ;
: walk-sized-init ( capacity width walk -- flag )
  >r 2dup walk-plan? if r> walk-format true else 2drop r> drop false then ;
: walk-size ( capacity -- u ) 1 walk-span ;
: walk2-size ( capacity -- u ) 2 walk-span ;
: walk-init ( capacity walk -- flag ) 1 swap walk-sized-init ;
: walk2-init ( capacity walk -- flag ) 2 swap walk-sized-init ;
: walk-sized ( capacity width "name" -- )
  2dup walk-plan? 0= abort" walk: bad capacity"
  create 2dup walk-span here swap allot walk-sized-init drop ;
: walk: ( capacity "name" -- ) 1 walk-sized ;
: walk2: ( capacity "name" -- ) 2 walk-sized ;

\ Set the budget for a walk; a negative fuel is refused and stores nothing.
: walk-budget ( fuel walk -- flag ) over 0< if 2drop false else walk-fuel ! true then ;

\ The work stack. A push fails, changing nothing, when the stack is full
\ (and the walk is not growable, or the heap refuses) or its count or
\ capacity is out of range; signed comparisons only.
: walk-fits? ( n walk -- flag )
  dup walk-pending @ swap walk-capacity @ rot - 0 swap between? ;
\ At least n more cells, double the capacity, at most the cells a cell
\ counts in address units (doubling past that would wrap).
max-n 1 cells / constant walk-most-cells
: walk-new-room ( n walk -- cells )
  dup walk-pending @ rot + swap walk-capacity @ walk-most-cells 2/ min 2* max
  walk-most-cells min ;
\ Move the items to a fresh heap block of cells cells; false, nothing
\ changed, when the heap refuses.
: walk-moved ( cells walk -- flag )
  over cells allocate if drop 2drop false exit then
  over walk-stack over 3 pick walk-pending @ cells move
  over walk-heap @ ?dup if free drop then
  over walk-heap ! walk-capacity ! true ;
\ A corrupted count, or a capacity below 1 (which no record has), is not
\ grown.
: walk-grow ( n walk -- flag )
  dup walk-capacity @ 1 < if 2drop false exit then
  dup walk-pending @ 0 2 pick walk-capacity @ between? 0= if 2drop false exit then
  2dup walk-new-room rot 2 pick walk-pending @ + over > if 2drop false exit then
  swap walk-moved ;
: walk-room-for? ( n walk -- flag )
  2dup walk-fits? if 2drop true exit then
  dup walk-grows @ if walk-grow else 2drop false then ;
\ Make a walk growable; give a growable walk's heap block back.
: walk-growable ( walk -- ) true swap walk-grows ! ;
: walk-free ( walk -- )
  dup walk-heap @ ?dup if free drop then 0 over walk-heap ! 0 over walk-pending !
  dup walk-room @ swap walk-capacity ! ;
: walk-room? ( walk -- flag ) 1 swap walk-room-for? ;
: walk-top ( walk -- addr ) dup walk-pending @ cells swap walk-stack + ;
: walk-push ( index walk -- flag )
  dup walk-room? if tuck walk-top ! 1 swap walk-pending +! true else 2drop false then ;
: walk-push-pair ( node context walk -- flag )
  2 over walk-room-for? if dup >r walk-top 2! 2 r> walk-pending +! true
  else drop 2drop false then ;
\ Unchecked: width <= pending <= capacity, and pending is a multiple of the
\ width (walk-loop only pops a nonempty stack).
: walk-pop ( walk -- index ) -1 over walk-pending +! walk-top @ ;
: walk-pop-pair ( walk -- node context ) -2 over walk-pending +! walk-top 2@ ;

\ Pushing children from a visitor. walk-child and walk-children require an
\ earlier node than the one being visited, which rules out cycles and
\ forward edges; walk-push-outcome, walk-push2 and the paired words do not
\ check, for inputs whose shape an earlier pass validated. A push that
\ finds no room is full, whatever fuel is left.
: walk-push-outcome ( index walk -- outcome ) walk-push room>outcome ;
: walk-push2 ( first second walk -- outcome )
  rot over walk-push if walk-push-outcome else 2drop outcome-full then ;
: walk-pair-outcome ( node context walk -- outcome ) walk-push-pair room>outcome ;
\ Paired: push first with the current node's context, then second with
\ the given one (so second is visited first).
: walk-children-at ( first second context walk -- outcome )
  >r rot r@ walk-context @ r@ walk-push-pair
  if r> walk-pair-outcome else 2drop r> drop outcome-full then ;
: walk-child? ( index walk -- flag ) walk-node @ index? ;
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
: walk-visit ( walk store xt -- outcome )
  >r walk-read if r> execute else r> drop outcome-invalid then ;
: walk-bad-tag ( first second walk tag -- outcome tag ) >r drop 2drop outcome-invalid r> ;

\ The loop. A step with no fuel left is exhausted; a root that cannot be
\ pushed (only a corrupted capacity) is invalid, spending nothing. A walk
\ starts with an empty work stack and no node being visited (-1), so a
\ walk that ends before its first visit names no node of an earlier one.
: walk-spend? ( walk -- flag )
  walk-fuel dup @ 0= if drop false else -1 swap +! true then ;
: walk-take-pair ( walk -- ) dup walk-pop-pair rot tuck walk-context ! walk-node ! ;
: walk-take ( walk -- )
  dup walk-paired? if walk-take-pair else dup walk-pop swap walk-node ! then ;
: walk-next ( xt walk -- outcome ) dup walk-take swap execute outcome-sane ;
: walk-step ( xt walk -- outcome )
  dup walk-spend? if walk-next else 2drop outcome-exhausted then ;
: walk-loop ( xt walk -- outcome )
  begin dup walk-pending @ 0> while
    2dup walk-step dup ok? 0= if nip nip exit then drop
  repeat 2drop outcome-ok ;
: walk-clear ( walk -- ) 0 over walk-pending ! -1 swap walk-node ! ;
: walk-start ( root walk -- flag ) dup walk-clear walk-push ;
: walk-run ( root xt walk -- outcome )
  rot over walk-start if walk-loop else 2drop outcome-invalid then ;
: walk-start-pair ( node context walk -- flag ) dup walk-clear walk-push-pair ;
: walk-run-pair ( node context xt walk -- outcome )
  >r -rot r@ walk-start-pair if r> walk-loop else drop r> drop outcome-invalid then ;
