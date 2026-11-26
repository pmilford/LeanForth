\ The lean walk of instantiation (group kernel-speed-3, the prototype's P3;
\ docs/design/TERM_STORE.md, "As landed"): a rebuilding walk of a node's
\ subtree on its pass's frames record (lib/frame.fs) in which only a node
\ to rebuild takes room on the frames' stack, two cells: the node, then
\ the first child's result. A kept child -- a leaf, a node the pass gives
\ back unvisited, a result the replace memo gives -- is tested and charged
\ its unit of fuel inline, with no frame. [kernel] code: not through the
\ review gate (AGENTS.md).
\
\ The walk visits the nodes the frame machine visits, in the same order,
\ each for one unit of fuel at the moment its visit would have begun and
\ after the same test (frame-admit's: zero or negative fuel is
\ exhausted): a binary node's first child after the node's own tests (so
\ the binder check comes before any child is charged), its second child
\ only after the first child's subtree has returned, one binder deeper
\ under a lambda or Pi. The pass gives two steps, set while loading
\ (mixed-open.fs):
\
\   look ( x frames -- r outcome true | x false )   x's visit, its unit spent:
\       a result, or false for a binary node to rebuild
\   join ( r1 node r2 -- result outcome )          node from its children's results
\
\ A walk runs inside its root's own visit (lf-walk-node, from the
\ frame-call that admitted the root and charged it), from the cells the
\ stack then holds, kept in the frames' job cell; a failure gives the
\ frames back to them, the context as at the start, and the failure
\ itself. A stack the heap cannot grow is full, as before, but at another
\ step: the walk asks room only for a node to rebuild (the exception
\ declared in TERM_STORE.md). Depth is bounded only by the heap, as the
\ frame machine's.
\
\ Interface: lf-walk-look, lf-walk-join (deferred, set while loading),
\ lf-walk-node ( x frames -- r outcome frames ). State: the two steps,
\ fixed once loaded; every word works on the frames record it is given.

require ../lib/lib.fs
require ../core/terms.fs
require ./mixed-rebuild.fs

defer lf-walk-look ( x frames -- r outcome true | x false )
defer lf-walk-join ( r1 node r2 -- result outcome )
\ The mark of a node whose first child is being walked (no result is
\ negative but -1, a failure's).
-2 constant lf-walk-first

\ One unit of fuel: true, or false when none is left, the fuel unchanged.
: lf-walk-fuel? ( frames -- flag )
  frame-fuel dup @ 0> if -1 swap +! true else drop false then ;
\ A visit's result, or a failure, with the frames on top.
: lf-walk-result ( frames r outcome -- r outcome frames true ) rot true ;
: lf-walk-failed ( frames outcome -- -1 outcome frames true ) -1 swap lf-walk-result ;
\ x to rebuild: kept with the mark, its first child walked next.
: lf-walk-into ( x frames -- x' frames false | -1 outcome frames true )
  2 over frame-room? 0= if nip outcome-full lf-walk-failed exit then
  2dup frame-save lf-walk-first over frame-save swap lf-term-first@ swap false ;
\ x visited, its unit spent; then x charged its unit first.
: lf-walk-seen ( x frames -- x' frames false | r outcome frames true )
  tuck lf-walk-look if lf-walk-result exit then swap lf-walk-into ;
: lf-walk-visit ( x frames -- x' frames false | r outcome frames true )
  dup lf-walk-fuel? 0= if nip outcome-exhausted lf-walk-failed exit then lf-walk-seen ;
: lf-walk-down ( x frames -- r outcome frames ) begin lf-walk-visit until ;

\ Up from a child's result: the node's second child next, one binder
\ deeper under a lambda or Pi; or, after it, the node from both results.
: lf-walk-deeper ( frames node -- frames node )
  dup lf-rebuild-binder? if over 1 swap frame-context+! then ;
: lf-walk-shallower ( frames node -- frames node )
  dup lf-rebuild-binder? if over -1 swap frame-context+! then ;
: lf-walk-second ( r1 frames -- x' frames false )
  tuck frame-save 1 over frame-pick lf-walk-deeper lf-term-second@ swap false ;
: lf-walk-joined ( r2 r1 frames -- r outcome frames true )
  dup frame-restore lf-walk-shallower swap >r rot lf-walk-join r> true ;
: lf-walk-up ( r frames -- x' frames false | r' outcome frames true )
  dup frame-restore dup lf-walk-first = if drop lf-walk-second exit then
  swap lf-walk-joined ;

\ The walk's own cells, from its base (the job cell) up; a failure takes
\ them back, a node's binder with them.
: lf-walk-base? ( frames -- flag ) dup frame-used @ swap frame-job @ = ;
: lf-walk-pop ( frames -- frames )
  dup frame-restore lf-walk-first = over frame-restore swap
  if drop else lf-walk-shallower drop then ;
: lf-walk-settle ( r outcome frames -- r outcome frames )
  over ok? if exit then begin dup lf-walk-base? 0= while lf-walk-pop repeat ;
\ Up while results come back ok above the base; down again at a second
\ child.
: lf-walk-on? ( r outcome frames -- r outcome frames flag )
  over ok? if dup lf-walk-base? 0= else false then ;
: lf-walk-rise ( r outcome frames -- r outcome frames true | x' frames false )
  begin lf-walk-on? while nip lf-walk-up 0= if false exit then repeat
  lf-walk-settle true ;
: lf-walk-run ( x frames -- r outcome frames ) begin lf-walk-down lf-walk-rise until ;
\ x's subtree walked, x's unit spent (the visit that runs this): its result.
: lf-walk-node ( x frames -- r outcome frames )
  dup frame-used @ over frame-job ! lf-walk-seen 0= if lf-walk-run then ;
