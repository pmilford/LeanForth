\ Bottom-up walks of the front end's DAGs (plan task FE1b): terms or
\ levels, with the edges a walk follows beyond a node's own children (a
\ metavariable's assignment, src/front/mvars.fs). Each node reached gets an
\ image, made once from its children's images, which the walk keeps in a
\ memo: instantiating metavariables makes a new term, an occurs check a
\ flag. The pending nodes are on a stack in the heap that doubles as it
\ fills, so no walk's depth depends on the host's stacks (plan task
\ 6.2.0); a stack the heap cannot grow ends the walk full. A node met
\ again while its own walk is still under way is a cycle, which only a
\ broken assignment can make: the walk ends invalid, never with an image.
\ A walk is a record (/dw) of its two words, its size and its tables:
\   pending ( node walk -- child true | false )  the first child whose
\     image is not made yet (dw-done? tells; dw-want ( child walk -- child
\     true | false ) gives the child when it is one, dw-want2 ( a b walk --
\     child true | false ) the first of two, dw-want-parts ( node walk --
\     child true | false ) the first of a binary term's two parts), nodes
\     below the size only;
\   build ( node walk -- image )  the image, from the children's (dw-image,
\     dw-part-images ( node walk -- i1 i2 ) for a binary term's parts);
\     it may end the walk with dw-refuse ( outcome walk -- ), or with
\     dw-made ( x true | false walk -- x ) when a result needed room.
\ dw-on-terms and dw-on-levels ( build pending walk -- walk ) set a walk's
\ two words and its size: every term, or every level, there is now.
\ dw-run ( root walk -- image outcome ) runs a walk; its stack and its
\ states are heap blocks made when it starts and freed before it returns,
\ so a walk keeps no address between runs. The states are an array of
\ every node for a walk of at most dw-array-most nodes, else a keyed memo
\ (lib/memo.fs) of only the nodes the walk meets, so that a walk costs
\ what it visits, not the size of the term store (performance scan,
\ 2026-11-18: the array, made and erased for each run, was 41,000 cells
\ on average for 2.3 nodes visited in a check of Init).
\ front/lib-decode.fs keeps its two walks' tables, arrays of every node,
\ for a text's run instead, through dw-tables, dw-go and dw-free (plan
\ 9.4.8b gives that use words of its own). A record runs one
\ walk at a time: a walk whose build needs another walk uses another
\ record (mvars.fs walks levels inside a term walk). Untrusted front-end
\ code.
\ No state of its own: every word takes the walk record.

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/memo.fs
require ../core/terms.fs
require ../core/levels.fs

16 constant dw-first-room
begin-structure /dw
  field: dw-pending      \ xt ( node walk -- child true | false )
  field: dw-build        \ xt ( node walk -- image )
  field: dw-size         \ the walk's nodes: every node at the start
  field: dw-memo         \ heap: per node 0 unseen, 1 under way, image + 2 made; or 0
  field: dw-stack        \ heap: the pending nodes
  field: dw-top          \ cells of the stack in use
  field: dw-room         \ cells of the stack allocated
  field: dw-outcome      \ ok, or the first refusal
  /memo +field dw-seen   \ dw-run's states by node, as dw-memo's, for the nodes met
end-structure

\ The first refusal stays; refusing with ok changes nothing.
: dw-refuse ( outcome walk -- ) dw-outcome outcome-first! ;
: dw-ok? ( walk -- flag ) dw-outcome @ ok? ;

\ The memo: one cell per node, 0 unseen, 1 under way, image + 2 made. A
\ walk's images are 0 or more (terms, levels, flags); a build that
\ refuses the walk may leave -1, which reads as "under way", but a refused
\ walk takes no further step. A node beyond the memo (a value given back
\ since it was assigned) is never done; its visit ends the walk invalid.
\ A run of dw-run keeps the states in the memo dw-seen instead (no entry:
\ 0); a state the heap has no room to record refuses the walk, full.
: dw-cell ( node walk -- addr ) dw-memo @ swap cells + ;
: dw-array? ( walk -- flag ) dw-memo @ 0<> ;
: dw-seen@ ( node walk -- n ) 0 swap dw-seen memo@ 0= if 0 then ;
: dw-state ( node walk -- n ) dup dw-array? if dw-cell @ else dw-seen@ then ;
: dw-seen-cell ( node walk -- addr | 0 )
  tuck 0 swap dw-seen memo-claim dup ok? if drop nip else nip swap dw-refuse 0 then ;
: dw-seen! ( n node walk -- ) dw-seen-cell ?dup if ! else drop then ;
: dw-state! ( n node walk -- ) dup dw-array? if dw-cell ! else dw-seen! then ;
\ Under way (state 1).
: dw-seen-mark ( node walk -- ) dw-seen-cell ?dup if 1 swap ! then ;
: dw-mark ( node walk -- ) dup dw-array? if dw-cell 1 swap ! else dw-seen-mark then ;
: dw-in? ( node walk -- flag ) dw-size @ index? ;
: dw-done? ( node walk -- flag ) 2dup dw-in? if dw-state 1 > else 2drop false then ;
\ A pending word's test of one child: the child and true when its image
\ is not made yet, else false.
: dw-want ( child walk -- child true | false )
  2dup dw-done? if 2drop false else drop true then ;
\ The same for two children, the first one first.
: dw-want2 ( a b walk -- child true | false )
  rot over dw-want if nip nip true else dw-want then ;
\ The same for a binary term's two parts (core/terms.fs).
: dw-want-parts ( node walk -- child true | false )
  over lf-term-first@ over dw-want if nip nip true exit then
  swap lf-term-second@ swap dw-want ;
\ A pending word of a walk down binary terms only: a leaf has no child.
: dw-want-binary ( node walk -- child true | false )
  over lf-term-binary? if dw-want-parts else 2drop false then ;
\ Never met: neither under way nor made; a node beyond the memo counts as
\ new, so pushing it ends the walk invalid.
: dw-new? ( node walk -- flag ) 2dup dw-in? if dw-state 0= else 2drop true then ;
: dw-image ( node walk -- image ) dw-state 2 - ;
\ The images of a binary term's two parts, the first first (the build
\ step after dw-want-parts).
: dw-part-images ( node walk -- i1 i2 )
  over lf-term-second@ over dw-image >r swap lf-term-first@ swap dw-image r> ;
\ A build step's result that needed room ( x true | false ): x, or a
\ full walk and the image 0.
: dw-made ( x true | false walk -- x )
  swap if drop else outcome-full swap dw-refuse 0 then ;

\ A walk set up over every term, or every level, there is now, with its
\ build and pending words (a walk's two words are best kept as one
\ 2constant, ' build ' pending 2constant name).
: dw-hooks ( build pending walk -- walk ) tuck dw-pending ! tuck dw-build ! ;
: dw-on-terms ( build pending walk -- walk )
  dw-hooks lf-term-base lf-term-count @ + over dw-size ! ;
: dw-on-levels ( build pending walk -- walk ) dw-hooks lf-level-count @ over dw-size ! ;

\ The stack.
: dw-slot ( i walk -- addr ) dw-stack @ swap cells + ;
: dw-peek ( walk -- node ) dup dw-top @ 1- swap dw-slot @ ;
: dw-drop ( walk -- ) -1 swap dw-top +! ;
: dw-grown ( walk -- flag )
  dup dw-stack @ over dw-room @ 2* cells resize if 2drop false exit then
  over dw-stack ! dw-room dup @ 2* swap ! true ;
: dw-roomy ( walk -- flag )
  dup dw-top @ over dw-room @ < if drop true else dw-grown then ;
: dw-top-slot ( walk -- addr ) dup dw-top @ swap dw-slot ;
: dw-put ( node walk -- ) tuck dw-top-slot ! dw-top 1 swap +! ;
: dw-push ( node walk -- )
  dup dw-roomy 0= if nip outcome-full swap dw-refuse exit then
  2dup dw-mark dw-put ;

\ The tables, for every node there is when the walk starts.
: dw-block ( u addr -- flag ) swap 1 max allocate if drop 0 then dup rot ! 0<> ;
: dw-memo-erase ( walk -- ) dup dw-memo @ swap dw-size @ cells erase ;
: dw-stack-made ( walk -- flag )
  dw-first-room over dw-room ! dw-first-room cells swap dw-stack dw-block ;
: dw-memo-made ( walk -- flag ) dup dw-size @ cells swap dw-memo dw-block ;
: dw-tables ( walk -- flag ) dup dw-stack-made swap dw-memo-made and ;
: dw-free ( walk -- ) dup dw-memo heap-release dw-stack heap-release ;
\ A run of a walk of more than dw-array-most nodes keeps its states in
\ dw-seen: an array of them all, made and erased for each run, would cost
\ more than the nodes it visits (the cut-over is where erasing 4,096 cells
\ takes about as long as a memo's first entries).
4096 constant dw-array-most
: dw-seen-made ( walk -- flag ) 1 1 rot dw-seen memo-init ok? ;
: dw-seen-start ( walk -- flag ) dup dw-stack-made swap dw-seen-made and ;
: dw-seen-end ( walk -- ) dup dw-stack heap-release dw-seen memo-free ;

\ One step: the node on top is made when its children are, else its first
\ pending child goes on top; a child under way is a cycle.
\ A node beyond the memo is no node of the walk: invalid.
: dw-pending? ( node walk -- child true | false ) dup dw-pending @ execute ;
: dw-cycle? ( child walk -- flag ) 2dup dw-in? if dw-state 1 = else 2drop true then ;
: dw-descend ( child walk -- )
  2dup dw-cycle? if nip outcome-invalid swap dw-refuse exit then dw-push ;
: dw-make ( node walk -- )
  tuck 2dup dup dw-build @ execute 2 + -rot dw-state! dw-drop ;
: dw-top-node ( walk -- node walk ) dup dw-peek swap ;
: dw-step ( walk -- )
  dw-top-node 2dup dw-pending? if over dw-descend 2drop else dw-make then ;
: dw-busy? ( walk -- flag ) dup dw-top @ 0> swap dw-ok? and ;
: dw-loop ( root walk -- )
  tuck dw-push begin dup dw-busy? while dup dw-step repeat drop ;
: dw-go ( root walk -- image outcome )
  2dup dw-in? 0= if 2drop -1 outcome-invalid exit then
  2dup dw-loop dup dw-ok? if dw-image outcome-ok else nip dw-outcome @ -1 swap then ;
: dw-array-run ( root walk -- image outcome )
  dup dw-tables 0= if dup dw-free 2drop -1 outcome-full exit then
  dup dw-memo-erase tuck dw-go rot dw-free ;
: dw-seen-run ( root walk -- image outcome )
  dup dw-seen-start 0= if dw-seen-end drop -1 outcome-full exit then
  dup >r dw-go r> dw-seen-end ;
: dw-run ( root walk -- image outcome )
  outcome-ok over dw-outcome ! 0 over dw-top !
  dup dw-size @ dw-array-most > if dw-seen-run else dw-array-run then ;
