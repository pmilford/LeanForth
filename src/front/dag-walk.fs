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
\     image is not made yet (dw-done? tells), nodes below the size only;
\   build ( node walk -- image )  the image, from the children's (dw-image);
\     it may end the walk with dw-refuse ( outcome walk -- ).
\ dw-run ( root walk -- image outcome ) runs a walk; the memo and the stack
\ are heap blocks made when it starts and freed before it returns, so a
\ walk keeps no address between runs. A record runs one walk at a time: a
\ walk whose build needs another walk uses another record (mvars.fs walks
\ levels inside a term walk). Untrusted front-end code.
\ No state of its own: every word takes the walk record.

require ../lib/lib.fs
require ../lib/bytes.fs

begin-structure /dw
  field: dw-pending      \ xt ( node walk -- child true | false )
  field: dw-build        \ xt ( node walk -- image )
  field: dw-size         \ nodes the memo holds: every node at the start
  field: dw-memo         \ heap: per node 0 unseen, 1 under way, image + 2 made
  field: dw-stack        \ heap: the pending nodes
  field: dw-top          \ cells of the stack in use
  field: dw-room         \ cells of the stack allocated
  field: dw-outcome      \ ok, or the first refusal
end-structure

16 constant dw-first-room
: dw-refuse ( outcome walk -- )
  dup dw-outcome @ ok? if dw-outcome ! else 2drop then ;
: dw-ok? ( walk -- flag ) dw-outcome @ ok? ;

\ The memo: one cell per node, 0 unseen, 1 under way, image + 2 made. A
\ walk's images are 0 or more (terms, levels, flags); a build that
\ refuses the walk may leave -1, which reads as "under way", but a refused
\ walk takes no further step. A node beyond the memo (a value given back
\ since it was assigned) is never done; its visit ends the walk invalid.
: dw-cell ( node walk -- addr ) dw-memo @ swap cells + ;
: dw-state ( node walk -- n ) dw-cell @ ;
: dw-in? ( node walk -- flag ) dw-size @ 0 swap within ;
: dw-done? ( node walk -- flag ) 2dup dw-in? if dw-state 1 > else 2drop false then ;
: dw-image ( node walk -- image ) dw-state 2 - ;
: dw-made ( image node walk -- ) dw-cell swap 2 + swap ! ;

\ The stack.
: dw-slot ( i walk -- addr ) dw-stack @ swap cells + ;
: dw-peek ( walk -- node ) dup dw-top @ 1- swap dw-slot @ ;
: dw-drop ( walk -- ) -1 swap dw-top +! ;
: dw-grown ( walk -- flag )
  dup dw-stack @ over dw-room @ 2* cells resize if 2drop false exit then
  over dw-stack ! dw-room dup @ 2* swap ! true ;
: dw-roomy ( walk -- flag )
  dup dw-top @ over dw-room @ < if drop true else dw-grown then ;
: dw-put ( node walk -- ) dup >r dup dw-top @ swap dw-slot ! 1 r> dw-top +! ;
: dw-push ( node walk -- )
  dup dw-roomy 0= if nip outcome-full swap dw-refuse exit then
  2dup dw-cell 1 swap ! dw-put ;

\ The tables, for every node there is when the walk starts.
: dw-block ( u addr -- flag ) swap 1 max allocate if drop 0 then dup rot ! 0<> ;
: dw-memo-erase ( walk -- ) dup dw-memo @ swap dw-size @ cells erase ;
: dw-tables ( walk -- flag )
  dw-first-room over dw-room ! dw-first-room cells over dw-stack dw-block
  over dw-size @ cells rot dw-memo dw-block and ;
: dw-free ( walk -- ) dup dw-memo heap-release dw-stack heap-release ;

\ One step: the node on top is made when its children are, else its first
\ pending child goes on top; a child under way is a cycle.
\ A node beyond the memo is no node of the walk: invalid.
: dw-pending? ( node walk -- child true | false ) dup dw-pending @ execute ;
: dw-cycle? ( child walk -- flag ) 2dup dw-in? if dw-state 1 = else 2drop true then ;
: dw-descend ( child walk -- )
  2dup dw-cycle? if nip outcome-invalid swap dw-refuse exit then dw-push ;
: dw-make ( node walk -- )
  dup >r 2dup dup dw-build @ execute -rot dw-made r> dw-drop ;
: dw-top-node ( walk -- node walk ) dup dw-peek swap ;
: dw-step ( walk -- )
  dw-top-node 2dup dw-pending? if over dw-descend 2drop else dw-make then ;
: dw-busy? ( walk -- flag ) dup dw-top @ 0> swap dw-ok? and ;
: dw-loop ( root walk -- )
  tuck dw-push begin dup dw-busy? while dup dw-step repeat drop ;
: dw-go ( root walk -- image outcome )
  2dup dw-in? 0= if 2drop -1 outcome-invalid exit then
  2dup dw-loop dup dw-ok? if dw-image outcome-ok else nip dw-outcome @ -1 swap then ;
: dw-run ( root walk -- image outcome )
  outcome-ok over dw-outcome ! 0 over dw-top !
  dup dw-tables 0= if dup dw-free 2drop -1 outcome-full exit then
  dup dw-memo-erase tuck dw-go rot dw-free ;
