\ Stack painting for Forth test files: how many cells of the host's data
\ and return stacks a word uses below its caller. Test-only words.
\ Both stacks are filled with a mark for paint-cells cells below their
\ tops (16 cells under the caller's stack pointers, room for the words
\ here); afterwards the deepest cell that no longer holds the mark gives
\ the use. Gforth's RP@ and SP@ (0.7.3 and 1.0), stacks that grow down.
\ A word that goes deeper than paint-cells, or writes the mark itself at
\ its deepest cell, is under-measured.

1400 constant paint-cells
48879 constant paint-mark
: paint-span ( top -- end start ) dup paint-cells cells - ;
: paint ( top -- ) paint-span ?do paint-mark i ! 1 cells +loop ;
: painted-cells ( top -- cells )
  dup paint-span ?do i @ paint-mark <> if i - 1 cells / unloop exit then 1 cells +loop
  drop 0 ;
: paint-tops ( -- rtop stop ) rp@ 16 cells - sp@ 16 cells - ;
\ Run xt ( -- ) and give the return-stack and data-stack cells it used
\ below the tops.
: stack-painted ( xt -- return-cells data-cells )
  paint-tops 2dup paint paint 2>r execute
  2r> painted-cells swap painted-cells swap ;
