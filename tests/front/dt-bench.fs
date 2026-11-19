\ Speed of src/front/discr-tree.fs (plan slice MF2+DT; not a test
\ target): n values under one root of the Init slice, each with a child
\ key of its own (Add's root key, then a constant key no slice has),
\ inserted, then inserted again (every child found through the child
\ table); times in microseconds. Usage, with gforth-fast:
\   gforth-fast tests/front/dt-bench.fs -e "300 run 3594 run 7000 run bye"
require ../../src/front/discr-tree.fs
require ./whnf-cases.fs
create tree /dtree allot   tree /dtree erase
: add0 ( t -- t' ) >r l0 1 s" Add" cn r> app ;
variable root-k
: key-like ( k -- k' ) elab-key-const elab-key-new made dup >r ek swap ek swap /ek move r> ;
: own-key ( i -- k ) elab-key-const elab-key-new made tuck elab-key-ref! ;
create paths 8000 cells allot
: path! ( i -- ) root-k @ key-like over 100000 + own-key drop swap cells paths + ! ;
: put ( i -- ) dup cells paths + @ 2 rot tree lf-dtree-insert drop ;
: now ( -- t ) utime d>s ;
: timed-puts ( n -- n us ) now over 0 do i put loop now swap - ;
: run ( n -- )   \ at most 8000
  tree lf-dtree-free nat add0 lf-dt-path made drop root-k !
  dup 0 do i path! loop timed-puts >r timed-puts r>
  rot . ." values: insert " 0 .r ."  us, insert again " 0 .r ."  us; nodes "
  tree lf-dtree-nodes# . cr ;
