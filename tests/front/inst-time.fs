\ Timing of the instance table on all of Init (plan slice MF2+DT; not a
\ test target): Init's export and elaboration data loaded as
\ tests/front/synth-init.fs does, then timed: lf-inst-classes (before
\ MF2, the check of every record; since, the roots), S1's 13
\ getInstances problems and synth-init's 29 searches, their answers
\ printed as synth-init.fs prints them; then the tree's sizes (roots,
\ roots built, nodes, values, the widest node's children). Usage, with
\ gforth-fast (docs/development/FORTH_LIBRARY.md, the discrimination tree):
\   gforth-fast tests/front/inst-time.fs -e 's" EXPORT" s" DATA" timed stats bye'
require ./synth-init.fs
: now ( -- t ) utime d>s ;
: ms. ( t0 -- ) now swap - 1000 / 0 .r ."  ms" cr ;
: timed ( c-addr u c-addr' u' -- )
  now >r init-load ." load " r> ms.
  now lf-inst-classes swap >r ." classes " outcome-text type space r> ms.
  now >r problems ." problems " r> ms.
  now >r searches ." searches " r> ms. ;
: built# ( -- n ) 0 it-dt lf-dtree-roots# 0 ?do i it-dt lf-dtree-root-trie 0< 0= - loop ;
: children# ( n -- k )
  0 swap dn@ dn-child @ begin dup 0< 0= while swap 1+ swap dn@ dn-sibling @ repeat drop ;
: widest ( -- k ) it-dt dt-use 0 it-dt lf-dtree-nodes# 0 ?do i children# max loop ;
: stats ( -- )
  ." roots " it-dt lf-dtree-roots# . ." built " built# . ." nodes " it-dt lf-dtree-nodes# .
  ." values " it-dt lf-dtree-vals# . ." widest node's children " widest . cr ;
