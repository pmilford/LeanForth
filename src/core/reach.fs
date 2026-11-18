\ The nodes a declaration reaches (plan row FE1f; ADR 0021 D2): the term
\ and level nodes that given root terms reach through their parts, marked
\ in one sweep down each store. The stores only append, so a node's parts
\ come before it, and a sweep from the newest node to the oldest marks
\ every part of a marked node before it is visited. A term's parts are a
\ binary node's two children (application, binders, let, projection), a
\ Sort's level and a constant's universe arguments; a level's are its
\ successor's level and a max or imax's two. A metavariable's assignment
\ is no part: a reached metavariable is a hole, whatever the front end
\ assigned (core/mvar-leaves.fs). The export writer writes only reached
\ nodes for the front end (author/export.fs, lf-author-export-reached),
\ and the hand-over refuses a declaration that reaches a hole
\ (front/handover.fs), so a hole left unreachable in the stores, a
\ metavariable the elaborator made and no longer uses, blocks nothing.
\ Every term number from 0, an input view's too (core/terms.fs; authoring
\ runs read none); a negative count is taken as none. Untrusted, like the
\ writer and the front end.
\ Words: lf-reach-open ( -- flag ) the tables, for every node there is
\ now, nothing reached (false: no heap); lf-reach-close ( -- ) frees them;
\ lf-reach-term ( term -- ) a root (anything that is no node of the store,
\ -1 for an axiom's missing value, is ignored); lf-reach-sweep ( -- )
\ marks what the roots reach; lf-reached? ( term -- flag ),
\ lf-level-reached? ( level -- flag ); lf-reach-holes? ( -- flag ) whether
\ a reached node is a metavariable; lf-reach-annotations? ( -- flag )
\ whether a reached term is a smart-unfolding marker (core/annotations.fs:
\ a front-end node no declaration may hold; its child is no part, so the
\ hand-over refuses it first); lf-reach-param? ( name -- flag )
\ whether a reached level is the universe parameter name (Lean's
\ collectLevelParams, asked of one name); lf-holes-reached? ( term1 term2 --
\ flag outcome ) all of it for two roots: ok, or full when the heap has
\ no room for the tables (flag false then).
\ Example:
\   lf-reach-open drop  t lf-reach-term  lf-reach-sweep
\   t lf-reached?  lf-reach-holes?  lf-reach-close   \ true, then the holes
\ State: one context record, lf-reach (the two tables' heap blocks, freed
\ by lf-reach-close).

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/blocks.fs
require ../lib/bits.fs
require ./terms.fs
require ./levels.fs
require ./constant-references.fs
require ./constant-term-boundary.fs
require ./tagged-sort-boundary.fs
require ./mvar-leaves.fs

begin-structure /lf-reach
  field: lf-reach-terms     \ heap: a bit per term node, set when reached
  field: lf-reach-levels    \ heap: a bit per level, set when reached
  field: lf-reach-term#     \ term nodes the table holds
  field: lf-reach-level#    \ levels the table holds
end-structure
/lf-reach context-record: lf-reach

\ The tables: a bit per node (lib/bits.fs), erased (lib/blocks.fs).
: lr-erased ( n addr -- flag ) swap bits>cells cells swap block-zeroed ok? ;
\ A store's count, a corrupted negative one taken as none (review fe1f L4).
: lr-count ( addr -- n ) @ 0 max ;
\ Every term number: under an input view the store's own nodes start
\ lf-term-base higher (core/terms.fs), and the view's are marked too.
: lr-counts ( -- )
  lf-term-count lr-count lf-term-base + lf-reach lf-reach-term# !
  lf-level-count lr-count lf-reach lf-reach-level# ! ;
: lf-reach-close ( -- )
  lf-reach lf-reach-terms heap-release lf-reach lf-reach-levels heap-release ;
: lf-reach-open ( -- flag )
  lr-counts lf-reach lf-reach-term# @ lf-reach lf-reach-terms lr-erased
  lf-reach lf-reach-level# @ lf-reach lf-reach-levels lr-erased and
  dup 0= if lf-reach-close then ;

\ A node's bit; a number outside the table is never marked or reached.
: lr-terms ( -- a-addr ) lf-reach lf-reach-terms @ ;
: lr-levels ( -- a-addr ) lf-reach lf-reach-levels @ ;
\ Node i of a table of n bits: marked, or whether it is marked.
: lr-mark ( i n bits -- ) >r over swap index? if r> bit-on else r> 2drop then ;
: lr-marked? ( i n bits -- flag )
  >r over swap index? if r> bit@ else r> 2drop false then ;
: lr-term# ( -- n ) lf-reach lf-reach-term# @ ;
: lr-level# ( -- n ) lf-reach lf-reach-level# @ ;
: lf-reach-term ( term -- ) lr-term# lr-terms lr-mark ;
: lr-level! ( level -- ) lr-level# lr-levels lr-mark ;
: lf-reached? ( term -- flag ) lr-term# lr-terms lr-marked? ;
: lf-level-reached? ( level -- flag ) lr-level# lr-levels lr-marked? ;

\ A reached term's parts.
: lr-pair ( term -- ) dup lf-term-first@ lf-reach-term lf-term-second@ lf-reach-term ;
: lr-universes ( term -- )
  lf-const-slot lf-cref-pairs 0 ?do dup i lf-cref-pair@ drop lr-level! loop
  drop ;
\ A CASE with one arm per kind of term that has parts outside the binary tags.
: lr-leaf ( term tag -- )
  case lf-tag-symbolic-sort of lf-term-first@ lr-level! endof
    lf-tag-constant of lr-universes endof nip endcase ;
: lr-parts ( term -- )
  dup lf-term-tag@ dup lf-term-binary-tag? if drop lr-pair else lr-leaf then ;
: lr-visit ( term -- ) dup lf-reached? if lr-parts else drop then ;

\ A reached level's parts: a CASE with one arm per kind of level that has
\ parts.
: lr-level-pair ( level -- ) dup lf-level-first@ lr-level! lf-level-second@ lr-level! ;
: lr-level-parts ( level -- )
  dup lf-level-tag@ case lf-level-tag-succ of lf-level-first@ lr-level! endof
    lf-level-tag-max of lr-level-pair endof lf-level-tag-imax of lr-level-pair endof
    nip endcase ;
: lr-level-visit ( level -- ) dup lf-level-reached? if lr-level-parts else drop then ;

\ The sweeps, newest node first (n nodes; none when n is 0).
: lr-down ( n xt -- ) swap ?dup if 1- 0 swap do i over execute -1 +loop then drop ;
: lf-reach-sweep ( -- )
  lf-reach lf-reach-term# @ ['] lr-visit lr-down
  lf-reach lf-reach-level# @ ['] lr-level-visit lr-down ;

\ A reached metavariable, term or level.
: lr-term-hole? ( term -- flag ) dup lf-reached? swap lf-mvar? and ;
: lr-level-hole? ( level -- flag ) dup lf-level-reached? swap lf-level-mvar? and ;
: lr-term-holes? ( -- flag ) lf-reach lf-reach-term# @ ['] lr-term-hole? any? ;
: lr-level-holes? ( -- flag ) lf-reach lf-reach-level# @ ['] lr-level-hole? any? ;
: lf-reach-holes? ( -- flag ) lr-term-holes? lr-level-holes? or ;
\ A reached smart-unfolding marker.
: lr-annot? ( term -- flag ) dup lf-reached? swap lf-term-tag@ lf-tag-annotation = and ;
: lf-reach-annotations? ( -- flag ) lf-reach lf-reach-term# @ ['] lr-annot? any? ;

\ A reached universe parameter of that name.
: lr-param= ( name level -- flag )
  lf-level-slot dup node-tag @ lf-level-tag-param = swap node-first @ rot = and ;
: lr-param-reached? ( name level -- flag )
  dup lf-level-reached? if lr-param= else 2drop false then ;
: lf-reach-param? ( name -- flag )
  false lf-reach lf-reach-level# @ 0 ?do over i lr-param-reached? or loop nip ;

\ Two roots at once (a declaration's type and value).
: lr-roots ( term1 term2 -- ) lf-reach-term lf-reach-term lf-reach-sweep ;
: lf-holes-reached? ( term1 term2 -- flag outcome )
  lf-reach-open 0= if 2drop false outcome-full exit then
  lr-roots lf-reach-holes? lf-reach-close outcome-ok ;
