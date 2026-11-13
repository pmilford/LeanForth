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
\ The stores' own nodes only, numbered from 0: authoring runs read no
\ input view (core/terms.fs). Untrusted, like the writer and the front end.
\ Words: lf-reach-open ( -- flag ) the tables, for every node there is
\ now, nothing reached (false: no heap); lf-reach-close ( -- ) frees them;
\ lf-reach-term ( term -- ) a root (anything that is no node of the store,
\ -1 for an axiom's missing value, is ignored); lf-reach-sweep ( -- )
\ marks what the roots reach; lf-reached? ( term -- flag ),
\ lf-level-reached? ( level -- flag ); lf-reach-holes? ( -- flag ) whether
\ a reached node is a metavariable; lf-reach-param? ( name -- flag )
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
require ./terms.fs
require ./levels.fs
require ./constant-references.fs
require ./constant-term-boundary.fs
require ./tagged-sort-boundary.fs
require ./mvar-leaves.fs

begin-structure /lf-reach
  field: lf-reach-terms     \ heap: a cell per term node, true when reached
  field: lf-reach-levels    \ heap: a cell per level, true when reached
  field: lf-reach-term#     \ term nodes the table holds
  field: lf-reach-level#    \ levels the table holds
end-structure
/lf-reach context-record: lf-reach

\ The tables: a cell per node, erased.
: lr-block ( u addr -- flag ) swap 1 max allocate if drop 0 then dup rot ! 0<> ;
: lr-erased ( n addr -- flag ) over cells over lr-block if @ swap cells erase true
  else 2drop false then ;
: lr-counts ( -- )
  lf-term-count @ lf-reach lf-reach-term# ! lf-level-count @ lf-reach lf-reach-level# ! ;
: lf-reach-close ( -- )
  lf-reach lf-reach-terms heap-release lf-reach lf-reach-levels heap-release ;
: lf-reach-open ( -- flag )
  lr-counts lf-reach lf-reach-term# @ lf-reach lf-reach-terms lr-erased
  lf-reach lf-reach-level# @ lf-reach lf-reach-levels lr-erased and
  dup 0= if lf-reach-close then ;

\ A node's cell; a number outside the table is never marked or reached.
: lr-in? ( i n -- flag ) 0 swap within ;
: lr-term ( term -- addr ) cells lf-reach lf-reach-terms @ + ;
: lr-level ( level -- addr ) cells lf-reach lf-reach-levels @ + ;
: lr-term? ( term -- flag ) lf-reach lf-reach-term# @ lr-in? ;
: lr-level? ( level -- flag ) lf-reach lf-reach-level# @ lr-in? ;
: lf-reach-term ( term -- ) dup lr-term? if true swap lr-term ! else drop then ;
: lr-level! ( level -- ) dup lr-level? if true swap lr-level ! else drop then ;
: lf-reached? ( term -- flag ) dup lr-term? if lr-term @ else drop false then ;
: lf-level-reached? ( level -- flag ) dup lr-level? if lr-level @ else drop false then ;

\ A reached term's parts.
: lr-pair ( term -- ) dup lf-term-first@ lf-reach-term lf-term-second@ lf-reach-term ;
: lr-universes ( term -- )
  lf-term-first@ lf-cref-slot lf-cref-pairs 0 ?do dup i lf-cref-pair@ drop lr-level! loop
  drop ;
\ A CASE with one arm per kind of term that has parts outside the binary tags.
: lr-leaf ( term tag -- )
  case lf-tag-symbolic-sort of lf-term-first@ lr-level! endof
    lf-tag-constant of lr-universes endof nip endcase ;
: lr-parts ( term -- )
  dup lf-term-tag@ dup lf-term-binary-tag? if drop lr-pair else lr-leaf then ;
: lr-visit ( term -- ) dup lf-reached? if lr-parts else drop then ;

\ A reached level's parts.
: lr-level-tag ( level -- tag ) lf-level-slot node-tag @ ;
: lr-level-pair ( level -- )
  lf-level-slot dup node-first @ lr-level! node-second @ lr-level! ;
: lr-level-parts ( level -- )
  dup lr-level-tag dup lf-level-binary-tag? if drop lr-level-pair exit then
  lf-level-tag-succ = if lf-level-slot node-first @ lr-level! else drop then ;
: lr-level-visit ( level -- ) dup lf-level-reached? if lr-level-parts else drop then ;

\ The sweeps, newest node first (n nodes; none when n is 0).
: lr-down ( n xt -- ) swap ?dup if 1- 0 swap do i over execute -1 +loop then drop ;
: lf-reach-sweep ( -- )
  lf-reach lf-reach-term# @ ['] lr-visit lr-down
  lf-reach lf-reach-level# @ ['] lr-level-visit lr-down ;

\ A reached metavariable, term or level.
: lr-term-hole? ( flag term -- flag' ) dup lf-reached? swap lf-mvar? and or ;
: lr-level-hole? ( flag level -- flag' )
  dup lf-level-reached? swap lf-level-mvar? and or ;
: lr-term-holes? ( -- flag )
  false lf-reach lf-reach-term# @ 0 ?do i lr-term-hole? loop ;
: lr-level-holes? ( -- flag )
  false lf-reach lf-reach-level# @ 0 ?do i lr-level-hole? loop ;
: lf-reach-holes? ( -- flag ) lr-term-holes? lr-level-holes? or ;

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
