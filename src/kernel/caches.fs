\ The checker's result caches, as Lean's type checker keeps them (ADR 0014
\ Q10 and its Amendment 1; plan task 4.2.7): ports of type_checker::state
\ (type_checker.h 25-49) at the referee commit eb6cafb7. [kernel] code:
\ experimental, not through the review gate, not independently audited.
\
\ What is cached, and where (Lean's lines in type_checker.cpp):
\ - inferred types, one table per mode, m_infer_type[infer_only]: looked
\   up when inference enters a node (332-334), filled when it ends with a
\   type (356); checking and infer-only (lf-minfer-aside) never share;
\ - whnf_core results, m_whnf_core: looked up when whnf_core enters a
\   node that is no easy case (490-493), and at each step that goes on
\   with a new node within a visit (Lean's recursive calls, 523, 533, 538,
\   543); filled when the visit ends with a result other than its node
\   (547-549), unless it ran with cheap_proj (whnf.fs);
\ - whnf results, m_whnf: looked up after the easy cases (724-727),
\   filled with the result (733, 739);
\ - unfolded values, m_unfold: a constant with universe arguments and its
\   value with them put for the parameters (573-579);
\ - pairs shown equal, m_success: looked up by quick_is_def_eq after ==
\   (804, succeeded_before 927-937), filled when is_def_eq answers yes
\   (1211-1212, cache_success 939-944), both orders;
\ - pairs whose same-head argument test failed, m_failure: read and
\   filled only by lazy delta's same-declaration test (1004-1009,
\   failed_before 908-918, cache_failure 920-925).
\ Lean 4.35.0 has no union-find (equivalence manager): type_checker.h
\ 33-39 explains that is_def_eq is not transitive, so a closure of the
\ successes would make answers depend on the order of evaluation; nor
\ does LeanForth.
\
\ Keys: Lean's == by skeletons (ADR 0014 Q3). Lean compares keys with ==
\ (structural equality, expr_eq_fn). LeanForth's term store is not hash-
\ consed (a rebuilt term is a new node), so every node a cache meets gets
\ a skeleton: a number that two nodes share only when they are Lean's ==
\ -- the same tag, and the skeletons of their children (application,
\ lambda, Pi), or, for a leaf, the same bound-variable index, the same
\ free-variable node (one per local-context entry), the same level
\ syntax (levels get skeletons the same way: zero, the same parameter,
\ succ, max or imax of the same skeletons), the same constant name and
\ universe-argument skeletons, the same literal value, the same
\ projection name and index, or the same let flag (mixed-compare.fs
\ compares exactly these). A literal of several limbs, a string literal,
\ or any other leaf, has a skeleton of its own node, so it equals itself only: a miss
\ where Lean might hit, never a false hit. A skeleton is found in a table
\ of (kind, part, part) keys, and kept per node with its identity
\ (identities never repeat, so a rolled-back index is a new node), with
\ the node's loose bound variables (1 + the largest index beyond its own
\ binders, or 0: Lean's loose_bvar_range), computed once from its
\ children's on a growable stack. Names are compared by their number
\ (equal names share one in the stage's tier: import/feed.fs), so names
\ equal by text with two numbers are a miss.
\ A cached value is a node with its identity; an entry whose node no
\ longer has it (its scratch was discarded) is a miss. An inferred type's
\ key also names the scope: inference reads a source node under the
\ scope (mixed-infer.fs), a loose bound variable k being the scope's
\ free variable k places from the top, so the key is the skeleton with 0
\ when the node has no loose bound variable, else with the identity of
\ the scope's innermost free variable, which fixes the whole scope (each
\ binder gets a new free variable over an unchanged scope). A lambda read
\ as the body of a lambda (mixed-infer.fs's chain) has a type over the
\ chain's bound variables, not closed: it is neither looked up nor kept.
\ The pair caches take closed terms only (as Lean compares only closed
\ terms; check-block.fs compares open ones, whose types the typer reads
\ under the scope), ordered by skeleton, so a success on (t, s) answers
\ (s, t).
\
\ Why each is sound. Kernel terms have no metavariables and free
\ variables are unique with fixed types (type_checker.h 33-39), so
\ inference, whnf_core, whnf, unfolding and is_def_eq are functions of
\ their arguments within one check's environment snapshot and one local
\ context. Every table is emptied when either changes: when a check
\ begins (check-declaration.fs) and when an inference job starts, which
\ empties the local context (mixed-infer.fs; an inductive block's check
\ starts several jobs without discarding scratch). Within a job the local
\ context only grows. A block's recursor builder (inductive-recursor.fs)
\ runs whnf outside any job, on the last job's tables: its terms name no
\ free variable, so no key they meet depends on that context (ADR 0014
\ Amendment 1, review rvCACHE L4). While the caches are on, inference and comparison
\ keep their scratch until the job ends (mixed-infer.fs's discard and
\ mixed-convert.fs's restore do nothing) where the stores have ample room
\ (below), so entries stay useful, as Lean's live for the whole check.
\ Only definite results are kept: a pass that ends unknown, exhausted,
\ full, invalid or rejected keeps nothing. LeanForth's doubt record
\ (defeq.fs) cannot arise where the pair caches work: they work only
\ when the comparison has a typer (in a check it always has), and a
\ failure is kept only without doubt. Beyond Lean's, LeanForth also
\ keeps a whnf_core result reached by iota or quotient reduction or from
\ a let variable (Lean returns at 533 and 503 without keeping): a memo
\ of the same function, which changes no answer.
\
\ When the caches are on: in a check of the checked environment
\ (lf-whnf-env?), with the derivation log off (with it on every step is
\ logged; plan task 4.2.7b would log a hit), and unless a test turned
\ them off (lf-caches-enable). Off, every pass runs exactly as without
\ this module.
\
\ Fuel (ADR 0014 Q9). Entering a pass costs one unit, a hit too, as
\ before; a hit then ends the pass. A miss costs nothing more: the cache's
\ step gives back the unit of the visit it opens around the pass. Looking
\ up, keeping and skeletons cost no fuel (Lean's caches, hashes and
\ cached node data cost no steps either); each is bounded by the nodes
\ the check has. A table or stack that cannot grow (no heap) keeps
\ nothing more: a miss, never a verdict.
\
\ Lean's cached node data. The skeleton table also keeps, per node, what
\ Lean keeps in each node: its loose bound variables and whether it has a
\ free variable or a universe parameter. whnf.fs's has_loose_bvars and
\ has_fvar walks are then answered from it, mixed-open.fs's instantiate
\ and abstract keep a node that cannot change without visiting it (Lean's
\ replace), defeq.fs's == holds at once for one skeleton, and
\ core/terms.fs's lf-term-data@ gives the three as one data word (until
\ the compact store keeps it in each record: plan step S3).
\
\ Interface: lf-caches-enable ( flag -- ), lf-caches-on? ( -- flag ),
\ lf-caches-clear ( -- ), lf-term-facts ( node -- id bits true | false ),
\ lf-cache-stats ( cache -- hits misses ) with the caches lf-cache-infer,
\ lf-cache-infer-only, lf-cache-whnf-core, lf-cache-whnf,
\ lf-cache-unfold, lf-cache-success and lf-cache-failure ( -- cache ).
\ Loading this module sets the hooks of whnf.fs, defeq.fs, mixed-infer.fs,
\ mixed-convert.fs, mixed-open.fs and core/terms.fs (lf-term-data@).
\ State: one record, lf-caches (the switch, the key being looked up, the
\ next skeleton, two stacks' depths, and nine tables: each a hash table
\ of lib/htab.fs over a slab of entries), and two growable stacks
\ (lf-caches-stack, lf-caches-lstack), members of the checker context
\ (lib/context.fs), freed with it. The tables' hooks are shared and
\ read-only.

require ../lib/lib.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ../lib/slab.fs
require ../core/derivation-log.fs
require ../core/local-context.fs
require ../core/terms.fs
require ./whnf.fs
require ./defeq.fs
require ./mixed-convert.fs
require ./mixed-infer.fs
require ./mixed-open.fs

\ ---------------------------------------------------------------------------
\ A cache: a hash table first (its hooks find the cache at its address),
\ over a slab of entries of four key cells and two value cells.
6 cells constant /lf-cent
begin-structure /lf-cache
  /htab +field lf-cache-table
  /slab +field lf-cache-entries
  field: lf-cache-hits
  field: lf-cache-misses
end-structure
9 constant lf-caches#
begin-structure /lf-caches
  field: lf-caches-off            \ true when a test turned the caches off
  field: lf-caches-next           \ the last skeleton given
  field: lf-caches-sp             \ cells on lf-caches-stack
  field: lf-caches-lsp            \ cells on lf-caches-lstack
  4 cells +field lf-caches-key    \ the key being looked up or kept
  /lf-cache lf-caches# * +field lf-caches-tables
end-structure
/lf-caches context-record: lf-caches
1 cells context-slab: lf-caches-stack    \ terms waiting for their skeletons
1 cells context-slab: lf-caches-lstack   \ levels waiting for theirs
: lf-cache-nth ( i -- cache ) /lf-cache * lf-caches lf-caches-tables + ;
: lf-cache-infer ( -- cache ) 0 lf-cache-nth ;        \ m_infer_type[false]
: lf-cache-infer-only ( -- cache ) 1 lf-cache-nth ;   \ m_infer_type[true]
: lf-cache-whnf-core ( -- cache ) 2 lf-cache-nth ;    \ m_whnf_core
: lf-cache-whnf ( -- cache ) 3 lf-cache-nth ;         \ m_whnf
: lf-cache-unfold ( -- cache ) 4 lf-cache-nth ;       \ m_unfold
: lf-cache-success ( -- cache ) 5 lf-cache-nth ;      \ m_success
: lf-cache-failure ( -- cache ) 6 lf-cache-nth ;      \ m_failure
: lf-cache-memo ( -- cache ) 7 lf-cache-nth ;         \ node -> skeleton, loose
: lf-cache-skel ( -- cache ) 8 lf-cache-nth ;         \ key -> skeleton
: lf-cache-stats ( cache -- hits misses ) dup lf-cache-hits @ swap lf-cache-misses @ ;

\ Entries and the key.
: lf-cent ( n cache -- addr ) lf-cache-entries slab-at ;
: lf-cent-hash ( addr -- h )
  0 over @ hash-step over cell+ @ hash-step over 2 cells + @ hash-step
  swap 3 cells + @ hash-step ;
: lf-cache-key ( -- addr ) lf-caches lf-caches-key ;
: lf-key! ( k1 k2 k3 k4 -- )
  lf-cache-key 3 cells + ! lf-cache-key 2 cells + ! lf-cache-key cell+ ! lf-cache-key ! ;
: lf-cache-rehash ( n htab -- h ) lf-cent lf-cent-hash ;
: lf-cache-same ( n key htab -- flag ) rot swap lf-cent 4 cells tuck compare 0= ;
create lf-cache-hooks /htab-hooks allot
' lf-cache-rehash ' lf-cache-same lf-cache-hooks htab-hooks!

\ Each context's tables: made when first emptied, so a new context holds
\ no heap block until it checks (a table the heap refuses is not live: it
\ then keeps nothing), and freed with the context.
: lf-cache-table-init ( cache -- ) 4 lf-cache-hooks rot lf-cache-table htab-init drop ;
: lf-cache-make ( cache -- )
  dup lf-cache-table-init
  /lf-cent dup slab-limit-max rot lf-cache-entries slab-init drop ;
: lf-cache-release ( cache -- ) dup lf-cache-table htab-free lf-cache-entries slab-free ;
: lf-caches-some ( xt n -- )
  0 lf-cache-nth swap 0 ?do 2dup swap execute /lf-cache + loop 2drop ;
: lf-caches-each ( xt -- ) lf-caches# lf-caches-some ;
:noname ( -- ) ['] lf-cache-release lf-caches-each ; context-teardown

\ Emptying: a large table or slab goes back to a small one, so that an
\ emptying costs little whatever an earlier check needed.
1024 constant lf-cache-small
: lf-cache-small? ( cache -- flag )
  lf-cache-table dup htab-live? if htab-slots lf-cache-small <= else drop false then ;
: lf-cache-trim ( slab -- )
  dup slab-capacity lf-cache-small > if dup slab-trim drop then drop ;
: lf-cache-empty ( cache -- )
  dup lf-cache-table htab-live? 0= if lf-cache-make exit then
  dup lf-cache-entries dup slab-clear lf-cache-trim
  dup lf-cache-small? if lf-cache-table htab-clear exit then
  dup lf-cache-table htab-free lf-cache-table-init ;
\ Empty every table and start the skeletons again (a check begins, an
\ inference job starts).
: lf-caches-clear ( -- ) ['] lf-cache-empty lf-caches-each 0 lf-caches lf-caches-next ! ;

\ The switch, and whether the caches are on now (see the header).
: lf-caches-enable ( flag -- ) 0= lf-caches lf-caches-off ! ;
: lf-caches-on? ( -- flag )
  lf-caches lf-caches-off @ if false exit then
  lf-log? if false exit then lf-whnf-env? ;

\ ---------------------------------------------------------------------------
\ Finding and keeping, with the key in lf-cache-key.
: lf-cache-find ( cache -- n true | i false )
  >r lf-cache-key dup lf-cent-hash r> lf-cache-table htab-find ;
\ The entry's address, or 0.
: lf-cache-entry ( cache -- addr|0 )
  dup lf-cache-table htab-live? 0= if drop 0 exit then
  dup lf-cache-find if swap lf-cent else 2drop 0 then ;
: lf-cent-value! ( v1 v2 addr -- ) tuck 5 cells + ! 4 cells + ! ;
: lf-cent-values ( addr -- v1 v2 ) dup 4 cells + @ swap 5 cells + @ ;
: lf-cent-fill ( v1 v2 addr -- ) lf-cache-key over 4 cells move lf-cent-value! ;
: lf-cache-add ( v1 v2 i cache -- flag )
  1 over lf-cache-entries slab-claim ok-then? 0= if 2drop 2drop drop false exit then
  2dup swap lf-cent >r -rot lf-cache-table htab-put r> lf-cent-fill true ;
\ Keep the key with v1 v2, replacing an entry's values: true, or false
\ when the table cannot grow (nothing kept).
: lf-cache-put ( v1 v2 cache -- flag )
  dup lf-cache-table htab-live? 0= if drop 2drop false exit then
  dup lf-cache-table htab-ready ok? 0= if drop 2drop false exit then
  dup lf-cache-find if swap lf-cent lf-cent-value! true else swap lf-cache-add then ;

\ ---------------------------------------------------------------------------
\ Skeletons (see the header). A key's kind: a term's tag (all below 64),
\ a level's tag plus 64, a cell of a universe-argument list, or a node of
\ its own.
64 constant lf-skel-level
128 constant lf-skel-cons
129 constant lf-skel-node
lf-tag-let lf-skel-level < lf-tag-lit lf-skel-level < and lf-tag-proj lf-skel-level < and
lf-tag-str lf-skel-level < and
0= [if] .( caches.fs: term tags must be below 64) cr abort [then]
\ The skeleton of the key (kind a b), a new one when the key is new; 0 is
\ none (an empty list).
: lf-skel-new ( -- id ) lf-caches lf-caches-next dup @ 1+ dup rot ! ;
: lf-skel ( kind a b -- id true | false )
  0 lf-key! lf-cache-skel lf-cache-entry ?dup if 4 cells + @ true exit then
  lf-skel-new dup 0 lf-cache-skel lf-cache-put if true else drop false then ;

\ Growable stacks: depth cell sp, cells in slab.
: lf-sk-push ( x sp slab -- flag )
  over @ 1+ over slab-hold ok? 0= if 2drop drop false exit then
  over @ swap slab-at rot swap ! 1 swap +! true ;
: lf-sk-top ( sp slab -- x ) swap @ 1- swap slab-at @ ;
: lf-sk-pop ( flag sp -- flag ) over if -1 swap +! else drop then ;

\ Levels: kept per level index with its identity (kind 2 of the memo),
\ with the skeleton and whether a universe parameter occurs in the level
\ (1, else 0: Lean's has_param_univ).
: lf-lmemo-key ( level -- flag )
  dup lf-level-identity if >r 2 swap r> 0 lf-key! true else drop false then ;
: lf-level-memo@ ( level -- id params true | false )
  lf-lmemo-key 0= if false exit then
  lf-cache-memo lf-cache-entry ?dup if lf-cent-values true else false then ;
: lf-level-id@ ( level -- id true | false ) lf-level-memo@ if drop true else false then ;
: lf-level-id! ( level id params -- flag )
  rot lf-lmemo-key if lf-cache-memo lf-cache-put else 2drop false then ;
: lf-cl-sp ( -- addr ) lf-caches lf-caches-lsp ;
: lf-cl-push ( level -- flag ) lf-cl-sp lf-caches-lstack lf-sk-push ;
: lf-cl-pop ( flag -- flag ) lf-cl-sp lf-sk-pop ;
\ Whether a parameter occurs in a level whose children are kept: 1 or 0,
\ or -1 when a child has no entry (then the level gets none either).
: lf-cl-child ( level -- params ) lf-level-memo@ if nip else -1 then ;
: lf-cl-either ( p1 p2 -- params ) 2dup min 0< if 2drop -1 else or then ;
: lf-cl-pair ( level -- params )
  dup lf-level-first@ lf-cl-child swap lf-level-second@ lf-cl-child lf-cl-either ;
: lf-cl-params ( level -- params )
  dup lf-level-tag@ case
    lf-level-tag-param of drop 1 endof  lf-level-tag-zero of drop 0 endof
    lf-level-tag-succ of lf-level-first@ lf-cl-child endof  swap lf-cl-pair swap endcase ;
: lf-cl-keep ( level id -- flag )
  over lf-cl-params dup 0< if drop 2drop false else lf-level-id! then ;
: lf-cl-done ( level kind a b -- flag )
  lf-skel if lf-cl-keep else drop false then lf-cl-pop ;
: lf-cl-succ ( level -- flag )
  dup lf-level-first@ lf-level-id@ if lf-skel-level lf-level-tag-succ + swap 0 lf-cl-done
  else lf-level-first@ lf-cl-push then ;
: lf-cl-binary ( level tag -- flag )
  over lf-level-first@ lf-level-id@ 0= if drop lf-level-first@ lf-cl-push exit then
  2 pick lf-level-second@ lf-level-id@ 0= if 2drop lf-level-second@ lf-cl-push exit then
  rot lf-skel-level + -rot lf-cl-done ;
: lf-cl-node ( level tag -- flag )
  dup lf-level-binary-tag? if lf-cl-binary exit then
  dup lf-level-tag-succ = if drop lf-cl-succ exit then
  dup lf-level-tag-zero = if lf-skel-level + 0 0 lf-cl-done exit then
  dup lf-level-tag-param = if lf-skel-level + over lf-level-first@ 0 lf-cl-done exit then
  2drop false ;
: lf-cl-step ( -- flag )
  lf-cl-sp lf-caches-lstack lf-sk-top dup lf-level-id@ if 2drop true lf-cl-pop exit then
  dup lf-level-tag@ lf-cl-node ;
: lf-cl-run ( -- flag )
  begin lf-cl-sp @ while lf-cl-step 0= if 0 lf-cl-sp ! false exit then repeat true ;
: lf-level-id ( level -- id true | false )
  dup lf-level-id@ if nip true exit then
  dup lf-level-identity if drop else drop false exit then
  0 lf-cl-sp ! dup lf-cl-push 0= if drop false exit then
  lf-cl-run if lf-level-id@ else drop false then ;
\ A constant's universe arguments, a list of cells from the last.
: lf-list-cell ( rest lid -- rest' true | false ) lf-skel-cons -rot swap lf-skel ;
: lf-cref-list ( slot -- id true | false )
  lf-cref-pairs 0 swap
  begin dup while 1- >r
    over r@ lf-cref-pair@ drop lf-level-id 0= if r> drop 2drop false exit then
    lf-list-cell 0= if r> drop drop false exit then
  r> repeat drop nip true ;

\ Terms: kept per node with its identity (kind 1 of the memo), with the
\ data Lean caches in each node (expr.h): bits, four times its loose
\ bound variables (loose_bvar_range: 1 + the largest index beyond its
\ own binders, or 0), plus 2 when a universe parameter occurs in it
\ (has_param_univ: in a Sort's level or a constant's universe
\ arguments), plus 1 when it has a free variable (has_fvar). Only a
\ node every pass takes has facts: a leaf of a known tag, a well-formed
\ bound variable, a free variable live in this job's local context (the
\ tables are emptied when a job starts); any other node, and every node
\ above it, has none, and the passes then meet it as without the caches.
: lf-bits-loose ( bits -- n ) 2 rshift ;
: lf-bits-params ( bits -- 0|1 ) 1 rshift 1 and ;
: lf-bits-fvar ( bits -- 0|1 ) 1 and ;
\ Some loose bound variable or free variable (whnf.fs's has_fvar test,
\ which counts a loose bound variable too).
: lf-bits-open? ( bits -- flag ) dup lf-bits-loose 0<> swap lf-bits-fvar 0<> or ;
: lf-tmemo-key ( node -- flag )
  dup lf-term-identity if >r 1 swap r> 0 lf-key! true else drop false then ;
: lf-term-facts@ ( node -- id bits true | false )
  lf-tmemo-key 0= if false exit then
  lf-cache-memo lf-cache-entry ?dup if lf-cent-values true else false then ;
: lf-term-facts! ( node id bits -- flag )
  rot lf-tmemo-key if lf-cache-memo lf-cache-put else 2drop false then ;
: lf-ts-sp ( -- addr ) lf-caches lf-caches-sp ;
: lf-ts-push ( node -- flag ) lf-ts-sp lf-caches-stack lf-sk-push ;
: lf-ts-pop ( flag -- flag ) lf-ts-sp lf-sk-pop ;
\ A leaf's key (kind a b), by its tag.
: lf-tk-first ( node tag -- kind a b true ) swap lf-term-first@ 0 true ;
: lf-tk-own ( node tag -- kind a b true | false )
  drop lf-skel-node swap lf-term-identity if 0 true else drop false then ;
\ A bound variable whose index would overflow its bits (four times 1 +
\ the index, in a cell: lf-leaf-bits) has no facts, so every pass meets
\ it uncached (review rvCACHE L1; unreachable today: the audit bounds
\ every index by the binders around it).
: lf-tk-index? ( node -- flag ) lf-term-first@ 0 max-n 2 rshift 1- within ;
: lf-tk-bvar ( node tag -- kind a b true | false )
  over dup lf-term-first@ swap lf-term-second@ lf-repr-leaf? 2 pick lf-tk-index? and
  if lf-tk-first else 2drop false then ;
: lf-tk-fvar ( node tag -- kind a b true | false )
  over lf-fvar-live? 0= if 2drop false exit then
  swap lf-term-identity if 0 true else drop false then ;
: lf-tk-sort ( node tag -- kind a b true | false )
  swap lf-term-first@ lf-level-id if 0 true else drop false then ;
: lf-tk-const ( node tag -- kind a b true | false )
  swap lf-term-first@ lf-cref-slot dup lf-crec-name @ swap lf-cref-list
  if true else 2drop false then ;
: lf-tk-pair ( node tag -- kind a b true )
  swap dup lf-term-first@ swap lf-term-second@ true ;
: lf-tk-lit ( node tag -- kind a b true | false )
  over lf-term-second@ 2 < if lf-tk-pair else lf-tk-own then ;
: lf-tk-leaf ( node tag -- kind a b true | false )
  dup case
    lf-tag-bvar of lf-tk-bvar endof
    lf-tag-let of lf-tk-first endof
    lf-tag-fvar of lf-tk-fvar endof
    lf-tag-symbolic-sort of lf-tk-sort endof
    lf-tag-constant of lf-tk-const endof
    lf-tag-lit of lf-tk-lit endof
    lf-tag-str of lf-tk-own endof
    lf-tag-proj of lf-tk-pair endof
    drop 2drop false 0 endcase ;
\ A node's skeleton and bits from its key: kept, and the node off the
\ stack.
: lf-tf-done ( node kind a b bits -- flag )
  >r lf-skel if r> lf-term-facts! else r> 2drop false then lf-ts-pop ;
\ Whether a parameter occurs in a constant's universe arguments, whose
\ levels lf-tk-const has kept: 1, 0, or -1 when one has no entry.
: lf-const-params ( node -- params )
  lf-term-first@ lf-cref-slot lf-cref-pairs 0 swap 0 ?do
    over i lf-cref-pair@ drop lf-cl-child lf-cl-either loop nip ;
\ A leaf's bits, or -1 when its level facts are missing.
: lf-param-bits ( params -- bits ) dup 0< if exit then 2* ;
: lf-leaf-bits ( node kind -- bits )
  case lf-tag-bvar of lf-term-first@ 1+ 2 lshift endof  lf-tag-fvar of drop 1 endof
    lf-tag-symbolic-sort of lf-term-first@ lf-cl-child lf-param-bits endof
    lf-tag-constant of lf-const-params lf-param-bits endof  nip 0 swap endcase ;
: lf-tf-leaf ( node tag -- flag )
  over swap lf-tk-leaf 0= if drop false exit then
  2over lf-leaf-bits dup 0< if 2drop 2drop drop false else lf-tf-done then ;
\ A child's facts, or the child pushed (false, with the push's flag).
: lf-tf-child ( child -- id bits true | flag false )
  dup lf-term-facts@ if rot drop true else lf-ts-push false then ;
\ An application's loose bound variables are its children's largest, a
\ binder's body counts one less; a free variable or a universe parameter
\ in either is one in it.
: lf-tf-loose ( tag l1 l2 -- loose ) rot lf-tag-app <> if 1- 0 max then max ;
: lf-tf-bits ( tag b1 b2 -- bits )
  2dup or 3 and >r lf-bits-loose swap lf-bits-loose swap lf-tf-loose 2 lshift r> or ;
: lf-tf-binary ( node tag -- flag )
  over lf-term-first@ lf-tf-child 0= if nip nip exit then
  3 pick lf-term-second@ lf-tf-child 0= if >r 2drop 2drop r> exit then
  rot swap 4 pick -rot lf-tf-bits lf-tf-done ;
: lf-ts-step ( -- flag )
  lf-ts-sp lf-caches-stack lf-sk-top
  dup lf-term-facts@ if 2drop drop true lf-ts-pop exit then
  dup lf-term-tag@ dup lf-term-binary-tag? if lf-tf-binary else lf-tf-leaf then ;
: lf-ts-run ( -- flag )
  begin lf-ts-sp @ while lf-ts-step 0= if 0 lf-ts-sp ! false exit then repeat true ;
\ node's skeleton and bits, or false when it has none (see above) or
\ they cannot be kept (no heap).
: lf-term-facts ( node -- id bits true | false )
  dup lf-term-facts@ if rot drop true exit then
  dup lf-term-valid? 0= if drop false exit then
  0 lf-ts-sp ! dup lf-ts-push 0= if drop false exit then
  lf-ts-run if lf-term-facts@ else drop false then ;

\ Lean's cached node data where Lean reads it. whnf.fs's scans:
\ has_loose_bvars (lf-whnf-scan-visit), and has_fvar where a loose bound
\ variable counts too (lf-whnf-free-visit). mixed-open.fs's passes keep a
\ node unchanged without visiting it as Lean's replace does
\ (instantiate.cpp 103: no loose bound variable at or beyond the offset;
\ abstract.cpp 19: no free variable). defeq.fs's ==: one skeleton.
: lf-cs-known ( node visit -- flag true | false )
  lf-caches-on? 0= if 2drop false exit then
  swap lf-term-facts 0= if drop false exit then nip
  swap ['] lf-whnf-scan-visit = if lf-bits-loose 0<> else lf-bits-open? then true ;
' lf-cs-known is lf-whnf-known
: lf-co-unchanged? ( node frames -- flag )
  lf-caches-on? 0= if 2drop false exit then
  swap lf-term-facts 0= if drop false exit then nip
  over lf-open-abstract? if nip lf-bits-fvar 0= exit then
  lf-bits-loose swap frame-context @ > 0= ;
' lf-co-unchanged? is lf-open-unchanged?
: lf-cs-same? ( t s -- flag )
  lf-caches-on? 0= if 2drop false exit then
  lf-term-facts 0= if drop false exit then drop
  swap lf-term-facts 0= if drop false exit then drop = ;
' lf-cs-same? is lf-dq-known-same?
\ lf-term-data@ (core/terms.fs): the facts as ADR 0016 C1's data word,
\ while the caches are on and the range fits its 20 bits.
: lf-cd-word ( bits -- data true | false )
  dup lf-bits-loose dup lf-data-ranges u< 0= if 2drop false exit then
  over lf-bits-params 0<> rot lf-bits-fvar 0<> lf-data true ;
: lf-cd-data ( node -- data true | false )
  lf-caches-on? 0= if drop false exit then
  lf-term-facts if nip lf-cd-word else false then ;
' lf-cd-data is lf-term-data@

\ ---------------------------------------------------------------------------
\ Nodes as keys (by skeleton) and values (a live node and its identity).
: lf-node-key ( node -- flag ) lf-term-facts if drop 0 0 0 lf-key! true else false then ;
: lf-cache-count ( flag cache -- flag )
  over if lf-cache-hits else lf-cache-misses then 1 swap +! ;
\ An entry's value node when it still has the identity kept with it.
: lf-cent-node ( addr -- r true | false )
  lf-cent-values over lf-term-identity if = else drop false then dup 0= if nip then ;
: lf-cache-found ( cache -- r true | false )
  dup >r lf-cache-entry ?dup if lf-cent-node else false then r> lf-cache-count ;
: lf-cache-node@ ( node cache -- r true | false )
  swap lf-node-key if lf-cache-found else drop false then ;
: lf-cache-value! ( r cache -- )
  over lf-term-identity if swap lf-cache-put drop else 2drop then ;
: lf-cache-node! ( node r cache -- )
  rot lf-node-key if lf-cache-value! else 2drop then ;

\ ---------------------------------------------------------------------------
\ The steps around the passes. A hit ends the visit with the value; a miss
\ keeps the key's node on the frames, gives back the unit just spent, and
\ opens the pass's own visit, whose result the storing step keeps and
\ returns.
: lf-cache-hit ( x frames r -- r ok frames 0 ) rot drop outcome-ok rot 0 ;
: lf-cache-refund ( frames -- frames ) 1 over frame-fuel +! ;

\ whnf_core and whnf (whnf.fs). An easy case runs as before.
: lf-cwc-plain? ( node -- flag )
  dup lf-term-tag@ dup lf-tag-fvar = if drop lf-whnf-let? 0= exit then
  lf-whnf-normal? nip ;
: lf-cwc-cacheable? ( node -- flag )
  lf-caches-on? 0= if drop false exit then
  dup lf-term-valid? if lf-cwc-plain? 0= else drop false then ;
\ whnf_core keeps a result that is not the node itself (547-549), never
\ one of a visit with cheap_proj (547; whnf.fs), whose lookups still read.
: lf-cwc-store ( r outcome frames -- r outcome frames 0 )
  >r r@ frame-restore over ok? 0= lf-whnf-cheap? or if drop r> 0 exit then
  2 pick 2dup = if 2drop else lf-cache-whnf-core lf-cache-node! then r> 0 ;
: lf-cwc-visit ( node frames -- ... frames next )
  over lf-cwc-cacheable? 0= if lf-wc-visit exit then
  over lf-cache-whnf-core lf-cache-node@ if lf-cache-hit exit then
  2dup frame-save lf-cache-refund ['] lf-cwc-store ['] lf-wc-visit lf-whnf-open ;
' lf-cwc-visit is lf-wc-entry

: lf-cw-cacheable? ( node -- flag )
  lf-caches-on? 0= if drop false exit then
  dup lf-term-valid? if lf-whnf-easy? 0= else drop false then ;
: lf-cw-store ( r outcome frames -- r outcome frames 0 )
  >r r@ frame-restore over ok?
  if 2 pick lf-cache-whnf lf-cache-node! else drop then r> 0 ;
: lf-cw-visit ( node frames -- ... frames next )
  over lf-cw-cacheable? 0= if lf-whnf-visit exit then
  over lf-cache-whnf lf-cache-node@ if lf-cache-hit exit then
  2dup frame-save lf-cache-refund ['] lf-cw-store ['] lf-whnf-visit lf-whnf-open ;
' lf-cw-visit is lf-whnf-entry

\ m_unfold: only for a constant with universe arguments, as Lean (573).
: lf-cu-cacheable? ( const -- flag )
  lf-caches-on? if lf-whnf-cref lf-cref-pairs nip 0<> else drop false then ;
: lf-cu-value ( decl const frames -- value outcome )
  over lf-cu-cacheable? 0= if lf-whnf-value exit then
  over lf-cache-unfold lf-cache-node@ if >r drop 2drop r> outcome-ok exit then
  over >r lf-whnf-value dup ok?
  if r> 2 pick lf-cache-unfold lf-cache-node! else r> drop then ;
' lf-cu-value is lf-whnf-valued

\ ---------------------------------------------------------------------------
\ The pair caches (defeq.fs), on only with a typer (see the header). A
\ pair's key: the two skeletons, the smaller first, both closed.
: lf-cp-on? ( -- flag ) lf-caches-on? if lf-dq-typer @ 0<> else false then ;
: lf-closed-id ( node -- id true | false )
  lf-term-facts if lf-bits-loose if drop false else true then else false then ;
: lf-pair-key ( t s -- flag )
  lf-closed-id 0= if drop false exit then
  swap lf-closed-id 0= if drop false exit then
  2dup > if swap then 0 0 lf-key! true ;
: lf-pair@ ( t s cache -- flag )
  >r lf-pair-key if r@ lf-cache-entry 0<> else false then r> lf-cache-count ;
: lf-pair! ( t s cache -- ) >r lf-pair-key if 0 0 r@ lf-cache-put drop then r> drop ;

\ is_def_eq: a yes is kept (1211-1212); the visit keeps t and s.
: lf-cq-store ( flag outcome frames -- flag outcome frames 0 )
  >r r@ frame-restore r@ frame-restore swap 2over ok? and
  if lf-cache-success lf-pair! else 2drop then r> 0 ;
: lf-cq-visit ( t s frames -- ... frames next )
  lf-cp-on? 0= if lf-dq-visit exit then
  >r 2dup swap r@ frame-save r@ frame-save
  r> lf-cache-refund ['] lf-cq-store ['] lf-dq-visit lf-dq-open ;
' lf-cq-visit is lf-dq-entry
\ quick_is_def_eq after ==: succeeded_before (804) answers yes.
: lf-cq-quick ( t s frames -- ... frames next )
  lf-cp-on? if >r 2dup lf-cache-success lf-pair@ r> swap
    if nip nip lf-dq-yes outcome-ok rot 0 exit then then
  lf-qk-kinds ;
' lf-cq-quick is lf-qk-other
\ Lazy delta's same-declaration test on the visit's tn and sn: skipped
\ when it failed before (1004), recorded when it fails (1009) without
\ doubt.
: lf-cf-failed? ( frames -- frames flag )
  lf-cp-on? 0= if false exit then dup lf-dq-sides lf-cache-failure lf-pair@ ;
: lf-cf-failure ( frames -- frames )
  lf-cp-on? 0= if exit then lf-dq-state lf-dqs-doubt @ if exit then
  dup lf-dq-sides lf-cache-failure lf-pair! ;
' lf-cf-failed? is lf-lz-failed?
' lf-cf-failure is lf-lz-failure

\ ---------------------------------------------------------------------------
\ Inference (mixed-infer.fs): the key's skeleton and scope (see the
\ header), or false for a node read beyond the scope, a chained lambda,
\ or one whose skeleton cannot be kept.
: lf-ci-top ( -- identity true | false )
  lf-minfer-context-depth @ 1- lf-minfer-fvar-cell @ lf-term-identity ;
: lf-ci-scope ( loose -- scope true | false )
  ?dup 0= if 0 true exit then lf-minfer-context-depth @ > if false else lf-ci-top then ;
\ Only a node inference may read (lf-minfer-source?: a source node, or
\ any node aside) is looked up or kept, so a node it refuses as invalid
\ meets that refusal, never a cached type (review rvCACHE L2).
: lf-ci-ready? ( node -- id scope true | false )
  lf-caches-on? 0= if drop false exit then
  lf-minfer-chain @ 0< 0= if drop false exit then
  dup lf-minfer-source? 0= if drop false exit then
  lf-term-facts 0= if false exit then lf-bits-loose lf-ci-scope dup 0= if nip then ;
: lf-ci-table ( -- cache )
  lf-minfer-aside @ if lf-cache-infer-only else lf-cache-infer then ;
: lf-ci-key ( id scope -- ) 0 0 lf-key! ;
\ The visit keeps the scope and the skeleton.
: lf-ci-store ( type status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore 2 pick ok?
  if lf-ci-key over lf-ci-table lf-cache-value! else 2drop then r> 0 ;
: lf-ci-open ( node frames cont xt -- ... frames next )
  >r over lf-minfer-room dup ok? if drop r> frame-open else r> drop frame-refuse then ;
: lf-ci-miss ( node frames id scope -- ... frames next )
  2 pick tuck frame-save frame-save lf-cache-refund
  ['] lf-ci-store ['] lf-minfer-visit-step lf-ci-open ;
: lf-ci-visit ( node frames -- ... frames next )
  over lf-ci-ready? 0= if lf-minfer-visit-step exit then
  2dup lf-ci-key lf-ci-table lf-cache-found if >r 2drop r> lf-cache-hit exit then
  lf-ci-miss ;
' lf-ci-visit is lf-minfer-entry

\ Scratch kept until the job ends while the term, level and reference
\ stores each have this much room left (the command line gives a check
\ 2^20 terms, 2^16 levels and 2^18 references: import/feed.fs); with
\ less, inference and comparison discard as without the caches, so a
\ small store (a test's) fills no sooner. A discarded node's entries
\ then miss: the result's identity, or the node's, no longer matches.
262144 constant lf-caches-term-room
16384 constant lf-caches-level-room
65536 constant lf-caches-cref-room
: lf-room? ( count limit room -- flag ) >r swap - r> < 0= ;
: lf-caches-keep? ( -- flag )
  lf-caches-on? 0= if false exit then
  lf-term-count @ lf-term-capacity lf-caches-term-room lf-room?
  lf-level-count @ lf-level-capacity lf-caches-level-room lf-room? and
  lf-cref-count @ lf-cref-capacity lf-caches-cref-room lf-room? and ;
' lf-caches-keep? is lf-minfer-keeps?
' lf-caches-keep? is lf-mconvert-keeps?
\ The result tables emptied when a job starts.
' lf-caches-clear is lf-minfer-fresh
