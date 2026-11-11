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
\ Keys: Lean's == by node (ADR 0014 Q3, Amendment 5). Lean compares keys
\ with == (structural equality, expr_eq_fn). Since compact-store plan
\ step S4 the term store hash-conses every node but a free variable (one
\ per local-context entry), levels are hash-consed and references
\ interned (core/terms.fs, levels.fs, constant-references.fs), so equal
\ constants and Sorts are one node too, and a node's number is its class
\ under ==: a key is the node's identity (identities never repeat, so a
\ rolled-back index made again is another key). Two nodes that are ==
\ but not one node (made while sharing was off, two literals of one
\ value, a Sort or constant made again because its stamps no longer
\ held) are two keys: a miss where Lean hits, never a false hit. (Until
\ step S4 a skeleton memo gave every node a structural class number,
\ since constants and Sorts were made anew by each universe
\ substitution.) A node has a key only when it has Lean's node facts
\ (below).
\ A cached value is a node with its identity; an entry whose node no
\ longer has it (its scratch was discarded) is a miss. Inference reads a
\ source node under the scope (mixed-infer.fs), a loose bound variable k
\ being the scope's free variable k places from the top; Lean infers the
\ term with those free variables put in, and keys its type by that term
\ (type_checker.h 26-30). So an inferred type's key is the identity of
\ the node closed with the scope (the closing is remembered per scope,
\ mixed-open.fs; plan task 6.5.5), the node's own when it has no loose
\ bound variable, with 0 for the scope (until plan task 6.5.5 the key was
\ the node's class with the identity of the scope's innermost free
\ variable, which missed under every new binder). A lambda read
\ as the body of a lambda (mixed-infer.fs's chain) has a type over the
\ chain's bound variables, not closed: it is neither looked up nor kept.
\ The pair caches take closed terms only (as Lean compares only closed
\ terms; check-block.fs compares open ones, whose types the typer reads
\ under the scope), ordered by identity, so a success on (t, s) answers
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
\ Amendment 1, review rvCACHE L4). An open term's whnf depends on no
\ context either, except where iota's K or structure eta types an open
\ major premise under the inference job's scope (iota.fs; ADR 0015
\ Amendment 3): whnf.fs counts each, and no whnf or whnf_core result
\ reached through one is kept for an open key (lf-cache-restore). While the caches are on, inference and comparison
\ keep their scratch until the job ends (mixed-infer.fs's discard and
\ mixed-convert.fs's restore do nothing) where the stores have ample room
\ (below), so entries stay useful, as Lean's live for the whole check.
\ Only definite results are kept: a pass that ends unknown, exhausted,
\ full, invalid or rejected keeps nothing. LeanForth's doubt record
\ (defeq.fs) cannot arise where the pair caches work: they work only
\ when the comparison has a typer (in a check it always has), and a
\ failure is kept only without doubt. The whnf_core table's entries are
\ not quite Lean's: LeanForth also keeps a result reached by iota or
\ quotient reduction or from a let variable (Lean returns at 533 and 503
\ without keeping), and keeps none for the head of an application whose
\ whole spine its iota hook reduces (Lean's whnf_core of the head, 513,
\ keeps one at 547). Every entry is the full whnf_core of its key, so a
\ full visit gets the same result either way. A cheap visit (cheap_proj,
\ plan task 5.2.2) reads the table too, as Lean's does (490-493), so where
\ the tables differ it may get the full result where Lean computes the
\ cheap one, or the reverse: the comparison then takes another path
\ through is_def_eq_core's steps 5-9, with other fuel. Every probe gave
\ Lean's verdict (review rvPSE L1, its projection probes t1-t6 and wrong
\ twins); the table is left as it is until a verdict differs.
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
\ up, keeping and node facts cost no fuel (Lean's caches, hashes and
\ cached node data cost no steps either); each is bounded by the nodes
\ the check has. Closing an open node for its inferred type's key is
\ substitution work, paid as mixed-open.fs pays it (Lean's instantiate
\ when it opens a binder). A table or stack that cannot grow (no heap)
\ keeps nothing more: a miss, never a verdict.
\
\ Lean's cached node data: what Lean keeps in each node, its loose bound
\ variables and whether it has a free variable or a universe parameter,
\ is each term record's data word (core/terms.fs's lf-term-data@, since
\ plan step S3). whnf.fs, mixed-infer.fs and mixed-open.fs read the word
\ themselves (plan task 6.5.5); the hooks here answer for a node whose
\ word names a free variable, from the free-variable memo (lf-term-facts).
\
\ Interface: lf-caches-enable ( flag -- ), lf-caches-on? ( -- flag ),
\ lf-caches-clear ( -- ), lf-term-facts ( node -- id bits true | false ),
\ lf-cache-stats ( cache -- hits misses ) with the caches lf-cache-infer,
\ lf-cache-infer-only, lf-cache-whnf-core, lf-cache-whnf,
\ lf-cache-unfold, lf-cache-success and lf-cache-failure ( -- cache ).
\ Loading this module sets the hooks of whnf.fs, defeq.fs, mixed-infer.fs,
\ mixed-convert.fs and mixed-open.fs.
\ State: one record, lf-caches (the switch, the key being looked up, a
\ stack's depth, and eight tables: each a hash table of lib/htab.fs over
\ a slab of entries), and a growable stack (lf-caches-stack), members of
\ the checker context (lib/context.fs), freed with it. The tables' hooks
\ are shared and read-only.

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
8 constant lf-caches#
begin-structure /lf-caches
  field: lf-caches-off            \ true when a test turned the caches off
  field: lf-caches-sp             \ cells on lf-caches-stack
  4 cells +field lf-caches-key    \ the key being looked up or kept
  /lf-cache lf-caches# * +field lf-caches-tables
end-structure
/lf-caches context-record: lf-caches
1 cells context-slab: lf-caches-stack    \ nodes waiting for their memo entry
: lf-cache-nth ( i -- cache ) /lf-cache * lf-caches lf-caches-tables + ;
: lf-cache-infer ( -- cache ) 0 lf-cache-nth ;        \ m_infer_type[false]
: lf-cache-infer-only ( -- cache ) 1 lf-cache-nth ;   \ m_infer_type[true]
: lf-cache-whnf-core ( -- cache ) 2 lf-cache-nth ;    \ m_whnf_core
: lf-cache-whnf ( -- cache ) 3 lf-cache-nth ;         \ m_whnf
: lf-cache-unfold ( -- cache ) 4 lf-cache-nth ;       \ m_unfold
: lf-cache-success ( -- cache ) 5 lf-cache-nth ;      \ m_success
: lf-cache-failure ( -- cache ) 6 lf-cache-nth ;      \ m_failure
: lf-cache-memo ( -- cache ) 7 lf-cache-nth ;         \ node -> free variables live
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
\ Empty every table (a check begins, an inference job starts).
: lf-caches-clear ( -- ) ['] lf-cache-empty lf-caches-each ;

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
\ Keys (see the header): a node is its own key, by its identity
\ (compact-store plan step S4), when it has facts. Lean's node facts
\ (expr.h; ADR 0016 C1) are each record's data word (core/terms.fs's
\ lf-term-data@, made from the children when the node is made): bits,
\ four times its loose bound variables (loose_bvar_range: 1 + the
\ largest index beyond its own binders, or 0), plus 2 when a universe
\ parameter occurs in it (has_param_univ: in a Sort's level or a
\ constant's universe arguments), plus 1 when it has a free variable
\ (has_fvar). Only a node every pass takes has facts: one with a data
\ word, and, when the word names a free variable, every free variable
\ in it live in this job's local context (the tables are emptied when a
\ job starts); any other node, and every node above it, has none, and
\ the passes then meet it as without the caches.
: lf-bits-loose ( bits -- n ) 2 rshift ;
: lf-bits-params ( bits -- 0|1 ) 1 rshift 1 and ;
: lf-bits-fvar ( bits -- 0|1 ) 1 and ;
\ Some loose bound variable or free variable (whnf.fs's has_fvar test,
\ which counts a loose bound variable too).
: lf-bits-open? ( bits -- flag ) dup lf-bits-loose 0<> swap lf-bits-fvar 0<> or ;
: lf-data-bits ( data -- bits )
  dup lf-data-loose 2 lshift over lf-data-params? 2 and or swap lf-data-fvar? 1 and or ;

\ Growable stacks: depth cell sp, cells in slab.
: lf-sk-push ( x sp slab -- flag )
  over @ 1+ over slab-hold ok? 0= if 2drop drop false exit then
  over @ swap slab-at rot swap ! 1 swap +! true ;
: lf-sk-top ( sp slab -- x ) swap @ 1- swap slab-at @ ;
: lf-sk-pop ( flag sp -- flag ) over if -1 swap +! else drop then ;
: lf-ts-sp ( -- addr ) lf-caches lf-caches-sp ;
: lf-ts-push ( node -- flag ) lf-ts-sp lf-caches-stack lf-sk-push ;
: lf-ts-pop ( flag -- flag ) lf-ts-sp lf-sk-pop ;

\ The free-variable memo: whether every free variable in a node whose
\ word has the bit is live, kept per node with its identity, found once
\ from its children's on a growable stack. A child without the bit has
\ none; a free-variable leaf is live when its own entry is
\ (local-context.fs). Within a job an entry goes only with its node (a
\ scratch rollback), so a live node's answer stays.
: lf-fvmemo-key ( node -- flag )
  dup lf-term-identity if >r 1 swap r> 0 lf-key! true else drop false then ;
: lf-live@ ( node -- flag true | false )
  lf-fvmemo-key 0= if false exit then
  lf-cache-memo lf-cache-entry ?dup if lf-cent-values drop true else false then ;
\ Keep node's answer, then take it off the stack: false when the memo
\ cannot keep it (no heap), which ends the walk.
: lf-live! ( node flag -- flag )
  swap lf-fvmemo-key if 0 lf-cache-memo lf-cache-put else drop false then lf-ts-pop ;
: lf-fv-known ( child -- flag true | false )
  dup lf-term-data-word lf-data-fvar? 0= if drop true true exit then lf-live@ ;
: lf-fv-binary ( node -- flag )
  dup lf-term-first@ lf-fv-known 0= if lf-term-first@ lf-ts-push exit then
  over lf-term-second@ lf-fv-known 0= if drop lf-term-second@ lf-ts-push exit then
  and lf-live! ;
: lf-fv-leaf ( node -- flag )
  dup dup lf-term-tag@ lf-tag-fvar = if lf-fvar-live? else drop false then lf-live! ;
: lf-fv-step ( -- flag )
  lf-ts-sp lf-caches-stack lf-sk-top dup lf-live@ if 2drop true lf-ts-pop exit then
  dup lf-term-tag@ lf-term-binary-tag? if lf-fv-binary else lf-fv-leaf then ;
: lf-fv-run ( -- flag )
  begin lf-ts-sp @ while lf-fv-step 0= if 0 lf-ts-sp ! false exit then repeat true ;
: lf-fvars-live? ( node -- flag true | false )
  dup lf-live@ if nip true exit then
  0 lf-ts-sp ! dup lf-ts-push 0= if drop false exit then
  lf-fv-run if lf-live@ else drop false then ;
\ node's identity and bits, or false when it has none (see above) or
\ they cannot be kept (no heap).
: lf-word-facts ( node data -- id bits true | false )
  swap lf-term-identity 0= if drop false exit then swap lf-data-bits true ;
: lf-term-facts ( node -- id bits true | false )
  dup lf-term-data@ 0= if drop false exit then
  dup lf-data-fvar? 0= if lf-word-facts exit then
  over lf-fvars-live? if if lf-word-facts exit then then 2drop false ;

\ Lean's cached node data where Lean reads it. whnf.fs's scans:
\ has_loose_bvars (lf-whnf-scan-visit), and has_fvar where a loose bound
\ variable counts too (lf-whnf-free-visit). mixed-open.fs's passes keep a
\ node unchanged without visiting it as Lean's replace does
\ (instantiate.cpp 103: no loose bound variable at or beyond the offset;
\ abstract.cpp 19: no free variable). defeq.fs's ==: one node. Each
\ record keeps these facts in its data word (core/terms.fs, since plan
\ step S3); a node whose word names a free variable is asked of the
\ free-variable memo, which knows a free variable only while it is live
\ in this job's local context, so the passes meet a dead one as before.
: lf-cs-facts ( node -- bits true | false ) lf-term-facts if nip true else false then ;
: lf-cs-known ( node visit -- flag true | false )
  lf-caches-on? 0= if 2drop false exit then
  swap lf-cs-facts 0= if drop false exit then
  swap ['] lf-whnf-scan-visit = if lf-bits-loose 0<> else lf-bits-open? then true ;
' lf-cs-known is lf-whnf-known
: lf-co-unchanged? ( node frames -- flag )
  lf-caches-on? 0= if 2drop false exit then
  swap lf-cs-facts 0= if drop false exit then
  over lf-open-abstract? if nip lf-bits-fvar 0= exit then
  lf-bits-loose swap frame-context @ > 0= ;
' lf-co-unchanged? is lf-open-unchanged?
\ mixed-infer.fs's scan of how many of the scope's variables a term
\ names: its loose_bvar_range (expr.cpp 102-103).
: lf-ci-range ( node -- m true | false )
  lf-caches-on? 0= if drop false exit then
  lf-cs-facts if lf-bits-loose true else false then ;
' lf-ci-range is lf-minfer-range
\ ==: one node is equal at once (Lean's is_eqp); two nodes, the walk of
\ mixed-compare.fs's lf-expr-equal decides.
: lf-cs-same? ( t s -- flag ) lf-caches-on? if = else 2drop false then ;
' lf-cs-same? is lf-dq-known-same?
\ The facts' bits as ADR 0016 C1's data word, when the range fits its 20
\ bits (the tests compare it with lf-term-data@).
: lf-cd-word ( bits -- data true | false )
  dup lf-bits-loose dup lf-data-ranges u< 0= if 2drop false exit then
  over lf-bits-params 0<> rot lf-bits-fvar 0<> lf-data true ;
\ ---------------------------------------------------------------------------
\ Nodes as keys (by identity) and values (a live node and its identity).
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
\ The key and the count of open terms typed under the scope (whnf.fs,
\ lf-whnf-scope-uses) are saved across the pass. A key with loose bound
\ variables keeps no result whose pass typed one (iota.fs's K and
\ structure eta on a major premise read under the inference job's scope):
\ the result is the scope's, which the key does not name, and the same
\ key read under another scope may reduce otherwise (Lean keys closed
\ terms, whose free variables name their local).
: lf-cache-save ( node frames -- node frames )
  2dup frame-save lf-whnf-scope-uses over frame-save ;
: lf-cache-open? ( node -- flag ) lf-term-data@ if lf-data-loose 0<> else true then ;
: lf-cache-restore ( frames -- node keep? )
  dup frame-restore lf-whnf-scope-uses = swap frame-restore tuck lf-cache-open? 0= or ;
\ whnf_core keeps a result that is not the node itself (547-549), never
\ one of a visit with cheap_proj (547; whnf.fs), whose lookups still read.
: lf-cwc-store ( r outcome frames -- r outcome frames 0 )
  >r r@ lf-cache-restore 0= 2 pick ok? 0= or lf-whnf-cheap? or if drop r> 0 exit then
  2 pick 2dup = if 2drop else lf-cache-whnf-core lf-cache-node! then r> 0 ;
: lf-cwc-visit ( node frames -- ... frames next )
  over lf-cwc-cacheable? 0= if lf-wc-visit exit then
  over lf-cache-whnf-core lf-cache-node@ if lf-cache-hit exit then
  lf-cache-save lf-cache-refund ['] lf-cwc-store ['] lf-wc-visit lf-whnf-open ;
' lf-cwc-visit is lf-wc-entry

: lf-cw-cacheable? ( node -- flag )
  lf-caches-on? 0= if drop false exit then
  dup lf-term-valid? if lf-whnf-easy? 0= else drop false then ;
: lf-cw-store ( r outcome frames -- r outcome frames 0 )
  >r r@ lf-cache-restore 2 pick ok? and
  if 2 pick lf-cache-whnf lf-cache-node! else drop then r> 0 ;
: lf-cw-visit ( node frames -- ... frames next )
  over lf-cw-cacheable? 0= if lf-whnf-visit exit then
  over lf-cache-whnf lf-cache-node@ if lf-cache-hit exit then
  lf-cache-save lf-cache-refund ['] lf-cw-store ['] lf-whnf-visit lf-whnf-open ;
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
\ pair's key: the two identities, the smaller first, both closed.
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
\ Inference (mixed-infer.fs): the key's identity and scope (see the
\ header), or false for a node read beyond the scope, a chained lambda,
\ or one that has no key. Lean keys an inferred type by the
\ term inferred, which infer_lambda, infer_pi and infer_let instantiated
\ with the free variables of the binders they opened (type_checker.cpp
\ 125-171, 208-230; looked up 332-334, kept 356, in an expr_map compared
\ with ==, type_checker.h 26-30): so a term that names only outer binders
\ hits under any inner one. A node read under the scope is keyed so: by
\ its copy closed with the scope's free variables (mixed-infer.fs's
\ closing, on the job's fuel, which mixed-open.fs remembers per scope, so
\ that a node's closing costs about one visit once its parent's is done;
\ plan task 6.5.5), a closed node by itself; the scope part of the key is
\ then 0. A closing that runs out of fuel or room ends the visit so, as
\ every step of inference does; one that fails otherwise (a dead free
\ variable) keys nothing, and inference meets the node uncached. So does
\ every open node while scratch is not kept (lf-caches-keep?, below: a
\ small store, whose room the copies would take, and whose discarded
\ scratch the entries would miss anyway), and a loose bound variable,
\ whose type inference reads from its free variable's entry at once
\ (infer_fvar, 93-99), as Lean's would after opening. A node without a
\ key gives ( ok false ), a failed closing ( outcome false ).
defer lf-ci-room? ( -- flag )
: lf-ci-short ( outcome -- outcome )
  dup outcome-exhausted = over outcome-full = or 0= if drop outcome-ok then ;
: lf-ci-copy ( node -- id true | outcome false )
  lf-ci-room? 0= if drop outcome-ok false exit then
  dup lf-term-tag@ lf-tag-bvar = if drop outcome-ok false exit then
  lf-minfer-close ok-then? 0= if lf-ci-short false exit then
  lf-closed-id if true else outcome-ok false then ;
: lf-ci-skeleton ( node -- id true | outcome false )
  dup lf-term-facts 0= if drop outcome-ok false exit then
  lf-bits-loose if drop lf-ci-copy else nip true then ;
\ Only a node inference may read (lf-minfer-source?: a source node, or
\ any node aside) is looked up or kept, so a node it refuses as invalid
\ meets that refusal, never a cached type (review rvCACHE L2).
: lf-ci-none ( node -- ok false ) drop outcome-ok false ;
: lf-ci-ready? ( node -- id scope true | outcome false )
  lf-caches-on? 0= if lf-ci-none exit then
  lf-minfer-chain @ 0< 0= if lf-ci-none exit then
  lf-minfer-inner @ if lf-ci-none exit then
  dup lf-minfer-source? 0= if lf-ci-none exit then
  lf-ci-skeleton if 0 true else false then ;
: lf-ci-table ( -- cache )
  lf-minfer-aside @ if lf-cache-infer-only else lf-cache-infer then ;
: lf-ci-key ( id scope -- ) 0 0 lf-key! ;
\ The visit keeps the scope and the key.
: lf-ci-store ( type status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore 2 pick ok?
  if lf-ci-key over lf-ci-table lf-cache-value! else 2drop then r> 0 ;
: lf-ci-open ( node frames cont xt -- ... frames next )
  >r over lf-minfer-room dup ok? if drop r> frame-open else r> drop frame-refuse then ;
: lf-ci-miss ( node frames id scope -- ... frames next )
  2 pick tuck frame-save frame-save lf-cache-refund
  ['] lf-ci-store ['] lf-minfer-visit-step lf-ci-open ;
: lf-ci-fail ( node frames outcome -- -1 outcome frames 0 ) rot drop no-result rot 0 ;
: lf-ci-uncached ( node frames outcome -- ... frames next )
  dup ok? if drop lf-minfer-visit-step else lf-ci-fail then ;
: lf-ci-visit ( node frames -- ... frames next )
  over lf-ci-ready? 0= if lf-ci-uncached exit then
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
' lf-caches-keep? is lf-ci-room?
\ The result tables emptied when a job starts.
' lf-caches-clear is lf-minfer-fresh
