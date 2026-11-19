\ Check structural term storage, field ordering, failure behavior and reset.
\ These are storage tests, not well-scopedness, type checking or proof tests.
include ../support/tester.fs
require ../../src/lib/lib.fs
require ../../src/core/terms.fs
require ../support/store-faults.fs

lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 1 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-app -> 2 true }T
T{ 0 1 lf-term-lam -> 3 true }T
T{ 0 1 lf-term-pi -> 4 true }T
T{ 0 lf-term-read -> lf-tag-sort 0 0 true }T
T{ 1 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 2 lf-term-read -> lf-tag-app 0 1 true }T
T{ 3 lf-term-read -> lf-tag-lam 0 1 true }T
T{ 4 lf-term-read -> lf-tag-pi 0 1 true }T
T{ -1 lf-term-sort -> false }T
T{ -1 lf-term-bvar -> false }T
T{ -1 0 lf-term-app -> false }T
T{ 0 -1 lf-term-lam -> false }T
T{ 5 0 lf-term-pi -> false }T
T{ 0 5 lf-term-app -> false }T
T{ 0 1 0 lf-term-binary -> false }T
T{ 0 1 lf-tag-sort lf-term-binary -> false }T
T{ -1 lf-term-read -> false }T
T{ 5 lf-term-read -> false }T
T{ 100000 lf-term-read -> false }T
T{ lf-term-count @ -> 5 }T
\ A node's kind by its tag (plan 9.4.8a): application, lambda, Pi, bound
\ variable, binary (two children), binder (lambda or Pi), the bound
\ variable #n, any tag.
T{ 2 lf-term-app? 3 lf-term-app? 0 lf-term-app? 1 lf-term-app? -> true false false false }T
T{ 3 lf-term-lam? 4 lf-term-lam? 4 lf-term-pi? 3 lf-term-pi? -> true false true false }T
T{ 1 lf-term-bvar? 0 lf-term-bvar? 2 lf-term-bvar? -> true false false }T
T{ 2 lf-term-binary? 3 lf-term-binary? 4 lf-term-binary? -> true true true }T
T{ 0 lf-term-binary? 1 lf-term-binary? -> false false }T
T{ 3 lf-term-binder? 4 lf-term-binder? 2 lf-term-binder? 1 lf-term-binder? -> true true false false }T
T{ 2 lf-tag-app lf-term-tag? 2 lf-tag-lam lf-term-tag? 0 lf-tag-sort lf-term-tag? -> true false true }T
T{ 1 1 lf-term-bvar-is? 1 0 lf-term-bvar-is? 1 2 lf-term-bvar-is? -> true false false }T
T{ 0 0 lf-term-bvar-is? 2 1 lf-term-bvar-is? 0 1 lf-term-bvar-is? -> false false false }T
T{ 2 lf-term-read -> lf-tag-app 0 1 true }T

\ Fill all remaining slots to exercise failure at the allocation boundary,
\ with the store's hash-consing off so that each equal leaf is a node of
\ its own (compact-store plan step S3). A full store refuses even a node
\ it holds an equal of.
: fill-terms ( -- )
  false lf-term-sharing! begin lf-term-count @ lf-term-capacity < while
    0 lf-term-sort 0= if -1 throw then drop
  repeat true lf-term-sharing! ;
fill-terms
T{ 0 lf-term-sort -> false }T
T{ 0 lf-term-bvar -> false }T
T{ 0 1 lf-term-app -> false }T
T{ 0 1 lf-term-lam -> false }T
T{ 0 1 lf-term-pi -> false }T
T{ lf-term-count @ -> lf-term-capacity }T
T{ 2 lf-term-read -> lf-tag-app 0 1 true }T
lf-term-reset
T{ 0 lf-term-read -> false }T
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-read -> lf-tag-sort 0 0 true }T

\ Build the structure of polymorphic identity over propositions. These tests
\ only inspect its nodes; they do not claim the term is scoped or well typed.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-pi -> 3 true }T
T{ 0 3 lf-term-pi -> 4 true }T
T{ 1 1 lf-term-lam -> 5 true }T
T{ 0 5 lf-term-lam -> 6 true }T
T{ 4 lf-term-read -> lf-tag-pi 0 3 true }T
T{ 6 lf-term-read -> lf-tag-lam 0 5 true }T

\ Corrupt counts must never permit reads or allocations outside storage.
-1 lf-term-count !
T{ 0 lf-term-read -> false }T
T{ 0 lf-term-sort -> false }T
T{ 0 lf-term-bvar -> false }T
T{ 0 0 lf-term-app -> false }T
T{ lf-term-count @ -> -1 }T
lf-term-capacity 1+ lf-term-count !
T{ 0 lf-term-read -> false }T
T{ 0 lf-term-sort -> false }T
T{ 0 lf-term-bvar -> false }T
T{ 0 0 lf-term-pi -> false }T
T{ lf-term-count @ -> lf-term-capacity 1+ }T

\ Identities are fresh for each allocation and never reused after a reset;
\ each reset advances the generation by one. Handles rely on both.
lf-term-reset
term-serial constant term-serial0
lf-term-generation @ constant term-generation0
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-identity -> term-serial0 1+ true }T
T{ 1 lf-term-identity -> false }T
T{ -1 lf-term-identity -> false }T
lf-term-reset
T{ lf-term-generation @ -> term-generation0 1+ }T
T{ 0 lf-term-identity -> false }T
T{ 0 lf-term-bvar -> 0 true }T
T{ 0 lf-term-identity -> term-serial0 2 + true }T

\ A spent identity serial refuses every constructor and changes nothing.
max-n term-serial!
T{ 0 lf-term-sort -> false }T
T{ 0 0 lf-term-app -> false }T
T{ lf-term-count @ term-serial -> 1 max-n }T
T{ 0 lf-term-read -> lf-tag-bvar 0 0 true }T

\ A saturated generation poisons the store: nothing is readable or allocated,
\ and further resets do not revive it.
0 term-serial!
max-n lf-term-generation !
lf-term-reset
T{ lf-term-generation @ lf-term-count-valid? -> -1 false }T
T{ 0 lf-term-sort -> false }T
lf-term-reset
T{ lf-term-generation @ -> -1 }T
T{ 0 lf-term-read -> false }T
0 lf-term-generation !
lf-term-reset

\ The leaf constructor refuses non-leaf tags, so it cannot create a node
\ with a dangling child.
T{ 999 lf-tag-app lf-term-leaf -> false }T
T{ 0 99 lf-term-leaf -> false }T
T{ 0 lf-tag-bvar lf-term-leaf -> 0 true }T

\ Failed constructors leave the serial and count unchanged.
term-serial constant term-serial1
T{ 0 0 99 lf-term-binary -> false }T
T{ 0 5 lf-term-app -> false }T
T{ 5 0 99 lf-term-binary -> false }T
T{ -1 lf-term-sort -> false }T
T{ term-serial lf-term-count @ -> term-serial1 1 }T

\ Identities are unreadable under a corrupted count.
-1 lf-term-count !
T{ 0 lf-term-identity -> false }T
lf-term-capacity 1+ lf-term-count !
T{ 0 lf-term-identity -> false }T
1 lf-term-count !
T{ 0 lf-term-identity -> term-serial1 true }T
lf-term-reset

\ Checked roots, reads by index (compact-store plan step S2). A root
\ checks the whole header; a read checks only index < count <= capacity,
\ so nothing past the count is read. With the seal broken and the count
\ sound, every root refuses the store, an allocation too, and a read by
\ index still reads.
T{ 0 lf-term-sort drop 0 lf-term-bvar drop -> 0 1 }T
T{ 1 lf-term-root? 2 lf-term-root? -1 lf-term-root? 1 lf-term-valid?
   -> true false false true }T
T{ 2 lf-term-valid? 2 lf-term-read 2 lf-term-identity -1 lf-term-valid?
   -> false false false false }T
T{ 2 lf-terms store-at? 1 lf-terms store-at? -> false true }T
term-seal-flip
T{ lf-term-count-valid? 0 lf-term-root? 0 1 lf-term-pair-valid? 0 lf-term-sort
   -> false false false false }T
T{ 1 lf-term-valid? 1 lf-term-read 2 lf-term-read -> true lf-tag-bvar 0 0 true false }T
term-seal-flip
T{ lf-term-count-valid? 0 lf-term-root? 0 1 lf-term-pair-valid? -> true true true }T
lf-term-reset
\ A record the table still lists past a corrupted count (lowered by one)
\ is not given for an equal record (lf-term-same asks lf-term-valid?
\ first; review of pf1-fix L3): that record is made again at its index,
\ and the count is whole again.
T{ 0 lf-term-sort drop 0 lf-term-bvar -> 0 1 true }T
lf-term-count @ 1- lf-term-count !
T{ 0 lf-term-bvar lf-term-count @ -> 1 true 2 }T
lf-term-reset

\ The data word of lf-term-data@ is ADR 0016 C1's: the range in bits
\ 0-19, the parameter bit 20, the free-variable bit 21, the depth in
\ bits 22-31; it is kept in each record, computed when the node is made
\ (compact-store plan step S3). Here, without core/constant-term-
\ boundary.fs, only bound variables and the nodes over them have data;
\ a concrete Sort has none, and nor has any node above it.
T{ 5 true false lf-data  5 false true lf-data -> 1 20 lshift 5 +  1 21 lshift 5 + }T
T{ 1 20 lshift 2 - true true lf-data dup lf-data-loose over lf-data-params? rot lf-data-fvar?
   -> 1 20 lshift 2 - true true }T
T{ 0 lf-term-sort drop lf-term-data@ -> false }T
T{ 3 lf-term-bvar drop lf-term-data@ -> 4 true }T
T{ 0 lf-term-bvar 2drop  1 1 lf-term-app 2drop  3 lf-term-data@ -> 1 22 lshift 4 or true }T
T{ 2 1 lf-term-lam 2drop  4 lf-term-data@ -> 1 22 lshift 3 or true }T
T{ 3 2 lf-term-app 2drop  5 lf-term-data@ -> 2 22 lshift 4 or true }T
T{ 0 1 lf-term-pi 2drop  6 lf-term-data@ -> false }T
\ The largest range is no data (Lean stops at 2^20; terms.fs), and an
\ index that is not allocated has none.
T{ 1 20 lshift 2 - lf-term-bvar drop lf-term-data@ -> false }T
T{ 1 20 lshift 3 - lf-term-bvar drop lf-term-data@ -> 1 20 lshift 2 - true }T
T{ 99 lf-term-data@ -1 lf-term-data@ -> false false }T
lf-term-reset

\ Hash-consing (compact-store plan step S3): an equal record is the node
\ already made, with its identity; a rollback takes the records it gives
\ back out of the table, so an equal record made after it is new; a tag
\ marked unshared, or a context with sharing off, makes new nodes.
create hc-mark /store-mark allot
T{ 3 lf-term-bvar 3 lf-term-bvar 0 0 lf-term-app 0 0 lf-term-app -> 0 true 0 true 1 true 1 true }T
T{ 0 lf-term-identity 1 lf-term-identity lf-term-count @ -> term-serial 1- true term-serial true 2 }T
T{ hc-mark lf-terms store-mark 4 lf-term-bvar 1 2 lf-term-lam -> outcome-ok 2 true 3 true }T
T{ 1 2 lf-term-lam 4 lf-term-bvar lf-term-count @ -> 3 true 2 true 4 }T
T{ hc-mark lf-term-rollback lf-term-count @ lf-term-table htab-count -> outcome-ok 2 2 }T
T{ 1 2 lf-term-lam 5 lf-term-bvar 4 lf-term-bvar 3 lf-term-bvar -> false 2 true 3 true 0 true }T
T{ hc-mark lf-term-rollback lf-term-count @ 4 lf-term-bvar -> outcome-ok 2 2 true }T
T{ false lf-term-sharing! 3 lf-term-bvar 0 0 lf-term-app true lf-term-sharing!
   -> 3 true 4 true }T
T{ 3 lf-term-bvar 0 0 lf-term-app lf-term-count @ -> 0 true 1 true 5 }T
lf-tag-sort lf-term-unshare
T{ 9 lf-term-sort 9 lf-term-sort lf-term-sharing? -> 5 true 6 true true }T
0 lf-term-unshared-tags !
T{ 9 lf-term-sort -> 7 true }T
\ Each field takes part (review FRI B2): records equal but for the tag,
\ the first or the second field are new nodes; each made again is the
\ node already made.
T{ hc-mark lf-terms store-mark -> outcome-ok }T
T{ 0 1 lf-term-app 1 1 lf-term-app 0 1 lf-term-lam 0 1 lf-term-pi
   -> 8 true 9 true 10 true 11 true }T
T{ 0 1 lf-term-pi 0 1 lf-term-lam 1 1 lf-term-app 0 1 lf-term-app
   -> 11 true 10 true 9 true 8 true }T
T{ hc-mark lf-term-rollback lf-term-count @ -> outcome-ok 8 }T
\ A field beyond 32 bits, or a negative one, is refused as a full store.
lf-diag-clear
T{ 1 32 lshift lf-term-bvar  lf-tag-bvar -1 0 lf-term-add  lf-term-count @ -> false false 8 }T
T{ lf-diag@ nip -> 1 32 lshift u32-mask lf-diag-terms-full }T
\ A reset empties the table with the store.
lf-term-reset
T{ 3 lf-term-bvar 3 lf-term-bvar lf-term-table htab-count -> 0 true 0 true 1 }T
\ Records equal only in their tag (or in their hash's slot) stay apart:
\ 25 bound variables, then 25 applications of the first to each, all new
\ and all found again.
: bvars-apart? ( -- flag )
  true 25 0 do i 100 + lf-term-bvar drop i 1+ = and loop ;
: apps-apart? ( -- flag )
  true 26 1 do 1 i lf-term-app drop i 25 + = and loop ;
T{ bvars-apart? apps-apart? bvars-apart? apps-apart? lf-term-count @ -> true true true true 51 }T
lf-term-reset

\ The capacity is a setting of the context (plan task 3.3.1; ADR 0016
\ C9 step 3): raised, the store and its columns grow as terms are added,
\ every node and identity kept; at the new limit it is full again, with
\ the same diagnostic; lowered to the records in use, the block shrinks.
/slab context-record: probe-column
1 cells ' probe-column lf-term-columns column-add
T{ lf-term-capacity lf-term-default -> 64 64 }T
T{ 999 lf-term-capacity! lf-term-capacity -> outcome-ok 999 }T
: fill-to ( n -- )
  false lf-term-sharing!
  begin lf-term-count @ over < while 7 lf-term-bvar 2drop repeat drop true lf-term-sharing! ;
term-serial constant serial0
T{ 300 fill-to lf-term-count @ lf-terms store-capacity @ 299 lf-term-read -> 300 512
   lf-tag-bvar 7 0 true }T
T{ 0 lf-term-identity 299 lf-term-identity -> serial0 1+ true serial0 300 + true }T
\ The column covers every record, and its new units read zero.
T{ probe-column slab-capacity 512 >= 299 probe-column column-at @ -> true 0 }T
lf-diag-clear
T{ 999 fill-to 7 lf-term-bvar lf-term-count @ -> false 999 }T
T{ lf-diag@ nip -> 999 999 lf-diag-terms-full }T
T{ 998 lf-term-capacity! -> outcome-invalid }T
lf-term-reset
T{ 100 lf-term-capacity! lf-terms store-capacity @ -> outcome-ok 100 }T
T{ lf-term-default lf-term-capacity! lf-terms store-capacity @ -> outcome-ok 64 }T
\ lf-term-inner (reuse-out-2): a body one binder deeper under a lambda or
\ Pi, no room at max-n, the same depth under any other tag.
T{ 5 lf-tag-lam lf-term-inner 5 lf-tag-pi lf-term-inner 5 lf-tag-app lf-term-inner -> 6 true 6 true 5 true }T
T{ max-n lf-tag-pi lf-term-inner max-n lf-tag-app lf-term-inner -> false max-n true }T
\ lf-tag-bit (integration review 2026-11-18, plan 9.4.8n (6)): a tag's own
\ bit; above 31, bit 31; a negative tag, bit 0, which no tag has, so it is
\ in no tag set (never a shift by a negative count).
T{ lf-tag-app lf-tag-bit 31 lf-tag-bit 99 lf-tag-bit -> 8 1 31 lshift 1 31 lshift }T
T{ -1 lf-tag-bit max-n invert lf-tag-bit 0 lf-tag-bit -> 1 1 1 }T
T{ -1 lf-term-binary-tag? max-n invert lf-term-binary-tag? lf-tag-pi lf-term-binary-tag?
   -> false false true }T
\ lf-tags and lf-tag-in? (reuse-b, plan 9.4.8n (3)): a set of none, one
\ and several tags, a tag twice; membership at the set's ends, a tag
\ outside, a negative tag, and the sets made from them equal the old OR
\ chains on every tag from -2 to 40.
T{ 0 lf-tags lf-tag-app 1 lf-tags lf-tag-app lf-tag-lam 2 lf-tags -> 0 8 lf-tag-lam lf-tag-bit 8 or }T
T{ lf-tag-pi lf-tag-pi 2 lf-tags lf-tag-pi 1 lf-tags = -> true }T
T{ lf-tag-app lf-binary-tags lf-tag-in? lf-tag-let-nondep lf-binary-tags lf-tag-in? -> true true }T
T{ lf-tag-bvar lf-binary-tags lf-tag-in? -1 lf-binary-tags lf-tag-in? 99 lf-binary-tags lf-tag-in?
   -> false false false }T
: old-binder? ( tag -- flag ) dup lf-tag-lam = swap lf-tag-pi = or ;
: old-let? ( tag -- flag ) dup lf-tag-let = swap lf-tag-let-nondep = or ;
: tags-agree? ( -- flag )
  true 41 -2 do i lf-term-binder-tag? i old-binder? = and
    i lf-term-let-tag? i old-let? = and loop ;
T{ tags-agree? -> true }T
\ The leaf-table tag set takes each tag's bit by lf-tag-bit (Forth review
\ of small-fixes-1118, L3): a tag above 31 adds bit 31, a negative one bit 0.
lf-tin-leaf-tags @ constant leaf-tags-before
T{ 0 lf-tin-leaf-tags ! lf-tag-app lf-tin-leaf-tags+ 40 lf-tin-leaf-tags+ -1 lf-tin-leaf-tags+
   lf-tin-leaf-tags @ -> 8 1 31 lshift or 1 or }T
leaf-tags-before lf-tin-leaf-tags !
\ A hash table that cannot take one more entry (here frozen: htab-ready
\ answers invalid) leaves a shared node unshared: lf-term-cons appends it
\ as a new node, ok, and finds no node of the table (reuse-front-a2, the
\ path that the front end's walks once reached through a heap refusal).
true lf-term-sharing!  lf-term-capacity lf-term-count @ - 3 < [if] cr .( no room) bye [then]
9 lf-term-bvar drop constant shared-9
T{ 9 lf-term-bvar drop shared-9 = -> true }T
lf-term-table htab-freeze
T{ 9 lf-term-bvar nip 9 lf-term-bvar drop shared-9 <> -> true true }T
T{ 9 lf-term-bvar drop 9 lf-term-bvar drop <> -> true }T
\ The tag tables are sealed with the context layout (re-entrancy audit of
\ 2026-11-18, L2): once a context was made, every word that registers a
\ tag aborts and the tables stay as loading left them.
lf-term-unshared-tags @ constant unshared-before
lf-tin-leaf-tags @ constant leaf-before
tag-app 1 lf-tin-entry @ constant app-code
tag-app 0 lf-tin-entry @ constant app-twin
context-new throw context-free throw
T{ lf-tag-sort ' lf-term-unshare catch nip -> -2 }T
T{ lf-tag-app ' lf-tin-leaf-tags+ catch nip -> -2 }T
T{ 0 tag-app ' lf-term-input-tag! catch nip nip -> -2 }T
T{ 0 tag-app ' lf-term-input-twin! catch nip nip -> -2 }T
T{ lf-tag-app tag-app ' lf-term-input-leaf-tag catch nip nip -> -2 }T
T{ lf-tag-app 0 tag-app ' lf-term-input-leaf-twin catch nip nip nip -> -2 }T
T{ lf-term-unshared-tags @ lf-tin-leaf-tags @ tag-app 1 lf-tin-entry @ tag-app 0 lf-tin-entry @
   -> unshared-before leaf-before app-code app-twin }T
bye
