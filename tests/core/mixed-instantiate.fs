\ Structural transformation tests; these do not establish theorem validity.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/local-context.fs
require ../../src/core/names.fs
require ../../src/core/scratch-marks.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/core/literals.fs
require ../../src/core/string-literals.fs
require ../../src/kernel/mixed-instantiate.fs
require ../../src/kernel/mixed-open.fs
require ../../src/kernel/mixed-shift.fs
require ../support/store-faults.fs

\ These cases number their nodes and identity serials: the term store's
\ hash-consing (compact-store plan step S3) is off here, so that each
\ constructor and each rebuilt node is a new node, as the cases count.
false lf-term-sharing!

variable rid variable cid variable sid variable rootid variable outid variable serial-before
create args 2 cells allot
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-ssession-begin 0= abort" session"
  0 s" x" lf-name-str 0= abort" name" drop
  0 args ! 0 lf-level-identity 0= abort" level" args cell+ !
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref" rid ! drop
  0 rid @ lf-cterm-new 0= abort" constant" cid ! drop
  0 args cell+ @ lf-hterm-sort 0= abort" sort" sid ! drop
  0 lf-hterm-bvar 0= abort" bound" 2drop
  1 lf-hterm-bvar 0= abort" free" 2drop
  0 3 lf-term-app 0= abort" app" drop
  2 4 lf-term-app 0= abort" app" drop
  1 5 lf-term-lam 0= abort" lam" drop
  term-serial rootid ! ;
\ Source lambda: domain constant, body app(local 0, target 1).
setup
T{ 2 3 lf-term-app -> 7 true }T
T{ 0 7 lf-term-lam -> 8 true }T
term-serial rootid !
\ Replacement app(Sort, bvar 0): the free variable shifts under lambda.
T{ 1 2 lf-term-app -> 9 true }T
term-serial rid !
T{ 8 rootid @ 9 rid @ 100 lf-mixed-instantiate -> 13 term-serial outcome-ok }T
term-serial outid !
T{ 10 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 11 lf-term-read -> lf-tag-app 1 10 true }T
T{ 12 lf-term-read -> lf-tag-app 2 11 true }T
T{ 13 lf-term-read -> lf-tag-lam 0 12 true }T
T{ 13 outid @ 100 lf-cterm-check -> outcome-ok }T
\ Free variables above the target are lowered; leaves keep identities.
T{ 3 3 lf-term-identity drop 0 cid @ 100 lf-mixed-instantiate -> 14 term-serial outcome-ok }T
T{ 14 lf-term-read -> lf-tag-bvar 0 0 true }T
T{ 0 cid @ 1 sid @ 100 lf-mixed-instantiate -> 0 cid @ outcome-ok }T
T{ 2 2 lf-term-identity drop 0 cid @ 100 lf-mixed-instantiate -> 0 cid @ outcome-ok }T
T{ 2 2 lf-term-identity drop 1 sid @ 100 lf-mixed-instantiate -> 1 sid @ outcome-ok }T
T{ lf-minst-fuel @ 0> -> true }T
T{ 0 cid @ 1 sid @ -1 lf-mixed-instantiate -> -1 0 outcome-invalid }T
T{ lf-minst-fuel @ -> 0 }T
\ Two leaf audits cost four visits; visiting the source costs one more.
T{ 0 cid @ 1 sid @ 4 lf-mixed-instantiate -> -1 0 outcome-exhausted }T
T{ 0 cid @ 1 sid @ 5 lf-mixed-instantiate -> 0 cid @ outcome-ok }T
T{ lf-minst-fuel @ -> 0 }T
\ Even unused invalid or exhausted replacements are audited first.
lf-term-count @ rootid ! term-serial serial-before !
T{ 0 cid @ 9 0 100 lf-mixed-instantiate lf-minst-fuel @ -> -1 0 outcome-invalid 0 }T
T{ 0 cid @ 9 rid @ -1 lf-mixed-instantiate -> -1 0 outcome-invalid }T
T{ 0 cid @ 9 rid @ 2 lf-mixed-instantiate -> -1 0 outcome-exhausted }T
T{ lf-minst-fuel @ -> 0 }T
T{ lf-term-count @ -> rootid @ }T
T{ term-serial -> serial-before @ }T
\ A malformed unused replacement must fail without allocations.
1 2 term-second!
T{ 0 cid @ 9 rid @ 100 lf-mixed-instantiate -> -1 0 outcome-invalid }T
0 2 term-second!
T{ lf-term-count @ -> rootid @ }T
\ Exhaust after allocations, discard output, and never reuse the old identity:
\ the audit takes 4, the root's visit 1, the lowered variable's 1 (a new
\ leaf), and the target's visit finds no fuel (its replacement, lifted by
\ 0, would be the replacement itself: expr.cpp 449).
setup
T{ 3 2 lf-term-app -> 7 true }T
term-serial rootid !
term-serial serial-before !
T{ 7 rootid @ 2 2 lf-term-identity drop 6 lf-mixed-instantiate -> -1 0 outcome-exhausted }T
T{ lf-term-count @ -> 8 }T
T{ term-serial serial-before @ > -> true }T
term-serial outid !
T{ 0 lf-term-bvar -> 8 true }T
T{ 8 outid @ lf-hterm-valid? -> false }T
\ A stale constant reference invalidates either complete input.
setup lf-cref-reset
T{ 2 2 lf-term-identity drop 0 cid @ 100 lf-mixed-instantiate -> -1 0 outcome-invalid }T
T{ 0 cid @ 2 2 lf-term-identity drop 100 lf-mixed-instantiate -> -1 0 outcome-invalid }T
\ Pi body and a replacement with its own binder: its local variable stays 0,
\ while its free variable shifts past the enclosing Pi.
setup
T{ 2 3 lf-term-app -> 7 true }T
T{ 1 7 lf-term-lam -> 8 true }T
term-serial rid !
T{ 0 3 lf-term-pi -> 9 true }T
term-serial rootid !
T{ 9 rootid @ 8 rid @ 100 lf-mixed-instantiate -> 13 term-serial outcome-ok }T
T{ 10 lf-term-read -> lf-tag-bvar 2 0 true }T
T{ 11 lf-term-read -> lf-tag-app 2 10 true }T
T{ 12 lf-term-read -> lf-tag-lam 1 11 true }T
T{ 13 lf-term-read -> lf-tag-pi 0 12 true }T
T{ 13 term-serial 100 lf-cterm-check -> outcome-ok }T
\ Shifting a maximum index fails after the audits, with rollback: the
\ index has no room to grow, which is full (the largest index a term's
\ 32-bit field holds, since compact-store plan step S3; a cell's before).
setup
T{ u32-mask lf-term-bvar -> 7 true }T
T{ 0 3 lf-term-lam -> 8 true }T
term-serial rootid !
T{ 8 rootid @ 7 7 lf-term-identity drop 100 lf-mixed-instantiate -> -1 0 outcome-full }T
T{ lf-term-count @ -> 9 }T
\ Rebuilding in a full arena is full, without changing count.
: fill-arena ( -- ) begin lf-term-count @ lf-term-capacity < while
  0 lf-term-bvar 0= abort" fill" drop repeat ;
fill-arena
T{ 3 3 lf-term-identity drop 0 cid @ 100 lf-mixed-instantiate -> -1 0 outcome-full }T
T{ lf-term-count @ -> lf-term-capacity }T
\ Interface: the replacement shift runs on mixed-shift's record with the
\ instantiation's remaining fuel and hands back what it leaves, so both
\ fuel cells end equal; mixed-beta and mixed-infer continue with it.
setup
T{ 2 3 lf-term-app -> 7 true }T
T{ 0 7 lf-term-lam -> 8 true }T
term-serial rootid !
T{ 1 2 lf-term-app -> 9 true }T
term-serial rid !
T{ 8 rootid @ 9 rid @ 100 ' lf-mixed-instantiate rs-checked lf-minst-fuel @ lf-mshift-fuel @ ->
  13 term-serial outcome-ok 82 82 }T
\ The fuel runs out inside the lent shift: with the replacement app(bvar 0,
\ Sort) and 17 units, the shift moves the variable (one allocation) and
\ cannot visit the Sort. Both fuel cells end at zero, the count is
\ restored, and the serial keeps the allocation; 18 units suffice.
setup
T{ 2 3 lf-term-app -> 7 true }T
T{ 0 7 lf-term-lam -> 8 true }T
term-serial rootid !
T{ 2 1 lf-term-app -> 9 true }T
term-serial rid !  term-serial serial-before !
: inst-fuels ( -- inst shift count ) lf-minst-fuel @ lf-mshift-fuel @ lf-term-count @ ;
T{ 8 rootid @ 9 rid @ 17 lf-mixed-instantiate inst-fuels -> -1 0 outcome-exhausted 0 0 10 }T
T{ term-serial serial-before @ - -> 1 }T
\ A shift record already in use refuses the replacement's shift: the
\ instantiation fails as invalid and rolls back, and the shift's fuel and
\ amount stay as they were.
77 lf-mshift-fuel !  5 lf-mshift-amount !  1 lf-mshift-frames frame-depth !
T{ 8 rootid @ 9 rid @ 100 lf-mixed-instantiate lf-term-count @ lf-mshift-fuel @
  lf-mshift-amount @ -> -1 0 outcome-invalid 10 77 5 }T
lf-mshift-frames frame-reset
T{ 8 rootid @ 9 rid @ 18 lf-mixed-instantiate lf-minst-fuel @ ->
  13 term-serial outcome-ok 0 }T
\ A chain that fills the store (node 0 is bvar 0, node k is lam(k-1, 0)) is
\ visited 64 frames deep down to node 0, the target, whose replacement
\ node 1, lifted by 0 (itself: expr.cpp 449), makes node 1 a new lambda
\ that the full store cannot hold (full): audits 127 and 3 visits, the
\ walk 64 and node 1's body.
: chain ( -- root identity )
  lf-term-reset lf-ssession-begin 0= abort" session" 0 lf-term-bvar 2drop
  63 0 do i 0 lf-term-lam 0= abort" chain" drop loop 63 dup lf-term-identity drop ;
T{ chain 1 1 lf-term-identity drop 1000 lf-mixed-instantiate
  lf-minst-fuel @ lf-term-count @ -> -1 0 outcome-full 805 64 }T
\ With bound variable 0 for itself every node comes back unchanged
\ (update_app, update_binding): the root, after 128 audit visits and 127
\ walk visits (each lambda's body once).
T{ chain 0 0 lf-term-identity drop 1000 lf-mixed-instantiate nip lf-minst-fuel @
  -> 63 outcome-ok 745 }T
\ A loose variable above the target under a binder is lowered there too:
\ fun _ : c => #0 #2 with #0 replaced by #0 becomes fun _ : c => #0 #1.
setup
T{ 2 lf-term-bvar -> 7 true }T
T{ 2 7 lf-term-app -> 8 true }T
T{ 0 8 lf-term-lam -> 9 true }T
T{ 9 9 lf-term-identity drop 2 2 lf-term-identity drop 100 lf-mixed-instantiate
  -> 12 term-serial outcome-ok }T
T{ 10 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 11 lf-term-read -> lf-tag-app 2 10 true }T
T{ 12 lf-term-read -> lf-tag-lam 0 11 true }T

\ ---------------------------------------------------------------------------
\ The local context (src/core/local-context.fs; plan task 4.2.2a). After
\ setup: 0 constant c, 1 Sort, 2 bvar 0, 3 bvar 1, 4 c #1, 5 #0 (c #1), 6
\ fun _ : Sort => 5.
setup lf-lctx-reset
T{ lf-lctx-count @ -> 0 }T
\ x : Sort, y : x (y's type is the free variable x), and a let z : Sort := c.
T{ 1 lf-lctx-local -> 7 outcome-ok }T
T{ 7 lf-term-read -> lf-tag-fvar 0 0 true }T
T{ 7 lf-lctx-local -> 8 outcome-ok }T
T{ 1 0 lf-lctx-let -> 9 outcome-ok }T
T{ lf-lctx-count @ 7 lf-fvar-live? 8 lf-fvar-live? 9 lf-fvar-live? -> 3 true true true }T
T{ 7 lf-fvar-type 8 lf-fvar-type 8 lf-fvar-number -> 1 7 1 }T
T{ 8 lf-fvar-value 8 lf-fvar-let? 9 lf-fvar-value 9 lf-fvar-let? -> -1 false 0 true }T
\ No other node is a free variable: a leaf, a forged node of the tag with
\ an entry's number, an index beyond the store.
T{ 2 lf-fvar-live? 1 lf-fvar-live? -1 lf-fvar-live? 99 lf-fvar-live? -> false false false false }T
T{ lf-tag-fvar 0 0 lf-term-add -> 10 true }T
T{ 10 lf-fvar-live? lf-tag-fvar 5 0 lf-term-add drop lf-fvar-live? -> false false }T
\ A type or value that is no live node is invalid; nothing changes.
T{ -1 lf-lctx-local lf-lctx-count @ -> -1 outcome-invalid 3 }T
T{ 1 99 lf-lctx-let lf-lctx-count @ -> -1 outcome-invalid 3 }T
\ The audit accepts live free variables only.
T{ 7 7 lf-term-identity drop 100 lf-cterm-check -> outcome-ok }T
T{ 10 10 lf-term-identity drop 100 lf-cterm-check -> outcome-invalid }T
\ A rollback of the term store alone (a store mark, as the input's rollback
\ makes; a scratch mark would drop the entry too) leaves a discarded free
\ variable's entry dead, even when its index is used again with the same
\ fields.
create term-mark /store-mark allot
: term-marked ( -- n )
  term-mark lf-terms store-mark ok? 0= abort" term mark" term-mark mark-count @ ;
: terms-back ( -- outcome ) term-mark lf-term-rollback ;
term-marked constant before-w
T{ 1 lf-lctx-local -> before-w outcome-ok }T
T{ terms-back -> outcome-ok }T
T{ before-w lf-fvar-live? -> false }T
T{ lf-tag-fvar 3 0 lf-term-add -> before-w true }T
T{ before-w lf-fvar-live? lf-lctx-count @ -> false 4 }T
\ Capacity: a full local context is full, never ok, recorded as a full
\ binder context with its count and capacity; it makes no node.
T{ 5 lf-lctx-capacity! 1 lf-lctx-local nip -> outcome-ok outcome-ok }T
lf-term-count @ constant before-full
T{ lf-diag-clear 1 lf-lctx-local lf-term-count @ lf-lctx-count @ lf-diag@ nip
  -> -1 outcome-full before-full 5 5 5 lf-diag-binders-full }T
T{ 3 lf-lctx-capacity! -> outcome-invalid }T
T{ lf-lctx-default-limit lf-lctx-capacity! -> outcome-ok }T
\ A full term store is full too, and the entry is not claimed.
: fill-terms ( -- ) begin lf-term-count @ lf-term-capacity < while
  0 lf-term-bvar 0= abort" fill" drop repeat ;
lf-lctx-count @ constant entries-before
fill-terms
T{ 1 lf-lctx-local lf-lctx-count @ -> -1 outcome-full entries-before }T
\ A reset ends every free variable.
lf-lctx-reset
T{ 7 lf-fvar-live? lf-lctx-count @ -> false 0 }T

\ ---------------------------------------------------------------------------
\ Opening and closing binders (src/kernel/mixed-open.fs): instantiate,
\ instantiate_rev, abstract and mk_pi on the free variables x : Sort and
\ y : x, held in subst.
create subst 4 cells allot
: open-setup ( -- )
  setup lf-lctx-reset
  1 lf-lctx-local drop subst !  subst @ lf-lctx-local drop subst cell+ ! ;
: x ( -- node ) subst @ ;
: y ( -- node ) subst cell+ @ ;
: fields ( node -- tag first second ) lf-term-read 0= abort" read" ;
: rev ( node n -- node' outcome ) 1000 lf-open-fuel ! subst swap lf-instantiate-rev ;
: inst ( node n -- node' outcome ) 1000 lf-open-fuel ! subst swap lf-instantiate ;
: abstracted ( node n -- node' outcome ) 1000 lf-open-fuel ! subst swap lf-abstract ;
: index-of ( leaf -- n ) fields drop nip ;
open-setup
\ #1 #0 (node 9): instantiate_rev puts x for #1 and y for #0 (the last of
\ the n names the innermost binder), instantiate the other way round.
T{ 3 2 lf-term-app -> 9 true }T
T{ 9 2 rev nip 9 2 rev drop fields -> outcome-ok lf-tag-app x y }T
T{ 9 2 inst drop fields -> lf-tag-app y x }T
\ Under a binder #0 stays and #1 is the first loose one: fun _ : Sort =>
\ #0 #1 with x for #1 is fun _ : Sort => #0 x.
T{ 2 3 lf-term-app -> 13 true }T
T{ 1 13 lf-term-lam -> 14 true }T
T{ 14 1 rev drop fields rot drop swap 1 = swap fields -> true lf-tag-app 2 x }T
\ A variable beyond the n is lowered by n (a term with more loose
\ variables than binders opened), and n = 0 gives the node itself,
\ visiting nothing.
T{ 5 lf-term-bvar -> 17 true }T
T{ 17 2 rev drop fields -> lf-tag-bvar 3 0 }T
T{ 9 0 rev lf-open-fuel @ -> 9 outcome-ok 1000 }T
\ What does not change is kept: a closed term comes back as the same
\ node, and nothing is made.
1 2 lf-term-lam drop constant closed
lf-term-count @ constant count-closed
T{ closed 2 rev lf-term-count @ -> closed outcome-ok count-closed }T
\ abstract makes x #1 and y #0 again; a leaf of an index made before is
\ shared, not made again.
: round-trip ( -- tag i j ) 9 2 rev drop 2 abstracted drop fields >r index-of r> index-of ;
T{ round-trip -> lf-tag-app 1 0 }T
: second-leaf ( -- leaf ) 9 2 rev drop 2 abstracted drop fields >r 2drop r> ;
T{ second-leaf second-leaf = -> true }T
\ Only free variables of the n are abstracted; another stays.
T{ x 1 lf-term-app -> lf-term-count @ 1- true }T
T{ lf-term-count @ 1- subst cell+ 1 1000 lf-open-fuel ! lf-abstract drop fields
  -> lf-tag-app x 1 }T
\ Malformed: abstract over a node that is no live free variable, a dead
\ free variable met in the term, or a negative n. Any n the heap can copy
\ is taken (plan task 6.2.0): a copy it refuses is full.
T{ 1 subst cell+ ! 9 2 abstracted -> -1 outcome-invalid }T
open-setup
1 heap-refusals !
T{ 9 100000 rev -> -1 outcome-full }T
T{ 9 -1 rev -> -1 outcome-invalid }T
term-marked constant before-dead
T{ 1 lf-lctx-local -> before-dead outcome-ok }T
T{ terms-back -> outcome-ok }T
T{ lf-tag-fvar 2 0 lf-term-add -> before-dead true }T
T{ before-dead 1 lf-term-app -> before-dead 1+ true }T
T{ before-dead 1+ 2 abstracted -> -1 outcome-invalid }T
\ Fuel: none left is exhausted and discards what the pass made; one
\ unit per node visited (three for #1 #0).
open-setup
T{ 3 2 lf-term-app -> 9 true }T
lf-term-count @ constant count-before
T{ 2 lf-open-fuel ! 9 subst 2 lf-instantiate-rev lf-term-count @ lf-open-fuel @
  -> -1 outcome-exhausted count-before 0 }T
T{ 3 lf-open-fuel ! 9 subst 2 lf-instantiate-rev nip lf-open-fuel @ -> outcome-ok 0 }T
\ A pass in progress refuses another, changing nothing; after a THROW out
\ of a pass (which leaves the record busy), lf-open-reset makes it idle
\ again and the next pass runs.
: thrower ( -- ) 1 lf-open-frames frame-depth ! -77 throw ;
T{ ' thrower catch -> -77 }T
T{ 9 2 rev -> -1 outcome-invalid }T
lf-open-reset
T{ lf-open-frames frame-busy? 9 2 rev nip -> false outcome-ok }T
\ No depth limit (plan task 6.2.0): a chain lf-walk-room + 1 deep is
\ opened, on a stack that grows; a growth the heap refuses is full.
: deep ( -- node ) 2 lf-walk-room 0 do 1 swap lf-term-lam 0= abort" deep" loop ;
lf-walk-room 4 * lf-term-capacity! drop
create before-deep /lf-scratch allot
T{ before-deep lf-scratch-mark -> outcome-ok }T
T{ deep 1 rev nip -> outcome-ok }T
T{ before-deep lf-scratch-rollback -> outcome-ok }T
lf-open-frames frame-free  1 heap-refusals !
\ Declared change (group kernel-speed-3, TERM_STORE.md "As landed"): a
\ closed root takes no frame room, so the closed chain comes back, still
\ for its one unit, the heap's refusal unused; an open chain needs room
\ and is full.
T{ deep 1 rev nip lf-open-fuel @ heap-refusals @ -> outcome-ok 999 1 }T
0 heap-refusals !
: deep-open ( -- node ) lf-walk-room 2 + lf-term-bvar drop
  lf-walk-room 0 do 1 swap lf-term-lam 0= abort" deep" loop ;
deep-open constant open-chain
lf-open-frames frame-free  1 heap-refusals !
T{ open-chain 1 rev -> -1 outcome-full }T
0 heap-refusals !
\ The open chain walked leanly: one unit a node, as the frame machine
\ charged; the walk's room is two cells a rebuilt node.
T{ open-chain 1 rev nip lf-open-fuel @ -> outcome-ok 1000 lf-walk-room 2* 1+ - }T
\ mk_pi: fun over x : Sort and y : x of y is (x : Sort) -> (y : x) -> y,
\ in de Bruijn form Pi Sort (Pi #0 #0), the domain x abstracted over x.
open-setup
: pi-parts ( node -- domain body ) fields rot lf-tag-pi <> abort" no Pi" ;
variable made
T{ 1000 lf-open-fuel ! y subst 2 lf-mk-pi swap made ! -> outcome-ok }T
T{ made @ pi-parts drop -> 1 }T
T{ made @ pi-parts nip pi-parts drop fields -> lf-tag-bvar 0 0 }T
T{ made @ pi-parts nip pi-parts nip fields -> lf-tag-bvar 0 0 }T
\ A let variable would need a let term: unsupported.
T{ 1 0 lf-lctx-let drop subst ! 1000 lf-open-fuel ! 1 subst 1 lf-mk-pi
  -> -1 outcome-unsupported }T
\ A shared node is rebuilt once per offset, as Lean's replace caches it
\ (replace_fn.cpp): M = #0 #0 shared twice in M M, with x for #0, gives
\ one node x x for both, in five visits (M M, M, #0, #0, then M again: its
\ result), not seven; the result shares as the input does.
open-setup
2 2 lf-term-app drop constant twice-0
twice-0 twice-0 lf-term-app drop constant pair
: halves ( node -- first second ) fields rot drop ;
T{ pair 1 inst nip lf-open-fuel @ -> outcome-ok 995 }T
T{ pair 1 inst drop halves = -> true }T
T{ pair 1 inst drop halves drop fields -> lf-tag-app x x }T
\ What a pass kept is its own: the next pass, with y for #0, gets y y.
T{ 1000 lf-open-fuel ! pair subst cell+ 1 lf-instantiate drop halves drop fields
  -> lf-tag-app y y }T
\ The same node at another offset is another result: in (fun _ : Sort =>
\ M) M, M under the binder keeps its #0 (bound there), M outside gets x.
1 twice-0 lf-term-lam drop twice-0 lf-term-app drop constant beta-pair
: shared-parts ( node -- inner outer ) halves >r halves nip r> ;
T{ beta-pair 1 inst drop shared-parts drop -> twice-0 }T
T{ beta-pair 1 inst drop shared-parts nip fields -> lf-tag-app x x }T
\ The replace memo (kernel/replace-memo.fs, plan task 6.5.5) keys a result
\ by the node and its offset: N = #1 #1 met first outside, then under a
\ binder, in N (fun _ : Sort => N), with x for #0: outside #0 #0 (#1 is
\ lowered), inside x x.
3 3 lf-term-app drop constant n11
1 n11 lf-term-lam drop constant lam-n11
n11 lam-n11 lf-term-app drop constant outer-first
T{ outer-first 1 inst drop halves drop fields rot drop index-of swap index-of -> 0 0 }T
T{ outer-first 1 inst drop halves nip fields nip nip fields -> lf-tag-app x x }T
\ instantiate_rev with an inference scope (lf-instantiate-scope): a node
\ closed before under the same scope comes back for no fuel; another
\ scope, named by its innermost free variable, gets its own result.
: scoped ( node addr -- node' outcome ) 1 lf-instantiate-scope ;
T{ 1000 lf-open-fuel ! twice-0 subst scoped drop fields lf-open-fuel @
   -> lf-tag-app x x 997 }T
T{ 1000 lf-open-fuel ! twice-0 subst scoped drop fields lf-open-fuel @
   -> lf-tag-app x x 1000 }T
T{ 1000 lf-open-fuel ! twice-0 subst cell+ scoped drop fields -> lf-tag-app y y }T
\ A kept result discarded since is a miss, never the node that takes its
\ index: #1 #0 closed with x and y, its result rolled back and its index
\ taken by #0 #0, is closed again.
3 2 lf-term-app drop constant n10
term-marked constant before-close
T{ 1000 lf-open-fuel ! n10 subst 2 lf-instantiate-scope drop fields -> lf-tag-app x y }T
T{ terms-back -> outcome-ok }T
T{ 2 2 lf-term-app 2drop 1000 lf-open-fuel ! n10 subst 2 lf-instantiate-scope drop fields
   -> lf-tag-app x y }T
\ A free variable no longer live is met even in a node with no loose bound
\ variable, which instantiate keeps unvisited only when no free variable
\ hides in it: invalid.
term-marked constant before-gone
T{ 1 lf-lctx-local -> before-gone outcome-ok }T
T{ terms-back -> outcome-ok }T
T{ lf-tag-fvar 2 0 lf-term-add -> before-gone true }T
T{ before-gone 1 lf-term-app -> before-gone 1+ true }T
T{ before-gone 1+ 1 inst -> -1 outcome-invalid }T
\ The single-binder pass keeps its results by node and depth too: in N
\ (fun _ : c => N), N = #0 #1, with c for the target, N is c #0 outside
\ and #0 c under the binder.
2 3 lf-term-app drop constant n01
0 n01 lf-term-lam drop constant lam-n01
n01 lam-n01 lf-term-app drop constant inst-pair
: inst1 ( node -- node' outcome )
  dup lf-term-identity drop 0 dup lf-term-identity drop 100 lf-mixed-instantiate nip ;
T{ inst-pair inst1 drop halves drop fields rot drop index-of -> 0 0 }T
T{ inst-pair inst1 drop halves nip fields nip nip fields -> lf-tag-app 2 0 }T
\ Literal leaves are kept as they are (coverage COV2): #0 5 "ab" with c
\ for the target is c 5 "ab", over the same literal nodes.
5 lf-hterm-cell drop drop constant lit-five
s" ab" lf-str-new ok? drop drop constant str-ab
2 lit-five lf-term-app drop str-ab lf-term-app drop constant lit-term
T{ lit-term inst1 drop halves swap halves -> str-ab 0 lit-five }T
\ A replace memo that cannot keep a result (lf-rmemo-kept, cell-pair!
\ since cleanup-families-2): memo-put refused by the heap keeps nothing
\ and leaves the stack clean; with room the result is kept.
create t-rmemo /lf-rmemo allot  t-rmemo /lf-rmemo erase
0 t-rmemo lf-rmemo-begin
T{ 1 heap-refusals ! 7 8 t-rmemo lf-rmemo-kept t-rmemo lf-rmemo-count heap-refusals @ -> 0 0 }T
T{ 7 8 t-rmemo lf-rmemo-kept t-rmemo lf-rmemo-count -> 1 }T
t-rmemo lf-rmemo-release
\ The scratch memo (group kernel-speed-3): an unstamped call's entries are
\ found within the call and by no other call, whether it ended, failed or
\ never ended (a THROW); a stamped call's stay for its stamp, an unstamped
\ call in between finding none of them.
create u-rmemo /lf-rmemo allot  u-rmemo /lf-rmemo erase
: u-call ( -- ) 0 u-rmemo lf-rmemo-begin ;
: u-keep ( offset -- ) n11 twice-0 rot u-rmemo lf-rmemo! ;
: u-find ( offset -- flag ) twice-0 swap u-rmemo lf-rmemo@ dup if nip then ;
: u-end ( outcome -- ) u-rmemo lf-rmemo-end ;
T{ u-call 0 u-keep 0 u-find u-rmemo lf-rmemo-count u-rmemo lf-rmemo-stamp @ -> true 1 -1 }T
T{ outcome-ok u-end u-rmemo lf-rmemo-count u-call 0 u-find -> 0 false }T
T{ 0 u-keep outcome-invalid u-end u-call 0 u-find -> false }T
T{ 0 u-keep u-rmemo lf-rmemo-count u-call 0 u-find u-rmemo lf-rmemo-count -> 1 false 0 }T
T{ 7 u-rmemo lf-rmemo-begin 0 u-keep outcome-ok u-end u-call 0 u-find -> false }T
T{ outcome-ok u-end 7 u-rmemo lf-rmemo-begin 0 u-find outcome-ok u-end -> true }T
\ A stamped call that fails has its entries taken out: the next call of
\ its stamp finds the earlier entry, not the failed call's.
T{ 7 u-rmemo lf-rmemo-begin 5 u-keep outcome-invalid u-end -> }T
T{ 7 u-rmemo lf-rmemo-begin 5 u-find 0 u-find outcome-ok u-end -> false true }T
\ A call that keeps 600 entries grows the scratch memo while it runs and
\ finds each; the next unstamped call begins by emptying it whole (more
\ than lf-rmemo-scratch-most), its numbering begun again; the stamped
\ entry stays.
: u-many ( -- ) 600 0 do i u-keep loop ;
: u-all? ( -- flag ) true 600 0 do i u-find and loop ;
T{ u-call u-many u-all? u-rmemo lf-rmemo-unheld outcome-ok u-end -> true 600 }T
T{ u-call u-rmemo lf-rmemo-scratch memo-count u-rmemo lf-rmemo-stamp @ 0 u-find -> 0 -1 false }T
T{ outcome-ok u-end 7 u-rmemo lf-rmemo-begin 0 u-find outcome-ok u-end -> true }T
\ Below the threshold the scratch memo is kept: two entries stay there,
\ unreachable, after the next call begins.
T{ u-call 0 u-keep 1 u-keep outcome-ok u-end u-call u-rmemo lf-rmemo-scratch memo-count -> 2 }T
T{ u-rmemo lf-rmemo-empty u-rmemo lf-rmemo-count 7 u-rmemo lf-rmemo-begin 0 u-find -> 0 false }T
\ A negative stamp is taken as 0 (stamps are >= 0): the call is numbered
\ and never finds the entries of the scratch call whose number it names.
T{ outcome-ok u-end u-call 0 u-keep outcome-ok u-end u-rmemo lf-rmemo-stamp @ u-rmemo lf-rmemo-begin
   0 u-find u-rmemo lf-rmemo-scratch? -> false true }T
outcome-ok u-end
u-rmemo lf-rmemo-release
\ A refused memo: the heap refuses the scratch memo, made second. The
\ table is made, and a stamped call keeps, finds and, failing, has its
\ entries cut as before; an unstamped call keeps nothing (a miss). The
\ next call makes the scratch memo alone, the table's entries kept.
create v-rmemo /lf-rmemo allot  v-rmemo /lf-rmemo erase
: v-made ( -- n ) live-blocks @ 0 v-rmemo lf-rmemo-begin live-blocks @ swap - ;
v-made 2/ constant memo-blocks  v-rmemo lf-rmemo-release
: v-refused ( stamp -- ) v-rmemo lf-rmemo-release memo-blocks 1+ heap-refusals ! v-rmemo lf-rmemo-begin ;
: v-live ( -- table? scratch? ) v-rmemo lf-rmemo-table memo-live? v-rmemo lf-rmemo-scratch memo-live? ;
: v-keep ( offset -- ) n11 twice-0 rot v-rmemo lf-rmemo! ;
: v-find ( offset -- flag ) twice-0 swap v-rmemo lf-rmemo@ dup if nip then ;
: v-end ( outcome -- ) v-rmemo lf-rmemo-end ;
T{ memo-blocks 0> 7 v-refused v-live heap-refusals @ -> true true false 0 }T
T{ 0 v-keep 0 v-find outcome-ok v-end 7 v-rmemo lf-rmemo-begin v-live 0 v-find -> true true true true }T
outcome-ok v-end
T{ 7 v-refused 5 v-keep 5 v-find outcome-invalid v-end 7 v-rmemo lf-rmemo-begin 5 v-find -> true false }T
outcome-ok v-end
T{ 0 v-refused 0 v-keep 0 v-find outcome-ok v-end v-rmemo lf-rmemo-count -> false 0 }T
v-rmemo lf-rmemo-release

\ ---------------------------------------------------------------------------
\ The lean walk (kernel/open-walk.fs, group kernel-speed-3), with steps
\ that log each visit's fuel, context and node: the frame machine's order
\ and charges -- the root's unit spent by its own visit, each child's at
\ the start of its visit, a kept leaf's too, the second child only after
\ the first's subtree, one binder deeper under a lambda; a join logs -1.
create walk-log 64 cells allot  variable walk-n
: log, ( x -- ) walk-log walk-n @ cells + ! 1 walk-n +! ;
: log@ ( i -- x ) cells walk-log + @ ;
: stub-look ( x frames -- r outcome true | x false )
  dup frame-fuel @ log, frame-context @ log, dup log,
  dup lf-term-tag@ lf-term-binary-tag? if false else outcome-ok true then ;
: stub-join ( r1 node r2 -- result outcome ) drop nip -1 log, outcome-ok ;
' noop frames: tf
: stubbed ( x frames -- r outcome frames )
  ['] lf-walk-look defer@ >r ['] lf-walk-join defer@ >r
  ['] stub-look is lf-walk-look ['] stub-join is lf-walk-join
  0 walk-n ! lf-walk-node r> is lf-walk-join r> is lf-walk-look ;
: walk-with ( x fuel -- r outcome ) tf frame-fuel ! tf stubbed drop ;
2 3 lf-term-app drop constant ab
ab 2 lf-term-app drop constant ab-c
T{ ab-c 100 walk-with walk-n @ tf frame-used @ -> ab-c outcome-ok 17 0 }T
T{ 0 log@ 2 log@ 3 log@ 5 log@ 6 log@ 8 log@ 9 log@ 11 log@ 12 log@ 13 log@ 15 log@ 16 log@
   -> 100 ab-c 99 ab 98 2 97 3 -1 96 2 -1 }T
\ Fuel runs out at the second child: the kept leaf's visit took the last
\ unit; the walk's cells are given back.
T{ ab-c 3 walk-with tf frame-used @ tf frame-fuel @ walk-n @ -> -1 outcome-exhausted 0 0 13 }T
\ Under a lambda the second child is one binder deeper, and the context
\ is back after it.
1 ab lf-term-lam drop constant lam-ab
T{ lam-ab 100 walk-with tf frame-context @ -> lam-ab outcome-ok 0 }T
T{ 4 log@ 7 log@ 10 log@ 13 log@ -> 0 1 1 1 }T
\ A failure deep inside gives the cells and the context back.
T{ lam-ab 2 walk-with tf frame-used @ tf frame-context @ -> -1 outcome-exhausted 0 0 }T
\ A node to rebuild whose room the heap refuses is full, nothing kept.
T{ tf frame-free 1 heap-refusals ! ab tf lf-walk-into heap-refusals @ tf frame-used @
   -> -1 outcome-full tf true 0 0 }T
\ The real steps at the binder limit: a lambda over a live free variable
\ (no data word decides it) at context max-n is full before any child is
\ charged, recorded as a full binder context.
open-setup
1 x lf-term-lam drop constant lam-x
T{ subst 1 lf-open-mode-rev lf-open-ready lf-open-marked -> outcome-ok outcome-ok }T
max-n lf-open-frames frame-context !  100 lf-open-fuel !
T{ lf-diag-clear lam-x lf-open-frames lf-walk-node drop lf-open-fuel @ lf-diag@ nip
   -> -1 outcome-full 100 max-n max-n lf-diag-binders-full }T
lf-open-reset
\ Each leaf's fail-closed test stays in the walk: a node the pass may not
\ read and a free variable no longer live are tested above (before-gone);
\ a bound variable that is no well-formed leaf, inside a term, is invalid.
lf-tag-bvar 0 1 lf-term-add drop constant bad-bvar
T{ 1 bad-bvar lf-term-app drop 1 inst nip -> outcome-invalid }T
\ A leaf of a tag the pass does not know (a plain Sort) inside an open
\ term is invalid, and so is a root past the store's count (not read).
0 lf-term-sort drop constant plain-sort
T{ plain-sort 0 lf-term-bvar drop lf-term-app drop 1 inst nip -> outcome-invalid }T
0 lf-term-bvar drop 77 lf-term-bvar drop lf-term-app drop constant fresh-app
T{ fresh-app 1+ lf-term-count @ lf-term-base + = -> true }T
T{ -1 lf-term-count +! fresh-app 1 inst 1 lf-term-count +! -> -1 outcome-invalid }T
\ A binary node whose child is not below it (a record changed in place)
\ is refused before any child is visited.
: first-field ( node -- addr ) lf-term-slot 1 u32s + ;
T{ fresh-app first-field u32@ fresh-app fresh-app first-field u32! fresh-app 1 inst
   rot fresh-app first-field u32! -> -1 outcome-invalid }T
\ A closed root comes back for its one unit; with none left it is
\ exhausted, as the frame machine's admission refuses.
1 1 lf-term-app drop constant closed-11
T{ closed-11 lf-open-closed? 5 lf-open-fuel ! closed-11 subst 1 lf-instantiate-rev lf-open-fuel @
   -> true closed-11 outcome-ok 4 }T
T{ 0 lf-open-fuel ! closed-11 subst 1 lf-instantiate-rev lf-open-fuel @ -> -1 outcome-exhausted 0 }T
\ The closed root's test of the stores' counts (lf-scratch-counts?) stands
\ for the scratch mark's refusal: each family whose count is not valid
\ (its seal broken) is refused, and the root is invalid, fuel unchanged.
: counts-without ( store -- flag ) dup seal-flip lf-scratch-counts? swap seal-flip ;
T{ lf-scratch-counts? lf-terms counts-without lf-levels counts-without lf-crefs counts-without
   -> true false false false }T
: closed-without ( store -- node outcome fuel )
  5 lf-open-fuel ! dup seal-flip closed-11 subst 1 lf-instantiate-rev rot seal-flip lf-open-fuel @ ;
T{ lf-terms closed-without -> -1 outcome-invalid 5 }T
T{ lf-levels closed-without -> -1 outcome-invalid 5 }T
T{ lf-crefs closed-without -> -1 outcome-invalid 5 }T
\ A closed root under a scope makes the memo call its pass makes: the
\ memo stamped with x's identity plus one, its base the table's count.
: x-stamp ( -- stamp ) x lf-term-identity drop 1+ ;
: memo-based? ( -- flag ) lf-open-memo dup lf-rmemo-base @ swap lf-rmemo-table memo-count = ;
max-n lf-open-memo lf-rmemo-base !
T{ 5 lf-open-fuel ! closed-11 subst scoped lf-open-fuel @ lf-open-memo lf-rmemo-stamp @ x-stamp =
   memo-based? -> closed-11 outcome-ok 4 true true }T
bye
