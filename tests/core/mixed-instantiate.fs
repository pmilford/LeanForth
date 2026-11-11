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
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-instantiate.fs
require ../../src/kernel/mixed-open.fs
require ../../src/kernel/mixed-shift.fs
require ../support/store-faults.fs

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
\ Exhaust after allocations, discard output, and never reuse the old identity.
setup
T{ 2 3 lf-term-app -> 7 true }T
term-serial rootid !
term-serial serial-before !
T{ 7 rootid @ 2 2 lf-term-identity drop 7 lf-mixed-instantiate -> -1 0 outcome-exhausted }T
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
\ index has no room to grow, which is full.
setup
T{ lf-mshift-max lf-term-bvar -> 7 true }T
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
\ cannot be copied into the full store (full): audits 127 and 1 visits, the
\ walk 64, the shift 1.
: chain ( -- root identity )
  lf-term-reset lf-ssession-begin 0= abort" session" 0 lf-term-bvar 2drop
  63 0 do i 0 lf-term-lam 0= abort" chain" drop loop 63 dup lf-term-identity drop ;
T{ chain 0 0 lf-term-identity drop 1000 lf-mixed-instantiate
  lf-minst-fuel @ lf-mshift-fuel @ lf-term-count @ -> -1 0 outcome-full 807 807 64 }T
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
\ A rollback of the term store leaves a discarded free variable's entry
\ dead, even when its index is used again with the same fields.
lf-term-count @ constant before-w
T{ 1 lf-lctx-local -> before-w outcome-ok }T
before-w lf-term-count !
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
lf-term-count @ constant before-dead
T{ 1 lf-lctx-local -> before-dead outcome-ok }T
before-dead lf-term-count !
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
lf-term-count @ constant before-deep
T{ deep 1 rev nip -> outcome-ok }T
before-deep lf-term-count !  lf-open-frames frame-free  1 heap-refusals !
T{ deep 1 rev -> -1 outcome-full }T
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
bye
