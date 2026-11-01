include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs

create args 4 cells allot
variable name-id
variable ref-id
variable old-id
variable level-id
create eight-args 16 cells allot
: setup ( -- )
lf-name-reset lf-level-reset lf-cref-reset
0 s" alpha" lf-name-str 0= abort" name" name-id !
0 args ! lf-level-identities @ args cell+ !
0 lf-level-identities @ lf-hlevel-succ 0= abort" level"
 dup level-id ! args 3 cells + ! args 2 cells + ! ;
setup
T{ name-id @ lf-name-generation @ 0 0 lf-cref-new -> 0 1 true }T
T{ 0 1 lf-cref-read -> name-id @ lf-name-generation @ 0 true }T
T{ name-id @ lf-name-generation @ args 2 lf-cref-new -> 1 2 true }T
2 ref-id !
T{ 1 ref-id @ lf-cref-read -> name-id @ lf-name-generation @ 2 true }T
T{ 1 ref-id @ 0 lf-cref-level -> 0 lf-level-identities @ true }T
T{ 1 ref-id @ 1 lf-cref-level -> 1 level-id @ true }T
T{ 1 ref-id @ 2 lf-cref-level -> false }T
T{ -1 1 lf-cref-valid? -> false }T
T{ 2 1 lf-cref-valid? -> false }T
T{ 1 ref-id @ -1 lf-cref-level -> false }T
T{ name-id @ lf-name-generation @ args -1 lf-cref-new -> false }T
T{ name-id @ lf-name-generation @ args 9 lf-cref-new -> false }T
T{ -1 lf-name-generation @ args 2 lf-cref-new -> false }T
T{ name-id @ lf-name-generation @ 1- args 2 lf-cref-new -> false }T
-1 args 3 cells + !
T{ name-id @ lf-name-generation @ args 2 lf-cref-new -> false }T
T{ lf-cref-count @ lf-cref-serial @ -> 2 2 }T
level-id @ args 3 cells + !
\ Rollback and reuse a level slot invalidates the captured pair.
1 lf-level-count !
: reuse-level ( -- ) 0 lf-level-identities @ lf-hlevel-succ 0= abort" level reuse" 2drop ;
reuse-level
T{ 1 ref-id @ lf-cref-valid? -> false }T
\ Rollback and reuse a reference slot must not resurrect the old handle.
1 lf-cref-count !
T{ name-id @ lf-name-generation @ 0 0 lf-cref-new -> 1 3 true }T
T{ 1 ref-id @ lf-cref-valid? -> false }T
3 old-id !
lf-cref-reset
T{ name-id @ lf-name-generation @ 0 0 lf-cref-new -> 0 4 true }T
T{ 0 4 lf-cref-valid? -> true }T
\ Slot zero was reused after reset; its first identity remains stale.
T{ 0 1 lf-cref-valid? -> false }T
T{ 1 old-id @ lf-cref-valid? -> false }T
lf-name-reset
: reuse-name ( -- ) 0 s" alpha" lf-name-str 0= abort" name reuse" drop ;
reuse-name
T{ 0 4 lf-cref-valid? -> false }T
\ Fill reference storage; the rejected allocation does not advance serial.
lf-cref-reset
: fill-refs ( -- ) lf-cref-capacity 0 do
  0 lf-name-generation @ 0 0 lf-cref-new 0= abort" fill" 2drop
loop ;
fill-refs
T{ 0 lf-name-generation @ 0 0 lf-cref-new -> false }T
T{ lf-cref-count @ lf-cref-serial @ -> lf-cref-capacity 36 }T
\ Maximum argument count preserves every ordered pair.
lf-cref-reset
: prepare-eight ( -- ) 8 0 do
  i 2 mod if 1 else 0 then eight-args i 2 * cells + !
  i 2 mod if lf-level-serial @ else lf-level-identities @ then
  eight-args i 2 * 1+ cells + !
loop ;
prepare-eight
T{ 0 lf-name-generation @ eight-args 8 lf-cref-new -> 0 37 true }T
T{ 0 37 0 lf-cref-level -> 0 lf-level-identities @ true }T
T{ 0 37 7 lf-cref-level -> 1 lf-level-serial @ true }T
lf-level-reset
T{ 0 37 lf-cref-valid? -> false }T
\ Saturation refuses allocation without changing the live reference count.
lf-cref-reset
-1 1 rshift lf-cref-serial !
T{ 0 lf-name-generation @ 0 0 lf-cref-new -> false }T
T{ lf-cref-count @ -> 0 }T
bye
