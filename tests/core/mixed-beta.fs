\ Structural reduction tests, not proof or type checking.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-beta.fs
require ../../src/kernel/mixed-instantiate.fs
require ../../src/kernel/mixed-shift.fs

variable cid variable sid variable rootid variable count-before variable serial-before
create args 2 cells allot
create beta-mark /lf-scratch allot   \ the stores before a probe's pass
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-ssession-begin 0= abort" session"
  0 s" x" lf-name-str 0= abort" name" drop
  0 args ! 0 lf-level-identity 0= abort" level" args cell+ !
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref"
  lf-cterm-new 0= abort" constant" cid ! drop
  0 args cell+ @ lf-hterm-sort 0= abort" sort" sid ! drop
  0 lf-term-bvar 0= abort" bvar" drop
  0 2 lf-term-lam 0= abort" identity" drop ;

setup
\ Identity preserves a constant's allocation stamp, including its reference.
T{ 3 0 lf-term-app -> 4 true }T
T{ 4 lf-term-serial @ 200 lf-mixed-beta -> 0 cid @ outcome-ok }T
T{ 0 cid @ 100 lf-cterm-check -> outcome-ok }T
\ A generated lambda becomes the head of the next contraction.
T{ 3 3 lf-term-app -> 5 true }T
T{ 5 0 lf-term-app -> 6 true }T
lf-term-serial @ rootid !
T{ 6 rootid @ 500 lf-mixed-beta -> 0 cid @ outcome-ok }T
\ Non-lambda heads are rebuilt; neither arguments nor binder bodies reduce.
setup
T{ 3 0 lf-term-app -> 4 true }T
T{ 3 2 lf-term-app -> 5 true }T
T{ 5 4 lf-term-app -> 6 true }T
T{ 6 lf-term-serial @ 500 lf-mixed-beta -> 8 lf-term-serial @ outcome-ok }T
T{ 8 lf-term-read -> lf-tag-app 7 4 true }T
T{ 8 lf-term-serial @ 100 lf-cterm-check -> outcome-ok }T
T{ 3 3 lf-term-identity drop 100 lf-mixed-beta -> 3 3 lf-term-identity drop outcome-ok }T
\ A malformed discarded argument must fail before any allocations.
T{ 0 lf-term-symbolic-sort -> 9 true }T
T{ 0 0 lf-term-lam -> 10 true }T
T{ 10 9 lf-term-app -> 11 true }T
lf-term-count @ count-before ! lf-term-serial @ serial-before !
T{ 11 lf-term-serial @ 200 lf-mixed-beta -> -1 0 outcome-invalid }T
T{ lf-term-count @ -> count-before @ }T
T{ lf-term-serial @ -> serial-before @ }T
6 lf-term-identity drop rootid !
T{ 6 rootid @ -1 lf-mixed-beta -> -1 0 outcome-invalid }T
T{ 6 rootid @ 0 lf-mixed-beta -> -1 0 outcome-exhausted }T
\ A failed audit leaves no fuel.
T{ 6 0 500 lf-mixed-beta lf-mbeta-fuel @ -> -1 0 outcome-invalid 0 }T
\ Find exhaustion after allocation and check atomic rollback and serial use;
\ a pass that succeeds is given back through a scratch mark.
: probe-marked ( -- flag )
  lf-term-count @ count-before ! lf-term-serial @ serial-before !
  beta-mark lf-scratch-mark ok? ;
: probe-back ( -- flag ) beta-mark lf-scratch-rollback ok? ;
: rollback-probe ( -- flag )
  500 1 do
    probe-marked 0= if false unloop exit then
    6 rootid @ i lf-mixed-beta
    dup outcome-exhausted = lf-term-serial @ serial-before @ > and if
      2drop drop lf-term-count @ count-before @ = unloop exit
    then
    2drop drop probe-back 0= if false unloop exit then
  loop false ;
T{ rollback-probe -> true }T
\ Reuse the first rolled-back slot; its prior allocation identity stays stale.
T{ 0 lf-term-bvar -> count-before @ true }T
T{ count-before @ serial-before @ 1+ lf-hterm-valid? -> false }T
T{ count-before @ lf-term-serial @ lf-hterm-valid? -> true }T
T{ probe-back -> true }T
\ Omega never ends: with 200 units it runs out of fuel (exhausted), and with
\ 300 it fills the store first, 47 units to spare (full). Both roll back all
\ generated terms.
T{ 2 2 lf-term-app -> 12 true }T
T{ 0 12 lf-term-lam -> 13 true }T
T{ 13 13 lf-term-app -> 14 true }T
lf-term-count @ count-before !
T{ 14 lf-term-serial @ 200 lf-mixed-beta lf-mbeta-fuel @ -> -1 0 outcome-exhausted 0 }T
T{ lf-term-count @ -> count-before @ }T
T{ 14 dup lf-term-identity drop 300 lf-mixed-beta lf-mbeta-fuel @ ->
  -1 0 outcome-full 47 }T
T{ lf-term-count @ -> count-before @ }T
\ Capture avoidance under a binder preserves the constant annotation.
setup
T{ 1 lf-term-bvar -> 4 true }T
T{ 0 4 lf-term-lam -> 5 true }T
T{ 1 5 lf-term-lam -> 6 true }T
T{ 6 2 lf-term-app -> 7 true }T
T{ 7 lf-term-serial @ 500 lf-mixed-beta -> 9 lf-term-serial @ outcome-ok }T
T{ 8 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 9 lf-term-read -> lf-tag-lam 0 8 true }T
T{ 9 lf-term-serial @ 100 lf-cterm-check -> outcome-ok }T
lf-cref-reset
T{ 7 7 lf-term-identity drop 500 lf-mixed-beta -> -1 0 outcome-invalid }T
\ Deep nesting: R = app(F, L) with F = lam(c, L) and L = m lambdas over
\ bvar m. Contracting R instantiates L (m+1 frames deep) and shifts L
\ inside it (m+1 more). After this file's four-node setup, m = 57 fills the
\ store and the shift is full at the bottom, 117 frames deep; with m = 18
\ everything fits. The fuel cells of all three passes end equal.
: lams ( body n -- node ) 0 ?do 0 swap lf-term-lam 0= abort" lam" loop ;
: deep ( m -- root identity )
  setup >r r@ lf-term-bvar 0= abort" bvar" r> lams
  dup 0 swap lf-term-lam 0= abort" F" swap lf-term-app 0= abort" R"
  dup lf-term-identity drop ;
: fuels ( -- beta inst shift ) lf-mbeta-fuel @ lf-minst-fuel @ lf-mshift-fuel @ ;
T{ 57 deep 100000 ' lf-mixed-beta rs-checked fuels lf-term-count @ ->
  -1 0 outcome-full 99076 99076 99076 64 }T
T{ 18 deep 100000 ' lf-mixed-beta rs-checked fuels ->
  61 lf-term-serial @ outcome-ok 99699 99700 99700 }T
T{ 61 lf-term-read -> lf-tag-lam 0 60 true }T
\ An audit failure (stale root) or negative fuel leaves zero fuel.
setup
T{ 3 lf-term-serial @ 1+ 100 lf-mixed-beta lf-mbeta-fuel @ -> -1 0 outcome-invalid 0 }T
T{ 3 lf-term-serial @ -1 lf-mixed-beta lf-mbeta-fuel @ -> -1 0 outcome-invalid 0 }T
\ An irreducible root comes back with its own index and identity and
\ nothing is allocated: a variable head over a redex argument, and a lambda
\ whose body is a redex (weak-head reduction stops at both).
setup
T{ 3 0 lf-term-app -> 4 true }T
T{ 2 4 lf-term-app -> 5 true }T
T{ 1 4 lf-term-lam -> 6 true }T
lf-term-serial @ serial-before !
T{ 5 5 lf-term-identity drop 100 lf-mixed-beta -> 5 5 lf-term-identity drop outcome-ok }T
T{ 6 6 lf-term-identity drop 100 lf-mixed-beta -> 6 6 lf-term-identity drop outcome-ok }T
T{ lf-term-count @ lf-term-serial @ -> 7 serial-before @ }T

\ The deepest nesting found for a 64-node store: from a store holding only
\ the constant c, R = app(T, T) with T = 61 lambdas over bvar 60. The
\ contraction instantiates T's body (61 frames) and shifts T inside it (62
\ frames), 124 frames in all; the store fills and the shift is full at the
\ bottom without overflowing the host's stacks (about 700 return-stack and
\ 500 data-stack cells, measured).
: setup1 ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-ssession-begin 0= abort" session" 0 s" x" lf-name-str 0= abort" name" drop
  0 args ! 0 lf-level-identity 0= abort" level" args cell+ !
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref"
  lf-cterm-new 0= abort" c" 2drop ;
: twin ( m -- root identity )
  setup1 dup 1- lf-term-bvar 0= abort" bvar" swap lams
  dup lf-term-app 0= abort" R" dup lf-term-identity drop ;
T{ 61 twin 100000 ' lf-mixed-beta rs-checked fuels lf-term-count @ ->
  -1 0 outcome-full 99020 99020 99020 64 }T
T{ 60 twin 100000 lf-mixed-beta fuels lf-term-count @ ->
  -1 0 outcome-full 99036 99036 99036 63 }T

\ Records in use. A record left busy (by a THROW out of a pass, or a pass
\ asked again from inside itself) refuses its pass as invalid, changing
\ nothing a running pass relies on, so the outer pass fails closed;
\ lf-mixed-rebuild-reset makes the four records idle again (mixed-open's
\ too, plan task 4.2.2a).
setup
T{ 3 0 lf-term-app -> 4 true }T
T{ 4 lf-term-serial @ 200 lf-mixed-beta -> 0 cid @ outcome-ok }T
1 lf-minst-frames frame-depth !
T{ 4 lf-term-serial @ 200 lf-mixed-beta lf-term-count @ -> -1 0 outcome-invalid 5 }T
1 lf-mbeta-frames frame-depth !  1 lf-mshift-frames frame-depth !
T{ 4 lf-term-serial @ 200 lf-mixed-beta -> -1 0 outcome-invalid }T
T{ 0 cid @ 0 1 9 lf-mixed-shift -> -1 0 outcome-invalid }T
1 lf-open-frames frame-depth !
lf-mixed-rebuild-reset
T{ lf-mbeta-frames frame-busy? lf-minst-frames frame-busy? lf-mshift-frames frame-busy? ->
  false false false }T
T{ lf-open-frames frame-busy? -> false }T
T{ 4 lf-term-serial @ 200 ' lf-mixed-beta rs-checked -> 0 cid @ outcome-ok }T
bye
