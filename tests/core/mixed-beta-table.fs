\ Test-only comparison with Lean kernel weak-head beta reduction.
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/kernel/mixed-rebuild.fs
include ../../src/kernel/mixed-shift.fs
include ../../src/kernel/mixed-instantiate.fs
include ../../src/kernel/mixed-beta.fs
decimal
variable beta-root
: named ( addr len -- ) 0 -rot lf-name-str 0= if -1 throw then drop ;
: make-constant ( name -- )
  lf-name-generation @ 0 0 lf-cref-new 0= if -1 throw then
  lf-cterm-new 0= if -1 throw then 2drop ;
: build-base ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  s" c" named s" d" named s" f" named
  lf-ssession-begin 0= if -1 throw then
  1 make-constant 2 make-constant 3 make-constant
  0 dup lf-level-identity 0= if -1 throw then lf-hterm-sort 0= if -1 throw then 2drop
  2 0 do i lf-term-bvar 0= if -1 throw then drop loop ;
: make-app ( a b -- node ) lf-term-app 0= if -1 throw then ;
: make-lam ( a b -- node ) lf-term-lam 0= if -1 throw then ;
\ Nodes 0..5: constants c,d,f; Sort 0; variables #0 and #1.
: build-case ( n -- node )
  case
    0 of 0 endof
    1 of 3 4 make-lam 0 make-app endof
    2 of 3 1 make-lam 0 make-app endof
    3 of 3 5 make-lam 3 swap make-lam 0 make-app 1 make-app endof
    4 of 3 4 make-lam 0 make-app 2 swap make-app endof
    5 of 2 4 make-app 3 swap make-lam 0 make-app endof
    6 of 3 4 make-lam 4 make-app 3 swap make-lam endof
    -1 throw
  endcase ;
: emit-term ( node -- )
  lf-term-read 0= if -1 throw then rot case
    lf-tag-symbolic-sort of 0<> swap 0<> or if -1 throw then s" S " type endof
    lf-tag-constant of drop case
      0 of s" C " type endof 1 of s" D " type endof 2 of s" F " type endof -1 throw endcase endof
    lf-tag-bvar of drop s" V " type . endof
    lf-tag-app of s" A " type swap recurse recurse endof
    lf-tag-lam of s" L " type swap recurse recurse endof
    lf-tag-pi of s" P " type swap recurse recurse endof
    -1 throw
  endcase ;
: emit-table ( -- )
  7 0 do
    build-base i build-case beta-root ! i .
    beta-root @ dup lf-term-identity 0= if -1 throw then
    10000 lf-mixed-beta lf-mbeta-ok <> if 2drop -1 throw then
    2dup 10000 lf-cterm-check lf-repr-ok <> if 2drop -1 throw then
    drop emit-term cr
  loop ;
emit-table bye
