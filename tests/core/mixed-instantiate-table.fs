\ Compare mixed-term syntax with Lean, not type or theorem validity.
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs
include ../../src/experimental/constant-term-boundary.fs
include ../../src/experimental/mixed-shift.fs
include ../../src/experimental/mixed-instantiate.fs
decimal
create actual 2 cells allot
variable source-root
variable replacement-root
variable case-number
variable replacement-number

: named ( addr len -- ) 0 -rot lf-name-str 0= if -1 throw then drop ;
: set-actual ( level -- ) dup actual ! lf-level-identity 0= if -1 throw then actual cell+ ! ;
: make-constant ( name level -- )
  set-actual lf-name-generation @ actual 1 lf-cref-new 0= if -1 throw then
  lf-cterm-new 0= if -1 throw then 2drop ;
: make-sort ( level -- )
  dup lf-level-identity 0= if -1 throw then lf-hterm-sort 0= if -1 throw then 2drop ;

\ Nodes 0..6: constants c.{u}, d.{0}, sorts 0/u, variables #0/#1/#2.
: build-base ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  s" c" named s" d" named s" u" named
  3 lf-lscope-context-add 0= if -1 throw then
  lf-ssession-begin 0= if -1 throw then
  3 lf-hlevel-param 0= if -1 throw then 2drop
  1 1 make-constant 2 0 make-constant 0 make-sort 1 make-sort
  3 0 do i lf-term-bvar 0= if -1 throw then drop loop ;
: make-app ( a b -- node ) lf-term-app 0= if -1 throw then ;
: make-lam ( a b -- node ) lf-term-lam 0= if -1 throw then ;
: make-pi ( a b -- node ) lf-term-pi 0= if -1 throw then ;
: build-source ( n -- node )
  case
    0 of 0 endof
    1 of 0 4 make-app endof
    2 of 0 5 make-app 4 swap make-app 1 swap make-lam endof
    3 of 1 4 make-app 5 0 make-app make-pi endof
    4 of 5 1 make-app 6 swap make-app 0 swap make-lam 3 swap make-lam endof
    5 of 4 5 make-app 5 swap make-app 1 swap make-lam 4 swap make-app endof
    -1 throw
  endcase ;
: build-replacement ( n -- node )
  case
    0 of 4 endof
    1 of 1 4 make-app endof
    2 of 0 endof
    3 of 3 endof
    4 of 0 5 make-app 4 swap make-app 2 swap make-lam endof
    -1 throw
  endcase ;

\ The fixture intentionally has distinct constant references and Sort levels.
: emit-term ( node -- )
  lf-term-read 0= if -1 throw then rot case
    lf-tag-symbolic-sort of drop case 0 of s" S " type endof 1 of s" U " type endof -1 throw endcase endof
    lf-tag-constant of drop case 0 of s" C " type endof 1 of s" D " type endof -1 throw endcase endof
    lf-tag-bvar of drop s" V " type . endof
    lf-tag-app of s" A " type swap recurse recurse endof
    lf-tag-lam of s" L " type swap recurse recurse endof
    lf-tag-pi of s" P " type swap recurse recurse endof
    -1 throw
  endcase ;
: handle ( node -- node identity ) dup lf-term-identity 0= if -1 throw then ;
: emit-table ( -- )
  6 0 do i case-number !
    5 0 do i replacement-number !
      build-base case-number @ build-source source-root !
      replacement-number @ build-replacement replacement-root !
      case-number @ . replacement-number @ .
      source-root @ handle replacement-root @ handle 10000 lf-mixed-instantiate
      lf-minst-ok <> if 2drop -1 throw then
      2dup 10000 lf-cterm-check lf-repr-ok <> if 2drop -1 throw then
      drop emit-term cr
    loop
  loop ;
emit-table bye
