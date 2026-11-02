\ Finite observations against Lean; unknown does not mean inequality.
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
include ../../src/experimental/mixed-beta.fs
include ../../src/experimental/mixed-compare.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/mixed-convert.fs
decimal
: named ( addr len -- ) 0 -rot lf-name-str 0= if -1 throw then drop ;
: make-constant ( name -- )
  lf-name-generation @ 0 0 lf-cref-new 0= if -1 throw then
  lf-cterm-new 0= if -1 throw then 2drop ;
: make-sort ( level -- )
  dup lf-level-identity 0= if -1 throw then lf-hterm-sort 0= if -1 throw then 2drop ;
: make-app ( a b -- ) lf-term-app 0= if -1 throw then drop ;
: make-lam ( a b -- ) lf-term-lam 0= if -1 throw then drop ;
: make-pi ( a b -- ) lf-term-pi 0= if -1 throw then drop ;
: handle ( node -- node identity ) dup lf-term-identity 0= if -1 throw then ;
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  s" c" named s" d" named s" f" named
  lf-ssession-begin 0= if -1 throw then
  0 dup lf-level-identity 0= if -1 throw then lf-hlevel-succ 0= if -1 throw then 2drop
  1 make-constant 2 make-constant 3 make-constant
  0 make-sort 1 make-sort
  0 lf-term-bvar 0= if -1 throw then drop
  3 5 make-lam 6 0 make-app 6 1 make-app
  7 0 make-pi 0 0 make-pi 0 7 make-lam 0 0 make-lam
  2 7 make-app 2 0 make-app ;
: emit-case ( left right index -- )
  . swap handle rot handle 10000 lf-mixed-convert
  case lf-mconvert-equal of s" E" type endof
       lf-mconvert-unknown of s" U" type endof
       -1 throw endcase cr ;
setup
7 0 0 emit-case
8 0 1 emit-case
9 10 2 emit-case
11 12 3 emit-case
13 14 4 emit-case
0 1 5 emit-case
3 4 6 emit-case
bye
