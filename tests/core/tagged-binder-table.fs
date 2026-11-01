\ Differential fixture only: inferred syntax is not a theorem certificate.
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs
include ../../src/experimental/tagged-compare.fs
include ../../src/experimental/tagged-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/tagged-convert.fs
include ../../src/experimental/tagged-infer.fs
decimal
variable assignment
: node ( index identity true | false -- index ) 0= abort" allocation" drop ;
: handle ( index -- index identity ) dup lf-term-identity 0= abort" identity" ;
: lam ( domain body -- index ) handle rot handle 2swap lf-hterm-lam node ;
: pi-node ( domain body -- index ) handle rot handle 2swap lf-hterm-pi node ;
: var-node ( index -- node ) lf-hterm-bvar node ;
\ All cases use Sort u (node 0), bvar 0 (node 1), bvar 1 (node 2).
: fixture ( case -- root )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  42 lf-lscope-context-add 0= abort" context"
  42 lf-hlevel-param 0= abort" parameter"
  lf-ssession-begin 0= abort" session"
  lf-hterm-sort node drop 0 var-node drop 1 var-node drop
  case
    0 of 1 1 lam 0 swap lam endof
    1 of 2 2 lam 1 swap lam 0 swap lam endof
    2 of 1 2 pi-node 0 swap pi-node endof
    3 of 1 2 pi-node 2 2 lam lam 0 swap lam endof
    4 of 1 endof
    5 of 0 2 lam endof
    -1 throw
  endcase ;
\ Evaluate a level graph at u = assignment; constructors have backward edges.
: level-value ( index -- n )
  lf-level-read 0= abort" bad level"
  rot case
    lf-level-tag-zero of 2drop 0 endof
    lf-level-tag-param of drop 42 <> abort" unexpected parameter" assignment @ endof
    lf-level-tag-succ of drop recurse 1+ endof
    lf-level-tag-max of >r recurse r> recurse max endof
    lf-level-tag-imax of >r recurse r> recurse dup 0= if nip else max then endof
    -1 throw
  endcase ;
\ Prefix syntax: S level, V index, P domain body, L domain body, A fn arg.
: emit-term ( index -- )
  lf-term-read 0= abort" bad term"
  rot case
    lf-tag-symbolic-sort of drop ." S " level-value . endof
    lf-tag-bvar of drop ." V " . endof
    lf-tag-pi of ." P " >r recurse r> recurse endof
    lf-tag-lam of ." L " >r recurse r> recurse endof
    lf-tag-app of ." A " >r recurse r> recurse endof
    -1 throw
  endcase ;
: emit-binder-table ( -- )
  3 0 do i assignment !
    6 0 do
      assignment @ . i . i fixture handle 10000 lf-tinfer
      i 4 < if
        lf-tinfer-ok <> abort" positive inference failed"
        drop ." OK " emit-term cr
      else
        \ These cases are specifically unbound and must report invalid.
        lf-tinfer-invalid <> abort" expected invalid unbound variable"
        0<> abort" negative identity" -1 <> abort" negative index"
        ." REJECT " cr
      then
    loop
  loop ;
emit-binder-table
bye
