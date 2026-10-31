\ Finite differential fixture for untrusted tagged weak-head reduction.
\ Prefix output is a test representation, not a proof certificate.
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs
include ../../src/experimental/tagged-beta.fs
decimal
variable chain-input
variable chain-identity
variable source-count

: node ( index identity true | false -- index ) 0= abort" allocation" drop ;
: handle ( index -- index identity ) dup lf-term-identity 0= abort" identity" ;
: var-node ( index -- node ) lf-hterm-bvar node ;
: app-node ( fn arg -- node ) handle rot handle 2swap lf-hterm-app node ;
: lam-node ( domain body -- node ) handle rot handle 2swap lf-hterm-lam node ;
: pi-node ( domain body -- node ) handle rot handle 2swap lf-hterm-pi node ;
\ Construct each Sort through the handle API, stamping its live level identity.
: sort-node ( level -- node )
  lf-hlevel-zero 0= abort" level zero"
  rot 0 ?do lf-hlevel-succ 0= abort" level successor" loop
  lf-hterm-sort node ;
: reset-case ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  lf-ssession-begin 0= abort" session" ;

\ Rebuild the six explicit expressions from tests/reference/beta-table.lean.
: build-case ( number -- root )
  reset-case
  case
    0 of 0 sort-node endof
    1 of 0 sort-node drop 0 var-node drop 0 1 pi-node endof
    2 of 0 sort-node drop 1 sort-node drop 0 var-node drop
      1 2 lam-node drop 3 0 app-node endof
    3 of 0 sort-node drop 1 sort-node drop 0 var-node drop
      2 2 lam-node drop 1 3 lam-node drop 4 0 app-node endof
    4 of 0 sort-node drop 1 sort-node drop 2 sort-node drop 0 var-node drop
      3 3 lam-node drop 2 4 lam-node drop 5 1 app-node drop 6 0 app-node endof
    5 of 1 sort-node drop 0 var-node drop 0 1 lam-node drop
      2 1 app-node drop 0 3 lam-node endof
    -1 throw
  endcase ;

\ These fixtures contain only concrete successor levels; reject any other form.
: level-value ( index -- n )
  lf-level-read 0= abort" level read"
  rot case
    lf-level-tag-zero of 2drop 0 endof
    lf-level-tag-succ of drop recurse 1+ endof
    -1 throw
  endcase ;
\ Render the actual result tree. Every reachable Sort must be an original
\ stamped input node; lf-hterm-check below also audits its level stamp.
: emit-term ( index -- )
  dup lf-term-read 0= abort" term read"
  rot case
    lf-tag-symbolic-sort of
      >r >r source-count @ >= abort" reconstructed Sort"
      r> r> drop ." S " level-value . endof
    lf-tag-bvar of rot drop drop ." V " . endof
    lf-tag-pi of rot drop ." P " >r recurse r> recurse endof
    lf-tag-lam of rot drop ." L " >r recurse r> recurse endof
    lf-tag-app of rot drop ." A " >r recurse r> recurse endof
    -1 throw
  endcase ;
: reduce-and-emit ( root -- )
  lf-term-count @ source-count !
  handle 100000 lf-tagged-beta lf-tbeta-ok <> abort" reduction failed"
  2dup 100000 lf-hterm-check lf-repr-ok <> abort" invalid result handle"
  drop emit-term cr ;
: emit-table ( -- )
  6 0 do i . i build-case reduce-and-emit loop
  3 0 do
    3 0 do
      6 j 3 * + i + . reset-case
      j sort-node chain-input !
      j 1+ sort-node 0 var-node lam-node chain-identity !
      i 1+ 0 do chain-identity @ chain-input @ app-node chain-input ! loop
      chain-input @ reduce-and-emit
    loop
  loop ;
emit-table
bye
