\ Test-only builders for tables that compare current kernel passes with
\ pinned Lean on small terms without constants. Sorts are symbolic: Sort n
\ (n = 0..4) has the level succ^n zero, which is level index n; the
\ parameters u and v are levels level-u and level-v. Every case starts a
\ fresh session, so its node indices are predictable. Nothing here checks
\ or accepts a theorem. Requires the kernel's entry, src/load/kernel.fs.
decimal
5 constant level-u
6 constant level-v

: must ( flag -- ) 0= if -1 throw then ;
: u-name ( -- name ) 0 s" u" lf-name-str must ;
: v-name ( -- name ) 0 s" v" lf-name-str must ;

\ A fresh session: u and v in the level context, levels succ^1..4 zero at
\ indices 1..4, u at level-u, v at level-v, and an empty assignment table.
: fresh-session ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  u-name lf-lscope-context-add must v-name lf-lscope-context-add must
  4 0 do i lf-level-succ must drop loop
  u-name lf-level-param must drop v-name lf-level-param must drop
  lf-ssession-begin must lf-lassign-reset ;
\ Evaluate u (and v) as given numbers when results are printed.
: assign-u ( n -- ) u-name swap lf-lassign-add must ;
: assign-v ( n -- ) v-name swap lf-lassign-add must ;

\ Node constructors; each fails the test if the store refuses.
: make-sort ( level -- node ) dup lf-level-identity must lf-hterm-sort must drop ;
: make-var ( index -- node ) lf-term-bvar must ;
: make-app ( fn arg -- node ) lf-term-app must ;
: make-lam ( domain body -- node ) lf-term-lam must ;
: make-pi ( domain body -- node ) lf-term-pi must ;
: handle ( node -- node identity ) dup lf-term-identity must ;
\ A fresh signature-index token for inference (no candidate signatures).
: empty-token ( -- token ) lf-msp-begin must lf-msp-token must ;

\ Prefix syntax as the Lean tables print it: S level, V index, A fn arg,
\ L domain body, P domain body. Levels are evaluated, using the assignment
\ table for u and v.
: emit-level ( level -- ) 50000 lf-level-value-assigned ok? must . ;
: emit-term ( node -- )
  lf-term-read must rot case
    lf-tag-symbolic-sort of drop ." S " emit-level endof
    lf-tag-bvar of drop ." V " . endof
    lf-tag-app of ." A " swap recurse recurse endof
    lf-tag-lam of ." L " swap recurse recurse endof
    lf-tag-pi of ." P " swap recurse recurse endof
    -1 throw
  endcase ;
