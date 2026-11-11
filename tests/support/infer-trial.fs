\ The harness of the typed-term trial (tests/core/infer_typed_trial.py;
\ plan task 4.2.2a, review rvD2A F1): the cases the generator writes run
\ here, one case per line, and print one line per run: kind, case,
\ outcome, diagnostic code, the D-rule mask (codes 59 and 60, else 0) and,
\ for an inference that is ok, its type in a canonical prefix form. Kinds:
\ I the term's inference; DI and TI the definition and theorem probe on
\ (inferred type, term); DB on (fun (X : Sort 2) => X) T, a redex of the
\ inferred type; DR on (a fixed claim, term). Two constants are in the
\ signature index: id.{u} : (A : Sort u) -> A -> A and k : Type. MODE 0
\ gives ample fuel and room; 1 a random fuel below 3,000 per run; 2 a term
\ store of the case's input plus up to 120. Test-only: nothing here
\ accepts a theorem outside the code under test.
require ../../src/main.fs
include ./plain-terms.fs
decimal

variable tok  variable case#  variable mode  variable seed2
create formals 1 cells allot
create pairs 2 cells allot
: step2 ( -- u ) seed2 @ 1103515245 * 12345 + 2147483647 and dup seed2 ! 16 rshift ;
: rnd2 ( n -- u ) step2 swap mod ;
: intern ( c-addr u -- id ) 0 -rot lf-name-str must ;
\ id : (A : Sort u) -> A -> A, k : Type.
: id-sig ( -- node ) level-u make-sort 0 make-var 1 make-var make-pi make-pi ;
: signatures ( -- )
  empty-token tok ! u-name formals !
  tok @ s" id" intern id-sig handle formals 1 50000 lf-msp-put ok? must
  tok @ s" k" intern 1 make-sort handle formals 0 50000 lf-msp-put ok? must ;
: constant-node ( name count -- node )
  >r lf-name-generation @ pairs r> lf-cref-new must lf-cterm-new must drop ;
\ id at a level (an index of fresh-session's levels).
: idl ( level -- node )
  dup lf-level-identity must swap pairs 2! s" id" intern 1 constant-node ;

\ Canonical printing: levels structurally, constants by name and levels;
\ a free variable would print as ?tag.
: .n ( n -- ) 0 .r space ;
: .level ( level -- )
  lf-level-read must rot case
    lf-level-tag-zero of 2drop ." z " endof
    lf-level-tag-succ of drop ." s " recurse endof
    lf-level-tag-max of ." m " swap recurse recurse endof
    lf-level-tag-imax of ." i " swap recurse recurse endof
    lf-level-tag-param of drop ." p " .n endof
    ." ?level " nip nip endcase ;
: .levels ( cref identity count -- )
  0 ?do 2dup i lf-cref-level must drop .level loop 2drop ;
: .constant ( cref identity -- )
  2dup lf-cref-read must >r drop ." C " .n r@ .n r> .levels ;
: .term ( node -- )
  dup lf-term-read 0= if ." ?node " drop exit then rot case
    lf-tag-symbolic-sort of drop nip ." S " .level endof
    lf-tag-bvar of drop nip ." V " .n endof
    lf-tag-constant of rot drop lf-cterm-pair .constant endof
    lf-tag-app of ." A " rot drop swap recurse recurse endof
    lf-tag-lam of ." L " rot drop swap recurse recurse endof
    lf-tag-pi of ." P " rot drop swap recurse recurse endof
    ." ?tag " dup .n >r 2drop drop r> endcase ;

\ Resources by mode, from a generator seeded per case.
1000000 constant ample
: fuel ( -- n ) mode @ 1 = if 3000 rnd2 else ample then ;
: room ( -- )
  mode @ 2 = if lf-term-count @ 120 rnd2 + else 100000 then lf-term-capacity! drop ;
: mask ( code n1 -- mask ) over dup 59 = swap 60 = or and nip ;
: .diag ( -- ) lf-diag@ nip nip tuck swap mask swap .n .n ;
: .head ( c-addr u -- ) type space case# @ .n ;

variable term  variable inferred  variable value  variable claim
: infer ( -- type status ) tok @ term @ handle fuel lf-mixed-infer nip ;
: .inferred ( type status -- )
  s" I" .head dup .n .diag dup ok? if drop dup inferred ! .term else 2drop then cr ;
: run-probe ( claim theorem? -- status )
  >r lf-diag-clear tok @ swap handle value @ handle fuel
  r> if lf-mixed-theorem-probe else lf-mixed-definition-probe then ;
: probe-line ( claim theorem? c-addr u -- ) 2>r run-probe 2r> .head .n .diag cr ;
: redex-of ( type -- node ) 2 make-sort 0 make-var make-lam swap make-app ;
\ A redex that does not fit a small store (mode 2) is a full run.
: redex-probe ( -- )
  inferred @ ['] redex-of catch
  if drop s" DB" .head outcome-full .n 0 .n 0 .n cr exit then false s" DB" probe-line ;
: inferred-probes ( -- )
  inferred @ 0< if exit then
  inferred @ false s" DI" probe-line inferred @ true s" TI" probe-line redex-probe ;

\ A case: a fresh session and index, built by the generated line; then
\ the inference and the probes. A probe that does not fit a small store
\ (mode 2) ends the inferred-type probes.
: begin-case ( n -- )
  case# ! case# @ 7919 * 17 + seed2 ! 100000 lf-term-capacity! drop
  fresh-session signatures -1 inferred ! ;
: run-case ( term claim -- )
  claim ! term ! room lf-diag-clear infer .inferred term @ value !
  ['] inferred-probes catch drop term @ value ! claim @ false s" DR" probe-line ;
