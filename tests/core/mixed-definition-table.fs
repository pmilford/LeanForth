\ lf-mixed-definition-probe on the nine pairs of
\ tests/reference/definition-table.lean. Rows are "section index status".
\ Section 0: five closed pairs with an empty signature index. Section 1:
\ four pairs over universe u whose values use the candidate signature of id
\ (an assumption, not a checked declaration) or an unknown constant. The
\ probe checks definitions: a claim in any Sort is allowed (owner question
\ O1 in the coverage report), so it is compared with Lean's definition
\ outcome. Status 0 is an untrusted diagnostic, never theorem acceptance.
include ../../src/main.fs
include ../support/plain-terms.fs
create formals 1 cells allot
create actuals 2 cells allot

\ Pi _ : domain => Pi _ : #0 => #1, and fun _ : domain => fun _ : #0 => #i.
: target-on ( domain -- node ) 0 make-var 1 make-var make-pi make-pi ;
: identity-on ( domain i -- node ) >r 0 make-var r> make-var make-lam make-lam ;
: beta-prop ( -- node ) 1 make-sort 0 make-var make-lam 0 make-sort make-app ;
: closed-pair ( n -- claim value )
  case
    0 of 0 make-sort target-on 0 make-sort 0 identity-on endof
    1 of 0 make-sort target-on 0 make-sort 1 identity-on endof
    2 of 0 make-sort 0 identity-on dup endof
    3 of 1 make-sort 0 make-sort endof
    4 of beta-prop target-on 0 make-sort 0 identity-on endof
    -1 throw
  endcase ;

\ Section 1: the signature index holds id : Pi (A : Sort u), A -> A.
: intern ( addr len -- id ) 0 -rot lf-name-str must ;
: constant-at-u ( addr len -- node )
  intern lf-name-generation @ actuals 1 lf-cref-new must lf-cterm-new must drop ;
: stage-id ( token -- )
  s" id" intern level-u make-sort target-on handle formals 1 50000 lf-msp-put ok? must ;
\ fun A : Sort u => fun x : A => head A #last
: body-with ( last addr len -- node )
  constant-at-u 1 make-var make-app swap make-var make-app
  0 make-var swap make-lam level-u make-sort swap make-lam ;
: polymorphic-pair ( n -- claim value )
  case
    0 of level-u make-sort target-on 0 s" id" body-with endof
    1 of level-u make-sort target-on 1 s" id" body-with endof
    2 of
      level-u make-sort 0 make-var level-u make-sort make-pi make-pi
      0 s" id" body-with
    endof
    3 of level-u make-sort target-on 0 s" missing" body-with endof
    -1 throw
  endcase ;
: polymorphic-setup ( -- token )
  u-name formals ! level-u actuals ! level-u lf-level-identity must actuals cell+ !
  empty-token dup stage-id ;

: probe ( token claim value -- status )
  >r handle r> handle 50000 lf-mixed-definition-probe ;
: emit-closed ( n -- )
  ." 0 " dup . fresh-session closed-pair >r >r empty-token r> r> probe . cr ;
: emit-polymorphic ( n -- )
  ." 1 " dup . fresh-session polymorphic-setup swap polymorphic-pair probe . cr ;
: emit-definition-table ( -- )
  5 0 do i emit-closed loop  4 0 do i emit-polymorphic loop ;
emit-definition-table
bye
