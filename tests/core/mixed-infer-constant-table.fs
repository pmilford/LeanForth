\ A constant c with universe parameters u, v and a candidate signature (an
\ assumption, not a checked declaration) whose type is the term of
\ tests/reference/term-level-substitute-table.lean. For each of the three
\ argument lists, the specialized type is printed at u, v = 0..3, twice:
\ section S through lf-msp-specialize, section T as the type that
\ lf-mixed-infer gives the constant term c.{a0, a1}. 96 rows; the driver
\ strips the section letter and compares each section with the 48 Lean rows.
require ../../src/main.fs
decimal
create formals 2 cells allot
create actuals 4 cells allot
variable result-root
variable token

: must ( flag -- ) 0= if -1 throw then ;
: stamped-sort ( level -- term ) dup lf-level-identity must lf-hterm-sort must drop ;
: save-actual ( level position -- )
  2* cells actuals + >r dup r@ ! lf-level-identity must r> cell+ ! ;
: c-name ( -- name ) 0 s" c" lf-name-str must ;

\ Signature type: Pi (Sort (max u (succ v))) (fun (Sort u) => #0 (Sort (imax v u))),
\ node 6. Level parameters u and v have the name IDs 1 and 2.
: build-signature ( case -- )
  lf-name-reset lf-term-reset lf-level-reset lf-lscope-context-reset lf-cref-reset
  c-name drop
  1 lf-lscope-context-add must 2 lf-lscope-context-add must
  lf-ssession-begin must
  1 lf-level-param must drop 2 lf-level-param must drop
  2 lf-level-succ must drop 1 2 lf-level-max must drop
  1 lf-level-succ must drop 1 3 lf-level-max must drop 2 1 lf-level-imax must drop
  6 stamped-sort drop 1 stamped-sort drop 0 lf-term-bvar must drop 7 stamped-sort drop
  2 3 lf-term-app must drop 1 4 lf-term-lam must drop 0 5 lf-term-pi must drop
  1 formals ! 2 formals cell+ !
  case
    0 of 2 0 save-actual 1 1 save-actual endof
    1 of 3 0 save-actual 4 1 save-actual endof
    2 of 2 0 save-actual 5 1 save-actual endof
    -1 throw
  endcase
  lf-msp-begin must lf-msp-token must dup token !
  c-name 6 dup lf-term-identity must formals 2 50000 lf-msp-put ok? must ;
: specialized ( -- root )
  token @ c-name actuals 2 50000 lf-msp-specialize ok? must drop ;
: inferred ( -- root )
  c-name lf-name-generation @ actuals 2 lf-cref-new must lf-cterm-new must
  token @ -rot 50000 lf-mixed-infer ok? must drop ;

\ Prefix term tags, evaluating each symbolic Sort in the current assignment.
: emit-term ( term -- )
  lf-term-read must rot case
    lf-tag-symbolic-sort of
      drop 1 . 50000 lf-level-value-assigned ok? must .
    endof
    lf-tag-bvar of drop 2 . . endof
    lf-tag-app of 3 . swap recurse recurse endof
    lf-tag-lam of 4 . swap recurse recurse endof
    lf-tag-pi of 5 . swap recurse recurse endof
    -1 throw
  endcase ;
: emit-grid ( letter case -- )
  4 0 do 4 0 do
    lf-lassign-reset 1 j lf-lassign-add must 2 i lf-lassign-add must
    over emit space dup . j . i . result-root @ emit-term cr
  loop loop 2drop ;
: emit-table ( xt letter -- )
  3 0 do i build-signature over execute result-root ! dup i emit-grid loop 2drop ;
' specialized char S emit-table
' inferred char T emit-table
bye
