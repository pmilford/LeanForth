\ lf-mixed-convert on the 15 cases of tests/reference/convert-table.lean:
\ closed beta comparisons (section 0), nested binder capture (section 1) and
\ symbolic universes (section 2). Each row is "section index status" with
\ the conversion status (0 equal, 3 unknown); the differential driver maps
\ it onto Lean's flag. Equality here is not a theorem judgment.
require ../../src/load/kernel.fs
include ../support/plain-terms.fs

\ fun _ : domain => body
: lam-of ( domain body -- node ) make-lam ;
\ (fun _ : Sort 1 => #0) Sort 0, which reduces to Sort 0.
: beta-prop ( -- node ) 1 make-sort 0 make-var make-lam 0 make-sort make-app ;
\ fun P : Sort 0 => fun x : P => x
: prop-identity ( -- node ) 0 make-sort 0 make-var 0 make-var make-lam make-lam ;
: closed-pair ( n -- left right )
  case
    0 of 0 make-sort 0 make-sort endof
    1 of 0 make-sort 1 make-sort endof
    2 of beta-prop 0 make-sort endof
    3 of prop-identity prop-identity endof
    4 of 0 make-sort prop-identity endof
    5 of 0 make-sort 0 make-var make-lam beta-prop 0 make-var make-lam endof
    -1 throw
  endcase ;
\ fun _ : Sort 0 => (fun _ : Sort 0 => fun _ : Sort 0 => #1) #0, against
\ fun _ fun _ => #1 (equal) and fun _ fun _ => #0 (not equal).
: two-lambdas ( index -- node ) >r 0 make-sort 0 make-sort r> make-var make-lam make-lam ;
: capture-left ( -- node )
  0 make-sort 0 make-sort 0 make-sort 1 make-var make-lam make-lam
  0 make-var make-app make-lam ;
: capture-pair ( n -- left right ) capture-left swap 0= if 1 else 0 then two-lambdas ;
\ Levels for the universe section, by case: left and right level indices.
: max-level ( a b -- level ) lf-level-max must ;
: imax-level ( a b -- level ) lf-level-imax must ;
: universe-levels ( n -- left right )
  case
    0 of level-u level-u 0 max-level endof
    1 of level-u 0 imax-level 0 endof
    2 of level-u level-v endof
    3 of 0 1 endof
    4 of level-u 0 max-level lf-level-succ must level-u lf-level-succ must endof
    5 of 0 level-u imax-level 0 endof
    6 of level-u level-v max-level level-v level-u max-level endof
    -1 throw
  endcase ;
: universe-pair ( n -- left right ) universe-levels >r make-sort r> make-sort ;
: pair ( section n -- left right )
  fresh-session swap case
    0 of closed-pair endof
    1 of capture-pair endof
    2 of universe-pair endof
    -1 throw
  endcase ;
: emit-pair ( section n -- )
  over . dup . pair >r handle r> handle 20000 lf-mixed-convert . cr ;
: emit-convert-table ( -- )
  6 0 do 0 i emit-pair loop  2 0 do 1 i emit-pair loop  7 0 do 2 i emit-pair loop ;
emit-convert-table
bye
