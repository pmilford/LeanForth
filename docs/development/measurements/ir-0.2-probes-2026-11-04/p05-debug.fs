\ IR 0.2 probe 5 (ADR 0019 Amendment 1): the owner's debugging case in
\ plain Gforth. First lf-clamp with a `dup .` added; then the real clamp
\ wrapped by a second version of its name that shows the stack before
\ and after calling the first ("nested names"). Each call's output is
\ shown between < and >, then the stack it leaves. Run from this folder:
\   timeout -k 5 30 gforth p05-debug.fs </dev/null
' . constant dot-xt
: show ( n -- ) dot-xt execute ;
: label ( c-addr u -- ) cr type ." : " ;
: <| ( -- ) [char] < emit ;
: |> ( -- ) [char] > emit ;
: stack2 ( a b -- ) swap show show ;

\ 1. `dup .` inside the definition prints max(value, lower) on the path
\ where lower <= upper, and leaves the stack as the clamp without it.
: debug-clamp ( value lower upper -- result true | false )
  2dup > if 2drop drop false exit then
  >r max dup . r> min true ;
s" 5 0 10 debug-clamp (expect <5 > 5 -1)" label <| 5 0 10 debug-clamp |> stack2
s" 15 0 10 debug-clamp (expect <15 > 10 -1)" label <| 15 0 10 debug-clamp |> stack2
s" 5 10 0 debug-clamp (expect <> 0, depth 0 after)" label <| 5 10 0 debug-clamp |> show depth show

\ 2. The real lf-clamp, then a second lf-clamp that calls the first with
\ .S before and after: early binding nests the names.
include ../../../../src/program/clamp.fs
: lf-clamp ( value lower upper -- result true | false ) .s lf-clamp .s ;
s" 5 0 10 lf-clamp, second version (expect <<3> 5 0 10 <2> 5 -1 > 5 -1)" label
<| 5 0 10 lf-clamp |> stack2
cr bye
