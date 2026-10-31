\ Executable host-cell clamp for the program track. This ordinary Forth word
\ is tested but not formally verified. The Lean integer proof is not connected
\ to this implementation; host execution and integer representation are
\ assumptions, and the function accepts only values representable in one cell.

\ Clamp a signed cell to inclusive ordered bounds. Return the result and true;
\ for reversed bounds consume all inputs and return false without a result.
\ MIN and MAX use host signed-cell comparisons and perform no arithmetic.
: lf-clamp ( value lower upper -- result true | false )
  2dup > if 2drop drop false exit then
  >r max r> min true ;
