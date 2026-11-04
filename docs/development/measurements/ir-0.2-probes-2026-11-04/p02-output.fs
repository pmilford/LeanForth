\ IR 0.2 probe 2 (ADR 0019 Amendment 1): what the output words print in
\ plain Gforth, each output between < and >, and what they do to the
\ stacks. Run from this folder:
\   timeout -k 5 30 gforth p02-output.fs </dev/null
: label ( c-addr u -- ) cr type ." : " ;
: <| ( -- ) [char] < emit ;
: |> ( -- ) [char] > emit ;

\ . and U. with BASE ten: the number, then one space.
s" 5 . -5 . 0 ." label <| 5 . |> <| -5 . |> <| 0 . |>
s" largest and smallest cell ." label <| -1 1 rshift . |> <| -1 1 rshift invert . |>
s" -1 U. and 5 U." label <| -1 u. |> <| 5 u. |>
\ The same words run with BASE sixteen print in that base.
s" 255 . and -1 U. with BASE 16" label <| hex 255 . -1 u. decimal |>

\ CR, SPACE and SPACES; SPACES with zero and a negative count.
s" CR" label <| cr |>
s" SPACE, 3 SPACES, 0 SPACES, -2 SPACES" label
<| space |> <| 3 spaces |> <| 0 spaces |> <| -2 spaces |>

\ ." and S" ... TYPE inside a definition; the text after one space.
: hello ( -- ) ." hi there" ;
: two-spaces ( -- ) ."   two" ;
: typed ( -- ) s" typed text" type ;
s" .\q, a leading space kept, S\q TYPE" label <| hello |> <| two-spaces |> <| typed |>

\ .S shows the whole stack without changing it; its format is the host's.
s" .S with 0 and 3 cells" label <| .s |> <| 1 2 3 .s |> 2drop drop
s" .S with 12 cells" label
<| 1 2 3 4 5 6 7 8 9 10 11 12 .s |> 2drop 2drop 2drop 2drop 2drop 2drop
s" depth after the .S lines (expect 0)" label depth .

\ Each output word takes exactly its argument: cells below stay.
: tidy ( a b -- a ) . ;
s" 7 8 tidy leaves 7 (depth 1)" label <| 7 8 tidy |> depth . .

\ . uses the pictured-numeric buffer: a string from #> before it may be
\ overwritten.
: pictured ( -- c-addr u ) 12345 0 <# #s #> ;
s" a #> string, then 7 ., then the string again" label
pictured 2dup <| type |> <| 7 . |> <| type |>

\ .( inside a definition prints while the definition is compiled.
s" .( inside a definition: printed when compiled, not when run" label
: dotparen ( -- ) .( [compiled] ) ;
<| dotparen |>
cr bye
