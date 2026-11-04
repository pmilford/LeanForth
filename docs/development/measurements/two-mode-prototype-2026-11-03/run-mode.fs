\ Run mode: the same two source files, unchanged, loaded by plain Forth
\ before this file (gforth src/program/clamp.fs src/program/examples.fs
\ run-mode.fs), then run. Each line checks one call: the inputs, the word,
\ and the stack it must leave.
decimal
variable checks  variable failures
create want 8 cells allot  variable want#
: wanted ( i*x n -- ) dup want# ! 0 ?do want want# @ 1- i - cells + ! loop ;
: ran ( j*x n -- )
  1 checks +! dup want# @ <> if 1 failures +! 0 ?do drop loop exit then
  0 ?do want want# @ 1- i - cells + @ <> if 1 failures +! then loop ;
\ value lower upper lf-clamp
5 -1 2 wanted   5 0 10 lf-clamp 2 ran
0 -1 2 wanted   -5 0 10 lf-clamp 2 ran
10 -1 2 wanted   15 0 10 lf-clamp 2 ran
0 1 wanted   5 10 0 lf-clamp 1 ran
\ a b lf-checked-add
7 -1 2 wanted   3 4 lf-checked-add 2 ran
0 1 wanted   lf-example-max 1 lf-checked-add 1 ran
0 1 wanted   lf-example-min -1 lf-checked-add 1 ran
\ n lf-checked-abs
5 -1 2 wanted   -5 lf-checked-abs 2 ran
0 1 wanted   lf-example-min lf-checked-abs 1 ran
\ n lf-factorial
120 -1 2 wanted   5 lf-factorial 2 ran
1 -1 2 wanted   0 lf-factorial 2 ran
0 1 wanted   -1 lf-factorial 1 ran
0 1 wanted   100 lf-factorial 1 ran
\ a b lf-gcd
6 -1 2 wanted   12 18 lf-gcd 2 ran
0 -1 2 wanted   0 0 lf-gcd 2 ran
0 1 wanted   -4 6 lf-gcd 1 ran
\ value lower upper lf-in-range
-1 -1 2 wanted   5 0 10 lf-in-range 2 ran
0 -1 2 wanted   11 0 10 lf-in-range 2 ran
0 1 wanted   5 10 0 lf-in-range 1 ran
.( run mode: ) checks @ . .( calls checked, ) failures @ . .( failures) cr
depth 0<> [if] .( stack not empty) cr [then]
bye
