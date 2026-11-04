\ Run mode for v1-demo.fs: gforth v1-demo.fs v1-run.fs. Each line checks
\ one call: the expected value, then the call, which must leave it.
decimal
variable checks  variable failures
: is? ( want got -- ) 1 checks +! <> if 1 failures +! then ;
10 5 sum-below is?
9 pairs is?
8 100 first-big is?
0 5 count-down is?
120 5 fact is?
7 seven is?
0 total ! add-seven 7 total @ is?
9 3 square is?
.( run mode, v1 demo: ) checks @ . .( calls checked, ) failures @ . .( failures) cr
depth 0<> [if] .( stack not empty) cr [then]
bye
