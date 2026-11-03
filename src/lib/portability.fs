\ Portability adapter: Forth-2012 definitions of the few words the project
\ uses that are not in the Forth-2012 core word set, plus the standard
\ structure words. Each is compiled only when the host lacks it; under Gforth
\ 1.0 this file defines only max-n. No state, no dependencies.
\ Host assumption: cells are two's complement and arithmetic wraps, as on
\ every current host (Forth-2012 itself does not require it). upto? and
\ max-n rely on this.

\ Comparisons and stack words that Gforth provides as extensions.
[undefined] >= [if] : >= ( n1 n2 -- flag ) < 0= ; [then]
[undefined] <= [if] : <= ( n1 n2 -- flag ) > 0= ; [then]
[undefined] 0<= [if] : 0<= ( n -- flag ) 0> 0= ; [then]
[undefined] 0>= [if] : 0>= ( n -- flag ) 0< 0= ; [then]
[undefined] -rot [if] : -rot ( x1 x2 x3 -- x3 x1 x2 ) rot rot ; [then]

\ Largest positive cell value, and the size of a cell in address units
\ (Gforth 0.7.3 and 1.0 define cell; Forth-2012 does not).
[undefined] max-n [if] -1 1 rshift constant max-n [then]
[undefined] cell [if] 1 cells constant cell [then]

\ Forth-2012 structures (FACILITY EXT), from the standard's reference code;
\ each guarded separately, so a host with only some of them keeps its own.
[undefined] begin-structure [if]
: begin-structure ( "name" -- addr 0 ) create here 0 0 , does> @ ; [then]
[undefined] end-structure [if] : end-structure ( addr n -- ) swap ! ; [then]
[undefined] +field [if] : +field ( n1 n2 "name" -- n3 ) create over , + does> @ + ; [then]
[undefined] field: [if] : field: ( n1 "name" -- n2 ) aligned 1 cells +field ; [then]
