\ Portability adapter: Forth-2012 definitions of the few words the project
\ uses that are not in the Forth-2012 core word set (-ROT, BOUNDS, .S ...),
\ plus the standard structure words and the standard streams. Each is
\ compiled only when the host lacks it; under Gforth 1.0 this file
\ defines only max-n. No state, no dependencies but the streams' (below).
\ Host assumption: cells are two's complement and arithmetic wraps, as on
\ every current host (Forth-2012 itself does not require it). upto? and
\ max-n rely on this. tests/lib/lib.fs checks each one-line fallback
\ against the host's own word.

\ Comparisons and stack words that Gforth provides as extensions.
[undefined] >= [if] : >= ( n1 n2 -- flag ) < 0= ; [then]
[undefined] <= [if] : <= ( n1 n2 -- flag ) > 0= ; [then]
[undefined] u<= [if] : u<= ( u1 u2 -- flag ) u> 0= ; [then]
[undefined] 0<= [if] : 0<= ( n -- flag ) 0> 0= ; [then]
[undefined] 0>= [if] : 0>= ( n -- flag ) 0< 0= ; [then]
[undefined] -rot [if] : -rot ( x1 x2 x3 -- x3 x1 x2 ) rot rot ; [then]
\ A range for ?DO: the end and the start of u address units from addr.
[undefined] bounds [if] : bounds ( addr u -- addr+u addr ) over + swap ; [then]

\ The standard output and error streams' file ids, which both Gforths
\ name and Forth-2012 does not: elsewhere the POSIX device files, opened
\ when this file loads (a host without them stops here with a THROW).
\ FLUSH-FILE is of the optional File-Access extension: a host without it
\ is taken to write through, with nothing left to flush.
[undefined] stdout [if] s" /dev/stdout" w/o open-file throw constant stdout [then]
[undefined] stderr [if] s" /dev/stderr" w/o open-file throw constant stderr [then]
[undefined] flush-file [if] : flush-file ( fileid -- ior ) drop 0 ; [then]

\ SYNONYM (Forth-2012 TOOLS EXT; Gforth 1.0 has it, 0.7.3 not): where the
\ host lacks it, new becomes a colon definition that calls old, which is
\ right for ordinary words only: never name an immediate or parsing word
\ (new would not be immediate). The fallback cannot refuse one: telling
\ an immediate word apart needs FIND, a name lookup that src/lib may not
\ use (tests/core/check_log_isolation.py, N7). Its one use is
\ src/lib/u32.fs's synonym u32@ l@ and u32! l!, ordinary words.
[undefined] synonym [if]
: synonym ( "new" "old" -- ) : ' compile, postpone ; ;
[then]

\ .S, of the optional Programming-Tools word set, which the program words
\ (src/program/verify-semantics.fs) give verification semantics: the depth
\ in angle brackets, then the top nine cells at most, deepest first, each
\ as . prints it, as both Gforths print them (tests/program/verify_ir02.py
\ compares this text with the host's own .S).
[undefined] .s [if]
: .s ( -- ) ." <" depth 0 .r ." > " depth 9 min dup 0 ?do dup i - pick . loop drop ;
[then]

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
