\ IR 0.2 probe 4 (ADR 0019 Amendment 1): LSHIFT and RSHIFT at the cell's
\ edges; how each host reads Forth-2012's number prefixes and 32-bit
\ constants; and whether the words IR 0.2 would add are host words. Run
\ from this folder:
\   timeout -k 5 30 gforth p04-shifts-literals.fs </dev/null
: label ( c-addr u -- ) cr type ." : " ;
: cell-bits ( -- n ) 0 1 begin ?dup while 1 lshift swap 1+ swap repeat ;
s" cell bits" label cell-bits .

\ Shifts by 0, the cell width less one, the width, more, and -1 (an
\ ambiguous condition in Forth-2012 for counts of the width or more).
s" 1 by 0, 63, 64, 65, 127 and -1 LSHIFT (as U.)" label
1 0 lshift u. 1 63 lshift u. 1 64 lshift u. 1 65 lshift u. 1 127 lshift u. 1 -1 lshift u.
s" -1 by 0, 63, 64, 65 and -1 RSHIFT (as U.)" label
-1 0 rshift u. -1 63 rshift u. -1 64 rshift u. -1 65 rshift u. -1 -1 rshift u.
s" -1 1 LSHIFT and 2^31 1 LSHIFT (as .)" label -1 1 lshift . 65536 dup * 2/ 1 lshift .

\ Number syntaxes: each token EVALUATEd; its value, or the THROW code.
: leave-compiling ( -- ) postpone [ ;
: probe-try ( c-addr u -- i*x code )
  ['] evaluate catch dup if nip nip then leave-compiling ;
: reads ( "token" -- )
  parse-name 2dup cr type ."  -> " depth >r probe-try ?dup
  if ." refused " . r> drop exit then
  depth r> 2 - - dup 1 = if drop . exit then ." cells: " 0 ?do . loop ;
reads $10      reads $-10     reads -$10     reads #-10     reads #10
reads %101     reads %-101    reads 'a'      reads -'a'
reads $FFFFFFFF  reads $ffffffff  reads 4294967295  reads $100000000
reads -2147483648  reads $-80000000  reads 2147483648
reads $FFFFFFFFFFFFFFFF  reads 18446744073709551615  reads 18446744073709551616
reads $10000000000000000  reads 1_000  reads 0x10  reads $1_0

\ The words IR 0.2 would add or change: found in FORTH-WORDLIST?
: host? ( c-addr u -- )
  2dup cr type ."  in FORTH-WORDLIST: " forth-wordlist search-wordlist ?dup
  if nip ." yes, " 1 = if ." immediate" else ." not immediate" then
  else ." no" then ;
s" -rot" host?  s" lshift" host?  s" .s" host?  s" u." host?  s" emit" host?
s" spaces" host?  s\" .\"" host?  s\" s\"" host?  s" type" host?  s" [char]" host?
\ Gforth 0.7.3 gives every compile-only word one execution token: is the
\ token of ." the same as IF's?
s\" .\"" forth-wordlist search-wordlist drop
s" if" forth-wordlist search-wordlist drop
s\" token of .\q equals token of IF" label = .
cr bye
