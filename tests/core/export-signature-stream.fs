\ Test-only transport (protocol in tests/support/export-reader.fs) that puts
\ an exported declaration's claim into the candidate signature index under
\ its universe parameters and specializes it with lf-msp-specialize at the
\ given replacement levels. Output: the Lean-style shape of the specialized
\ type. Before that, a stale token, a wrong argument count and a stale level
\ handle must each be invalid, and afterwards the token of a replaced index
\ too. A candidate signature is an assumption, not a checked declaration.
\ Malformed input, or any guard that does not hold, prints nothing and fails.
require ../../src/main.fs
include ../support/export-reader.fs
variable token

: decl-name ( -- name ) 0 s" decl" lf-name-str must ;
: put-claim ( fuel -- )
  >r lf-msp-begin must lf-msp-token must dup token !
  decl-name claim-index @ claim-id @ params param-count @ r> lf-msp-put ok? must ;
: specialize ( token count -- root identity 0 | status )
  >r decl-name actuals r> 50000 lf-msp-specialize ;
: invalid? ( root identity 0 | status -- flag )
  dup ok? if drop 2drop false else outcome-invalid = then ;
: guards ( -- )
  token @ 1+ subst-count @ specialize invalid? must
  token @ subst-count @ 1- specialize invalid? must
  token @ subst-count @ 1+ specialize invalid? must
  actuals cell+ dup @ 1+ swap ! token @ subst-count @ specialize invalid? must
  actuals cell+ dup @ 1- swap ! ;
: run ( -- )
  read-export subst-count @ must put-claim guards
  token @ subst-count @ specialize ok? must drop >r
  lf-msp-begin must token @ subst-count @ specialize invalid? must
  r> emit-shape cr ;
: main ( -- ) ['] run catch if 1 (bye) then ;
main bye
