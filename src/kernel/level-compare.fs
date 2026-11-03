\ Untrusted conservative equality experiment for Lean-style level graphs.
\ Equal is only an experimental diagnostic, never a theorem or type
\ judgment. It assumes a store and context unchanged during a call, and that
\ equal opaque parameter IDs denote the same Lean name.
\ State: one record, lf-lcmp-state, holding the fuel left after a
\ comparison, which mixed-convert reads. The comparison recurses on the host
\ stacks through the deferred word lf-lcmp-walk, set once at load time. Not
\ re-entrant and single-threaded.
\ Stack use: about 8 return-stack cells per nesting level (measured about
\ 510 cells at depth 63), so lf-lcmp-depth-limit must stay well below the
\ return stack of every task that compares (Gforth 0.7.3's default is 1,920
\ cells). An overflow would throw, never return equal.

require ../lib/lib.fs
require ../core/level-scope.fs
require ../core/levels.fs
require ./level-value.fs

64 constant lf-lcmp-depth-limit

begin-structure /lf-lcrec
  field: lf-lcrec-fuel          \ visits left after a comparison
end-structure
create lf-lcmp-state /lf-lcrec allot
lf-lcmp-state /lf-lcrec erase

: lf-lcmp-fuel ( -- addr ) lf-lcmp-state lf-lcrec-fuel ;
\ Any failure except an unequal concrete value leaves no fuel: mixed-convert
\ continues with lf-lcmp-fuel whatever the outcome.
: lf-lcmp-fail ( status -- status ) 0 lf-lcmp-fuel ! ;
: lf-lcmp-settle ( status -- status ) dup ok? 0= if lf-lcmp-fail then ;

\ Fields of a node that has been read successfully.
: lf-lcmp-tag@ ( node -- tag ) lf-level-slot node-tag @ ;
: lf-lcmp-firsts ( left right -- first first' )
  lf-level-slot node-first @ swap lf-level-slot node-first @ swap ;
: lf-lcmp-seconds ( left right -- second second' )
  lf-level-slot node-second @ swap lf-level-slot node-second @ swap ;

\ Reduce only literal-zero identities: max with a zero child is the other
\ child, and imax with a zero second child is zero. Both roots were
\ completely scope-checked first; each node read costs fuel, and each
\ rewrite leads to an earlier node. This is not general Lean universe
\ normalization.
: lf-lcmp-max-zero ( first second -- node true | false )
  over 0= if nip true exit then dup 0= if drop true else 2drop false then ;
: lf-lcmp-rewrite ( tag first second -- node true | false )
  rot case lf-level-tag-max of lf-lcmp-max-zero endof
    lf-level-tag-imax of nip 0= if 0 true else false then endof
    >r 2drop false r> endcase ;
: lf-lcmp-spend? ( -- flag )
  lf-lcmp-fuel @ 0= if false else -1 lf-lcmp-fuel +! true then ;
: lf-lcmp-shrink ( node -- node status )
  begin lf-lcmp-spend? 0= if drop -1 outcome-exhausted exit then
    dup lf-level-read 0= if drop -1 outcome-invalid exit then
    lf-lcmp-rewrite while nip repeat outcome-ok ;
\ The right root shrinks first.
: lf-lcmp-shrink2 ( left right -- left' right' true | status false )
  lf-lcmp-shrink dup ok? 0= if nip nip false exit then drop
  swap lf-lcmp-shrink dup ok? 0= if nip nip false exit then drop swap true ;

\ Compare syntax after both roots have passed scope validation. Depth
\ counts the comparisons above; a visit needs fuel (else exhausted) and a
\ depth below the limit (else full); with neither, the fuel decides. Any
\ unmatched constructor or ID is unknown.
defer lf-lcmp-walk ( left right depth -- status )
: lf-lcmp-same-value ( x x' -- status ) = if outcome-ok else outcome-unknown then ;
: lf-lcmp-param ( left right -- status ) lf-lcmp-firsts lf-lcmp-same-value ;
\ Succ, max and imax: first children, then (except for succ) second children.
: lf-lcmp-inner ( left right depth -- status )
  >r 2dup lf-lcmp-firsts r@ lf-lcmp-walk dup ok? 0= if nip nip r> drop exit then drop
  over lf-lcmp-tag@ lf-level-tag-succ = if 2drop r> drop outcome-ok
  else lf-lcmp-seconds r> lf-lcmp-walk then ;
\ Nodes with the same tag; depth is their children's depth.
: lf-lcmp-same ( left right depth -- status )
  over lf-lcmp-tag@ case lf-level-tag-zero of drop 2drop outcome-ok endof
    lf-level-tag-param of drop lf-lcmp-param endof
    >r lf-lcmp-inner r> endcase ;
: lf-lcmp-node ( left right depth -- status )
  >r 2dup lf-lcmp-tag@ swap lf-lcmp-tag@ =
  if r> lf-lcmp-same else 2drop r> drop outcome-unknown then ;
: lf-lcmp-readable? ( left right -- flag ) lf-level-valid? swap lf-level-valid? and ;
: lf-lcmp-shrunk ( left right depth -- status )
  >r 2dup lf-lcmp-readable? if r> lf-lcmp-node else 2drop r> drop outcome-invalid then ;
: lf-lcmp-visit ( left right depth -- status )
  >r lf-lcmp-shrink2 if r> lf-lcmp-shrunk else r> drop then ;
: lf-lcmp-room ( depth -- outcome )
  lf-lcmp-fuel @ swap lf-lcmp-depth-limit < visit-outcome ;
: lf-lcmp-enter ( left right depth -- status )
  dup lf-lcmp-room ok-then? 0= if nip nip exit then
  -1 lf-lcmp-fuel +! 1+ lf-lcmp-visit ;
' lf-lcmp-enter is lf-lcmp-walk

\ If syntax did not match, independently evaluate both unassigned concrete
\ graphs, left first, each with the fuel left. Unequal or symbolic values are
\ unknown, never an inequality verdict.
: lf-lcmp-value ( root -- value status )
  lf-lcmp-fuel @ lf-level-value dup ok? if lf-lvalue-fuel @ lf-lcmp-fuel ! then ;
: lf-lcmp-values ( left right -- value value' true | status false )
  swap lf-lcmp-value ok-then? 0= if nip false exit then
  swap lf-lcmp-value ok-then? if true else nip false then ;
: lf-lcmp-concrete ( left right -- status )
  lf-lcmp-values if lf-lcmp-same-value else lf-lcmp-fail then ;

\ Scope-check a root with the fuel left, continuing with what it leaves.
: lf-lcmp-scope ( root -- status )
  lf-lcmp-fuel @ lf-lscope-check lf-lscope-fuel @ lf-lcmp-fuel ! ;
: lf-lcmp-scopes ( left right -- status )
  swap lf-lcmp-scope ok-then? if lf-lcmp-scope then ;
: lf-lcmp-roots ( left right -- status )
  2dup 0 lf-lcmp-walk dup outcome-unknown =
  if drop lf-lcmp-concrete else nip nip lf-lcmp-settle then ;

\ Compare two roots against one explicit parameter context. Scope checks run
\ before any equality shortcut and share fuel with comparison and evaluation.
\ Only one status is returned; this word cannot register a declaration.
: lf-level-compare ( left right fuel -- status )
  dup 0< if drop 2drop outcome-invalid lf-lcmp-fail exit then lf-lcmp-fuel !
  2dup lf-lcmp-scopes dup ok? if drop lf-lcmp-roots else nip nip lf-lcmp-fail then ;
