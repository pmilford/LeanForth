\ Untrusted concrete evaluator for the experimental symbolic level store. A
\ numeric result is not level equality, a checked type, or a theorem. A
\ parameter yields unknown unless explicitly assigned in the separate
\ instance evaluator; checking one instance does not prove a polymorphic
\ claim. Host cells and bounded host recursion are assumptions, not a
\ trusted boundary. Two exact tests of ADR 0011 evaluate under witness
\ assignments: lf-level-zero? (Lean's normalizes_to_zero, rule S3 and
\ the proof test P2) and lf-level-apart? (rule D1).
\ State: one record, lf-lvalue-state: the table of explicit parameter
\ assignments with the level-store and context generations it was made for,
\ the fuel left after an evaluation (level-compare reads it), how the
\ evaluation gives parameters values (free, from the table, or a witness
\ assignment) and the witness; a member of the checker context
\ (lib/context.fs), whose table a set-up word binds to the context's own
\ stores. The evaluation recurses on the host stacks through the deferred
\ word lf-lvalue-walk, which is set once at load time and shared.
\ Single-threaded within one context.
\ Stack use: about 8 return-stack cells per nesting level (measured about
\ 500 cells at depth 63), so lf-lvalue-depth-limit must stay well below the
\ return stack of every task that evaluates (Gforth 0.7.3's default is 1,920
\ cells). An overflow would throw, never return ok.

require ../lib/lib.fs
require ../core/diagnostics.fs
require ../core/level-scope.fs
require ../core/levels.fs

max-n constant lf-lvalue-cell-max
64 constant lf-lvalue-depth-limit

\ How an evaluation gives a parameter its value.
0 constant lf-lvalue-free       \ none: a parameter is symbolic
1 constant lf-lvalue-table      \ the assignment table's value, else symbolic
2 constant lf-lvalue-witness    \ the witness assignment's value

begin-structure /lf-lvrec
  field: lf-lvrec-fuel          \ visits left after an evaluation
  field: lf-lvrec-mode          \ lf-lvalue-free, -table or -witness
  field: lf-lvrec-witness       \ the witness assignment in witness mode
  field: lf-lvrec-count         \ assignments in the table
  field: lf-lvrec-levels        \ level-store generation of the table
  field: lf-lvrec-context       \ parameter-context generation of the table
end-structure
/lf-lvrec context-record: lf-lvalue-state
\ The table's IDs and values: growable arrays with no fixed limit (plan
\ task 6.2.0); a table the heap cannot grow refuses the assignment.
1 cells context-slab: lf-lassign-id-cells
1 cells context-slab: lf-lassign-value-cells

\ The record's fields under their established names; tests corrupt the
\ table through them.
: lf-lvalue-fuel ( -- addr ) lf-lvalue-state lf-lvrec-fuel ;
: lf-lassign-count ( -- addr ) lf-lvalue-state lf-lvrec-count ;
\ The first ID's and value's addresses, valid while the table does not grow.
: lf-lassign-ids ( -- addr ) 0 lf-lassign-id-cells slab-at ;
: lf-lassign-values ( -- addr ) 0 lf-lassign-value-cells slab-at ;

\ The assignment table: a finite map from parameter IDs to nonnegative
\ cells. A reset empties it and binds it to the current level store and
\ context, so a later reset of either makes it stale.
: lf-lassign-reset ( -- )
  0 lf-lassign-count ! lf-level-generation @ lf-lvalue-state lf-lvrec-levels !
  lf-lscope-generation @ lf-lvalue-state lf-lvrec-context ! ;
: lf-lassign-id@ ( i -- id ) lf-lassign-id-cells slab-at @ ;
: lf-lassign-value@ ( i -- value ) lf-lassign-value-cells slab-at @ ;
: lf-lassign-room ( -- n ) lf-lassign-id-cells slab-capacity lf-lassign-value-cells slab-capacity min ;
\ Position of an ID among the first n entries.
: lf-lassign-position ( id n -- i true | false )
  0 ?do dup i lf-lassign-id@ = if drop i true unloop exit then loop drop false ;
: lf-lassign-in? ( id n -- flag ) lf-lassign-position dup if nip then ;
\ Search a validated table; a missing ID returns only false.
: lf-lassign-find ( id -- value true | false )
  lf-lassign-count @ lf-lassign-position if lf-lassign-value@ true else false then ;

\ Revalidate the whole table against the current stores before use: the
\ count is in range, the generations are current, and every entry holds a
\ nonnegative value and a positive ID in the context that no earlier entry
\ holds. The quadratic scan is bounded and separate from evaluation fuel.
: lf-lassign-id-ok? ( i -- flag )
  dup lf-lassign-id@ dup 0> over lf-lscope-member? and
  if swap lf-lassign-in? 0= else 2drop false then ;
: lf-lassign-entry? ( i -- flag )
  dup lf-lassign-value@ 0< if drop false else lf-lassign-id-ok? then ;
: lf-lassign-entries? ( -- flag )
  lf-lassign-count @ 0 ?do i lf-lassign-entry? 0= if false unloop exit then loop true ;
: lf-lassign-current? ( -- flag )
  lf-level-generation @ lf-lvalue-state lf-lvrec-levels @ =
  lf-lscope-generation @ lf-lvalue-state lf-lvrec-context @ = and ;
: lf-lassign-valid? ( -- flag )
  lf-lassign-count @ lf-lassign-room upto? lf-lscope-context-valid? and
  lf-level-count-valid? and lf-lassign-current? and
  if lf-lassign-entries? else false then ;

\ Add one assignment to a valid table: a nonnegative value for an ID in the
\ context that has none yet. A table the heap cannot grow, a duplicate, a
\ stale table or a negative value returns false and changes nothing.
: lf-lassign-grown? ( -- flag )
  lf-lassign-count @ 1+ dup lf-lassign-id-cells slab-reserve ok?
  swap lf-lassign-value-cells slab-reserve ok? and ;
: lf-lassign-new? ( id value -- flag )
  0< 0= over lf-lscope-member? and swap lf-lassign-count @ lf-lassign-in? 0= and
  dup if drop lf-lassign-grown? then ;
: lf-lassign-append ( id value -- )
  lf-lassign-count @ tuck lf-lassign-value-cells slab-at ! lf-lassign-id-cells slab-at !
  1 lf-lassign-count +! ;
: lf-lassign-add ( id value -- flag )
  lf-lassign-valid? if 2dup lf-lassign-new? else false then
  if lf-lassign-append true else 2drop false then ;

\ Evaluation of a node already validated by the scope check. Depth counts
\ the nodes above it; a visit needs fuel (else exhausted) and a depth below
\ the limit (else full); with neither, the fuel decides. A successor of
\ the largest cell value is full too: the value has no room to grow.
\ The value -1 is a symbolic result: with ok it ends the evaluation of
\ every node above, and it cannot be confused with a concrete level.
\ Each such failure is recorded as a diagnostic.
defer lf-lvalue-walk ( node depth -- value status )
: lf-lvalue-site ( -- site ) c" level-value lf-level-value" ;
: lf-lvalue-deep ( depth -- )
  lf-lvalue-depth-limit lf-lvalue-site lf-diag-depth-limit lf-diag-note ;
: lf-lvalue-refused ( depth outcome -- outcome )
  dup outcome-full = if swap lf-lvalue-deep
  else nip lf-lvalue-fuel @ lf-lvalue-site lf-diag-exhausted then ;
: lf-lvalue-room ( depth -- outcome )
  dup lf-lvalue-fuel @ swap lf-lvalue-depth-limit < visit-outcome
  dup ok? if nip else lf-lvalue-refused then ;
\ A failure or a symbolic value is final; otherwise continue with the value.
: lf-lvalue-done? ( value status -- value status true | value false )
  dup ok? 0= if true exit then over -1 = if true else drop false then ;
: lf-lvalue-assigned ( id -- value ) lf-lassign-find 0= if -1 then ;
\ A witness assignment is one cell: -1 gives every parameter 1, 0 every
\ parameter 0, and a parameter ID w gives w 1 and every other parameter 0
\ (IDs are positive, so 0 and -1 name no parameter).
: lf-lvalue-witnessed ( id -- value )
  lf-lvalue-state lf-lvrec-witness @ dup 0< if 2drop 1 else = 1 and then ;
: lf-lvalue-param ( id -- value )
  lf-lvalue-state lf-lvrec-mode @ case
    lf-lvalue-table of lf-lvalue-assigned endof
    lf-lvalue-witness of lf-lvalue-witnessed endof
    nip -1 swap endcase ;
: lf-lvalue-ceiling ( value -- -1 status )
  1 lf-lvalue-site lf-diag-cell-maximum lf-diag-note -1 outcome-full ;
: lf-lvalue-succ+ ( value -- value status )
  dup lf-lvalue-cell-max = if lf-lvalue-ceiling else 1+ outcome-ok then ;
: lf-lvalue-succ ( first depth -- value status )
  lf-lvalue-walk lf-lvalue-done? 0= if lf-lvalue-succ+ then ;
\ Both children of a max or imax, first child first.
: lf-lvalue-pair ( first second depth -- left right true | value status false )
  tuck 2>r lf-lvalue-walk lf-lvalue-done? if 2r> 2drop false exit then
  2r> lf-lvalue-walk lf-lvalue-done? if rot drop false else true then ;
: lf-lvalue-max ( first second depth -- value status )
  lf-lvalue-pair if max outcome-ok then ;
\ imax u v is zero when v is zero, and max u v otherwise.
: lf-lvalue-imax-of ( left right -- value ) dup 0= if nip else max then ;
: lf-lvalue-imax ( first second depth -- value status )
  lf-lvalue-pair if lf-lvalue-imax-of outcome-ok then ;
\ One arm per level tag; depth here is the children's depth.
: lf-lvalue-dispatch ( first second depth tag -- value status )
  case lf-level-tag-zero of drop 2drop 0 outcome-ok endof
    lf-level-tag-param of 2drop lf-lvalue-param outcome-ok endof
    lf-level-tag-succ of nip lf-lvalue-succ endof
    lf-level-tag-max of lf-lvalue-max endof
    lf-level-tag-imax of lf-lvalue-imax endof
    >r drop 2drop -1 outcome-invalid r> endcase ;
: lf-lvalue-visit ( node depth -- value status )
  1+ swap lf-level-read if 2swap lf-lvalue-dispatch else drop -1 outcome-invalid then ;
: lf-lvalue-enter ( node depth -- value status )
  dup lf-lvalue-room ok-then? 0= if nip no-result exit then
  -1 lf-lvalue-fuel +! lf-lvalue-visit ;
' lf-lvalue-enter is lf-lvalue-walk

\ Scope-check the whole reachable graph first; validation and evaluation
\ share fuel, and lf-lvalue-fuel is set only once validation succeeds.
\ Negative fuel is invalid (lf-lscope-check refuses it). A symbolic result
\ is unknown, recorded as a symbolic level. Unknown, invalid, exhausted or
\ full returns -1 and never authorizes a theorem.
: lf-lvalue-symbolic ( root -1 status -- -1 status )
  drop swap 0 lf-lvalue-site lf-diag-symbolic-level lf-diag-note outcome-unknown ;
: lf-lvalue-known ( root value status -- value status )
  dup ok? if over -1 = if lf-lvalue-symbolic exit then then rot drop ;
: lf-lvalue-eval ( root -- value status )
  lf-lscope-fuel @ lf-lvalue-fuel ! dup 0 lf-lvalue-walk lf-lvalue-known ;
: lf-lvalue-checked ( root fuel -- value status )
  over swap lf-lscope-check ok-then? if lf-lvalue-eval else -1 swap then ;
\ With assignments the table must be valid first.
: lf-lvalue-mode? ( mode -- flag )
  case lf-lvalue-table of lf-lassign-valid? endof
    lf-lvalue-free of true endof lf-lvalue-witness of true endof false swap endcase ;
: lf-level-value-run ( root fuel mode -- value status )
  dup lf-lvalue-mode? 0= if drop 2drop -1 outcome-invalid exit then
  lf-lvalue-state lf-lvrec-mode ! lf-lvalue-checked ;

\ Evaluate without assignments; symbolic parameters remain unknown.
: lf-level-value ( root fuel -- value status ) lf-lvalue-free lf-level-value-run ;

\ Evaluate one explicit assignment instance. Missing assignments stay unknown;
\ an invalid assignment table or context never produces a concrete value.
: lf-level-value-assigned ( root fuel -- value status )
  lf-lvalue-table lf-level-value-run ;

\ Evaluate under a witness assignment (see lf-lvalue-witnessed); every
\ parameter in the context gets a value, so ok always gives a number.
\ Like the other evaluations it scope-checks first; unlike them, any
\ failure leaves no fuel (lf-lvalue-fuel 0), so a caller that goes on
\ after a failure never continues with the fuel of an earlier call.
: lf-lvalue-dry ( value status -- value status ) dup ok? 0= if 0 lf-lvalue-fuel ! then ;
: lf-level-value-witness ( root fuel witness -- value status )
  lf-lvalue-state lf-lvrec-witness ! lf-lvalue-witness lf-level-value-run
  lf-lvalue-dry ;

\ Lean's normalizes_to_zero (level.cpp 174-187; ADR 0011 fact 6): whether
\ a level is zero under every assignment of its parameters. It equals
\ "zero when every parameter is 1": zero is 0, a successor or a parameter
\ at least 1, max is 0 exactly when both sides are, and imax exactly when
\ its right side is (imax u v is 0 for v = 0, else max u v) -- the cases
\ of normalizes_to_zero, by induction. (flag ok), or (false failure) as
\ lf-level-value-witness.
: lf-level-zero? ( root fuel -- flag status )
  -1 lf-level-value-witness dup ok? if swap 0= swap else nip false swap then ;

\ Rule D1 (ADR 0011): whether some witness assignment gives two levels
\ different values -- every parameter 0, or one parameter of the context 1
\ and the others 0 -- so that Lean's level equivalence is false (fact 7).
\ (flag ok), or (false failure) at the first evaluation that fails; both
\ roots are scope-checked at every evaluation, left first.
: lf-lvalue-witness@ ( i -- w ) dup 0< if drop 0 else lf-lscope-id@ then ;
: lf-lvalue-under ( root w -- value status )
  lf-lvalue-fuel @ swap lf-level-value-witness ;
: lf-lvalue-left ( left right w -- right w v1 true | status false )
  rot over lf-lvalue-under dup ok? if drop true else nip nip nip false then ;
: lf-lvalue-both ( left right w -- v1 v2 true | status false )
  lf-lvalue-left 0= if false exit then
  -rot lf-lvalue-under dup ok? if drop true else nip nip false then ;
: lf-lvalue-differ ( left right w -- flag status )
  lf-lvalue-both if <> outcome-ok else false swap then ;
: lf-lvalue-settled? ( flag status -- flag status stop? ) 2dup ok? 0= or ;
: lf-lvalue-witnesses ( left right -- flag status )
  lf-lscope-context-count @ -1 ?do
    2dup i lf-lvalue-witness@ lf-lvalue-differ lf-lvalue-settled?
    if 2swap 2drop unloop exit then 2drop
  loop 2drop false outcome-ok ;
: lf-lvalue-refuse ( left right fuel -- false status )
  drop 2drop 0 lf-lvalue-fuel ! false outcome-invalid ;
: lf-level-apart? ( left right fuel -- flag status )
  dup 0< lf-lscope-context-valid? 0= or if lf-lvalue-refuse exit then
  lf-lvalue-fuel ! lf-lvalue-witnesses ;

\ Every context starts with an empty table bound to its own stores.
' lf-lassign-reset context-setup
