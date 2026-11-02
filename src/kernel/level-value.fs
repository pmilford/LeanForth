\ Untrusted concrete evaluator for the experimental symbolic level store.
\ A numeric result is not level equality, a checked type, or a theorem. A
\ parameter yields unknown unless explicitly assigned in the separate instance
\ evaluator; checking one instance does not prove a polymorphic claim. Host
\ cells and bounded host recursion are assumptions, not a trusted boundary.
\ Requires levels.fs and level-scope.fs.
\ State: one record, lf-lvalue-state: the table of explicit parameter
\ assignments with the level-store and context generations it was made
\ for, the fuel left after an evaluation (level-compare reads it), and
\ whether the evaluation reads the table. The evaluation recurses on the
\ host stacks through the deferred word lf-lvalue-walk, which is set once
\ at load time. Not re-entrant and single-threaded.
\ Stack use: about 8 return-stack cells per nesting level (measured about
\ 500 cells at depth 63), so lf-lvalue-depth-limit must stay well below the
\ return stack of every task that evaluates (Gforth 0.7.3's default is
\ 1,920 cells). An overflow would throw, never return ok.

outcome-ok constant lf-lvalue-ok
outcome-invalid constant lf-lvalue-invalid
outcome-exhausted constant lf-lvalue-exhausted
outcome-unknown constant lf-lvalue-unknown
max-n constant lf-lvalue-cell-max
64 constant lf-lvalue-depth-limit

begin-structure /lf-lvrec
  field: lf-lvrec-fuel          \ visits left after an evaluation
  field: lf-lvrec-assigned      \ true while an evaluation reads the table
  field: lf-lvrec-count         \ assignments in the table
  field: lf-lvrec-levels        \ level-store generation of the table
  field: lf-lvrec-context       \ parameter-context generation of the table
  lf-level-capacity cells +field lf-lvrec-ids
  lf-level-capacity cells +field lf-lvrec-values
end-structure
create lf-lvalue-state /lf-lvrec allot
lf-lvalue-state /lf-lvrec erase

\ The record's fields under their established names; tests corrupt the
\ table through them.
: lf-lvalue-fuel ( -- addr ) lf-lvalue-state lf-lvrec-fuel ;
: lf-lassign-count ( -- addr ) lf-lvalue-state lf-lvrec-count ;
: lf-lassign-ids ( -- addr ) lf-lvalue-state lf-lvrec-ids ;
: lf-lassign-values ( -- addr ) lf-lvalue-state lf-lvrec-values ;

\ The assignment table: a finite map from parameter IDs to nonnegative
\ cells. A reset empties it and binds it to the current level store and
\ context, so a later reset of either makes it stale.
: lf-lassign-reset ( -- )
  0 lf-lassign-count ! lf-level-generation @ lf-lvalue-state lf-lvrec-levels !
  lf-lscope-generation @ lf-lvalue-state lf-lvrec-context ! ;
: lf-lassign-id@ ( i -- id ) cells lf-lassign-ids + @ ;
: lf-lassign-value@ ( i -- value ) cells lf-lassign-values + @ ;
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
  lf-lassign-count @ lf-level-capacity upto? lf-lscope-context-valid? and
  lf-level-count-valid? and lf-lassign-current? and
  if lf-lassign-entries? else false then ;

\ Add one assignment to a valid table: a nonnegative value for an ID in the
\ context that has none yet. A full table, a duplicate, a stale table or a
\ negative value returns false and changes nothing.
: lf-lassign-new? ( id value -- flag )
  0< 0= over lf-lscope-member? and swap lf-lassign-count @ lf-lassign-in? 0= and
  lf-lassign-count @ lf-level-capacity < and ;
: lf-lassign-append ( id value -- )
  lf-lassign-count @ tuck cells lf-lassign-values + ! cells lf-lassign-ids + !
  1 lf-lassign-count +! ;
: lf-lassign-add ( id value -- flag )
  lf-lassign-valid? if 2dup lf-lassign-new? else false then
  if lf-lassign-append true else 2drop false then ;

\ Evaluation of a node already validated by the scope check. Depth counts
\ the nodes above it; a visit needs fuel and a depth below the limit.
\ The value -1 is a symbolic result: with ok it ends the evaluation of
\ every node above, and it cannot be confused with a concrete level.
defer lf-lvalue-walk ( node depth -- value status )
: lf-lvalue-room? ( depth -- flag ) lf-lvalue-depth-limit < lf-lvalue-fuel @ 0> and ;
\ A failure or a symbolic value is final; otherwise continue with the value.
: lf-lvalue-done? ( value status -- value status true | value false )
  dup ok? 0= if true exit then over -1 = if true else drop false then ;
: lf-lvalue-assigned ( id -- value ) lf-lassign-find 0= if -1 then ;
: lf-lvalue-param ( id -- value )
  lf-lvalue-state lf-lvrec-assigned @ if lf-lvalue-assigned else drop -1 then ;
: lf-lvalue-succ+ ( value -- value status )
  dup lf-lvalue-cell-max = if drop -1 outcome-exhausted else 1+ outcome-ok then ;
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
  dup lf-lvalue-room? 0= if 2drop -1 outcome-exhausted exit then
  -1 lf-lvalue-fuel +! lf-lvalue-visit ;
' lf-lvalue-enter is lf-lvalue-walk

\ Scope-check the whole reachable graph first; validation and evaluation
\ share fuel, and lf-lvalue-fuel is set only once validation succeeds.
\ Negative fuel is invalid (lf-lscope-check refuses it). A symbolic result
\ is unknown. Unknown, invalid or exhausted returns -1 and never
\ authorizes a theorem.
: lf-lvalue-known ( value status -- value status )
  dup ok? if over -1 = if drop outcome-unknown then then ;
: lf-lvalue-eval ( root -- value status )
  lf-lscope-fuel @ lf-lvalue-fuel ! 0 lf-lvalue-walk lf-lvalue-known ;
: lf-lvalue-checked ( root fuel -- value status )
  over swap lf-lscope-check ok-then? if lf-lvalue-eval else -1 swap then ;
\ With assignments the table must be valid first.
: lf-lvalue-mode? ( use-assignments -- flag ) if lf-lassign-valid? else true then ;
: lf-level-value-run ( root fuel use-assignments -- value status )
  dup lf-lvalue-mode? 0= if drop 2drop -1 outcome-invalid exit then
  lf-lvalue-state lf-lvrec-assigned ! lf-lvalue-checked ;

\ Evaluate without assignments; symbolic parameters remain unknown.
: lf-level-value ( root fuel -- value status ) false lf-level-value-run ;

\ Evaluate one explicit assignment instance. Missing assignments stay unknown;
\ an invalid assignment table or context never produces a concrete value.
: lf-level-value-assigned ( root fuel -- value status ) true lf-level-value-run ;

lf-lassign-reset
