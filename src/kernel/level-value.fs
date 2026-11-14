\ Untrusted concrete evaluator for the experimental symbolic level store. A
\ numeric result is not level equality, a checked type, or a theorem. A
\ parameter yields unknown unless explicitly assigned in the separate
\ instance evaluator; checking one instance does not prove a polymorphic
\ claim. Host cells are assumptions, not a trusted boundary. Two exact tests of ADR 0011 evaluate under witness
\ assignments: lf-level-zero? (Lean's normalizes_to_zero, rule S3 and
\ the proof test P2) and lf-level-apart? (rule D1).
\ State: one record, lf-lvalue-state: the table of explicit parameter
\ assignments with the level-store and context generations it was made for,
\ the fuel left after an evaluation (level-compare reads it), how the
\ evaluation gives parameters values (free, from the table, or a witness
\ assignment) and the witness; a member of the checker context
\ (lib/context.fs), whose table a set-up word binds to the context's own
\ stores, and the evaluation's frames (lib/frame.fs): its pending work
\ waits on an explicit stack that grows with the depth of the level graph
\ (plan task 6.2.0), so the host's stacks hold a constant number of cells
\ whatever the depth, and a stack the heap cannot grow is full.
\ Single-threaded within one context.

require ../lib/lib.fs
require ../core/diagnostics.fs
require ../core/level-scope.fs
require ../core/levels.fs

max-n constant lf-lvalue-cell-max

\ How an evaluation gives a parameter its value.
0 constant lf-lvalue-free       \ none: a parameter is symbolic
1 constant lf-lvalue-table      \ the assignment table's value, else symbolic
2 constant lf-lvalue-witness    \ the witness assignment's value

begin-structure /lf-lvrec
  /frames +field lf-lvrec-frames \ the evaluation's; its fuel, visits left after it
  field: lf-lvrec-mode          \ lf-lvalue-free, -table or -witness
  field: lf-lvrec-witness       \ the witness assignment in witness mode
  field: lf-lvrec-count         \ assignments in the table
  field: lf-lvrec-levels        \ level-store generation of the table
  field: lf-lvrec-context       \ parameter-context generation of the table
end-structure
/lf-lvrec context-record: lf-lvalue-state
: lf-lvrec-fuel ( rec -- addr ) lf-lvrec-frames frame-fuel ;
\ The table's IDs and values: growable arrays with no fixed limit (plan
\ task 6.2.0); a table the heap cannot grow refuses the assignment.
1 cells context-slab: lf-lassign-id-cells
1 cells context-slab: lf-lassign-value-cells

\ The record's fields under their established names; tests corrupt the
\ table through them.
: lf-lvalue-fuel ( -- addr ) lf-lvalue-state lf-lvrec-fuel ;
: lf-lassign-count ( -- addr ) lf-lvalue-state lf-lvrec-count ;
\ The first ID's and value's addresses, valid while the table does not grow.
: lf-lassign-ids ( -- addr ) lf-lassign-id-cells slab-base ;
: lf-lassign-values ( -- addr ) lf-lassign-value-cells slab-base ;

\ The assignment table: a finite map from parameter IDs to nonnegative
\ cells. A reset empties it and binds it to the current level store and
\ context, so a later reset of either makes it stale.
: lf-lassign-reset ( -- )
  0 lf-lassign-count ! lf-level-generation @ lf-lvalue-state lf-lvrec-levels !
  lf-lscope-generation @ lf-lvalue-state lf-lvrec-context ! ;
: lf-lassign-id@ ( i -- id ) cells lf-lassign-ids + @ ;
: lf-lassign-value@ ( i -- value ) cells lf-lassign-values + @ ;
: lf-lassign-room ( -- n ) lf-lassign-id-cells slab-capacity lf-lassign-value-cells slab-capacity min ;
\ Position of an ID among the first n entries.
: lf-lassign-position ( id n -- i true | false ) lf-lassign-ids swap cells-index ;
: lf-lassign-in? ( id n -- flag ) lf-lassign-ids swap cells-has? ;
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
: lf-lassign-entries? ( -- flag ) lf-lassign-count @ ['] lf-lassign-entry? all? ;
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
  lf-lassign-count @ 1+ dup lf-lassign-id-cells slab-hold ok?
  swap lf-lassign-value-cells slab-hold ok? and ;
: lf-lassign-new? ( id value -- flag )
  0< 0= over lf-lscope-member? and swap lf-lassign-count @ lf-lassign-in? 0= and
  dup if drop lf-lassign-grown? then ;
: lf-lassign-append ( id value -- )
  lf-lassign-count @ tuck lf-lassign-value-cells slab-at ! lf-lassign-id-cells slab-at !
  1 lf-lassign-count +! ;
: lf-lassign-add ( id value -- flag )
  lf-lassign-valid? if 2dup lf-lassign-new? else false then
  if lf-lassign-append true else 2drop false then ;

\ Evaluation of a node already validated by the scope check, a visit per
\ node on the frames: a visit needs fuel (else exhausted) and room on the
\ frames (else full); with neither, the fuel decides. A successor of
\ the largest cell value is full too: the value has no room to grow.
\ The value -1 is a symbolic result: with ok it ends the evaluation of
\ every node above, and it cannot be confused with a concrete level.
\ Each such failure is recorded as a diagnostic. A visit's steps ( ...
\ frames -- ... frames next ) end with ( value status frames 0 );
\ lf-lvalue-call asks for a node's visit, continuing with cont ( value
\ status frames -- ... ).
: lf-lvalue-frames ( -- frames ) lf-lvalue-state lf-lvrec-frames ;
: lf-lvalue-site ( -- site ) c" level-value lf-level-value" ;
: lf-lvalue-refused ( outcome -- outcome )
  dup outcome-full = if lf-lvalue-frames frame-room@
    lf-lvalue-site lf-diag-frame-limit lf-diag-note exit then
  dup outcome-exhausted = if lf-lvalue-fuel @ lf-lvalue-site lf-diag-exhausted then ;
: lf-lvalue-call ( node frames cont -- ... frames next )
  over frame-admit dup ok? if drop frame-opened else lf-lvalue-refused frame-refuse then ;
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
: lf-lvalue-succ-back ( value status frames -- value' status frames 0 )
  >r lf-lvalue-done? 0= if lf-lvalue-succ+ then r> 0 ;
\ Both children of a max or imax, first child first, combined by xt ( left
\ right -- value ): xt and the second child wait while the first is
\ evaluated, then xt and the left value.
: lf-lvalue-pair-2 ( right status frames -- value status frames 0 )
  >r lf-lvalue-done? if 2 r@ frame-drop r> 0 exit then
  r@ frame-restore r@ frame-restore >r swap r> execute outcome-ok r> 0 ;
: lf-lvalue-pair-1 ( left status frames -- ... frames next )
  >r lf-lvalue-done? if 2 r@ frame-drop r> 0 exit then
  r@ frame-restore swap r@ frame-save r> ['] lf-lvalue-pair-2 lf-lvalue-call ;
: lf-lvalue-pair ( first second frames xt -- ... frames next )
  over frame-save tuck frame-save ['] lf-lvalue-pair-1 lf-lvalue-call ;
: lf-lvalue-max-of ( left right -- value ) max ;
\ imax u v is zero when v is zero, and max u v otherwise.
: lf-lvalue-imax-of ( left right -- value ) dup 0= if nip else max then ;
\ One arm per level tag: zero and a parameter return their value, the
\ others visit their children; another tag is invalid.
: lf-lvalue-return ( value frames -- value status frames 0 ) >r outcome-ok r> 0 ;
: lf-lvalue-zero ( first second frames -- 0 status frames 0 ) nip nip 0 swap lf-lvalue-return ;
: lf-lvalue-named ( first second frames -- value status frames 0 )
  nip >r lf-lvalue-param r> lf-lvalue-return ;
: lf-lvalue-dispatch ( first second tag frames -- ... frames next )
  swap case lf-level-tag-zero of lf-lvalue-zero endof
    lf-level-tag-param of lf-lvalue-named endof
    lf-level-tag-succ of nip ['] lf-lvalue-succ-back lf-lvalue-call endof
    lf-level-tag-max of ['] lf-lvalue-max-of lf-lvalue-pair endof
    lf-level-tag-imax of ['] lf-lvalue-imax-of lf-lvalue-pair endof
    >r >r 2drop -1 outcome-invalid r> 0 r> endcase ;
\ lf-level-read gives the tag below the children.
: lf-lvalue-visit ( node frames -- ... frames next )
  >r lf-level-read if rot r> lf-lvalue-dispatch else -1 outcome-invalid r> 0 then ;
\ Evaluate a node to the end; the frames and their visitor are set up in
\ every context and freed with it.
: lf-lvalue-walk ( node -- value status )
  lf-lvalue-frames ['] lf-lvalue-call frame-through drop ;
: lf-lvalue-setup ( -- ) ['] lf-lvalue-visit lf-lvalue-frames frame-init ;
' lf-lvalue-setup context-setup
: lf-lvalue-release ( -- ) lf-lvalue-frames frame-free ;
' lf-lvalue-release context-teardown

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
  lf-lscope-fuel @ lf-lvalue-fuel ! dup lf-lvalue-walk lf-lvalue-known ;
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
