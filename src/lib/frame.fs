\ Bounded recursion for passes that rebuild a DAG node by node. A frames
\ record holds the fuel left, the number of visits in progress (frames)
\ and their limit, the visitor, a context cell for the visit in progress
\ (such as the number of binders around its node), and two cells for the
\ pass: an argument and a mark (such as a store count to roll back to).
\ Every word here takes the record's address, so separate records are
\ independent and this module has no state; a module that owns one record
\ must not start its pass again while that record is in use.
\ Requires: store.fs (store-zeroed,), outcome.fs.
\
\ frame-call spends one unit of fuel and one frame, calls the visitor
\ ( x -- result outcome ) on x and releases the frame. With no fuel left or
\ every frame in use it visits nothing and gives -1 (no result) and
\ exhausted. A visitor visits a child by calling frame-call, or frame-under
\ for a child one context level deeper, on the same record, so a node
\ shared by several parents is visited, and charged, once per path. A
\ visitor result outside the outcome vocabulary counts as invalid. Values
\ a visitor keeps across a child's visit stay on the data stack: each
\ frame also uses a few cells of the host's data and return stacks, which
\ the limit bounds.

begin-structure /frames
  field: frame-fuel      \ visits left
  field: frame-depth     \ visits in progress
  field: frame-limit     \ most visits in progress at once
  field: frame-visitor   \ xt ( x -- result outcome )
  field: frame-context   \ context of the visit in progress
  field: frame-arg       \ one cell for the pass
  field: frame-mark      \ one cell for the pass, such as a store count
end-structure

\ Defining word: name ( -- frames ), zeroed, allowing limit nested visits.
\ A limit below 1 aborts the definition.
: frames: ( limit "name" -- )
  dup 0> 0= abort" frames: bad limit" create /frames store-zeroed, frame-limit ! ;

\ Set the budget for a pass; a negative fuel is refused and stores nothing.
: frame-budget ( fuel frames -- flag )
  over 0< if 2drop false else frame-fuel ! true then ;

\ Visiting. A visit opens when fuel is left and a frame is free (signed
\ comparison, so a corrupted negative limit opens nothing).
: frame-open? ( frames -- flag )
  dup frame-fuel @ 0<> over frame-depth @ rot frame-limit @ < and ;
: frame-enter ( frames -- ) -1 over frame-fuel +! 1 swap frame-depth +! ;
: frame-leave ( frames -- ) -1 swap frame-depth +! ;
: frame-call ( x frames -- result outcome )
  dup frame-open? 0= if 2drop -1 outcome-exhausted exit then
  dup frame-enter tuck frame-visitor @ execute outcome-sane rot frame-leave ;
\ One context level deeper, restored afterwards. A context that cannot
\ grow is exhausted, visiting nothing.
: frame-deeper ( n frames -- ) frame-context +! ;
: frame-under ( x frames -- result outcome )
  dup frame-context @ max-n = if 2drop -1 outcome-exhausted exit then
  1 over frame-deeper tuck frame-call rot -1 swap frame-deeper ;

\ A pass: no visits in progress, the root's context and the visitor, then
\ the root's visit.
: frame-start ( context xt frames -- )
  tuck frame-visitor ! tuck frame-context ! 0 swap frame-depth ! ;
: frame-run ( x context xt frames -- result outcome ) dup >r frame-start r> frame-call ;
