\ Bounded recursion for passes that visit a DAG node by node on the host
\ stacks. A frames record holds the fuel left, the number of visits in
\ progress (frames) and their limit, the visitor, a context cell for the
\ visit in progress (such as the number of binders around its node), and a
\ job cell: the address of the pass's own record, where the visitor finds
\ the pass's inputs (0 when it has none). A record stands alone (frames:) or
\ is a field of a larger record (frame-init). Every word here takes the
\ record's address, so separate records are independent and this module has
\ no state.
\
\ frame-call spends one unit of fuel and one frame, calls the visitor
\ ( x frames -- result outcome ) on x and releases the frame; frame-call2
\ does the same for a visitor of two values ( x y frames -- outcome ), such
\ as a comparison. With no fuel left or every frame in use they visit
\ nothing and give exhausted (frame-call also -1, no result). The visitor
\ visits a child by calling frame-call, frame-call2 or frame-under (one
\ context level deeper) on the record it was given, so a node shared by
\ several parents is visited, and charged, once per path. A visitor result
\ outside the outcome vocabulary counts as invalid.
\
\ A record is busy while a visit is in progress. A busy record refuses a
\ new budget and a new pass, so a pass cannot be restarted from inside
\ itself. A THROW out of a visit (such as a host stack overflow) leaves the
\ record busy and its context changed: the code that catches it must
\ discard whatever the pass changed and call frame-reset.
\
\ Host stacks: values a visitor keeps across a child's visit stay on the
\ data stack, and every nested visit also holds a few return-stack cells.
\ The limit bounds the nesting of one record only; a module whose passes
\ nest checks at load time that the host's stacks hold all of them (see
\ mixed-beta.fs).

require ./outcome.fs
require ./portability.fs

begin-structure /frames
  field: frame-fuel      \ visits left
  field: frame-depth     \ visits in progress
  field: frame-limit     \ most visits in progress at once
  field: frame-visitor   \ xt ( x frames -- result outcome ) or ( x y frames -- outcome )
  field: frame-context   \ context of the visit in progress
  field: frame-job       \ the pass's own record, or 0
end-structure

\ Initialise a record in place: idle, no fuel, no job, allowing limit
\ nested visits of the visitor xt, which is set once here. A limit below 1
\ aborts. frames: defines a standalone record, name ( -- frames ).
: frame-init ( limit xt frames -- )
  rot dup 0> 0= abort" frames: bad limit"
  over /frames erase over frame-limit ! frame-visitor ! ;
: frames: ( limit xt "name" -- ) create here /frames allot frame-init ;

\ Busy while a visit is in progress (or after a THROW out of one); a
\ corrupted depth also counts as busy. frame-reset makes a record idle.
: frame-busy? ( frames -- flag ) frame-depth @ 0<> ;
: frame-reset ( frames -- ) 0 swap frame-depth ! ;

\ Set the budget for a pass. A negative fuel or a busy record is refused
\ and stores nothing.
: frame-budget ( fuel frames -- flag )
  over 0< over frame-busy? or if 2drop false else frame-fuel ! true then ;

\ Visiting. A visit opens when fuel is left and a frame is free (signed
\ comparisons, so a corrupted negative fuel or limit opens nothing).
: frame-open? ( frames -- flag )
  dup frame-fuel @ 0> over frame-depth @ rot frame-limit @ < and ;
: frame-enter ( frames -- ) -1 over frame-fuel +! 1 swap frame-depth +! ;
: frame-leave ( frames -- ) -1 swap frame-depth +! ;
\ frame-visit takes a frame the caller found open (frame-open?) and runs
\ the visitor on the values below the record, any number of them.
\ frame-call does the same for one value with the record kept on the data
\ stack instead: the passes recurse through frame-call, and every word and
\ return-stack cell between a visitor and its child's visit is held once
\ per nested frame.
: frame-visit ( i*x frames -- j*x outcome )
  dup frame-enter dup >r dup frame-visitor @ execute outcome-sane r> frame-leave ;
: frame-call ( x frames -- result outcome )
  dup frame-open? 0= if 2drop -1 outcome-exhausted exit then
  dup frame-enter tuck dup frame-visitor @ execute outcome-sane rot frame-leave ;
: frame-call2 ( x y frames -- outcome )
  dup frame-open? if frame-visit else drop 2drop outcome-exhausted then ;

\ One context level deeper, restored afterwards. A context that cannot
\ grow is exhausted, visiting nothing.
: frame-context+! ( n frames -- ) frame-context +! ;
: frame-under ( x frames -- result outcome )
  dup frame-context @ max-n = if 2drop -1 outcome-exhausted exit then
  1 over frame-context+! tuck frame-call rot -1 swap frame-context+! ;

\ A pass: an idle record takes the root's context, then the root is
\ visited. A busy record refuses, changing nothing: no result, invalid.
: frame-start ( context frames -- flag )
  dup frame-busy? if 2drop false else frame-context ! true then ;
: frame-run ( x context frames -- result outcome )
  tuck frame-start if frame-call else 2drop -1 outcome-invalid then ;
