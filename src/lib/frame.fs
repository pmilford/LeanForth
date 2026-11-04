\ Passes that visit a DAG node by node on an explicit, growable stack
\ (plan task 6.2.0), so that no pass's depth is bounded by the host's
\ stacks or by a constant. A frames record holds the fuel left, the
\ number of visits in progress (frames), the visitor, a context cell for
\ the visit in progress (such as the number of binders around its node), a
\ job cell for the pass's own use, 0 unless it sets one, and the pass's
\ stack: a heap block of cells that grows by doubling. A record stands
\ alone (frames:) or is a field of a larger record (frame-init); a record
\ in use holds a heap block until frame-free. A pass whose record is a
\ member of a checker context (lib/context.fs) must not keep an address in
\ the job cell, since the address of a context member goes stale when the
\ main context moves while modules load: it embeds the frames first in its
\ own record, so the visitor finds the pass's inputs at the frames address
\ it is given (mixed-shift.fs). Every word here takes the record's
\ address, so separate records are independent and this module has no
\ state.
\
\ Steps. A visit is a chain of steps, words ( i*x frames -- j*x frames
\ next ) that a loop runs one after another, so visits never nest on the
\ host's stacks. A step ends in one of two ways:
\ - it asks for the visit of a child with frame-call or frame-under,
\   naming the step that continues once the child's visit returns; that
\   step then gets the child's ( result outcome ) below the record;
\ - it returns its visit's result: ( result outcome frames 0 ).
\ The visitor ( x frames -- ... frames next ) is a visit's first step. A
\ value a visit keeps across a child's visit goes on the pass's stack
\ (frame-save, frame-restore): after the visit's admission or a child's
\ return, a step may save up to frame-spare cells without a check, and a
\ visit takes back everything it saved before it returns.
\
\ frame-call spends one unit of fuel and one frame and runs the visitor on
\ x; frame-under does the same one context level deeper, restored when
\ the visit returns (a context at max-n cannot grow: full). They visit
\ nothing when no fuel is left (exhausted) or when the stack cannot grow
\ for the visit (full: the heap refuses); with neither, the fuel decides:
\ exhausted. A record whose stack counts are out of range is corrupted,
\ which is invalid. A refused visit returns -1 and the outcome to the
\ continuing step at once. A node shared by several parents is visited,
\ and charged, once per path. A visitor result outside the outcome
\ vocabulary counts as invalid. The fuel-first rule covers only the
\ admission of a visit here: a limit that a visitor checks itself, inside
\ a visit already paid for (such as mixed-rebuild.fs's binder check), is
\ independent of fuel (ADR 0008).
\
\ A record is busy while a visit is in progress. A busy record refuses a
\ new budget and a new pass, so a pass cannot be restarted from inside
\ itself. A THROW out of a step leaves the record busy, its context and
\ stack changed: the code that catches it must discard whatever the pass
\ changed and call frame-reset.
\
\ Host stacks: a pass holds a constant number of cells of them whatever
\ its depth -- the loop, one step at a time, and what that step calls. A
\ step may run another pass on another record (beta runs instantiate,
\ which runs shift), which nests that pass's loop, still a constant.
\
\ Example: count the leaves of a binary tree whose node n > 1 has the
\ children n - 1 and n - 2, saving the first count across the second
\ child's visit.
\   : leaves-sum ( b outcome frames -- n outcome frames 0 )
\     >r r@ frame-restore over ok? if rot + swap else drop then r> 0 ;
\   : leaves-second ( a outcome frames -- x frames next | -1 outcome frames 0 )
\     >r dup ok? 0= if r@ frame-restore drop r> 0 exit then drop
\     r@ frame-restore 2 - swap r@ frame-save r> ['] leaves-sum frame-call ;
\   : leaves-visit ( n frames -- x frames next | n outcome frames 0 )
\     over 2 < if >r drop 1 outcome-ok r> 0 exit then
\     2dup frame-save swap 1- swap ['] leaves-second frame-call ;
\   ' leaves-visit frames: tree
\   1000 tree frame-budget drop  10 0 tree frame-run   \ 89 ok, 177 visits
\   tree frame-free

require ./bounds.fs
require ./outcome.fs
require ./portability.fs

begin-structure /frames
  field: frame-fuel      \ visits left
  field: frame-depth     \ visits in progress
  field: frame-visitor   \ xt ( x frames -- ... frames next ), the first step
  field: frame-context   \ context of the visit in progress
  field: frame-job       \ for the pass; never a context member's address
  field: frame-block     \ the stack's heap block, or 0
  field: frame-used      \ cells on the stack
  field: frame-capacity  \ cells the block holds
end-structure

\ Cells a step may save without checking (see Steps above), and the room
\ a visit's admission makes: its own continuation cells and that many.
8 constant frame-spare
3 frame-spare + constant frame-need
16 constant frame-first-cells

\ Initialise a record in place: idle, no fuel, no job, an empty stack, the
\ visitor xt, which is set once here. frames: defines a standalone record,
\ name ( -- frames ). frame-free gives the stack's block back; the record
\ stays usable (its stack starts again empty).
: frame-init ( xt frames -- ) dup /frames erase frame-visitor ! ;
: frames: ( xt "name" -- ) create here /frames allot frame-init ;
: frame-free ( frames -- )
  dup frame-block @ ?dup if free drop then
  0 over frame-block ! 0 over frame-used ! 0 swap frame-capacity ! ;

\ Busy while a visit is in progress (or after a THROW out of one); a
\ corrupted depth also counts as busy. frame-reset makes a record idle,
\ its stack empty.
: frame-busy? ( frames -- flag ) frame-depth @ 0<> ;
: frame-reset ( frames -- ) 0 over frame-depth ! 0 swap frame-used ! ;

\ Set the budget for a pass. A negative fuel or a busy record is refused
\ and stores nothing.
: frame-budget ( fuel frames -- flag )
  over 0< over frame-busy? or if 2drop false else frame-fuel ! true then ;

\ The stack. Unchecked: frame-save needs room (frame-spare, above), and
\ frame-restore, frame-pick (cell i from the top, 0 the last saved) and
\ frame-drop (n cells) cells saved by the same visit.
: frame-top ( frames -- addr ) dup frame-used @ cells swap frame-block @ + ;
: frame-save ( x frames -- ) tuck frame-top ! 1 swap frame-used +! ;
: frame-restore ( frames -- x ) -1 over frame-used +! frame-top @ ;
: frame-pick ( i frames -- x ) frame-top swap 1+ cells - @ ;
: frame-drop ( n frames -- ) frame-used swap negate swap +! ;
\ Room for n more cells: true, or false when the heap refuses the larger
\ block (the stack is then unchanged). 0 <= used <= capacity (sound).
: frame-sound? ( frames -- flag ) dup frame-used @ 0 rot frame-capacity @ between? ;
: frame-fits? ( n frames -- flag ) dup frame-capacity @ swap frame-used @ - > 0= ;
: frame-size ( n frames -- cells )
  tuck frame-used @ + swap frame-capacity @ 2* max frame-first-cells max ;
: frame-grow ( n frames -- flag )
  tuck frame-size dup cells 2 pick frame-block @ ?dup if swap resize else allocate then
  if 2drop drop false else rot tuck frame-block ! frame-capacity ! true then ;
: frame-room? ( n frames -- flag ) 2dup frame-fits? if 2drop true else frame-grow then ;

\ Visiting. A visit opens (ok) when the stack is sound, fuel is left and
\ the stack has room for the visit; otherwise the stack decides first
\ (unsound is invalid), then the fuel (none left, or a corrupted negative
\ fuel, is exhausted), then the room (full). Signed comparisons.
: frame-admit ( frames -- outcome )
  dup frame-sound? 0= if drop outcome-invalid exit then
  dup frame-fuel @ 0> 0= if drop outcome-exhausted exit then
  frame-need swap frame-room? room>outcome ;
\ A refused visit continues at once with no result and the outcome.
: frame-refuse ( x frames cont outcome -- -1 outcome frames cont ) 2>r nip -1 swap 2r> -rot ;
\ The step that ends every visit: one frame less, the result made sane.
: frame-exit ( result outcome frames -- result outcome' frames 0 )
  -1 over frame-depth +! swap outcome-sane swap 0 ;
\ The step that only returns, the continuation of a root (frame-run) or of
\ a visit whose result is its parent's (a tail call: mixed-beta.fs).
: frame-return ( frames -- frames 0 ) 0 ;
: frame-enter ( frames -- frames visitor )
  -1 over frame-fuel +! 1 over frame-depth +! dup frame-visitor @ ;
: frame-opened ( x frames cont -- x frames visitor )
  over frame-save ['] frame-exit over frame-save frame-enter ;
\ For a pass whose visits are of several kinds (mixed-infer.fs): open a
\ visit that frame-admit admitted, whose first step is xt, with values of
\ any kind below the record, continuing with cont. It ends with
\ frame-left: one frame less, the results as they are.
: frame-left ( frames -- frames 0 ) -1 over frame-depth +! 0 ;
: frame-open ( frames cont xt -- frames xt )
  >r over frame-save ['] frame-left over frame-save frame-enter drop r> ;
: frame-call ( x frames cont -- x frames visitor | -1 outcome frames cont )
  over frame-admit dup ok? if drop frame-opened else frame-refuse then ;
\ One context level deeper, restored when the visit returns. The visit
\ must open (frame-admit, so the fuel decides before the context), and
\ then a context that cannot grow (max-n) is full; a refused visit changes
\ nothing.
: frame-context+! ( n frames -- ) frame-context +! ;
: frame-up ( result outcome frames -- result outcome frames 0 ) -1 over frame-context+! 0 ;
: frame-deeper ( frames -- outcome )
  dup frame-admit ok-then? if frame-context @ max-n <> room>outcome then ;
: frame-under ( x frames cont -- x frames visitor | -1 outcome frames cont )
  over frame-deeper dup ok? 0= if frame-refuse exit then drop
  over frame-save ['] frame-up over frame-save 1 over frame-context+!
  ['] frame-exit over frame-save frame-enter ;

\ The loop: run steps until a return finds the stack at base, the cells it
\ held before the first step. Unchecked: every step keeps the stack's
\ discipline (above). A step may run a loop of its own on the same record
\ from the cells then in use (mixed-infer.fs).
: frame-loop ( i*x frames next base -- j*x frames )
  >r begin dup 0= if drop dup frame-used @ r@ = if r> drop exit then dup frame-restore then
    execute again ;
\ Run the step xt, and the steps it leads to, to its return.
: frame-steps ( i*x frames xt -- j*x frames ) over frame-used @ frame-loop ;

\ A pass: an idle record takes the root's context, then the root is
\ visited. A busy record refuses, changing nothing: no result, invalid.
: frame-start ( context frames -- flag )
  dup frame-busy? if 2drop false else frame-context ! true then ;
: frame-run ( x context frames -- result outcome )
  tuck frame-start 0= if 2drop -1 outcome-invalid exit then
  dup frame-used @ >r ['] frame-return frame-call r> frame-loop drop ;
