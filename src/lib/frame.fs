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
\ (frame-save, frame-restore, frame-pick, frame-drop). The visit's
\ admission makes room for frame-spare cells above what it pushes itself,
\ and a refused child makes none: so from its admission to its return the
\ cells a visit holds at once -- every value it saved and not yet took
\ back, and every continuation step it pushed itself -- never exceed
\ frame-spare, counted over all its steps. Only the block is checked
\ (frame-save): a visit that holds more than its share may still fit in
\ the block, but one that would write past it throws frame-overrun. A
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
\ and charged, once per path. A result of a frame-call or frame-under
\ visit outside the outcome vocabulary counts as invalid; a visit opened
\ by frame-open (another kind of visit, of its own results) keeps its
\ results as they are. The fuel-first rule covers only the
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
\ Heap: a record's block keeps the largest size its passes needed until
\ frame-free (a context's until the context is freed).
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
\   1000 tree frame-budget drop  10 0 tree frame-run . .   \ 0 (ok) 89
\   tree frame-free                                      \ prints: 0 89
\
\ Interface: /frames frame-fuel frame-depth frame-visitor frame-context
\ frame-job frame-block frame-used frame-capacity frame-spare frame-need
\ frame-init frames: frame-free frame-busy? frame-reset frame-budget
\ frame-overrun frame-save frame-restore frame-pick frame-drop
\ frame-sound? frame-room@ frame-room? frame-admit frame-refuse
\ frame-return frame-opened frame-left frame-open frame-call
\ frame-open-or frame-context+! frame-up frame-under frame-loop
\ frame-steps frame-through frame-start frame-run, public in lf-lib; the
\ stack's growth and the steps that open and end a visit are private (lf-lib-private;
\ ADR 0010).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./bounds.fs
require ./outcome.fs
require ./portability.fs
require ./module.fs

lf-lib-private module-open
lf-lib set-current

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
lf-lib-private set-current
16 constant frame-first-cells
lf-lib set-current

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

\ The stack. frame-save needs room (frame-spare, above): a save the block
\ cannot hold -- a step that broke the rule, or an unsound count --
\ throws frame-overrun instead of writing outside the block, a fault that
\ a check's CATCH turns into an invalid declaration, never a result.
\ Unchecked: frame-restore, frame-pick (cell i from the top, 0 the last
\ saved) and frame-drop (n cells) take cells saved by the same visit.
-4111 constant frame-overrun
lf-lib-private set-current
: frame-top ( frames -- addr ) dup frame-used @ cells swap frame-block @ + ;
: frame-held? ( frames -- flag ) dup frame-used @ swap frame-capacity @ u< ;
lf-lib set-current
: frame-save ( x frames -- )
  dup frame-held? 0= if frame-overrun throw then tuck frame-top ! 1 swap frame-used +! ;
: frame-restore ( frames -- x ) -1 over frame-used +! frame-top @ ;
: frame-pick ( i frames -- x ) frame-top swap 1+ cells - @ ;
: frame-drop ( n frames -- ) frame-used swap negate swap +! ;
\ Room for n more cells: true, or false when the heap refuses the larger
\ block (the stack is then unchanged). 0 <= used <= capacity (sound).
: frame-sound? ( frames -- flag ) dup frame-used @ 0 rot frame-capacity @ between? ;
\ The cells in use and the capacity, as diagnostics record them.
: frame-room@ ( frames -- used capacity ) dup frame-used @ swap frame-capacity @ ;
lf-lib-private set-current
: frame-fits? ( n frames -- flag ) dup frame-capacity @ swap frame-used @ - > 0= ;
\ The size to grow to: at least what n more cells need, double the
\ capacity and frame-first-cells, at most the cells a cell can count in
\ address units (doubling past that would wrap; RESIZE refuses before).
max-n 1 cells / constant frame-most-cells
: frame-size ( n frames -- cells )
  tuck frame-used @ + swap frame-capacity @ frame-most-cells 2/ min 2* max
  frame-first-cells max frame-most-cells min ;
\ A size that still does not hold n more cells (only past
\ frame-most-cells) is refused like a heap that refuses.
: frame-short? ( n cells frames -- flag ) frame-used @ rot + < ;
: frame-grow ( n frames -- flag )
  2dup frame-size 2dup 2>r swap frame-short? if 2r> 2drop false exit then 2r>
  dup cells 2 pick frame-block @ ?dup if swap resize else allocate then
  if 2drop drop false else rot tuck frame-block ! frame-capacity ! true then ;
lf-lib set-current
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
: frame-refuse ( x frames cont outcome -- -1 outcome frames cont )
  2>r nip -1 swap 2r> -rot ;
lf-lib-private set-current
\ The step that ends every visit: one frame less, the result made sane.
: frame-exit ( result outcome frames -- result outcome' frames 0 )
  -1 over frame-depth +! swap outcome-sane swap 0 ;
lf-lib set-current
\ The step that only returns, the continuation of a root (frame-run) or of
\ a visit whose result is its parent's (a tail call: mixed-beta.fs).
: frame-return ( frames -- frames 0 ) 0 ;
lf-lib-private set-current
: frame-enter ( frames -- frames visitor )
  -1 over frame-fuel +! 1 over frame-depth +! dup frame-visitor @ ;
lf-lib set-current
: frame-opened ( x frames cont -- x frames visitor )
  over frame-save ['] frame-exit over frame-save frame-enter ;
\ For a pass whose visits are of several kinds (mixed-infer.fs), or that
\ keeps its own fuel (level-normalize.fs, level-geq.fs): open a visit
\ whose room the caller made (frame-admit, or frame-need frame-room?),
\ whose first step is xt, with values of any kind below the record,
\ continuing with cont. It spends the record's fuel, which a pass with
\ its own leaves unused, and ends with frame-left: one frame less, the
\ results as they are.
: frame-left ( frames -- frames 0 ) -1 over frame-depth +! 0 ;
: frame-open ( frames cont xt -- frames xt )
  >r over frame-save ['] frame-left over frame-save frame-enter drop r> ;
: frame-call ( x frames cont -- x frames visitor | -1 outcome frames cont )
  over frame-admit dup ok? if drop frame-opened else frame-refuse then ;
\ frame-open after frame-admit: xt, or, when the record refuses the visit,
\ refuse ( frames cont outcome -- ... ) on its outcome (a pass's own
\ diagnostic and failure, such as defeq.fs's and whnf.fs's).
: frame-open-or ( frames cont xt refuse -- frames xt | ... )
  2>r over frame-admit dup ok? if drop 2r> drop frame-open else 2r> nip execute then ;
\ One context level deeper, restored when the visit returns. The visit
\ must open (frame-admit, so the fuel decides before the context), and
\ then a context that cannot grow (max-n) is full; a refused visit changes
\ nothing.
: frame-context+! ( n frames -- ) frame-context +! ;
: frame-up ( result outcome frames -- result outcome frames 0 )
  -1 over frame-context+! 0 ;
lf-lib-private set-current
: frame-deeper ( frames -- outcome )
  dup frame-admit ok-then? if frame-context @ max-n <> room>outcome then ;
lf-lib set-current
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
\ Run one visit to its end, as a loop of its own from what the stack
\ holds: call ( i*x frames cont -- ... frames next ) asks for it
\ (frame-call, or a pass's own word), continuing with frame-return.
: frame-through ( i*x frames call -- j*x frames )
  over frame-used @ >r >r ['] frame-return r> execute r> frame-loop ;

\ A pass: an idle record takes the root's context, then the root is
\ visited. A busy record refuses, changing nothing: no result, invalid.
: frame-start ( context frames -- flag )
  dup frame-busy? if 2drop false else frame-context ! true then ;
: frame-run ( x context frames -- result outcome )
  tuck frame-start if ['] frame-call frame-through drop else 2drop -1 outcome-invalid then ;

module-close
base !   \ the BASE this file was loaded with
