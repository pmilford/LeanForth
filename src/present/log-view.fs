\ Reading the derivation log for printing (ADR 0013 L7, plan task 2.4.4):
\ the formulas of the log's records, printed by the term printer in the
\ scope of the binders around each step, and the list of every step that
\ the proof outline's --detail shows. Untrusted presentation code: the
\ checker never loads it, and nothing it prints is evidence of anything.
\
\ Formulas. An input object (a reference n >= 0) is printed from the
\ stores. A copy from the log's pools is first rebuilt as scratch nodes
\ above the input marks (lf-lv-term), printed, and then rolled back with
\ lf-input-rollback (lf-lv-release): the printer never prints a formula
\ the checker did not compute, and the input below the marks is never
\ written. So it runs only between checks, in the context that ran the
\ check, with its input intact; the scratch it allocates advances the
\ stores' identity serials, as a check does. A copied lambda or Pi takes
\ its binder name from the side table entry of the input node it was
\ made from: the lambda whose type it is (a lambda step), or the node a
\ shift, an instantiation or a universe instantiation rebuilt (lf-lv-names);
\ otherwise it prints as x, as the printer does.
\
\ Scopes. A record at depth d lies under d binders; the binder at depth k
\ is the subject of the nearest later lambda or Pi step at depth k whose
\ sub-derivation holds the record (lf-lv-scope-of). A formula is printed
\ open, under those binders' names (lf-print-scoped).
\
\ Text. Each line is built in a buffer by the term printer's sink and the
\ words below, then written to the output sink (default TYPE), padded by
\ characters (UTF-8 aware) where a column is wanted.
\ Depth (plan task 6.2.0): the walks over a formula's structure (naming
\ copies, rebuilding them, lf-ol-mentions in proof-outline.fs) and the
\ scope of binders run on growable stacks and arrays (lib/walk.fs,
\ lib/slab.fs), so no depth of a formula is tied to the host's stacks or
\ to a constant: a formula prints as "?" only when the heap refuses, the
\ log lacks it or the print fails. A rollback that fails (lf-lv-release)
\ is counted, and nothing is rebuilt after it.
\ State: one cell of the checker context, lf-lv-held, pointing to a heap
\ block (about 37 KB) that exists only while printing (lf-lv-setup to
\ lf-lv-done; lf-lv-open for a test that rebuilds formulas directly): the
\ output sink, the line buffer, the formula fuel, the rebuilt copies and
\ the names of copies; the context's teardown frees a block left by a
\ THROW. Beside it, growable members of the context: the scope's binder
\ nodes, a rebuilt reference's levels, and three walk records. Requires
\ a check's log in the current context.

require ./term-printer.fs
require ../lib/bytes.fs
require ../core/derivation-log.fs
require ../core/input.fs

1024 constant lf-lv-buffer-size

begin-structure /lf-lv
  field: lf-lv-sink          \ xt ( c-addr u -- ) of the finished text
  field: lf-lv-used          \ bytes in the line buffer
  field: lf-lv-fuel          \ fuel of each formula
  field: lf-lv-bad           \ formulas that failed to print
  field: lf-lv-lost          \ rollbacks that failed
  field: lf-lv-depth         \ binders in the scope
  field: lf-lv-tex           \ true: LaTeX style (lf-lv-latex!)
  field: lf-lv-mathing       \ open math groups in the line (LaTeX style)
  field: lf-lv-declname         \ xt ( id -- c-addr u flag ) of a declaration's name, or 0
  field: lf-lv-escape        \ xt ( c-addr u -- c-addr' u' flag ) escaping any text, or 0
  lf-log-term-capacity cells +field lf-lv-made      \ copy k's rebuilt term + 1, -1, or 0
  lf-log-level-capacity cells +field lf-lv-lmade    \ copy k's rebuilt level + 1, -1, or 0
  lf-log-term-capacity cells +field lf-lv-namer      \ input binder naming copy k, + 1
  lf-lv-buffer-size +field lf-lv-buffer
end-structure
1 cells context-record: lf-lv-held
\ A rebuilt reference's levels, as many as it has, and the scope's binder
\ nodes, outermost first, as many as there are (no fixed limit).
2 cells context-slab: lf-lv-pair-cells
1 cells context-slab: lf-lv-scope-cells
: lf-lv ( -- addr ) lf-lv-held @ ;
\ The block: made zeroed when there is none (false without memory), or
\ zeroed again when a THROW left one held (no count of failed rollbacks or
\ rebuilt copy survives into the next print); and given back. A FREE that
\ fails keeps the block recorded, so that the teardown tries again and
\ reports it.
: lf-lv-open ( -- flag )
  lf-lv ?dup if /lf-lv erase true exit then
  /lf-lv allocate0 if drop false exit then lf-lv-held ! true ;
: lf-lv-close ( -- ior )
  lf-lv dup 0= if exit then free dup 0= if 0 lf-lv-held ! then ;
:noname ( -- ) lf-lv-close throw ; context-teardown

\ Text: the buffer, the output, numbers, padding by characters.
: lf-lv-text ( -- c-addr u ) lf-lv lf-lv-buffer lf-lv lf-lv-used @ ;
: lf-lv-clear ( -- ) 0 lf-lv lf-lv-used ! ;
: lf-lv-room ( -- n ) lf-lv-buffer-size lf-lv lf-lv-used @ - ;
\ The outline's text goes into the buffer as it is (lf-lv-put-raw) or, in plain
\ style when the caller gave an escaping word (lf-outline-names!), escaped, so
\ that a name in a formula cannot start a line of its own; text that cannot
\ be escaped (no heap) shows as ?.
: lf-lv-put-raw ( c-addr u -- )
  lf-lv-room min tuck lf-lv-text + swap move lf-lv lf-lv-used +! ;
: lf-lv-safe ( c-addr u -- c-addr' u' )
  lf-lv lf-lv-escape @ ?dup 0= if exit then lf-lv lf-lv-tex @ if drop exit then
  execute 0= if 2drop s" ?" then ;
: lf-lv-put ( c-addr u -- ) lf-lv-safe lf-lv-put-raw ;
: lf-lv-out ( c-addr u -- ) lf-lv lf-lv-sink @ ?dup if execute else type then ;
: lf-lv-n ( n -- ) dup 0< if s" -" lf-lv-put negate then lf-pp-digits lf-lv-put ;
: lf-lv-chars ( c-addr u -- n )
  0 -rot begin dup while 2dup utf8-length 1 max /string rot 1+ -rot repeat 2drop ;
create lf-lv-blanks 64 allot lf-lv-blanks 64 bl fill
: lf-lv-blank-run ( n -- ) begin dup 0> while lf-lv-blanks over 64 min lf-lv-out
  64 - repeat drop ;
\ LaTeX style (lf-lv-latex!, used by the proof outline): n blanks are n
\ space widths of the font, a column ends with & and a line with \\.
: lf-lv-tex? ( -- flag ) lf-lv lf-lv-tex @ 0<> ;
: lf-lv-hspace ( n -- )
  dup 0> 0= if drop exit then s" \hspace*{" lf-lv-out lf-pp-digits lf-lv-out
  s" \fontdimen2\font}" lf-lv-out ;
: lf-lv-spaces ( n -- ) lf-lv-tex? if lf-lv-hspace else lf-lv-blank-run then ;
\ Write the buffer, padded with spaces to width characters, and empty it.
: lf-lv-flush ( width -- )
  lf-lv-text lf-lv-out lf-lv-text lf-lv-chars - lf-lv-spaces lf-lv-clear ;
: lf-lv-cr ( -- ) s\" \n" lf-lv-out ;
\ A table column ends: padded to width in plain style, & in LaTeX style.
: lf-lv-col ( width -- )
  lf-lv-tex? if drop 0 lf-lv-flush s"  & " lf-lv-out else lf-lv-flush then ;
\ A line ends: with \\ in LaTeX style. A blank line is a paragraph break there.
: lf-lv-eol ( -- ) lf-lv-tex? if s"  \\" lf-lv-out then lf-lv-cr ;
: lf-lv-gap ( -- ) lf-lv-tex? if s\" \\par\n" lf-lv-out else lf-lv-cr then ;
: lf-lv-step ( s -- ) s" s" lf-lv-put lf-lv-n ;

\ The records' fields.
: lf-lv-rule ( s -- rule ) lf-log-rule@ ;
: lf-lv-a ( s -- ref ) lf-log-a@ ;
: lf-lv-b ( s -- ref ) lf-log-b@ ;
: lf-lv-out-ref ( s -- ref ) lf-log-out@ ;
: lf-lv-depth@ ( s -- d ) lf-log-depth@ ;
: lf-lv-start ( s -- start ) lf-log-premise ;
: lf-lv-outcome ( s -- outcome ) lf-log-outcome@ ;
: lf-lv-binder-rule? ( rule -- flag ) dup lf-rule-lambda = swap lf-rule-pi = or ;
: lf-lv-infer-rule? ( rule -- flag ) lf-rule-sort lf-rule-form between? ;

\ Premises: s-1, then each start of the last, while above s's start and
\ strictly earlier than the one before (a log that passed the validator
\ always is; the guard keeps a damaged one from looping).
\ lf-lv-premises counts them; lf-lv-premise gives the i-th, ascending.
: lf-lv-earlier ( p -- p' ) dup lf-log-premise tuck > 0= if drop 0 then ;
: lf-lv-premises ( s -- n )
  dup lf-lv-start >r 0 swap 1- begin dup r@ > over 0> and while swap 1+ swap lf-lv-earlier
  repeat drop r> drop ;
: lf-lv-premise ( s i -- p )
  over lf-lv-premises swap - 1- swap 1- swap 0 ?do lf-log-premise loop ;
\ The i-th premise (ascending) that is an inference step.
: lf-lv-inference ( s i -- p true | false )
  swap dup lf-lv-premises 0 ?do dup i lf-lv-premise dup lf-lv-rule lf-lv-infer-rule?
    if rot ?dup 0= if nip true unloop exit then 1- -rot then drop
  loop 2drop false ;

\ Scopes: the binder at depth k around step s, and all d of them.
: lf-lv-encloses? ( s r k -- flag )
  over lf-lv-depth@ = >r dup lf-lv-rule lf-lv-binder-rule? >r lf-lv-start
  > r> r> and and ;
: lf-lv-binder ( s k -- r true | false )
  over lf-log-count 1+ swap 1+ ?do over i 2 pick lf-lv-encloses?
    if 2drop i true unloop exit then loop 2drop false ;
: lf-lv-scope! ( node k -- ) lf-lv-scope-cells slab-at ! ;
\ Room for d binders in the scope (false for a negative d, or when the
\ heap refuses).
: lf-lv-scope-room? ( d -- flag )
  dup 0< if drop false else lf-lv-scope-cells slab-hold ok? then ;
\ Fill the scope with step s's binders: their number, or -1 when one of
\ them is not in the log (a step of the rejection analysis) or there is
\ no room for them.
: lf-lv-scope-of ( s -- d )
  dup lf-lv-depth@ dup lf-lv-scope-room? 0= if 2drop -1 exit then
  dup 0 ?do over i lf-lv-binder 0= if 2drop -1 unloop exit then lf-lv-a i
  lf-lv-scope! loop
  nip ;
\ Bring node into the scope set, as its innermost binder: false, the
\ scope unchanged, when the heap has no room for it.
: lf-lv-depth+ ( node k -- ) lf-lv-scope! 1 lf-lv lf-lv-depth +! ;
: lf-lv-push ( node -- flag )
  lf-lv lf-lv-depth @ dup 1+ lf-lv-scope-room?
  if lf-lv-depth+ true else 2drop false then ;

\ Names of copies (see the header), computed once per log: the input
\ binder (or the copy's name source) that a copy of a lambda or Pi was
\ made from.
: lf-lv-namer@ ( k -- addr ) cells lf-lv lf-lv-namer + ;
: lf-lv-name-of ( ref -- node true | false )
  dup 0< 0= if true exit then
  dup lf-log-copy? 0= if drop false exit then
  lf-log-copy-index lf-lv-namer@ @ 1- dup 0< if drop false else true then ;
: lf-lv-name! ( node k -- ) lf-lv-namer@ dup @ if 2drop else swap 1+ swap ! then ;
\ A reference's node: tag first second, from the stores or the pool.
: lf-lv-node ( ref -- tag first second true | false )
  dup 0< 0= if lf-term-read exit then
  dup lf-log-copy? 0= if drop false exit then
  lf-log-copy-index dup lf-log-term-copies < if lf-log-term-node@ true else
  drop false then ;
\ Walk an input-or-copy reference a and a copy reference out of the same
\ shape together, naming each copied node from its partner (only lambda
\ and Pi nodes have names in the side table): a paired walk (lib/walk.fs)
\ of (a, out), first children before second ones, with the formula fuel.
\ Below an input object (out >= 0) every node is input, so the walk stops
\ there; a walk that runs out of fuel or room leaves the rest unnamed.
lf-walk-room context-walk2: lf-lv-pairs
: lf-lv-pair-name ( a out -- )
  dup lf-log-copy? 0= if 2drop exit then
  swap lf-lv-name-of if swap lf-log-copy-index lf-lv-name! else drop then ;
: lf-lv-tag ( ref -- tag true | false ) lf-lv-node if 2drop true else false then ;
: lf-lv-alike? ( a out -- flag )
  lf-lv-tag 0= if drop false exit then swap lf-lv-tag 0= if drop false exit then = ;
\ Part 1 (first) or 2 (second) of a reference to a binary node.
: lf-lv-child-ref ( ref part -- ref' true | false )
  swap lf-lv-node 0= if drop false exit then
  2 pick lf-term-binary-tag? 0= if 2drop 2drop false exit then
  rot drop rot 1 = if drop else nip then true ;
: lf-lv-both ( a out part -- a' out' true | false )
  tuck lf-lv-child-ref 0= if 2drop false exit then
  -rot lf-lv-child-ref 0= if drop false exit then swap true ;
\ Push the pair of parts (when both are there), the second first.
: lf-lv-push-part ( a out part walk -- outcome )
  >r lf-lv-both if r> walk-pair-outcome else r> drop outcome-ok then ;
: lf-lv-pair-parts ( a out walk -- outcome )
  >r 2dup 2 r@ lf-lv-push-part dup ok?
  if drop 1 r> lf-lv-push-part else nip nip r> drop then ;
: lf-lv-pair-visit ( walk -- outcome )
  dup walk-node @ over walk-context @ 2dup lf-lv-pair-name
  dup lf-log-copy? 0= if 2drop drop outcome-ok exit then
  2dup lf-lv-alike? if rot lf-lv-pair-parts else 2drop drop outcome-ok then ;
: lf-lv-parallel ( a out -- )
  lf-lv lf-lv-fuel @ lf-lv-pairs walk-budget drop
  ['] lf-lv-pair-visit lf-lv-pairs walk-run-pair drop ;
: lf-lv-rebuilt? ( rule -- flag )
  dup lf-rule-shift = over lf-rule-instantiate = or swap lf-rule-instantiate-levels = or ;
\ A lambda's type: each Pi down its spine named from the lambda at the
\ same place in the subject's, as Lean's mk_pi takes the binders' names
\ (since plan task 4.2.2a each lambda's type is made afresh over its free
\ variable, so the inner Pis are not the inner steps' copies).
: lf-lv-tag? ( ref tag -- flag ) swap lf-lv-tag if = else drop false then ;
: lf-lv-lam-pi? ( a out -- flag ) lf-tag-pi lf-lv-tag? swap lf-tag-lam lf-lv-tag? and ;
: lf-lv-spine ( a out -- )
  begin 2dup lf-lv-pair-name 2dup lf-lv-lam-pi? while 2 lf-lv-both 0= if exit then
  repeat 2drop ;
: lf-lv-name-step ( s -- )
  dup lf-lv-rule lf-rule-lambda = if dup lf-lv-a swap lf-lv-out-ref
  lf-lv-spine exit then
  dup lf-lv-rule lf-lv-rebuilt? if dup lf-lv-a swap lf-lv-out-ref lf-lv-parallel
  exit then drop ;
: lf-lv-names ( -- )
  lf-lv lf-lv-namer lf-log-term-capacity cells erase
  lf-log-count 0 ?do i 1+ lf-lv-name-step loop ;

\ Rebuilding copies as scratch nodes, children first, named from the side
\ table. A copy's children are input objects or earlier copies: the log
\ appends a copy after its children. So a copy is rebuilt in two passes,
\ each with no depth on the host's stacks: a walk (lib/walk.fs) from it
\ marks every copy it needs that is not made yet (-1 in its cell; a child
\ copy that is not earlier, only in a damaged log, fails it), then the
\ marked copies are built in the log's order, so each finds its children
\ made. A walk has fuel enough for every copy (each is marked once); one
\ that fails, or a build that fails, leaves no mark. Levels refer only to
\ levels, so a term's build may rebuild its levels, nesting once.
: lf-lv-made@ ( k -- addr ) cells lf-lv lf-lv-made + ;
: lf-lv-lmade@ ( k -- addr ) cells lf-lv lf-lv-lmade + ;
: lf-lv-made? ( addr -- index true | false ) @ dup 0> if 1- true else drop false then ;
: lf-lv-unmarked ( addr -- ) dup @ -1 = if 0 swap ! else drop then ;
: lf-lv-valid ( index flag -- index true | false ) dup 0= if nip then ;
: lf-lv-lost? ( -- flag ) lf-lv lf-lv-lost @ 0<> ;
\ A reference's copy index, when it names a copy the pool holds.
: lf-lv-copy-index ( ref copies -- k true | false )
  over lf-log-copy? 0= if 2drop false exit then
  swap lf-log-copy-index tuck > dup 0= if nip then ;

\ Levels. A child copy goes on the walk's stack (which checks that it is
\ earlier than its parent); the walk skips one marked or made.
lf-walk-room context-walk: lf-lv-level-work
: lf-lv-lcopy ( ref -- k true | false ) lf-log-level-copies lf-lv-copy-index ;
\ A level reference whose node is made already: input, or a rebuilt copy.
: lf-lv-level-known ( ref -- level true | false )
  dup 0< 0= if dup lf-level-valid? lf-lv-valid exit then
  lf-lv-lcopy if lf-lv-lmade@ lf-lv-made? else false then ;
: lf-lv-lmark-child ( ref walk -- outcome )
  swap lf-lv-lcopy if over walk-child nip else drop outcome-ok then ;
: lf-lv-lmark-pair ( first second walk -- outcome )
  tuck lf-lv-lmark-child ok-then? if lf-lv-lmark-child else nip then ;
: lf-lv-lmark-kids ( tag first second walk -- outcome )
  >r rot dup lf-level-tag-succ = if 2drop r> lf-lv-lmark-child exit then
  lf-level-binary-tag? if r> lf-lv-lmark-pair else 2drop r> drop outcome-ok then ;
: lf-lv-lmark ( walk -- outcome )
  dup walk-node @ lf-lv-lmade@ dup @ if 2drop outcome-ok exit then -1 swap !
  dup >r walk-node @ lf-log-level-node@ r> lf-lv-lmark-kids ;
: lf-lv-lmarked ( k -- outcome )
  max-n lf-lv-level-work walk-budget drop ['] lf-lv-lmark lf-lv-level-work walk-run ;
: lf-lv-lchild ( ref -- level true | false ) lf-lv-level-known ;
: lf-lv-lfields ( tag first second -- tag first' second' true | false )
  2 pick lf-level-tag-succ = if swap lf-lv-lchild 0= if 2drop false exit then
  swap true exit then
  2 pick lf-level-binary-tag? 0= if true exit then
  swap lf-lv-lchild 0= if 2drop false exit then swap
  lf-lv-lchild 0= if 2drop false exit then true ;
: lf-lv-lbuild ( k -- level true | false )
  dup lf-log-level-node@ lf-lv-lfields 0= if drop false exit then
  lf-level-add 0= if drop false exit then dup 1+ rot lf-lv-lmade@ ! true ;
: lf-lv-lready ( k -- flag )
  dup lf-lv-lmade@ @ -1 = if lf-lv-lbuild dup if nip then else drop true then ;
: lf-lv-lbuilt? ( k -- flag )
  1+ 0 ?do i lf-lv-lready 0= if false unloop exit then loop true ;
: lf-lv-lunmark ( k -- ) 1+ 0 ?do i lf-lv-lmade@ lf-lv-unmarked loop ;
: lf-lv-lnew ( k -- level true | false )
  dup lf-lv-lmarked ok? if dup lf-lv-lbuilt? if lf-lv-lmade@ lf-lv-made? exit then then
  lf-lv-lunmark false ;
: lf-lv-level-copy ( k -- level true | false )
  dup lf-log-level-copies < 0= if drop false exit then
  dup lf-lv-lmade@ lf-lv-made? if nip true else lf-lv-lnew then ;
: lf-lv-level ( ref -- level true | false )
  lf-lv-lost? if drop false exit then
  dup 0< 0= if dup lf-level-valid? lf-lv-valid exit then
  dup lf-log-copy? if lf-log-copy-index lf-lv-level-copy else drop false then ;

\ A copied constant reference rebuilt: its universe arguments' levels
\ into the pairs buffer, then a reference with its name and those levels.
: lf-lv-pair! ( level i -- )
  >r dup lf-level-identity 0= if 0 then swap r> lf-lv-pair-cells slab-at 2! ;
: lf-lv-arg ( offset i -- flag )
  tuck + lf-log-arg-ref lf-lv-level if swap lf-lv-pair! true else drop false then ;
: lf-lv-args ( offset count -- flag )
  0 ?do dup i lf-lv-arg 0= if drop false unloop exit then loop drop true ;
: lf-lv-cref ( ref -- cref id true | false )
  lf-log-copy-index dup lf-log-cref-copies < 0= if drop false exit then
  lf-log-cref@ over >r r@ lf-lv-pair-cells slab-hold ok? 0=
  if 2drop 2drop r> drop false exit then
  swap lf-lv-args 0= if 2drop r> drop false exit then
  0 lf-lv-pair-cells slab-at r> lf-cref-new ;

\ Terms, as levels: application, lambda and Pi have two children.
lf-walk-room context-walk: lf-lv-term-work
: lf-lv-tcopy ( ref -- k true | false ) lf-log-term-copies lf-lv-copy-index ;
\ A term reference whose node is made already: input, or a rebuilt copy.
: lf-lv-term-known ( ref -- term true | false )
  dup 0< 0= if dup lf-term-valid? lf-lv-valid exit then
  lf-lv-tcopy if lf-lv-made@ lf-lv-made? else false then ;
: lf-lv-tmark-child ( ref walk -- outcome )
  swap lf-lv-tcopy if over walk-child nip else drop outcome-ok then ;
: lf-lv-tmark-pair ( first second walk -- outcome )
  tuck lf-lv-tmark-child ok-then? if lf-lv-tmark-child else nip then ;
: lf-lv-tmark-kids ( tag first second walk -- outcome )
  >r rot lf-term-binary-tag? if r> lf-lv-tmark-pair else 2drop r> drop outcome-ok then ;
: lf-lv-tmark ( walk -- outcome )
  dup walk-node @ lf-lv-made@ dup @ if 2drop outcome-ok exit then -1 swap !
  dup >r walk-node @ lf-log-term-node@ r> lf-lv-tmark-kids ;
: lf-lv-tmarked ( k -- outcome )
  max-n lf-lv-term-work walk-budget drop ['] lf-lv-tmark lf-lv-term-work walk-run ;
\ A leaf: a symbolic Sort's level rebuilt, a copied reference rebuilt.
: lf-lv-tleaf ( tag first second -- tag first' second' true | false )
  2 pick lf-tag-symbolic-sort = if swap lf-lv-level 0= if 2drop false exit then
    swap true exit then
  2 pick lf-tag-constant = 2 pick 0< and if drop lf-lv-cref 0= if drop false exit
  then then true ;
: lf-lv-tfields ( tag first second -- tag first' second' true | false )
  2 pick lf-term-binary-tag? 0= if lf-lv-tleaf exit then
  swap lf-lv-term-known 0= if 2drop false exit then swap
  lf-lv-term-known 0= if 2drop false exit then true ;
: lf-lv-named ( term k -- term )
  lf-lv-namer@ @ ?dup 0= if exit then 1- lf-pres-binder@ 0= if exit then
  2 pick -rot lf-pres-binder! drop ;
: lf-lv-tbuild ( k -- term true | false )
  dup lf-log-term-node@ lf-lv-tfields 0= if drop false exit then
  lf-term-add 0= if drop false exit then
  over lf-lv-named dup 1+ rot lf-lv-made@ ! true ;
: lf-lv-tready ( k -- flag )
  dup lf-lv-made@ @ -1 = if lf-lv-tbuild dup if nip then else drop true then ;
: lf-lv-tbuilt? ( k -- flag )
  1+ 0 ?do i lf-lv-tready 0= if false unloop exit then loop true ;
: lf-lv-tunmark ( k -- ) 1+ 0 ?do i lf-lv-made@ lf-lv-unmarked loop ;
: lf-lv-tnew ( k -- term true | false )
  dup lf-lv-tmarked ok? if dup lf-lv-tbuilt? if lf-lv-made@ lf-lv-made? exit then then
  lf-lv-tunmark false ;
: lf-lv-term-copy ( k -- term true | false )
  dup lf-log-term-copies < 0= if drop false exit then
  dup lf-lv-made@ lf-lv-made? if nip true else lf-lv-tnew then ;
: lf-lv-term ( ref -- term true | false )
  lf-lv-lost? if drop false exit then
  dup 0< 0= if dup lf-term-valid? lf-lv-valid exit then
  dup lf-log-copy? if lf-log-copy-index lf-lv-term-copy else drop false then ;
\ Forget the rebuilt nodes: the stores back to the input marks. A rollback
\ that fails is counted (then nothing more is rebuilt or printed).
: lf-lv-release ( -- )
  lf-input-rollback ok? 0= if 1 lf-lv lf-lv-lost +! then
  lf-lv lf-lv-made lf-log-term-capacity cells erase
  lf-lv lf-lv-lmade lf-log-level-capacity cells erase ;

\ Formulas into the line buffer: a term or a level reference in step s's
\ scope (or the scope already set, lf-lv-depth binders); "?" for one that
\ cannot be printed (unkept, not in the log, or a print that failed).
: lf-lv-fail ( -- ) s" ?" lf-lv-put 1 lf-lv lf-lv-bad +! ;
: lf-lv-printed ( outcome -- ) ok? 0= if lf-lv-fail then ;
: lf-lv-scope-set ( -- addr d ) lf-lv-scope-cells slab-base lf-lv lf-lv-depth @ ;
\ LaTeX style: a formula, a name or a level is math, between $ and $ (once
\ when groups nest: the sentence "Assume f : A → B." opens one around the
\ name and the type). The buffer may be full: the closing $ then replaces
\ its last byte, so that no math is left open.
: lf-lv-last-dollar ( -- )
  lf-lv-room 0= if -1 lf-lv lf-lv-used +! then s" $" lf-lv-put ;
: lf-lv-math-open ( -- )
  lf-lv-tex? 0= if exit then 1 lf-lv lf-lv-mathing +!
  lf-lv lf-lv-mathing @ 1 = if s" $" lf-lv-put then ;
: lf-lv-math-close ( -- )
  lf-lv-tex? 0= if exit then -1 lf-lv lf-lv-mathing +!
  lf-lv lf-lv-mathing @ 0= if lf-lv-last-dollar then ;
: lf-lv-term-here ( term -- )
  lf-lv-math-open lf-lv-scope-set lf-lv lf-lv-fuel @ lf-print-scoped lf-lv-printed
  lf-lv-math-close ;
: lf-lv-ref-here ( ref -- ) lf-lv-term if lf-lv-term-here else lf-lv-fail
  then lf-lv-release ;
: lf-lv-at ( s -- flag ) lf-lv-scope-of dup 0 max lf-lv lf-lv-depth ! 0< 0= ;
\ The reference ref in step s's scope.
: lf-lv-formula ( ref s -- ) lf-lv-at if lf-lv-ref-here else drop lf-lv-fail then ;
\ Child part (1 first, 2 second) of a term reference, in step s's scope;
\ "?" unless the term is an application, a lambda or a Pi.
: lf-lv-part-here ( term part -- )
  lf-lv-child-ref if lf-lv-term-here else lf-lv-fail then ;
: lf-lv-part ( ref part s -- )
  lf-lv-at 0= if 2drop lf-lv-fail exit then
  swap lf-lv-term if swap lf-lv-part-here else drop lf-lv-fail then lf-lv-release ;
\ A level reference.
: lf-lv-level-here ( ref -- )
  lf-lv-math-open
  lf-lv-level if lf-lv lf-lv-fuel @ lf-print-level lf-lv-printed else lf-lv-fail
  then lf-lv-release lf-lv-math-close ;
\ The display name of the innermost binder of the scope set; of node,
\ brought into it first ("?" when there is no room for it).
: lf-lv-name-here ( -- )
  lf-lv-math-open lf-lv-scope-set lf-lv lf-lv-fuel @ lf-print-scope-name lf-lv-printed
  lf-lv-math-close ;
: lf-lv-name-of-node ( node -- ) lf-lv-push if lf-lv-name-here else lf-lv-fail then ;
\ A shift's input lies under amount fewer binders than its step.
: lf-lv-fewer ( amount -- ) negate lf-lv lf-lv-depth +! lf-lv lf-lv-depth dup
  @ 0 max swap ! ;
: lf-lv-lifted ( ref amount s -- )
  lf-lv-at 0= if 2drop lf-lv-fail exit then lf-lv-fewer lf-lv-ref-here ;
\ An instantiation's or a contraction's body (under one more binder) and
\ argument, shown as the redex they form: (fun x ↦ body) argument.
: lf-lv-unbuilt ( x -- ) drop lf-lv-fail lf-lv-release ;
: lf-lv-redex ( body arg s -- )
  lf-lv-at 0= if 2drop lf-lv-fail exit then
  swap lf-lv-term 0= if lf-lv-unbuilt exit then dup lf-term-lam 0= if
  lf-lv-unbuilt exit then
  swap lf-lv-term 0= if lf-lv-unbuilt exit then
  lf-term-app if lf-lv-term-here else lf-lv-fail then lf-lv-release ;
\ A name ID, and a declaration's name.
\ A name given a namer (plain style) is shown as it shows it, which escapes it
\ whole and is not escaped again.
: lf-lv-decl-shown ( id -- )
  lf-lv lf-lv-declname @ execute
  if lf-lv-put-raw else 2drop s" ?" lf-lv-put-raw 1 lf-lv lf-lv-bad +! then ;
: lf-lv-printed-name ( id -- )
  lf-lv-math-open lf-print-name lf-lv-printed lf-lv-math-close ;
: lf-lv-name-id ( id -- )
  lf-lv lf-lv-declname @ lf-lv-tex? 0= and if lf-lv-decl-shown else lf-lv-printed-name then ;
: lf-lv-decl-name ( i -- )
  dup 0 lf-input-count within if lf-input-name lf-lv-name-id else lf-lv-n then ;

\ Setting up: the state's block, and the term printer writing into the
\ line buffer, in Unicode (false, nothing set up, without memory for the
\ block); lf-lv-done gives the term printer back its sink and options and
\ the block back (a FREE that fails stays recorded for the teardown).
: lf-lv-setup ( sink fuel -- flag )
  lf-lv-open 0= if 2drop false exit then
  lf-lv lf-lv-fuel ! lf-lv lf-lv-sink ! 0 lf-lv lf-lv-bad !
  lf-lv-clear ['] lf-lv-put lf-print-unicode lf-print-setup lf-lv-names true ;
: lf-lv-done ( -- ) ['] type lf-print-unicode lf-print-setup lf-lv-close drop ;
\ The style of the next lines: LaTeX (true) or Unicode (false, the default
\ of a new block); the term printer follows.
: lf-lv-mode ( -- mode ) lf-lv-tex? if lf-print-latex else lf-print-unicode then ;
: lf-lv-printer ( -- ) ['] lf-lv-put lf-lv-mode lf-print-setup ;
: lf-lv-latex! ( flag -- ) lf-lv lf-lv-tex ! 0 lf-lv lf-lv-mathing ! lf-lv-printer ;

\ The list of every step (--detail, and a log no outline is printed from):
\ step, rule, depth, the formulas the rule relates, its premises and,
\ unless ok, its outcome.
: lf-lv-arrow ( -- ) s"  ⟶ " lf-lv-put ;
: lf-lv-as ( ref s -- ) over lf-log-none = if 2drop else lf-lv-formula then ;
: lf-lv-typed ( s -- )
  dup lf-lv-a over lf-lv-as dup lf-lv-out-ref lf-log-none = if drop exit then
  s"  : " lf-lv-put dup lf-lv-out-ref swap lf-lv-as ;
: lf-lv-reduced ( s -- ) dup lf-lv-a over lf-lv-as lf-lv-arrow dup
  lf-lv-out-ref swap lf-lv-as ;
: lf-lv-beta ( s -- )
  dup lf-lv-a over lf-lv-b 2 pick lf-lv-redex lf-lv-arrow dup
  lf-lv-out-ref swap lf-lv-as ;
: lf-lv-shifted ( s -- )
  dup lf-lv-a over lf-lv-b 2 pick lf-lv-lifted s"  shifted by " lf-lv-put
  dup lf-lv-b lf-lv-n
  lf-lv-arrow dup lf-lv-out-ref swap lf-lv-as ;
: lf-lv-defeq ( s -- ) dup lf-lv-a over lf-lv-as s"  ≡ " lf-lv-put dup
  lf-lv-b swap lf-lv-as ;
: lf-lv-levels ( s -- )
  dup lf-lv-a lf-lv-level-here s"  = " lf-lv-put lf-lv-b lf-lv-level-here ;
: lf-lv-counted ( s c-addr u -- )
  2>r dup lf-lv-a over lf-lv-as 2r> lf-lv-put dup lf-lv-b lf-lv-n
  lf-lv-arrow dup lf-lv-out-ref swap lf-lv-as ;
: lf-lv-resolve ( s -- ) dup lf-lv-a lf-lv-name-id lf-lv-out-ref dup 0<
  if drop s"  ↦ generated" lf-lv-put else s"  ↦ d" lf-lv-put lf-lv-n then ;
: lf-lv-decl ( s -- ) s" declaration " lf-lv-put lf-lv-a lf-lv-decl-name ;
: lf-lv-arity ( s -- )
  dup lf-lv-a lf-lv-n s"  levels for d" lf-lv-put lf-lv-b lf-lv-n ;
: lf-lv-formed ( s -- )
  dup lf-lv-a over lf-lv-as s"  : Sort " lf-lv-put lf-lv-out-ref lf-lv-level-here ;
: lf-lv-defined ( s -- ) dup lf-lv-a over lf-lv-as s"  := " lf-lv-put dup
  lf-lv-b swap lf-lv-as ;
: lf-lv-published ( s -- )
  s" d" lf-lv-put dup lf-lv-a lf-lv-n s" , " lf-lv-put lf-lv-b lf-lv-n s"  dependencies"
  lf-lv-put ;
\ A CASE with one arm per rule (read as a table).
: lf-lv-relates ( s -- )
  dup lf-lv-rule dup lf-lv-infer-rule? if drop lf-lv-typed exit then
  case lf-rule-whnf of lf-lv-reduced endof lf-rule-beta of lf-lv-beta endof
    lf-rule-defeq of lf-lv-defeq endof lf-rule-level-eq of lf-lv-levels endof
    lf-rule-instantiate of lf-lv-beta endof
    lf-rule-shift of lf-lv-shifted endof
    lf-rule-instantiate-levels of s"  with levels: " lf-lv-counted endof
    lf-rule-resolve of lf-lv-resolve endof
    lf-rule-universe-arity of lf-lv-arity endof
    lf-rule-universe-parameter of lf-lv-a lf-lv-name-id endof
    lf-rule-proposition of lf-lv-formed endof lf-rule-type of lf-lv-formed endof
    lf-rule-declaration of lf-lv-defined endof lf-rule-publish of lf-lv-published endof
    >r lf-lv-decl r> endcase ;
: lf-lv-premise-list ( s -- )
  dup lf-lv-premises dup 0= if 2drop exit then s"   ← " lf-lv-put
  0 ?do i if s" , " lf-lv-put then dup i lf-lv-premise lf-lv-step loop drop ;
: lf-lv-outcome. ( s -- )
  lf-lv-outcome dup ok? if drop exit then s"   [" lf-lv-put outcome-text lf-lv-put
  s" ]" lf-lv-put ;
\ One step's line.
: lf-lv-list-step ( s -- )
  s"   " lf-lv-put dup lf-lv-step 9 lf-lv-flush
  dup lf-lv-rule lf-log-rule-name lf-lv-put 20 lf-lv-flush
  s" depth " lf-lv-put dup lf-lv-depth@ lf-lv-n 10 lf-lv-flush
  dup lf-lv-relates dup lf-lv-premise-list lf-lv-outcome. 0 lf-lv-flush lf-lv-cr ;
\ Steps 1 to n.
: lf-lv-list ( n -- ) 0 ?do i 1+ lf-lv-list-step loop ;
