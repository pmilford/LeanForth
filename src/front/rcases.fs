\ rcases, the walk of a case pattern (plan row TB2, piece E, slice E1;
\ docs/design/TACTIC_PATTERNS.md sections 1-3), a port of Lean 4.35.0's
\ Elab/Tactic/RCases.lean: rcases (:423-445) with one target,
\ generalizeExceptFVar (:404), rcasesCore (:270-351), rcasesContinue
\ (:353), processConstructors (:237-251), processConstructor
\ (:214-231), align (:336-343), finish (:377) and tryClearMany' (:365),
\ for tactics/obtain.fs's by-obtain[ and by-rcases[. Lean's walk is a
\ chain of continuations; this one is a flat loop over a stack of tasks
\ (a run, lib/runs.fs, four cells a task: a goal, its substitution, the
\ hypotheses to clear and the pairs of a pattern and a target still to
\ match), each split's subgoals pushed last first, so goals come out
\ depth first in constructor order, as Lean's (probe p4).
\   lf-rcases ( i goal -- goals )  rcases of step i, read by
\       pattern-syntax.fs's tac-shape-pattern (argument 0 the target,
\       then the pattern in postfix order, its root last), on the main
\       goal goal, in its context, under Term.withSynthesize
\       (tactic-core.fs's lf-tac-with-synth): the target elaborated with
\       no expected type; a free variable taken as it is, any other term
\       generalized (meta-tactic/generalize.fs, named as the pattern when
\       it is a name, else an inaccessible x); then each task in turn:
\       the target put through the task's substitution (fvar-subst.fs);
\       a name or _ nothing; - the target added to the clears; a tuple or
\       alternatives a split (the target a free variable, else 470; its
\       type through whnfD an inductive type, else 471; the patterns
\       given to the constructors, Meta cases with Nat.casesAuxOn
\       (meta-tactic/cases.fs), each subgoal matched with its
\       constructor's patterns, those of a constructor with no subgoal
\       passed over); a task with nothing left finished: its clears put
\       through its substitution, those still free variables and every
\       local depending on one tried for clearing, last first
\       (tryClearMany'). goals: the goals finished, a run, in order
\ Pattern references: two cells, an argument k (-1: Lean's default _)
\ and -1 for the item itself, or s >= 0 for the children of tuple or
\ alternatives k from child s on (Lean's patterns built by
\ processConstructors: the last constructor's remaining alternatives,
\ the last field's remaining patterns). A list (asAlts, asTuple) is a run:
\ its container and first child (-1 0 for a list of one pattern), then a
\ reference per element.
\ Not supported yet: rfl (substEq, slice E2) and a quotient (Quot.ind,
\ slice E5), thrown unsupported (99); typed pieces, @ and several
\ targets have no form. Errors (Lean's, catchable by try): 470 "Tactic
\ `rcases` failed: `e` is not a free variable", 471 "Tactic `rcases`
\ failed: `e : T` is not an inductive datatype".
\ Lean call list: Term.withSynthesize -> lf-tac-with-synth; elabTerm ->
\ lf-tac-elab-arg; generalizeExceptFVar -> lf-goal-generalize; fs.apply ->
\ lf-fsubst-apply; whnfD, inferType -> lf-whnf-d!, lf-infer!;
\ matchConst -> lf-match-const-induct; getFunInfo's binder infos ->
\ lf-menv-kinds; MVarId.cases -> lf-goal-cases; fs.append ->
\ lf-fsubst-append; fs.get -> lf-fsubst-get; findLocalDeclDependsOn ->
\ lf-local-depends-on?; tryClearMany -> lf-goal-try-clear.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: rcs-frames (a frame per call open, meta-must.fs's
\ lf-with-record), in the checker context (ADR 0009); no other. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/runs.fs
require ../lib/bounds.fs
require ../lib/find.fs
require ../lib/context.fs
require ../core/input.fs
require ../present/binder-table.fs
require ../author/errors.fs
require ./goals.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./whnf.fs
require ./infer.fs
require ./meta-must.fs
require ./tactic-msg.fs
require ./tactic-core.fs
require ./fvar-subst.fs
require ./pattern-syntax.fs
require ./meta-tactic/assert.fs
require ./meta-tactic/generalize.fs
require ./meta-tactic/cases.fs

470 lfa-lean s" Tactic `rcases` failed:" lfa-code: lfa-e-rcases-fvar
471 lfa-lean s" Tactic `rcases` failed:" lfa-code: lfa-e-rcases-inductive

begin-structure /rcs
  field: rcs-step        \ the step
  field: rcs-tasks       \ the tasks, a run of four cells each
  field: rcs-goals       \ the goals finished, a run
  field: rcs-goal        \ the task's goal
  field: rcs-fs          \ its substitution
  field: rcs-clears      \ its hypotheses to clear, a run
  field: rcs-rest        \ its pairs still to match after the first, a run of triples
  field: rcs-e           \ the target of the first pair
  field: rcs-ind         \ a split's inductive type
  field: rcs-alts        \ processConstructors' alternatives, a list
  field: rcs-k           \ its next one
  field: rcs-names       \ the constructors' names given (AltVarNames), a run of runs
  field: rcs-r           \ per constructor its name and its fields' patterns
  field: rcs-h           \ processConstructor's patterns, a list
  field: rcs-hk          \ its next one
  field: rcs-ns          \ the fields' names so far
  field: rcs-ps          \ the fields' patterns so far, pairs
  field: rcs-kinds       \ the constructor's binder kinds (lf-menv-kinds)
  field: rcs-n           \ and their count
  field: rcs-subs        \ the split's subgoals (lf-goal-cases')
  field: rcs-kr          \ align's cursor in rcs-r
  field: rcs-new         \ the split's tasks, in order
  field: rcs-zps         \ the patterns zipped (rcs-zip)
  field: rcs-zfs         \ with these fields
end-structure
/rcs context-slab: rcs-frames
: rcs ( -- frame ) rcs-frames slab-last ;

\ ---- The pattern: the step's arguments, each with its span.
: rcs-x ( k -- x ) rcs rcs-step @ swap lf-tac-arg ;
: rcs-span ( k -- n ) rcs rcs-step @ swap lf-tac-arg-span ;
: rcs-kind ( node -- x ) dup 0< if drop 0 else rcs-x then ;
: rcs-name ( node s -- name ) drop rcs-kind 0 max ;   \ name?: a name's ID, else 0
\ A node's children, last first: back from the node over each one's span.
: rcs-back ( rev c -- rev' c' ) tuck lf-run+ swap dup rcs-span - ;
: rcs-kids ( node -- rev )
  dup rcs-span over swap - >r 0 swap 1- begin dup r@ > while rcs-back repeat drop r>
  drop ;

\ ---- Lists: asAlts (kind pat-alts) and asTuple (pat-tuple).
: rcs-pair+ ( run node s -- run' ) >r lf-run+ r> lf-run+ ;
: rcs-kid+ ( list rev j -- list rev )
  over run-count 1- swap - over swap run@ rot swap -1 rcs-pair+ swap ;
: rcs-container ( node s -- list )   \ s past the children: none
  0 max 2dup 0 -rot rcs-pair+ -rot swap rcs-kids dup run-count rot over min ?do
  i rcs-kid+ loop drop ;
: rcs-single ( node s -- list ) 0 -1 0 rcs-pair+ -rot rcs-pair+ ;
: rcs-list ( node s kind -- list ) >r over rcs-kind r> = if rcs-container else
  rcs-single then ;
: rcs-len ( list -- n ) run-count 2 - 2/ ;
: rcs-pair@ ( run k -- node s ) 2* 2dup run@ -rot 1+ run@ ;   \ pair k of a run
: rcs-elem ( list j -- node s ) 1+ rcs-pair@ ;   \ past the list's head pair
: rcs-elem0 ( list j -- node s ) 2dup swap rcs-len < if rcs-elem else 2drop -1 -1 then ;
: rcs-rest-of ( list j -- node s ) over 0 run@ -rot swap 1 run@ + ;

\ ---- processConstructor: a name and a pattern per field.
: rcs-field+ ( name node s -- )
  rot rcs rcs-ns @ swap lf-run+ rcs rcs-ns ! rcs rcs-ps @ -rot rcs-pair+ rcs rcs-ps ! ;
: rcs-default ( -- ) 0 -1 -1 rcs-field+ ;
: rcs-take ( -- node s ) rcs rcs-h @ rcs rcs-hk @ rcs-elem0 1 rcs rcs-hk +! ;
: rcs-next ( -- ) rcs-take 2dup rcs-name -rot rcs-field+ ;
\ The patterns left: none once the cursor has passed the end (Lean's tailD []).
: rcs-left ( -- n ) rcs rcs-h @ rcs-len rcs rcs-hk @ - 0 max ;
\ The last field: none left _, one its pattern, more a tuple of them.
: rcs-last ( -- )
  rcs-left dup 0= if drop rcs-default exit then 1 = if rcs-next exit then
  0 rcs rcs-h @ rcs rcs-hk @ rcs-rest-of rcs-field+ ;
: rcs-field ( idx -- )   \ an implicit field takes _ and no pattern (no @)
  dup rcs rcs-kinds @ cell-at@ lf-binder-default <> if drop rcs-default exit then
  1+ rcs rcs-n @ < if rcs-next else rcs-last then ;
: rcs-params# ( -- n ) rcs rcs-ind @ lf-menv-data lf-ity-params lf-more-field ;
: rcs-ctor ( name -- ns ps )
  0 rcs rcs-ns ! 0 rcs rcs-ps ! 0 rcs rcs-hk ! lf-menv-find lf-must lf-menv-kinds
  rcs rcs-n ! rcs rcs-kinds ! rcs rcs-n @ rcs-params# ?do i rcs-field loop
  rcs rcs-ns @ rcs rcs-ps @ ;

\ ---- processConstructors: the last constructor takes the alternatives
\ left (two or more) as one; each other its next one's tuple.
: rcs-ctors@ ( -- items n ) rcs rcs-ind @ lf-menv-data lf-ity-ctors@ ;
: rcs-last? ( i -- flag ) rcs-ctors@ nip 1- = ;
: rcs-many? ( last? -- flag ) rcs rcs-alts @ rcs-len rcs rcs-k @ - 2 < 0= and ;
: rcs-rest-alts ( -- list ) rcs rcs-alts @ rcs rcs-k @ rcs-rest-of rcs-single ;
: rcs-next-alt ( -- list )
  rcs rcs-alts @ rcs rcs-k @ rcs-elem0 pat-tuple rcs-list 1 rcs rcs-k +! ;
: rcs-alt ( last? -- ) rcs-many? if rcs-rest-alts else rcs-next-alt then rcs rcs-h ! ;
: rcs-r+ ( name ns ps -- )
  >r rcs rcs-names @ swap lf-run+ rcs rcs-names ! rcs rcs-r @ swap lf-run+ r> lf-run+ rcs
  rcs-r ! ;
: rcs-one-ctor ( name last? -- ) rcs-alt dup rcs-ctor rcs-r+ ;
: rcs-process ( node s -- )
  pat-alts rcs-list rcs rcs-alts ! 0 rcs rcs-k ! 0 rcs rcs-names ! 0 rcs rcs-r !
  rcs-ctors@ 0 ?do i over cell-at@ i rcs-last? rcs-one-ctor loop drop ;

\ ---- Tasks: rcs-task-cells each on the stack run (a goal, its
\ substitution, its clears, its pairs still to match).
4 constant rcs-task-cells
: rcs-task+ ( goal fs clears pending -- )
  >r >r >r rcs rcs-tasks @ swap lf-run+ r> lf-run+ r> lf-run+ r> lf-run+ rcs rcs-tasks ! ;
: rcs-top ( -- run k ) rcs rcs-tasks @ dup run-count rcs-task-cells - ;
: rcs-task@ ( k -- x ) >r rcs-top r> + run@ ;
: rcs-pop ( -- goal fs clears pending )
  0 rcs-task@ 1 rcs-task@ 2 rcs-task@ 3 rcs-task@
  rcs-top run-take lf-must rcs rcs-tasks ! ;
: rcs-again ( -- ) rcs rcs-goal @ rcs rcs-fs @ rcs rcs-clears @ rcs rcs-rest @ rcs-task+ ;
\ A triple: a pattern reference and its target.
: rcs-triple+ ( run node s e -- run' ) >r rcs-pair+ r> lf-run+ ;

\ ---- finish: the clears through the substitution, still free variables,
\ and every local depending on one, tried last first.
: rcs-got ( fs run c -- fs run' outcome )
  >r over r> lf-fsubst-get dup lf-meta-fvar? if lf-run+ else drop then outcome-ok ;
: rcs-cs ( -- run ) rcs rcs-fs @ 0 rcs rcs-clears @ ['] rcs-got run-each lf-must nip ;
: rcs-dep? ( lfvar run k -- lfvar run flag ) over swap run@ >r over r>
  lf-local-depends-on? lf-must ;
: rcs-erase+ ( run local -- run' outcome )
  lf-local-fvar swap dup run-count ['] rcs-dep? any? if swap lf-run+ else nip
  then outcome-ok ;
: rcs-erased ( goal -- run ) rcs-cs swap lf-goal-view ['] rcs-erase+ run-each lf-must ;
: rcs-cleared ( goal run -- goal' )
  dup run-count begin ?dup while 1- 2dup run@ >r rot r> lf-goal-try-clear -rot repeat
  drop ;
: rcs-finish-in ( goal -- goal' ) dup rcs-erased rcs-cleared ;
: rcs-finish ( -- )
  rcs rcs-goal @ dup ['] rcs-finish-in lf-with-goal rcs rcs-goals @ swap lf-run+ rcs
  rcs-goals ! ;

\ ---- A split (rcasesCore's last case), in the task's goal's context:
\ the target a free variable (470) of an inductive type (471; Quot 99).
: rcs-fvar-tail ( -- outcome ) s"  is not a free variable" lf-pp-emit outcome-ok ;
: rcs-fvar. ( e -- outcome ) ['] rcs-fvar-tail lf-tac-spaced. ;
: rcs-not-fvar ( e -- ) ['] rcs-fvar. lf-tac-inline lfa-e-rcases-fvar lf-tac-stop ;
: rcs-colon ( -- outcome ) s"  : " lf-pp-emit outcome-ok ;
: rcs-of. ( e -- outcome ) s"  `" lf-pp-emit lf-tac-term. ['] rcs-colon ok-and ;
: rcs-ind-tail ( -- outcome ) s" ` is not an inductive datatype" lf-pp-emit outcome-ok ;
: rcs-type. ( t -- outcome ) lf-tac-term. ['] rcs-ind-tail ok-and ;
: rcs-not-inductive ( e t -- )
  swap ['] rcs-of. lf-tac-inline ['] rcs-type. lf-tac-inline
  lfa-e-rcases-inductive lf-tac-stop ;
: rcs-quot? ( t -- flag ) lf-meta-head-name if s" Quot" lfa-intern lf-name-same? else
  false then ;
: rcs-inductive ( e t -- )
  dup lf-meta-head lf-match-const-induct if rcs rcs-ind ! 2drop exit then
  dup rcs-quot? if lf-tac-unported then rcs-not-inductive ;
: rcs-check ( -- )
  rcs rcs-e @ dup lf-meta-fvar? 0= if rcs-not-fvar then dup lf-infer!
  lf-whnf-d! rcs-inductive ;
: rcs-cases ( -- ) rcs rcs-goal @ rcs rcs-e @ rcs rcs-names @ true lf-goal-cases rcs
  rcs-subs ! ;

\ ---- align: each subgoal with the first constructor entry of its name
\ at or after the cursor (those passed over are dropped, as Lean's).
: rcs-r# ( -- n ) rcs rcs-r @ run-count 2/ ;
: rcs-r@ ( m k -- x ) swap 2* + rcs rcs-r @ swap run@ ;
: rcs-find ( ctor kr -- m true | false )
  rcs-r# swap ?do dup i 0 rcs-r@ lf-name-same? if drop i true unloop exit then loop
  drop false ;
: rcs-sub ( i -- subgoals i ) rcs rcs-subs @ swap ;
: rcs-new+ ( x -- ) rcs rcs-new lf-run+! ;
\ The constructor's patterns zipped with the subgoal's fields, then the rest.
: rcs-zip+ ( run j -- run' )
  dup >r rcs rcs-zps @ swap rcs-pair@ rcs rcs-zfs @ r> run@ rcs-triple+ ;
: rcs-zip# ( -- n ) rcs rcs-zfs @ run-count rcs rcs-zps @ run-count 2/ min ;
: rcs-zip ( ps fields -- pending )
  rcs rcs-zfs ! rcs rcs-zps ! 0 rcs-zip# 0 ?do i rcs-zip+ loop rcs rcs-rest @
  run-cat lf-must ;
: rcs-sub-task ( i m -- )
  1 rcs-r@ over rcs-sub lf-subgoal-fields rcs-zip >r dup rcs-sub lf-subgoal-goal rcs-new+
  rcs rcs-fs @ swap rcs-sub lf-subgoal-subst lf-fsubst-append rcs-new+
  rcs rcs-clears @ rcs-new+ r> rcs-new+ ;
: rcs-past ( m -- ) 1+ rcs rcs-kr ! ;   \ the cursor past entry m
: rcs-align ( i -- )
  dup rcs-sub lf-subgoal-ctor rcs rcs-kr @ rcs-find if dup rcs-past rcs-sub-task exit then
  rcs-r# rcs rcs-kr ! drop ;
\ The new tasks pushed last first, so the first subgoal is matched next.
: rcs-new@ ( t k -- x ) swap rcs-task-cells * + rcs rcs-new @ swap run@ ;
: rcs-push ( t -- ) >r r@ 0 rcs-new@ r@ 1 rcs-new@ r@ 2 rcs-new@ r> 3 rcs-new@ rcs-task+ ;
: rcs-pushed ( -- )
  rcs rcs-new @ run-count rcs-task-cells / begin ?dup while 1- dup rcs-push repeat ;
: rcs-split-in ( node s -- )
  rcs-check rcs-process rcs-cases 0 rcs rcs-new ! 0 rcs rcs-kr !
  rcs rcs-subs @ lf-subgoals# 0 ?do i rcs-align loop rcs-pushed ;
: rcs-split ( node s -- ) rcs rcs-goal @ ['] rcs-split-in lf-with-goal ;

\ ---- A task: its first pair matched (rcasesCore), the rest after it.
: rcs-task! ( goal fs clears -- ) rcs rcs-goal cell-triple! ;
: rcs-first ( pending -- node s )
  dup 3 run-after lf-must rcs rcs-rest ! dup 2 run@ rcs rcs-fs @ swap lf-fsubst-apply
  rcs rcs-e ! dup 0 run@ swap 1 run@ ;
: rcs-clears+ ( fvar -- ) rcs rcs-clears lf-run+! ;
: rcs-clear ( -- ) rcs rcs-e @ dup lf-meta-fvar? if rcs-clears+ else drop then rcs-again ;
: rcs-match ( node s -- )
  over rcs-kind dup 0< 0= if drop 2drop rcs-again exit then
  dup pat-clear = if drop 2drop rcs-clear exit then
  pat-rfl = if lf-tac-unported then rcs-split ;
: rcs-task-step ( goal fs clears pending -- )
  >r rcs-task! r> dup run-count if rcs-first rcs-match else drop rcs-finish then ;
: rcs-next-task ( -- ) rcs-pop rcs-task-step ;
: rcs-loop ( -- ) begin rcs rcs-tasks @ run-count while rcs-next-task repeat ;

\ ---- rcases: the target, generalized unless a free variable
\ (generalizeExceptFVar), matched with the pattern's root.
: rcs-root ( -- node s ) rcs rcs-step @ lf-tac-args# 1- -1 ;
: rcs-target ( goal e -- goal' v )
  dup lf-meta-fvar? if exit then
  0 swap lf-run+ rcs-root rcs-name lf-run+ lf-goal-generalize swap 0 run@ ;
: rcs-start ( goal e -- ) rcs-target >r 0 rcs-root r> rcs-triple+ >r 0 0 r> rcs-task+ ;
: rcs-run ( goal -- goals ) rcs rcs-step @ 0 lf-tac-elab-arg rcs-start rcs-loop rcs
  rcs-goals @ ;
: rcs-framed ( i goal -- goals ) swap rcs rcs-step ! dup ['] rcs-run lf-with-goal ;
: rcs-synth ( i goal -- goals ) rcs-frames ['] rcs-framed lf-with-record ;
: lf-rcases ( i goal -- goals ) ['] rcs-synth lf-tac-with-synth ;
base !   \ the BASE this file was loaded with
