\ The tactic runner (plan FE1g-3 as far as it goes before plan FE1e, the
\ statement's elaboration: FE1g-3a; design docs/design/FE1G_TACTICS.md
\ §4.3-4.6), after Lean 4.35.0's Elab/Tactic/Basic.lean (Tactic.run,
\ getMainGoal, focus, done, closeUsingOrAdmit, saveState and restore),
\ Elab/SyntheticMVars.lean's runTactic and Elab/MutualDef.lean's end of a
\ declaration (mkForallFVars, mkLambdaFVars).
\ End NAME of a tactic proof read whole (tactic-syntax.fs) runs it:
\ 1. lf-front-by-statement ( -- type ), the hook FE1e's := by fills: it
\    elaborates the declaration's binders, each a free variable whose
\    local it pushes on the current view (mvars.fs, lf-mctx-view), and
\    gives the statement's type in their context. Until plan FE1e it stops
\    the run, not supported yet (error 71), as a term proof's end does;
\    tests set a stand-in that builds the type directly.
\ 2. lf-tactic-by ( type -- goal ), Lean's runTactic: the type
\    instantiated, a new goal of it (synthetic opaque, untagged, in the
\    current view), the goal list [goal], the steps run in order, and at
\    the end of the proof no goal left (else error 89 at by: unsolved
\    goals, with the goals as Lean prints them).
\ 3. The binders (Lean's xs: the view's locals of the default kind, oldest
\    first; a let among them is not supported yet) close the type (Lean's
\    mkForallFVars) and the goal's instantiated value (mkLambdaFVars), and
\    FE1f's hand-over (handover.fs) checks and records them.
\ Running: an open block is a frame on a heap stack (no host recursion):
\ its step, the next step to look at and the goals outside it. The loop
\ runs the top frame's next child step, or ends the block: Lean's done
\ (no unsolved goal, else error 89 at the block's place, => for an
\ alternative or case, by for the proof) and the goals outside it put
\ back (closeUsingOrAdmit; LeanForth never admits, ADR 0021 D3). Each
\ step spends one unit of the run's own fuel (lf-tactic-fuel!; Lean
\ counts heartbeats instead, so where its limit and this one differ is
\ a listed difference, none known): none left is error 91, exhausted.
\ A step runs by its kind's row of a table: by-sorry here; the others
\ answer not supported yet (error 80, with the plan step that ports them,
\ FE1g-4 to FE1g-6, and the goals), until a later file sets their rows
\ (lf-tactic-action!).
\ by-sorry is Lean's sorry tactic (exact sorry: closeMainGoalUsing,
\ elabSorry, Meta/Sorry.lean): the main goal (none: error 90, Lean's "No
\ goals to be solved") is taken off the list and assigned
\ sorryAx.{u} T Bool.false, T its type and u T's level (Lean's getLevel,
\ infer.fs). Lean labels each sorry with a name made from the module,
\ the position and a hygienic counter, sorryAx.{0} (Lean.Name -> T)
\ Bool.false label; LeanForth's export has no string literals, so the
\ label waits for plan PD1 and the term differs from Lean's there; the
\ verdict is the same (accepted, depending on sorryAx: NOT PROVED). Each
\ goal by-sorry closes is an open part: its declaration, position and
\ goal as printed are kept for the whole run (they outlive the stores the
\ checker empties) and lf-open-parts. reports them after the verdicts.
\ Choice points (Lean's saveState and restore, for FE5's first and the
\ rfl alternatives): lf-tac-try ( xt -- code ) runs xt from a saved state
\ (a mark of the metavariable context, the goal list, the open blocks, the
\ open parts and the current local context) and keeps its changes when it
\ succeeds (0), or puts the state back when it fails with an authoring
\ error (its THROW code;
\ the error stays recorded until lf-tac-forget); any other THROW passes
\ on, the state put back. Fuel is not given back (nor are Lean's
\ heartbeats); nodes made by a failed attempt stay, reached by nothing.
\ Words: lf-front-by-statement, lf-tactic-by, lf-tactic-fuel! ( n -- )
\ (steps a run may take, from 0), lf-tactic-fuel-default ( -- ),
\ lf-tactic-fuel-left ( -- n ), lf-tactic-action! ( xt kind -- ),
\ lf-tac-step ( -- i ) the step running, lf-tac-main ( -- goal ),
\ lf-tac-fail ( code -- ) (an error at the step running, with the goals),
\ lf-tac-stop ( code -- ) (the same without the goals), lf-tac-must
\ ( outcome -- ) (a Meta step's failure stops the run), lf-tac-detail
\ ( x xt -- ) (xt's printing as the error's detail), lf-tac-later ( i -- )
\ (a step not ported yet), lf-tac-const0 ( c-addr u -- term ),
\ lf-tac-const1 ( level c-addr u -- term ), lf-tac-app ( f a -- t ),
\ lf-tac-block ( i rest -- ), lf-tac-done ( i -- ), lf-tac-focus ( --
\ rest ), lf-tac-unfocus ( rest -- ), lf-tac-save ( -- save outcome ),
\ lf-tac-restore, lf-tac-commit ( save -- outcome ), lf-tac-try,
\ lf-tac-forget ( -- ), lf-open-parts ( -- n ), lf-open-parts. ( -- ).
\ Errors stop the run (lfa-fail) with author/errors.fs's codes: 80, 89,
\ 90, 91, 92 for a record whose steps do not nest as the reader makes
\ them (checked before any step runs), 93 for a type inference or
\ reduction not ported yet (plan FE1c), 88 or 60 for no room, 71 and the
\ hand-over's 74-77. Untrusted: only the kernel's check of the finished
\ term decides anything.
\ State: the record trun (fuel, the step running, the universe argument
\ being built) and the slabs trun-frames, trun-saves, trun-xs and
\ trun-locals (one declaration's run), trun-parts and trun-text (the
\ open parts of the whole run, emptied by lfa-run-fresh), in the checker
\ context (ADR 0009); the table of rows lfr-rows is shared, set while the
\ modules load (lf-tactic-action!) and read-only afterwards (a test may
\ change a row in its own single-threaded run). Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/local-context.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../present/binder-table.fs
require ../present/print-job.fs
require ../author/errors.fs
require ../author/declarations.fs
require ./mvars.fs
require ./lctx-views.fs
require ./goals.fs
require ./goal-print.fs
require ./instantiate.fs
require ./infer.fs
require ./handover.fs
require ./tactic-syntax.fs

100000 constant lfr-default-fuel   \ tactic steps a run may take by default
begin-structure /trun
  field: trun-fuel       \ steps left in this run
  field: trun-limit      \ the steps lf-tactic-fuel! set
  field: trun-given      \ true when lf-tactic-fuel! set them
  field: trun-step       \ the step running, for its errors
  field: trun-cut        \ true when an open part's text found no room
  2 cells +field trun-pair  \ sorryAx's universe argument: level, identity
end-structure
/trun context-record: trun
begin-structure /tfr      \ an open block
  field: tfr-step         \ its step in the record
  field: tfr-next         \ the first step not looked at yet
  field: tfr-rest         \ the goals outside it (a run), put back at its end
end-structure
/tfr context-slab: trun-frames
begin-structure /tsv      \ a saved state
  field: tsv-mark         \ the metavariable context's mark
  field: tsv-goals        \ the goal list
  field: tsv-frames       \ how many blocks were open
  field: tsv-parts        \ how many open parts there were
  field: tsv-text         \ and their text's length
  field: tsv-view         \ the current local context (a tactic may set it)
end-structure
/tsv context-slab: trun-saves
1 cells context-slab: trun-xs       \ the binders' free variables (Lean's xs)
1 cells context-slab: trun-locals   \ and their locals
begin-structure /top      \ an open part
  field: top-at           \ the position of its by-sorry
  field: top-name         \ its declaration's name: first character in trun-text
  field: top-name#        \ and how many
  field: top-goal         \ the goal as printed: first character
  field: top-goal#        \ and how many
end-structure
/top context-slab: trun-parts
1 chars context-slab: trun-text

\ ---- Fuel: one unit a step.
: lf-tactic-fuel! ( n -- ) trun tuck trun-limit ! true swap trun-given ! ;
: lf-tactic-fuel-default ( -- ) false trun trun-given ! ;
: lf-tactic-fuel-left ( -- n ) trun trun-fuel @ ;
: lfr-limit ( -- n )
  trun dup trun-given @ if trun-limit @ else drop lfr-default-fuel then ;
: lfr-fuel-start ( -- ) lfr-limit trun trun-fuel ! ;
: lfr-spend? ( -- flag )
  lf-tactic-fuel-left dup 0> if 1- trun trun-fuel ! true else drop false then ;

\ ---- The record (tactic-syntax.fs). Step i's fields; unchecked.
: lfr-kind ( i -- kind ) lf-tactic-step tac-kind @ ;
: lfr-parent ( i -- j ) lf-tactic-step tac-parent @ ;
: lfr-at ( i -- pos ) lf-tactic-step tac-at @ ;
\ Where a block's unsolved goals are told: its => when it has one, else
\ its word (by).
: lfr-block-at ( i -- pos )
  lf-tactic-step dup tac-arrow @ dup 0< if drop tac-at @ else nip then ;
: lfr-block-word ( i -- c-addr u ) lfr-kind tac-k-by = if s" by" else s" =>" then ;

\ ---- The rows: per kind (1 to 11, tactic-syntax.fs's), its step's
\ action ( i -- ), the plan step that will port it (FE1g-N; 0: it runs
\ here) and its word's spelling.
11 constant lfr-kinds
24 constant lfr-room              \ characters of a spelling
begin-structure /trow
  field: trow-run
  field: trow-plan
  field: trow-length
  lfr-room chars +field trow-chars
end-structure
/trow aligned constant lfr-row-size
create lfr-rows lfr-kinds lfr-row-size * allot
\ A kind outside 1 to 11 has no row: a load-time slip (lf-tactic-action!),
\ since a run checks its record first.
: lfr-kind? ( kind -- flag ) 1 lfr-kinds 1+ within ;
: lfr-row ( kind -- addr )
  dup lfr-kind? 0= abort" tactic-run: no such tactic kind" 1- lfr-row-size * lfr-rows + ;
: lfr-spell ( c-addr u kind -- )
  over lfr-room > abort" tactic-run: a spelling too long"
  lfr-row 2dup trow-length ! trow-chars swap chars move ;
: lfr-set ( xt plan kind -- ) lfr-row tuck trow-plan ! trow-run ! ;
: lf-tactic-action! ( xt kind -- ) 0 swap lfr-set ;
: lfr-spelling ( i -- c-addr u ) lfr-kind lfr-row dup trow-chars swap trow-length @ ;
s" by" tac-k-by lfr-spell              s" by-rfl" tac-k-rfl lfr-spell
s" by-exact" tac-k-exact lfr-spell     s" by-intro:" tac-k-intro lfr-spell
s" by-induction" tac-k-induction lfr-spell
s" by-induction-with" tac-k-with lfr-spell
s" |" tac-k-alt lfr-spell              s" by-case:" tac-k-case lfr-spell
s" by-rw[" tac-k-rw lfr-spell          s" by-rewrite[" tac-k-rewrite lfr-spell
s" by-sorry" tac-k-sorry lfr-spell

\ ---- Errors: at the step running (its word and position) or at a
\ block's place; a tactic's error also shows the goals, kept as the
\ error's detail (for the first error only: a later one is not kept).
: lf-tac-step ( -- i ) trun trun-step @ ;
\ xt ( x -- outcome ) printing with the term printer's sink set to sink
\ for the while, the printer's settings put back however xt ends (a THROW
\ passes on); lf-tac-detail prints into the error's detail, unless an
\ error is recorded already.
: lfr-printed ( x xt sink -- outcome )
  lf-print-settings 2>r lf-print-unicode lf-print-setup catch 2r> lf-print-setup throw ;
: lf-tac-detail ( x xt -- )
  lf-author-code if 2drop exit then
  ['] lfa-detail+ lfr-printed ok? 0= if lfa-detail-cut then ;
: lfr-goals-of ( x -- outcome ) drop lf-goals-text ;
: lfr-with-goals ( -- ) 0 ['] lfr-goals-of lf-tac-detail ;
: lfr-at-step ( code -- ) >r lf-tac-step dup lfr-spelling rot lfr-at r> lfa-fail-at ;
\ (With no step of the record running, a word called directly: at the
\ current token.)
: lfr-fail ( code -- ) lf-tac-step lf-tactic-count < if lfr-at-step else lfa-fail then ;
: lf-tac-fail ( code -- ) lfr-with-goals lfr-fail ;
: lf-tac-stop ( code -- ) lfr-fail ;
: lfr-block-fail ( i code -- ) >r dup lfr-block-word rot lfr-block-at r> lfa-fail-at ;
\ An outcome other than ok stops the run: the run's own stores (no room
\ 88, else 92), or a Meta step (no room for terms 60, fuel 91, anything
\ else 93, not supported yet: the step works on goals Lean's invariants
\ keep well formed, so a refusal there is a gap of LeanForth's).
: lfr-own-code ( outcome -- code )
  outcome-full = if lfa-e-tac-full else lfa-e-tac-record then ;
: lfr-must ( outcome -- ) dup ok? if drop else lfr-own-code lfr-fail then ;
: lfr-meta-code ( outcome -- code )
  case outcome-full of lfa-e-terms-full endof outcome-exhausted of lfa-e-tac-fuel endof
    lfa-e-tac-meta swap endcase ;
: lfr-meta-must ( outcome -- ) dup ok? if drop else lfr-meta-code lf-tac-fail then ;
: lf-tac-must ( outcome -- ) lfr-meta-must ;
\ At end NAME (the current token): making the root goal and closing the
\ value, as the hand-over's errors (no room 60, a step not ported 77,
\ else malformed 76).
: lfr-close-code ( outcome -- code )
  case outcome-full of lfa-e-terms-full endof
    outcome-unsupported of lfa-e-instantiate endof lfa-e-malformed swap endcase ;
: lfr-ok ( outcome -- ) dup ok? if drop else lfr-close-code lfa-fail then ;
: lfr-close-must ( x outcome -- x ) ok-then? 0= if lfr-close-code lfa-fail then ;

\ ---- Steps not ported yet: error 80 with the plan step and the goals.
: lfr-plan! ( i -- )
  lf-author-code if drop exit then lfr-kind lfr-row trow-plan @ lfa-number! ;
: lf-tac-later ( i -- ) lfr-plan! lfa-e-tac-run lf-tac-fail ;
\ A step the record cannot hold there (a second by): malformed.
: lfr-misplaced ( i -- ) drop lfa-e-tac-record lfr-fail ;
' lfr-misplaced 0 tac-k-by lfr-set     ' lf-tac-later 4 tac-k-rfl lfr-set
' lf-tac-later 4 tac-k-exact lfr-set   ' lf-tac-later 4 tac-k-intro lfr-set
' lf-tac-later 5 tac-k-induction lfr-set   ' lf-tac-later 5 tac-k-with lfr-set
' lf-tac-later 5 tac-k-alt lfr-set     ' lf-tac-later 5 tac-k-case lfr-set
' lf-tac-later 6 tac-k-rw lfr-set      ' lf-tac-later 6 tac-k-rewrite lfr-set

\ ---- The goals (Lean's getMainGoal, focus, done).
: lfr-goals! ( list -- ) lf-goals! lfr-must ;
: lf-tac-main ( -- goal )
  lf-main-goal ok-then? if exit then
  outcome-invalid = if lfa-e-tac-no-goals else lfa-e-tac-full then lfr-fail ;
: lfr-unsolved ( -- list ) lf-goals-unsolved ok-then? 0= if lfr-own-code lfr-fail then ;
: lfr-unsolved-at ( i -- ) lfr-with-goals lfa-e-tac-unsolved lfr-block-fail ;
: lf-tac-done ( i -- ) lfr-unsolved run-count if lfr-unsolved-at else drop then ;
: lfr-split ( list -- rest ) dup 1 run-take lfr-must lfr-goals! 1 run-after lfr-must ;
: lf-tac-focus ( -- rest )
  lfr-unsolved dup run-count if lfr-split else drop lfa-e-tac-no-goals lfr-fail then ;
: lf-tac-unfocus ( rest -- ) lfr-unsolved swap run-cat lfr-must lfr-goals! ;

\ ---- Blocks: frames, the innermost on top. A block's steps are the
\ steps after it whose parent is it; the first step after them has a
\ parent before it (the reader's order: a block's steps follow it).
: lfr-depth ( -- n ) trun-frames slab-count ;
: lfr-frame ( k -- addr ) trun-frames slab-at ;
: lfr-top ( -- addr ) trun-frames slab-last ;
: lfr-frame! ( i rest addr -- ) tuck tfr-rest ! over 1+ over tfr-next ! tfr-step ! ;
: lf-tac-block ( i rest -- ) 1 trun-frames slab-claim lfr-must lfr-frame lfr-frame! ;
: lfr-inside? ( b j -- flag )
  dup lf-tactic-count < if lfr-parent swap < 0= else 2drop false then ;
: lfr-scan ( b j -- b j' )
  begin 2dup lfr-inside? while 2dup lfr-parent = if exit then 1+ repeat ;
: lfr-next ( frame -- j true | false )
  dup tfr-step @ swap tfr-next @ lfr-scan tuck lfr-inside? dup 0= if nip then ;
\ A step: its fuel, then its row's action.
: lfr-act ( i -- ) dup lfr-kind lfr-row trow-run @ execute ;
: lfr-step ( i -- )
  dup trun trun-step ! lfr-spend? 0= if drop lfa-e-tac-fuel lf-tac-fail then lfr-act ;
: lfr-go ( j -- ) dup 1+ lfr-top tfr-next ! lfr-step ;
\ A block's end: done at its place, the goals outside it put back.
: lfr-pop ( -- ) trun-frames slab-drop ;
: lfr-end-block ( -- )
  lfr-top dup tfr-step @ swap tfr-rest @ lfr-pop swap lf-tac-done lfr-goals! ;
: lfr-advance ( -- ) lfr-top lfr-next if lfr-go else lfr-end-block then ;
: lfr-loop ( -- ) begin lfr-depth while lfr-advance repeat ;

\ ---- The record checked before anything runs: step 0 the proof (kind
\ by, no parent), every other step of a known kind but by, its parent
\ before it, one of the blocks open at it (the step before it or a block
\ around that) and a block (by, with, alternative or case), alternatives
\ exactly the steps right inside a by-induction-with. Steps are checked
\ in order and the first bad one stops the check, so the parents walked
\ are known to come before their steps.
: lfr-holder? ( kind -- flag )
  dup tac-k-by = over tac-k-with = or over tac-k-alt = or swap tac-k-case = or ;
: lfr-alt-right? ( i p -- flag ) lfr-kind tac-k-with = swap lfr-kind tac-k-alt = = ;
\ p is j or a block around j: j's parents walked while they come after p.
: lfr-ancestor? ( p j -- flag ) begin 2dup < while lfr-parent repeat = ;
: lfr-on-chain? ( i p -- flag ) swap 1- lfr-ancestor? ;
: lfr-parent-ok? ( i p -- flag )
  2dup 0 rot within if lfr-on-chain? else 2drop false then ;
: lfr-linked? ( i -- flag )
  dup lfr-parent 2dup lfr-parent-ok? 0= if 2drop false exit then
  dup lfr-kind lfr-holder? if lfr-alt-right? else 2drop false then ;
: lfr-step-ok? ( i -- flag )
  dup lfr-kind dup lfr-kind? swap tac-k-by <> and if lfr-linked? else drop false then ;
: lfr-root-ok? ( -- flag ) 0 lfr-kind tac-k-by = 0 lfr-parent 0< and ;
: lfr-step-after? ( k -- flag ) 1+ lfr-step-ok? ;   \ steps 1 .. count - 1
: lfr-steps-ok? ( -- flag ) lf-tactic-count 1- ['] lfr-step-after? all? ;
: lfr-record-ok? ( -- flag )
  lf-tactic-count 0> if lfr-root-ok? lfr-steps-ok? and else false then ;
: lfr-checked ( -- ) lfr-record-ok? 0= if lfa-e-tac-record lfa-fail then ;

\ ---- by-sorry (Lean's sorry tactic). First the open part: the
\ declaration's name and the goal as printed, in trun-text.
: lfr-text# ( -- n ) trun-text slab-count ;
: lfr-text-cut ( c-addr u i -- ) 2drop drop true trun trun-cut ! ;
: lfr-text+ ( c-addr u -- )
  dup trun-text slab-claim ok? if trun-text slab-at swap move else lfr-text-cut then ;
: lfr-goal-text ( goal -- outcome ) ['] lf-goal-print ['] lfr-text+ lfr-printed ;
: lfr-part ( -- addr ) trun-parts slab-last ;
\ A span of trun-text: where it begins, then its length once written.
: lfr-span-end ( first addr -- length ) tuck ! lfr-text# swap @ - ;
: lfr-name-kept ( -- )
  lfr-text# lfa-full lfr-text+ lfr-part top-name lfr-span-end lfr-part top-name# ! ;
: lfr-goal-kept ( goal -- outcome )
  lfr-text# swap lfr-goal-text >r lfr-part top-goal lfr-span-end lfr-part top-goal# ! r> ;
: lfr-cut? ( outcome -- outcome' ) trun trun-cut @ if drop outcome-full then ;
: lfr-open-part ( goal -- )
  1 trun-parts slab-claim lfr-must drop lf-tac-step lfr-at lfr-part top-at !
  false trun trun-cut ! lfr-name-kept lfr-goal-kept lfr-cut? lfr-must ;
\ The term: sorryAx.{u} T Bool.false, its constants by name.
: lfr-pair ( -- addr ) trun trun-pair ;
: lfr-pair! ( level -- ) dup lf-level-identity 0= if 0 then swap lfr-pair 2! ;
: lfr-made ( flag -- ) 0= if outcome-full lfr-meta-must then ;
: lfr-const ( c-addr u n -- term )
  >r lfa-intern lf-name-generation @ lfr-pair r> lf-cref-new lfr-made
  lf-cterm-new lfr-made drop ;
: lfr-app ( f a -- t ) lf-term-app lfr-made ;
\ For the tactics: a constant with no universe argument or one, an
\ application.
: lf-tac-const0 ( c-addr u -- term ) 0 lfr-const ;
: lf-tac-const1 ( level c-addr u -- term ) 2>r lfr-pair! 2r> 1 lfr-const ;
: lf-tac-app ( f a -- t ) lfr-app ;
: lfr-sorry-term ( type level -- term )
  lfr-pair! s" sorryAx" 1 lfr-const swap lfr-app s" Bool.false" 0 lfr-const lfr-app ;
: lfr-level ( type -- level ) lf-get-level lfr-meta-must ;
: lfr-sorry-of ( goal -- term ) lf-mvar-type drop dup lfr-level lfr-sorry-term ;
\ (Lean takes the goal off the list first and puts it back when the term
\ fails; here the term is made first, with the same goals at a failure,
\ and the open part is recorded only once it is made.)
: lfr-sorry ( i -- )
  drop lf-tac-main dup lfr-sorry-of over lfr-open-part 0 lf-replace-main lfr-must
  lf-mvar-assign lfr-meta-must ;
' lfr-sorry tac-k-sorry lf-tactic-action!

\ ---- Saved states (choice points). Only the latest may be restored or
\ committed, as metavariable marks.
: lfr-saves ( -- n ) trun-saves slab-count ;
: lfr-save ( k -- addr ) trun-saves slab-at ;
: lfr-latest? ( save -- flag ) dup 0< 0= swap lfr-saves 1- = and ;
: lfr-fill ( mark addr -- )
  tuck tsv-mark ! lf-goals over tsv-goals ! lfr-depth over tsv-frames !
  trun-parts slab-count over tsv-parts ! lfr-text# over tsv-text !
  lf-mctx-view swap tsv-view ! ;
\ The metavariable context's trail (front/mvars.fs's marks, last in,
\ first out): the one place to change when the trail's interface does.
: lfr-trail-mark ( -- mark outcome ) lf-mctx-mark ;
: lfr-trail-undo ( mark -- outcome ) lf-mctx-rollback ;
: lfr-trail-keep ( mark -- outcome ) lf-mctx-commit ;
: lfr-unmark ( mark outcome -- -1 outcome ) swap lfr-trail-undo drop no-result ;
: lf-tac-save ( -- save outcome )
  lfr-trail-mark ok-then? 0= if no-result exit then
  1 trun-saves slab-claim ok-then? 0= if lfr-unmark exit then
  tuck lfr-save lfr-fill outcome-ok ;
: lfr-drop-save ( -- ) trun-saves slab-drop ;
\ A slab's count back to n (blocks, parts and text only grow in a try).
: lfr-cut-to ( n slab -- ) tuck slab-count - swap slab-commit ;
: lfr-back ( addr -- )
  dup tsv-frames @ trun-frames lfr-cut-to dup tsv-parts @ trun-parts lfr-cut-to
  dup tsv-text @ trun-text lfr-cut-to tsv-goals @ lf-goals! drop ;
: lfr-rolled ( addr -- outcome )
  dup lfr-back dup tsv-view @ lf-mctx-view! tsv-mark @ lfr-trail-undo ;
: lf-tac-restore ( save -- outcome )
  dup lfr-latest? 0= if drop outcome-invalid exit then lfr-save lfr-rolled lfr-drop-save ;
: lf-tac-commit ( save -- outcome )
  dup lfr-latest? 0= if drop outcome-invalid exit then
  lfr-save tsv-mark @ lfr-trail-keep lfr-drop-save ;
: lfr-kept ( save code -- code ) swap lf-tac-commit drop ;
: lfr-undone ( save code -- code ) swap lf-tac-restore drop ;
: lfr-caught ( save code -- code )
  ?dup 0= if 0 lfr-kept exit then lfr-undone dup lf-author-throw <> if throw then ;
: lf-tac-try ( xt -- code ) lf-tac-save lfr-must swap catch lfr-caught ;
: lf-tac-forget ( -- ) lfa-error-reset ;

\ ---- The run: the root goal, the steps, the end.
: lfr-fresh ( -- )
  trun-frames slab-clear trun-saves slab-clear lfr-fuel-start lf-pst-reset
  0 trun trun-step ! ;
: lfr-root ( type -- )
  lf-instantiate-mvars lfr-close-must 0 lf-mctx-view lf-goal-new lfr-close-must
  lf-pst-open lfr-must ;
: lf-tactic-by ( type -- goal )
  lfr-fresh lfr-checked lfr-root 0 0 lf-tac-block lfr-loop lf-pst-root ;

\ ---- Closing over the binders (Lean's mkForallFVars, mkLambdaFVars): the
\ term instantiated, its binders' free variables abstracted, then a
\ binder per variable from the last, each named as its local, its domain
\ the variable's type abstracted over the variables before it.
: lfr-let? ( fvar -- flag ) dup lf-fvar-let? swap lf-fvar-nondep? or ;
: lfr-close-push ( x slab -- ) slab-push lfr-ok ;
: lfr-x+ ( local -- )
  dup lf-local-fvar lfr-let? if drop lfa-e-tac-meta lfa-fail then
  dup lf-local-fvar trun-xs lfr-close-push trun-locals lfr-close-push ;
: lfr-binder+ ( view i -- ) lf-view-local dup lf-local-detail? if drop else lfr-x+ then ;
: lfr-xs ( -- )
  trun-xs slab-clear trun-locals slab-clear
  lf-mctx-view dup lf-view-count 0 ?do dup i lfr-binder+ loop drop ;
: lfr-n ( -- n ) trun-xs slab-count ;
: lfr-abstract ( e k -- e' ) 0 trun-xs slab-at swap lf-meta-abstract lfr-close-must ;
: lfr-type ( k -- type )
  trun-xs slab-at @ lf-fvar-type lf-instantiate-mvars lfr-close-must ;
: lfr-domain ( k -- d ) dup lfr-type swap lfr-abstract ;
: lfr-named ( t k -- t )
  trun-locals slab-at @ dup lf-local-name swap lf-local-binder >r over swap r>
  lf-pres-binder! lfr-ok ;
: lfr-around ( body k xt -- body' )
  >r tuck lfr-domain swap r> execute 0= if outcome-full lfr-ok then swap lfr-named ;
: lfr-wraps ( body xt -- body' )
  >r lfr-n begin dup while 1- swap over r@ lfr-around swap repeat drop r> drop ;
: lfr-close ( e xt -- e' )
  >r lf-instantiate-mvars lfr-close-must lfr-n lfr-abstract r> lfr-wraps ;

\ ---- End NAME of a tactic proof (tactic-syntax.fs's lf-tactic-proof-end).
defer lf-front-by-statement ( -- type )
: lfr-unelaborated ( -- type ) lfa-e-elaborate lfa-fail ;
' lfr-unelaborated is lf-front-by-statement
: lfr-assemble ( type goal -- type' value )
  ['] lf-term-lam lfr-close >r ['] lf-term-pi lfr-close r> ;
: lfr-proof-end ( -- )
  lf-front-by-statement lfr-xs dup lf-tactic-by lfr-assemble lf-front-hand-over
  lfa-declared ;
' lfr-proof-end is lf-tactic-proof-end

\ ---- The open parts, after the verdicts (ADR 0021 Amendment 1).
: lf-open-parts ( -- n ) trun-parts slab-count ;
: lfr-parts-reset ( -- ) trun-parts slab-clear trun-text slab-clear ;
action-of lfa-run-fresh constant lfr-run-fresh-before
: lfr-run-fresh ( -- ) lfr-run-fresh-before execute lfr-parts-reset ;
' lfr-run-fresh is lfa-run-fresh
: lfr-chars ( first n -- c-addr u ) swap trun-text slab-at swap ;
: lfr-.pos ( pos -- ) lfa-pos> swap lfa-.n ." :" lfa-.n ;
: lfr-.place ( addr -- ) ." (by-sorry at line:col " top-at @ lfr-.pos ." )" ;
: lfr-.head ( k addr -- )
  ." open part " swap 1+ lfa-.n ."  of " dup top-name @ over top-name# @ lfr-chars type
  space lfr-.place ." :" ;
: lfr-.goal ( addr -- ) dup top-goal @ swap top-goal# @ lfr-chars type ;
: lfr-.part ( k -- ) dup trun-parts slab-at tuck lfr-.head cr lfr-.goal cr ;
: lfr-.note ( -- )
  ." note: everything else in a declaration with open parts was checked by the kernel;" cr
  ." note: accepted, it holds if each of its open parts is true, and is NOT PROVED" cr ;
: lf-open-parts. ( -- ) lf-open-parts ?dup if 0 do i lfr-.part loop lfr-.note then ;
base !   \ the BASE this file was loaded with
