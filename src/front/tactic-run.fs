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
\    gives the statement's type in their context (front/elab-decl.fs; without
\    it the run stops, not supported yet, error 71, as a term proof's end
\    does); tests set a stand-in that builds the type directly.
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
\ a listed difference, none known) and one of the declaration's budget
\ (meta-config.fs, --elab-fuel): none left is error 91, exhausted.
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
\ rfl alternatives): lf-tac-try ( xt -- code ), xt ( -- ), runs xt from a
\ saved state and keeps its changes when it succeeds (0), or puts the
\ state back when it fails with an authoring error (its THROW code; the
\ error stays recorded until lf-tac-forget); any other THROW passes on,
\ the state put back. A save holds exactly: a mark of the metavariable
\ context (rolled back through every scope opened since, lf-mctx-rollback-to),
\ the current local context, the goal list, trun's open blocks, open
\ parts, step records, step log, its text and newest entry (trun-entry),
\ and the states other modules add with tac-state: ( save-xt back-xt -- )
\ (reviews C2 and N4 of 2026-11-18): the elaborator's pending list and
\ synthesis window (elab-pending.fs, registered by elab-decl.fs), the
\ induction blocks and their cases (tactic-induction.fs) and rw's
\ metavariables (tactic-rewrite.fs), as Lean's saveState holds the whole
\ Term and Meta state; lib/slab.fs's slab-keep and slab-kept do a
\ back-xt's work for a slab. A run
\ that stops inside a try has its open saves forgotten when the next
\ starts. A save that cannot be put back or kept stops the
\ run (THROW lfr-state-lost, an internal fault). Fuel is not given back
\ (nor are Lean's heartbeats); nodes made by a failed attempt stay,
\ reached by nothing.
\ Words: lf-front-by-statement, lf-tactic-by, lf-tactic-fuel! ( n -- )
\ (steps a run may take, from 0), lf-tactic-fuel-default ( -- ),
\ lf-tactic-fuel-left ( -- n ), lf-tactic-action! ( xt kind -- ),
\ lf-tac-step ( -- i ) the step running, lf-tac-main ( -- goal ),
\ lf-tac-fail ( code -- ) (an error at the step running, with the goals),
\ lf-tac-stop ( code -- ) (the same without the goals), lf-tac-must
\ ( outcome -- ) (a Meta step's failure stops the run), lf-tac-detail
\ ( x xt -- ) (xt's printing as the error's detail), lf-tac-later ( i -- )
\ (a step not ported yet), lf-tactic-end! ( xt kind -- ) (what
\ a block of the kind does at its end, before done: xt ( i -- )),
\ lf-tac-stop-at and lf-tac-fail-at ( j code -- ) (an error at step j's
\ word and place, without or with the goals), the step records (review
\ fe1g3 M2: one per step a tactic runs, kept for the step log of
\ s2-steps, dropped by a restore past them): lf-tac-in-record ( i*x i xt
\ -- j*x ), lf-tac-record ( -- addr ) (the running record's own fields,
\ else the last's), lf-tac-records ( -- n ), lf-tac-record-at ( k -- addr ),
\ lf-tac-block ( i rest -- ), lf-tac-done ( i -- ), lf-tac-focus ( --
\ rest ), lf-tac-unfocus ( rest -- ), lf-tac-save ( -- save outcome ),
\ lf-tac-restore, lf-tac-commit ( save -- outcome ), lf-tac-try,
\ lf-tac-forget ( -- ), lf-open-parts ( -- n ), lf-open-parts. ( -- ),
\ lf-front-close ( type value -- type' value' ) and lf-front-close-type
\ ( type -- type' ) (a term proof's or an axiom's closing over the
\ current view's binders, as a tactic proof's, front/elab-decl.fs).
\ The step log (S2 6, s2-steps): lf-steps-record! ( flag -- ) keeps one
\ (cli: check --steps); then each step the loop runs gets an entry
\ (/tlg: its kind, position, the entry of its block, the main goal before
\ and the goals after, printed), a restore drops those made since its
\ save, and a declaration handed over records its name, entries and open
\ parts (/tld); a log record or text that finds no room cuts the log
\ (nothing more is logged in the run; the run, its verdicts and its exit
\ code are as without the log, except when memory is exhausted: the log's
\ text takes room in trun-text that a later open part might have had,
\ which then stops the run full, 88); lf-steps-decls ( -- n ), lf-steps-decl
\ ( k -- addr ), lf-steps-entry ( k -- addr ), lf-steps-span ( k -- first
\ n ), lf-steps-text ( first n -- c-addr u ), lf-steps-cut? ( -- flag ) and
\ lf-tac-word ( kind -- c-addr u ) read them for front/step-log.fs;
\ emptied with the open parts.
\ Errors stop the run (lfa-fail) with author/errors.fs's codes: 80, 89,
\ 90, 91, 92 for a record whose steps do not nest as the reader makes
\ them (checked before any step runs), 93 for a type inference or
\ reduction not ported yet (plan FE1c), 88 or 60 for no room, 71 and the
\ hand-over's 74-77. A failure the tactic library throws (meta-must.fs)
\ out of a step or a try becomes, at once, the authoring error
\ lf-tac-must makes of its outcome (lfr-authored: lfr-meta-code stays the
\ one mapping); at the end of a proof, the closing's (lfr-close-code).
\ Terms are built by the library (app-builder.fs, telescope.fs).
\ Untrusted: only the kernel's check of the finished
\ term decides anything.
\ State: the record trun (fuel, the step running, the step record
\ running) and the slabs trun-frames, trun-saves, trun-steps and trun-xs
\ (one declaration's run), trun-parts and trun-text (the
\ open parts of the whole run and the step log's text, emptied by
\ lfa-run-fresh), trun-log, trun-log-spans and trun-log-decls (the step
\ log of the whole run, emptied with them), in the checker
\ context (ADR 0009); the table of rows lfr-rows is shared, set while the
\ modules load (lf-tactic-action!) and read-only afterwards (a test may
\ change a row in its own single-threaded run). Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../lib/slab.fs
require ../lib/xt-table.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/local-context.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../present/binder-table.fs
require ../present/print-job.fs
require ../present/term-printer.fs
require ../author/errors.fs
require ../author/declarations.fs
require ./mvars.fs
require ./meta-config.fs
require ./lctx-views.fs
require ./goals.fs
require ./goal-print.fs
require ./instantiate.fs
require ./infer.fs
require ./handover.fs
require ./tactic-syntax.fs
require ./meta-must.fs
require ./app-builder.fs
require ./telescope.fs

100000 constant lfr-default-fuel   \ tactic steps a run may take by default
begin-structure /trun
  field: trun-fuel       \ steps left in this run
  field: trun-limit      \ the steps lf-tactic-fuel! set
  field: trun-given      \ true when lf-tactic-fuel! set them
  field: trun-step       \ the step running, for its errors
  field: trun-cut        \ true when an open part's text found no room
  field: trun-record     \ the step record running (trun-steps), or -1
  field: trun-log-on     \ true: the step log is kept (lf-steps-record!)
  field: trun-entry      \ the step log's newest entry of this run, or -1
  field: trun-log-first  \ the declaration's first entry
  field: trun-parts-first \ and the open parts before it
  field: trun-log-cut    \ true once the step log found no room (L4)
end-structure
/trun context-record: trun
32 constant lf-tac-work-cells   \ the room of a tactic's own fields in a step record
begin-structure /tst      \ a step record (fe1g3 review M2): one per step run
  field: tst-step         \ its step in the record
  field: tst-parent       \ the record of the step it runs inside, or -1
  lf-tac-work-cells cells +field tst-work   \ the tactic's own fields
end-structure
/tst context-slab: trun-steps
begin-structure /tfr      \ an open block
  field: tfr-step         \ its step in the record
  field: tfr-next         \ the first step not looked at yet
  field: tfr-rest         \ the goals outside it (a run), put back at its end
  field: tfr-log          \ its step's step-log entry, or -1
end-structure
/tfr context-slab: trun-frames
begin-structure /tsv      \ a saved state
  field: tsv-mark         \ the metavariable context's mark
  field: tsv-goals        \ the goal list
  field: tsv-frames       \ how many blocks were open
  field: tsv-parts        \ how many open parts there were
  field: tsv-text         \ and their text's length
  field: tsv-view         \ the current local context (a tactic may set it)
  field: tsv-steps        \ how many step records there were
  field: tsv-log          \ step-log entries and their goal spans
  field: tsv-log-spans
  field: tsv-entry        \ the step log's newest entry (trun-entry)
end-structure
/tsv context-slab: trun-saves
1 cells context-slab: trun-xs       \ the binders' free variables (Lean's xs)
begin-structure /top      \ an open part
  field: top-at           \ the position of its by-sorry
  2 cells +field top-name \ its declaration's name: a span of trun-text (2@: first n)
  2 cells +field top-goal \ the goal as printed: likewise
end-structure
/top context-slab: trun-parts
1 chars context-slab: trun-text
begin-structure /tlg      \ a step-log entry (S2 6): one per step run
  field: tlg-kind         \ its step's kind (tactic-syntax.fs)
  field: tlg-at           \ its position
  field: tlg-parent       \ the entry of the block it runs in, or -1
  2 cells +field tlg-before  \ the main goal before, printed: a span of
                             \ trun-text, first -1 for none
  field: tlg-after        \ the goals after: their first span in trun-log-spans
  field: tlg-after#       \ and how many
end-structure
/tlg context-slab: trun-log
2 cells context-slab: trun-log-spans   \ a goal's text: first, length
begin-structure /tld      \ a declaration's step log
  2 cells +field tld-name \ its full name: a span of trun-text
  field: tld-first        \ its first entry
  field: tld-count        \ and how many
  field: tld-parts        \ its open parts (by-sorry)
  field: tld-cut          \ true: the log was cut before its end
end-structure
/tld context-slab: trun-log-decls

\ ---- Fuel: one unit a step.
: lf-tactic-fuel! ( n -- ) trun tuck trun-limit ! true swap trun-given ! ;
: lf-tactic-fuel-default ( -- ) false trun trun-given ! ;
: lf-tactic-fuel-left ( -- n ) trun trun-fuel @ ;
: lfr-limit ( -- n )
  trun dup trun-given @ if trun-limit @ else drop lfr-default-fuel then ;
: lfr-fuel-start ( -- ) lfr-limit trun trun-fuel ! ;
\ (A step also spends one of the declaration's budget, --elab-fuel: S1 8.)
: lfr-spend? ( -- flag )
  lf-tactic-fuel-left dup 0> if 1- trun trun-fuel ! lf-meta-spend? else drop false then ;

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
  field: trow-end                 \ ( i -- ) at its block's end, before done
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
\ (Spelling a kind also gives its block's end nothing to do.)
: lfr-spell ( c-addr u kind -- )
  over lfr-room > abort" tactic-run: a spelling too long"
  lfr-row ['] drop over trow-end ! 2dup trow-length ! trow-chars swap chars move ;
: lfr-set ( xt plan kind -- ) lfr-row tuck trow-plan ! trow-run ! ;
: lf-tactic-action! ( xt kind -- ) 0 swap lfr-set ;
: lf-tactic-end! ( xt kind -- ) lfr-row trow-end ! ;
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
\ lf-tac-detail ( x xt -- ): xt ( x -- outcome ) prints into the error's
\ detail (present/term-printer.fs's lf-print-with: the printer's settings
\ put back however xt ends), unless an error is recorded already.
: lf-tac-detail ( x xt -- )
  lf-author-code if 2drop exit then
  ['] lfa-detail+ lf-print-with ok? 0= if lfa-detail-cut then ;
: lfr-goals-of ( x -- outcome ) drop lf-goals-text ;
: lfr-with-goals ( -- ) 0 ['] lfr-goals-of lf-tac-detail ;
\ An error at step j's word and place (an alternative's |, an induction's
\ word at its block's end), with the goals or without.
: lf-tac-stop-at ( j code -- ) >r dup lfr-spelling rot lfr-at r> lfa-fail-at ;
: lfr-at-step ( code -- ) lf-tac-step swap lf-tac-stop-at ;
\ (With no step of the record running, a word called directly: at the
\ current token.)
: lfr-fail ( code -- ) lf-tac-step lf-tactic-count < if lfr-at-step else lfa-fail then ;
: lf-tac-fail ( code -- ) lfr-with-goals lfr-fail ;
: lf-tac-fail-at ( j code -- ) lfr-with-goals lf-tac-stop-at ;
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
\ A library failure's THROW code made that authoring error's; any other
\ code as it is.
: lfr-authored ( code -- code' )
  dup lf-meta-thrown? 0= if exit then lf-meta-outcome ['] lfr-meta-must catch nip ;
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
: lfr-frame! ( i rest addr -- )
  trun trun-entry @ over tfr-log ! tuck tfr-rest ! over 1+ over tfr-next ! tfr-step ! ;
: lf-tac-block ( i rest -- ) 1 trun-frames slab-claim lfr-must lfr-frame lfr-frame! ;
: lfr-inside? ( b j -- flag )
  dup lf-tactic-count < if lfr-parent swap < 0= else 2drop false then ;
: lfr-scan ( b j -- b j' )
  begin 2dup lfr-inside? while 2dup lfr-parent = if exit then 1+ repeat ;
: lfr-next ( frame -- j true | false )
  dup tfr-step @ swap tfr-next @ lfr-scan tuck lfr-inside? dup 0= if nip then ;
\ A step: its fuel, then its row's action.
: lfr-act ( i -- ) dup lfr-kind lfr-row trow-run @ execute ;
\ ---- Text: the open parts' and the step log's, in trun-text, which
\ outlives the stores. A span is where a text begins in trun-text and how
\ long it is: the declaration's full name, or a goal as goal-print.fs
\ prints it; full when the text found no room (trun-cut).
: lfr-text# ( -- n ) trun-text slab-count ;
: lfr-text-cut ( c-addr u i -- ) 2drop drop true trun trun-cut ! ;
: lfr-text+ ( c-addr u -- )
  dup trun-text slab-claim ok? if trun-text slab-at swap move else lfr-text-cut then ;
: lfr-goal-text ( goal -- outcome ) ['] lf-goal-print ['] lfr-text+ lf-print-with ;
: lfr-cut? ( outcome -- outcome' ) trun trun-cut @ if drop outcome-full then ;
: lfr-span ( first outcome -- first n outcome ) >r lfr-text# over - r> lfr-cut? ;
: lfr-text-from ( -- first ) false trun trun-cut ! lfr-text# ;
: lfr-name+ ( -- first n outcome ) lfr-text-from lfa-full lfr-text+ outcome-ok lfr-span ;
: lfr-goal+ ( goal -- first n outcome ) lfr-text-from swap lfr-goal-text lfr-span ;

\ ---- The step log (S2 6; front/step-log.fs writes it): with
\ lf-steps-record! on, each step the loop runs gets an entry, its kind,
\ position and block's entry, the main goal before and the goals after,
\ in slabs that outlive the stores (as the open parts); a restore drops
\ the entries made since its save (lfr-back). A record or text that finds
\ no room cuts the log (L4): the entry under way is dropped, nothing more
\ is logged in the run, and the run goes on as without the log (but for
\ exhausted memory: the log's text in trun-text may leave a later open
\ part no room, review re-check N3).
: lf-steps-record! ( flag -- ) trun trun-log-on ! ;
: lf-steps-cut? ( -- flag ) trun trun-log-cut @ ;
: lfg-on? ( -- flag ) trun trun-log-on @ lf-steps-cut? 0= and ;
: lfg-entry ( -- addr ) trun-log slab-last ;
: lfg-cut ( -- ) true trun trun-log-cut ! ;
: lfg-kept? ( outcome -- flag ) ok? dup 0= if trun-log slab-drop lfg-cut then ;
: lfg-before ( -- )
  lf-main-goal ok-then? if lfr-goal+ else drop -1 0 outcome-ok then
  lfg-kept? if lfg-entry tlg-before 2! else 2drop then ;
: lfg-fill ( i addr -- )
  0 over tlg-after# ! over lfr-kind over tlg-kind ! swap lfr-at over tlg-at !
  lfr-top tfr-log @ swap tlg-parent ! ;
: lfg-open ( i -- )
  lfg-on? 0= if drop exit then
  1 trun-log slab-claim ok-then? 0= if 2drop lfg-cut exit then
  dup trun trun-entry ! trun-log slab-at lfg-fill lfg-before ;
: lfg-goal+ ( goal -- outcome )
  lfr-goal+ ok-then2? if trun-log-spans slab-2push then ;
: lfg-after ( -- )
  trun-log-spans slab-count lfg-entry tlg-after !
  lfr-unsolved dup run-count lfg-entry tlg-after# ! ['] lfg-goal+ run-each
  lfg-kept? drop ;
: lfg-close ( -- ) lfg-on? if lfg-after then ;
: lfr-acted ( i -- ) ['] lfr-act catch ?dup if nip lfr-authored throw then ;
: lfr-step ( i -- )
  dup trun trun-step ! lfr-spend? 0= if drop lfa-e-tac-fuel lf-tac-fail then
  dup lfg-open lfr-acted lfg-close ;
: lfr-go ( j -- ) dup 1+ lfr-top tfr-next ! lfr-step ;
\ A block's end: done at its place, the goals outside it put back.
: lfr-pop ( -- ) trun-frames slab-drop ;
: lfr-ending ( i -- i ) dup dup lfr-kind lfr-row trow-end @ execute ;
: lfr-end-block ( -- )
  lfr-top dup tfr-step @ swap tfr-rest @ lfr-pop swap lfr-ending lf-tac-done lfr-goals! ;
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

\ ---- by-sorry (Lean's sorry tactic). First the open part: its
\ position, the declaration's name and the goal as printed (spans of
\ trun-text).
: lfr-part ( -- addr ) trun-parts slab-last ;
: lf-open-parts ( -- n ) trun-parts slab-count ;
: lfr-open-part ( goal -- )
  1 trun-parts slab-claim lfr-must drop lf-tac-step lfr-at lfr-part top-at !
  lfr-name+ lfr-must lfr-part top-name 2! lfr-goal+ lfr-must lfr-part top-goal 2! ;
\ The term: sorryAx.{u} T Bool.false (mkConst, mkApp2).
: lfr-sorry-term ( type level -- term )
  >r s" sorryAx" r> lf-mk-const1 swap s" Bool.false" lf-mk-const0 2 lf-mk-app-n ;
: lfr-sorry-of ( goal -- term ) lf-mvar-type drop dup lf-level! lfr-sorry-term ;
\ (Lean takes the goal off the list first and puts it back when the term
\ fails; here the term is made first, with the same goals at a failure,
\ and the open part is recorded only once it is made.)
: lfr-sorry ( i -- )
  drop lf-tac-main dup lfr-sorry-of over lfr-open-part 0 lf-replace-main lfr-must
  lf-mvar-assign lfr-meta-must ;
' lfr-sorry tac-k-sorry lf-tactic-action!

\ ---- Step records (fe1g3 review M2; S2_INTERFACE 5): each step a tactic
\ runs gets a record on a heap stack, its step, the record of the step it
\ runs inside (by-rw[ runs by-rfl) and the tactic's own fields, kept for
\ the step log (s2-steps); a restore drops the ones made since its save.
\ lf-tac-in-record ( i*x i xt -- j*x ) runs xt with a new record running;
\ lf-tac-record ( -- addr ) the running record's fields, else the last's.
: lfr-running ( -- addr ) trun trun-record ;
:noname ( -- ) -1 lfr-running ! ; context-setup
: lfr-record ( k -- addr ) trun-steps slab-at ;
: lfr-record+ ( i -- k )
  1 trun-steps slab-claim lfr-must tuck lfr-record dup /tst erase tuck tst-step !
  lfr-running @ swap tst-parent ! ;
\ (The record running before is the new one's parent: a restore cuts only
\ records made after its save, so the parent is still there after a THROW.)
: lfr-unrun ( -- ) lfr-running @ lfr-record tst-parent @ lfr-running ! ;
: lf-tac-in-record ( i*x i xt -- j*x )
  over lfr-record+ lfr-running ! catch lfr-unrun throw ;
\ The running record, else the newest; with none at all, refused as a
\ gap of LeanForth's (lfa-e-tac-record), never slab-at -1.
: lfr-recent ( -- k )
  lfr-running @ dup 0< if drop trun-steps slab-count 1- then
  dup 0< if lfa-e-tac-record lfr-fail then ;
: lf-tac-record ( -- addr ) lfr-recent lfr-record tst-work ;
: lf-tac-records ( -- n ) trun-steps slab-count ;
: lf-tac-record-at ( k -- addr ) lfr-record tst-work ;   \ unchecked: k < lf-tac-records

\ ---- Saved states (choice points). Only the latest may be restored or
\ committed, as metavariable marks.
: lfr-saves ( -- n ) trun-saves slab-count ;
: lfr-save ( k -- addr ) trun-saves slab-at ;
: lfr-latest? ( save -- flag ) dup 0< 0= swap lfr-saves 1- = and ;
: lfr-fill-log ( addr -- )
  trun-log slab-count over tsv-log ! trun-log-spans slab-count over tsv-log-spans !
  trun trun-entry @ swap tsv-entry ! ;
: lfr-fill ( mark addr -- )
  tuck tsv-mark ! lf-goals over tsv-goals ! lfr-depth over tsv-frames !
  trun-parts slab-count over tsv-parts ! lfr-text# over tsv-text !
  lf-tac-records over tsv-steps ! lf-mctx-view over tsv-view ! lfr-fill-log ;
\ The metavariable context's trail (front/mvars.fs's marks, last in,
\ first out): the one place to change when the trail's interface does.
: lfr-trail-mark ( -- mark outcome ) lf-mctx-mark ;
: lfr-trail-undo ( mark -- outcome ) lf-mctx-rollback-to ;
: lfr-trail-keep ( mark -- outcome ) lf-mctx-commit ;
: lfr-unmark ( mark outcome -- -1 outcome ) swap lfr-trail-undo drop no-result ;
\ Other modules' state in every save (reviews C2 and N4 of 2026-11-18):
\ tac-state: ( save-xt back-xt -- ), while the modules load, adds one;
\ save-xt ( -- outcome ) keeps it, back-xt ( undo? -- outcome ) puts the
\ newest kept back (true) or forgets it (false); each module keeps its
\ own, last in, first out (lib/slab.fs's slab-keep and slab-kept do so
\ for a slab). A table of pairs, 0 where none is set.
8 constant lfr-states#
lfr-states# 2* 0 xt-table: lfr-states
: lfr-state-xt ( k -- xt|0 ) lfr-states xt-table@ ;
: lfr-states-used ( -- n ) 0 begin dup 2* lfr-state-xt while 1+ repeat ;
: tac-state: ( save-xt back-xt -- )
  lfr-states-used dup lfr-states# < 0= abort" tac-state: no room for another state"
  2* tuck 1+ lfr-states xt-table! lfr-states xt-table! ;
: lfr-state-back ( undo? k -- outcome ) 2* 1+ lfr-state-xt execute ;
\ The first n states put back or forgotten, all of them: the first refusal.
: lfr-states-back ( undo? n -- outcome )
  outcome-ok swap 0 ?do over i lfr-state-back outcome-and loop nip ;
: lfr-states-undo ( k outcome -- outcome ) swap false swap lfr-states-back drop ;
\ Each state kept; on a refusal those kept before it forgotten.
: lfr-states-save ( -- outcome )
  lfr-states-used 0 ?do i 2* lfr-state-xt execute
    dup ok? 0= if i swap lfr-states-undo unloop exit then drop loop outcome-ok ;
: lfr-states-all ( undo? -- outcome ) lfr-states-used lfr-states-back ;
: lfr-drop-save ( -- ) trun-saves slab-drop ;
: lfr-unsaved ( save outcome -- -1 outcome )
  swap lfr-save tsv-mark @ lfr-drop-save swap lfr-unmark ;
: lf-tac-save ( -- save outcome )
  lfr-trail-mark ok-then? 0= if no-result exit then
  1 trun-saves slab-claim ok-then? 0= if lfr-unmark exit then
  tuck lfr-save lfr-fill lfr-states-save dup ok? 0= if lfr-unsaved then ;
\ The slabs' counts back to the save's (blocks, parts and text only grow
\ in a try), and the step log's newest entry.
: lfr-back-log ( addr -- )
  dup tsv-log @ trun-log slab-cut dup tsv-log-spans @ trun-log-spans slab-cut
  tsv-entry @ trun trun-entry ! ;
: lfr-back ( addr -- outcome )
  dup tsv-frames @ trun-frames slab-cut dup tsv-parts @ trun-parts slab-cut
  dup tsv-text @ trun-text slab-cut dup tsv-steps @ trun-steps slab-cut
  dup lfr-back-log tsv-goals @ lf-goals! ;
\ The trail first, through every scope opened since (review C1 of
\ 2026-11-18), then the view, the goal list, the slabs and the other
\ modules' states (each of them, whatever the goal list's outcome).
: lfr-rolled ( addr -- outcome )
  dup tsv-mark @ lfr-trail-undo ok-then? 0= if true lfr-states-all drop exit then
  dup tsv-view @ lf-mctx-view! lfr-back true lfr-states-all outcome-and ;
: lf-tac-restore ( save -- outcome )
  dup lfr-latest? 0= if drop outcome-invalid exit then lfr-save lfr-rolled lfr-drop-save ;
: lf-tac-commit ( save -- outcome )
  dup lfr-latest? 0= if drop outcome-invalid exit then
  lfr-save tsv-mark @ lfr-trail-keep false lfr-states-all outcome-and lfr-drop-save ;
\ A save that cannot be put back or kept is LeanForth's fault: the run
\ stops with a THROW no try catches (an internal fault, error 41).
-4134 constant lfr-state-lost   \ THROW code: a choice point refused
: lfr-sure ( outcome -- ) ok? 0= if lfr-state-lost throw then ;
: lfr-kept ( save code -- code ) swap lf-tac-commit lfr-sure ;
: lfr-undone ( save code -- code ) swap lf-tac-restore lfr-sure ;
: lfr-caught ( save code -- code )
  ?dup 0= if 0 lfr-kept exit then lfr-undone dup lf-author-throw <> if throw then ;
: lf-tac-try ( xt -- code ) lf-tac-save lfr-must swap catch lfr-authored lfr-caught ;
: lf-tac-forget ( -- ) lfa-error-reset ;

\ ---- The run: the root goal, the steps, the end.
\ Saves a run left open (it stopped inside a try): forgotten, with the
\ other modules' states kept for them.
: lfr-forget-saves ( -- )
  lfr-saves 0 ?do false lfr-states-all drop loop trun-saves slab-clear ;
: lfr-fresh ( -- )
  trun-frames slab-clear lfr-forget-saves trun-steps slab-clear lfr-fuel-start
  lf-pst-reset 0 trun trun-step ! -1 lfr-running ! -1 trun trun-entry !
  trun-log slab-count trun trun-log-first ! lf-open-parts trun trun-parts-first ! ;
: lfr-root ( type -- )
  lf-instantiate-mvars lfr-close-must 0 lf-mctx-view lf-goal-new lfr-close-must
  lf-pst-open lfr-must ;
: lf-tactic-by ( type -- goal )
  lfr-fresh lfr-checked lfr-root 0 0 lf-tac-block lfr-loop lf-pst-root ;

\ ---- Closing over the binders (Lean's mkForallFVars, mkLambdaFVars,
\ telescope.fs): the binders' free variables (Lean's xs) are the current
\ view's locals but its details (a let among them: 93), oldest first;
\ the term instantiated, then closed over them.
: lfr-let? ( fvar -- flag ) dup lf-fvar-let? swap lf-fvar-nondep? or ;
: lfr-x+ ( local -- )
  lf-local-fvar dup lfr-let? if drop lfa-e-tac-meta lfa-fail then trun-xs slab-push lfr-ok ;
: lfr-binder+ ( view i -- ) lf-view-local dup lf-local-detail? if drop else lfr-x+ then ;
: lfr-xs ( -- )
  trun-xs slab-clear lf-mctx-view dup lf-view-count 0 ?do dup i lfr-binder+ loop drop ;
: lfr-close ( e xt -- e' )   \ xt lf-mk-lambda-fvars or lf-mk-forall-fvars
  >r lf-instantiate-mvars lfr-close-must 0 trun-xs slab-at trun-xs slab-count r> 3 1
  lf-meta-catch lfr-close-must ;

\ ---- End NAME of a tactic proof (tactic-syntax.fs's lf-tactic-proof-end).
defer lf-front-by-statement ( -- type )
: lfr-unelaborated ( -- type ) lfa-e-elaborate lfa-fail ;
' lfr-unelaborated is lf-front-by-statement
: lfr-assemble ( type goal -- type' value )
  ['] lf-mk-lambda-fvars lfr-close >r ['] lf-mk-forall-fvars lfr-close r> ;
\ For a term proof or an axiom (front/elab-decl.fs): the type and value,
\ or the type alone, closed over the current view's binders in the same
\ way.
: lf-front-close ( type value -- type' value' ) lfr-xs lfr-assemble ;
: lf-front-close-type ( type -- type' ) lfr-xs ['] lf-mk-forall-fvars lfr-close ;
\ The declaration's step log, also when the log was cut (it says so); a
\ declaration whose record or name finds no room cuts the log, left out.
: lfg-entries ( addr -- addr )
  trun trun-log-first @ over tld-first ! trun-log slab-count over tld-first @ -
  over tld-count ! ;
: lfg-counts ( addr -- )
  lfg-entries lf-open-parts trun trun-parts-first @ - over tld-parts !
  lf-steps-cut? swap tld-cut ! ;
: lfg-record ( first n addr -- ) dup lfg-counts tld-name 2! ;
: lfg-decl ( -- )
  trun trun-log-on @ 0= if exit then
  lfr-name+ ok-then2? 0= if drop lfg-cut exit then
  1 trun-log-decls slab-claim ok-then? if trun-log-decls slab-at lfg-record exit then
  drop 2drop lfg-cut ;
: lfr-proof-end ( -- )
  lf-front-by-statement lfr-xs dup lf-tactic-by lfr-assemble lf-front-hand-over
  lfg-decl lfa-declared ;
' lfr-proof-end is lf-tactic-proof-end

\ ---- The open parts, after the verdicts (ADR 0021 Amendment 1).
: lfr-log-reset ( -- )
  trun-log slab-clear trun-log-spans slab-clear trun-log-decls slab-clear
  false trun trun-log-cut ! ;
: lfr-parts-reset ( -- ) trun-parts slab-clear trun-text slab-clear lfr-log-reset ;
action-of lfa-run-fresh constant lfr-run-fresh-before
: lfr-run-fresh ( -- ) lfr-run-fresh-before execute lfr-parts-reset ;
' lfr-run-fresh is lfa-run-fresh
: lfr-chars ( first n -- c-addr u ) swap trun-text slab-at swap ;
: lfr-.pos ( pos -- ) lfa-pos> swap lfa-.n ." :" lfa-.n ;
: lfr-.place ( addr -- ) ." (by-sorry at line:col " top-at @ lfr-.pos ." )" ;
: lfr-.head ( k addr -- )
  ." open part " swap 1+ lfa-.n ."  of " dup top-name 2@ lfr-chars type
  space lfr-.place ." :" ;
: lfr-.goal ( addr -- ) top-goal 2@ lfr-chars type ;
: lfr-.part ( k -- ) dup trun-parts slab-at tuck lfr-.head cr lfr-.goal cr ;
: lfr-.note ( -- )
  ." note: everything else in a declaration with open parts was checked by the kernel;" cr
  ." note: accepted, it holds if each of its open parts is true, and is NOT PROVED" cr ;
: lf-open-parts. ( -- ) lf-open-parts ?dup if 0 do i lfr-.part loop lfr-.note then ;

\ ---- The step log's records, read by front/step-log.fs after the
\ verdicts: the declarations logged, an entry, a goal's span, a span's
\ text, a kind's word. Unchecked: indexes below the counts.
: lf-steps-decls ( -- n ) trun-log-decls slab-count ;
: lf-steps-decl ( k -- addr ) trun-log-decls slab-at ;
: lf-steps-entry ( k -- addr ) trun-log slab-at ;
: lf-steps-span ( k -- first n ) trun-log-spans slab-at 2@ ;
: lf-steps-text ( first n -- c-addr u ) lfr-chars ;
: lf-tac-word ( kind -- c-addr u ) lfr-row dup trow-chars swap trow-length @ ;
base !   \ the BASE this file was loaded with
