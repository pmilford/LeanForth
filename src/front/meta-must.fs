\ Throwing faces of the Meta layer (docs/design/TACTIC_PLUGINS.md 2.1;
\ plan slice a2-i): Lean's Meta functions throw on failure, LeanForth's
\ Meta core returns an outcome; this file is the one bridge between the
\ two styles, for the tactic library (app-builder.fs, telescope.fs) and
\ the code that calls it.
\ Public words (the Lean function each ports, where there is one):
\   lf-must ( outcome -- )            a failure thrown (Lean's throw)
\   lf-must: ( xt "name" -- )         a throwing face of an outcome word
\   lf-made! ( flag -- )              a term store's false thrown as full
\   lf-whnf! lf-whnf-r! lf-whnf-d! ( e -- e' )  whnf, whnfR, whnfD
\   lf-infer! ( e -- type )           inferType
\   lf-level! ( type -- level )       getLevel
\   lf-defeq! ( t s -- flag )         isDefEq (the configuration in force)
\   lf-instantiate! ( e -- e' )       instantiateMVars
\   lf-meta-thrown? ( code -- flag )  whether a THROW code is a failure's
\   lf-meta-outcome ( code -- outcome ) the outcome a failure's code carries
\   lf-meta-catch ( i*x xt in out -- j*x outcome ) xt ( i*x -- j*x ) run
\                                     from outcome code (Lean's try/catch)
\   lf-commit-when ( i*x xt -- j*x flag ) commitWhen (Util/MonadBacktrack
\                                     .lean:50)
\   lf-with-goal ( i*x goal xt -- j*x ) MVarId.withContext (Meta/Basic.lean)
\ Fail-closed (the design's rule): a failure is thrown as the code
\ lf-meta-throw-base - outcome (-4201 to -4206), never for ok, so CATCH
\ gives 0 only when the code ran to its end; lf-meta-catch hands back
\ exactly the outcome thrown (unsupported never becomes rejected, never
\ ok) and passes every other code on untouched (an authoring error, an
\ internal fault); an outcome outside the vocabulary is thrown as
\ invalid. tactic-run.fs's lfr-meta-code stays the one mapping of a
\ failure to an authoring error. Every with- word puts its state back
\ on both paths.
\ Rule: no throwing word may run inside a dw-run walk (dag-walk.fs),
\ whose heap memo and stack are freed only on a normal return: builders
\ call walks, never the reverse. Every word above but lf-meta-thrown?,
\ lf-meta-outcome and lf-meta-catch throws.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ./mvars.fs
require ./meta-config.fs
require ./whnf.fs
require ./infer.fs
require ./defeq.fs

-4200 constant lf-meta-throw-base   \ a failure's code: base - outcome

\ ---- Throwing and catching an outcome.
: lf-meta-thrown? ( code -- flag )
  lf-meta-throw-base swap - outcome-invalid outcome-full 1+ within ;
: lf-meta-outcome ( code -- outcome ) lf-meta-throw-base swap - ;
: lf-must ( outcome -- )
  dup ok? if drop exit then outcome-sane lf-meta-throw-base swap - throw ;
: lf-made! ( flag -- ) 0= if outcome-full lf-must then ;
: lf-must: ( xt "name" -- ) create , does> @ execute lf-must ;
\ A failure's outcome, any other code thrown on.
: lfm-caught ( code -- outcome ) dup lf-meta-thrown? 0= if throw then lf-meta-outcome ;
: lfm-drops ( i*x n -- ) 0 ?do drop loop ;
: lfm-nones ( n -- -1 .. -1 ) 0 ?do -1 loop ;
\ xt takes in cells and gives out; after a failure its in cells (as
\ CATCH leaves them) give way to out cells of -1, then the outcome.
: lf-meta-catch ( i*x xt in out -- j*x outcome )
  2>r catch ?dup 0= if 2r> 2drop outcome-ok exit then
  lfm-caught 2r> rot >r >r lfm-drops r> lfm-nones r> ;

\ ---- The Meta core's throwing faces.
' lf-meta-whnf lf-must: lf-whnf!
' lf-meta-whnf-r lf-must: lf-whnf-r!
: lf-whnf-d! ( e -- e' ) ['] lf-whnf! lf-tr-default lf-meta-at ;
' lf-infer lf-must: lf-infer!
' lf-get-level lf-must: lf-level!
: lfm-defeq ( t s -- flag outcome ) lf-meta-defeq outcome-sane ;
' lfm-defeq lf-must: lf-defeq!
' lf-instantiate-mvars lf-must: lf-instantiate!

\ ---- commitWhen: the metavariable context marked, xt run; its changes
\ kept on true, rolled back on false and on a THROW (thrown on). A
\ rollback the context refuses is thrown as invalid, a LeanForth fault.
: lfm-undo ( mark -- ) lf-mctx-rollback-to lf-must ;
: lfm-settle ( flag mark -- flag )
  over if lf-mctx-commit else lfm-undo outcome-ok then lf-must ;
: lf-commit-when ( i*x xt -- j*x flag )
  lf-mctx-mark lf-must >r catch ?dup if r> lfm-undo throw then r> lfm-settle ;

\ ---- withContext: xt run in the goal's local context, the current one
\ put back however xt ends.
: lfm-view ( goal -- view ) lf-mvar-view 0= if outcome-invalid lf-must then ;
: lf-with-goal ( i*x goal xt -- j*x )
  swap lfm-view lf-mctx-view >r lf-mctx-view! catch r> lf-mctx-view! throw ;
base !   \ the BASE this file was loaded with
