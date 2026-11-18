\ Throwing faces of the Meta layer (docs/design/TACTIC_PLUGINS.md 2.1;
\ plan slice a2-i): Lean's Meta functions throw on failure, LeanForth's
\ Meta core returns an outcome; this file is the one bridge between the
\ two styles, for the tactic library (app-builder.fs, telescope.fs) and
\ the code that calls it.
\ Public words (the Lean function each ports, where there is one):
\   lf-must ( outcome -- )            a failure thrown (Lean's throw): an
\                                     outcome word's throwing face is the
\                                     word followed by lf-must
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
\   lf-with-view ( i*x xt view -- j*x ) xt in that local context (withLCtx)
\ Fail-closed (the design's rule): a failure is thrown as the code
\ lf-meta-throw-base - outcome (-4201 to -4206), never for ok, so CATCH
\ gives 0 only when the code ran to its end; lf-meta-catch hands back
\ exactly the outcome thrown (unsupported never becomes rejected, never
\ ok) and passes every other code on untouched (an authoring error, an
\ internal fault); an outcome outside the vocabulary is thrown as
\ invalid. tactic-run.fs's lfr-meta-code stays the one mapping of a
\ failure to an authoring error. Every with- word puts its state back
\ on both paths.
\ Rule: no throwing word may run inside code that frees its state only
\ on a normal return: a dw-run walk (dag-walk.fs: its heap memo and
\ stack, so no lf-term-holds? predicate throws), defeq.fs's machine (its
\ saved frames around the synth hooks lf-meta-synth and
\ lf-meta-synth-pending), synth.fs's search between sy-enter and
\ sy-leave, and the elaborator's frames (elab-*.fs). Builders call
\ those, never the reverse; outcome code that calls a builder wraps it
\ in lf-meta-catch. Every word above but lf-meta-thrown?, lf-meta-outcome
\ and lf-meta-catch throws.
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
\ A failure's outcome, any other code thrown on.
: lfm-caught ( code -- outcome ) dup lf-meta-thrown? 0= if throw then lf-meta-outcome ;
: lfm-drop-under ( i*x o out in -- o out ) 0 ?do rot drop loop ;
: lfm-nones ( o out -- -1 .. -1 o ) 0 ?do -1 swap loop ;
\ The depth xt must leave when it ends: the cells under xt, less in, plus
\ out; another depth is a wrong count, an internal fault (invalid thrown).
: lfm-want ( xt in out -- xt in out d ) 2dup - depth 4 - swap - ;
: lfm-left ( j*x d -- j*x outcome )
  depth 1- = if outcome-ok else outcome-invalid lf-must then ;
\ xt takes in cells and gives out; after a failure its in cells (as
\ CATCH leaves them) give way to out cells of -1, then the outcome.
: lf-meta-catch ( i*x xt in out -- j*x outcome )
  lfm-want >r 2>r catch ?dup 0= if 2r> 2drop r> lfm-left exit then
  lfm-caught 2r> swap lfm-drop-under lfm-nones r> drop ;

\ ---- The Meta core's throwing faces.
: lf-whnf! ( e -- e' ) lf-meta-whnf lf-must ;
: lf-whnf-r! ( e -- e' ) lf-meta-whnf-r lf-must ;
: lf-whnf-d! ( e -- e' ) ['] lf-whnf! lf-tr-default lf-meta-at ;
: lf-infer! ( e -- type ) lf-infer lf-must ;
: lf-level! ( type -- level ) lf-get-level lf-must ;
: lf-defeq! ( t s -- flag ) lf-meta-defeq outcome-sane lf-must ;
: lf-instantiate! ( e -- e' ) lf-instantiate-mvars lf-must ;

\ ---- commitWhen: the metavariable context marked, xt run; its changes
\ kept on true, rolled back on false and on a THROW (thrown on). A
\ rollback the context refuses is thrown as invalid, a LeanForth fault.
: lfm-undo ( mark -- ) lf-mctx-rollback-to lf-must ;
: lfm-settle ( flag mark -- flag )
  over if lf-mctx-commit else lfm-undo outcome-ok then lf-must ;
: lf-commit-when ( i*x xt -- j*x flag )
  lf-mctx-mark lf-must >r catch ?dup if r> lfm-undo throw then r> lfm-settle ;

\ ---- withLCtx and withContext: xt run in a local context (a view) or the
\ goal's, the current one put back however xt ends.
: lf-with-view ( i*x xt view -- j*x )
  lf-mctx-view swap lf-mctx-view! >r catch r> lf-mctx-view! throw ;
: lfm-view ( goal -- view ) lf-mvar-view 0= if outcome-invalid lf-must then ;
: lf-with-goal ( i*x goal xt -- j*x ) swap lfm-view lf-with-view ;
base !   \ the BASE this file was loaded with
