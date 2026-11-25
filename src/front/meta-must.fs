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
\   lf-run+ ( run x -- run' )         run-push's throwing face (lib/runs.fs)
\   lf-run+! ( x addr -- )            the run in the cell at addr made
\                                     that run, then x (a frame's list)
\   lf-run2 ( x y -- run )            the run of x then y
\   lf-menv-find? ( name -- d true | false ) Environment.find? (and
\                                     contains): false when no declaration
\                                     has the name, any other failure
\                                     (no room, a declaration not decoded)
\                                     thrown
\   lf-whnf! lf-whnf-r! lf-whnf-d! ( e -- e' )  whnf, whnfR, whnfD
\   lf-infer! ( e -- type )           inferType
\   lf-level! ( type -- level )       getLevel
\   lf-defeq! ( t s -- flag )         isDefEq (the configuration in force)
\   lf-defeq-approx! ( t s -- flag )  approxDefEq <| isDefEqGuarded
\                                     (Basic.lean:2125): foApprox, ctxApprox
\                                     and quasiPatternApprox added to the
\                                     configuration in force (meta-config.fs's
\                                     lf-with-approx); apply's and rfl's test
\   lf-instantiate! ( e -- e' )       instantiateMVars
\   lf-open-mvar-free ( e -- e )      e, which holds no such metavariable,
\                                     else unsupported thrown (the goal
\                                     words' and tactics' holes LeanForth
\                                     does not port: new goals, Lean's
\                                     natural-hole errors)
\   lf-has-open-mvar? ( e -- flag )   whether e holds a metavariable
\                                     neither assigned nor delayed-assigned
\                                     (getMVarsNoDelayed e not empty;
\                                     mvars.fs's lf-mvar-open? on each leaf)
\   lf-meta-thrown? ( code -- flag )  whether a THROW code is a failure's
\   lf-meta-outcome ( code -- outcome ) the outcome a failure's code carries
\   lf-meta-fail ( term code -- )     a Lean error with a message of its
\                                     own (synthInstance's "failed to
\                                     synthesize"), thrown as rejected: its
\                                     authoring code and the term its message
\                                     shows kept for the runner
\   lf-meta-failed ( -- term code )   the error the last failure thrown
\                                     carried; code 0 when it carried none
\                                     (any lf-must failure clears it)
\   lf-meta-catch ( i*x xt in out -- j*x outcome ) xt ( i*x -- j*x ) run
\                                     from outcome code (Lean's try/catch)
\   lf-commit-when ( i*x xt -- j*x flag ) commitWhen (Util/MonadBacktrack
\                                     .lean:50)
\   lf-with-goal ( i*x goal xt -- j*x ) MVarId.withContext (Meta/Basic.lean)
\   lf-with-view ( i*x xt view -- j*x ) xt in that local context (withLCtx)
\   lf-with-record ( i*x slab xt -- j*x ) xt ( i*x -- j*x ) run with a
\                                     new frame, erased, on top of slab (a
\                                     call's working record), freed however
\                                     xt ends, with any frame left above it;
\                                     xt reads its frame as slab-last, again
\                                     after each word that may claim on slab
\                                     (rule below)
\   lf-defeq-elab-at ( t s mode -- flag outcome ) the tactics' isDefEq:
\                                     the elaborator's flags added to the
\                                     configuration in force, at
\                                     transparency mode, the stuck signal
\                                     made invalid (outcome-sane); no THROW
\   lf-tac-defeq ( t s -- flag outcome ) the same at default transparency
\   lf-found ( x true | false -- x )  a lookup's answer, none thrown invalid
\                                     (a record LeanForth made is missing: a fault)
\   lf-match-const-induct ( f -- d true | false ) matchConstInduct
\                                     (MonadEnv.lean:64) of a head f: d
\                                     its declaration when f is the
\                                     constant of an inductive type; false
\                                     for any other term, a name no
\                                     declaration has (Lean's find? none)
\                                     or a declaration of another kind; a
\                                     lookup that cannot answer (no room, a
\                                     library declaration not decoded)
\                                     thrown. (Here, not in meta-env.fs,
\                                     which lies below this file and
\                                     throws nothing.)
\   lf-with-cells ( i*x n slab xt -- j*x ) xt ( i*x addr -- j*x ) run
\                                     with n cells claimed on slab (units
\                                     of a cell; Lean's Array of n, such as
\                                     introN's free variables), addr the
\                                     first's, not erased, given back
\                                     however xt ends; addr is valid while
\                                     nothing else claims on slab
\                                     (slab.fs), so xt never nests a claim
\                                     on the same slab
\   lf-goal-type lf-goal-tag lf-goal-view lf-goal-kind ( goal -- x )
\                                     MVarId.getType (as stored), getTag, the
\                                     goal's local context and kind (getDecl);
\                                     a goal with no record thrown invalid
\   lf-view-local-of ( view fvar -- local )  a free variable's local in a
\                                     view (getLocalDecl), none thrown invalid
\   lf-fvar-user-name ( fvar -- name )  its user name in the context in
\                                     force (FVarId.getUserName)
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
\ State: the record mmf (the Lean error the last failure carried), in the
\ checker context (ADR 0009). Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/runs.fs
require ../core/input.fs
require ../core/constant-term-boundary.fs
require ./mvars.fs
require ./meta-config.fs
require ./meta-env.fs
require ./whnf.fs
require ./infer.fs
require ./defeq.fs
require ./term-find.fs

-4200 constant lf-meta-throw-base   \ a failure's code: base - outcome

\ ---- Throwing and catching an outcome.
: lf-meta-thrown? ( code -- flag )
  lf-meta-throw-base swap - outcome-invalid outcome-full 1+ within ;
: lf-meta-outcome ( code -- outcome ) lf-meta-throw-base swap - ;
\ The Lean error a failure carries: set by lf-meta-fail, cleared by every
\ other failure, so it always describes the last one thrown.
begin-structure /mmf
  field: mmf-code   \ its authoring code, or 0 (first: read and set with 2@ 2!)
  field: mmf-term   \ the term its message shows
end-structure
/mmf context-record: mmf
: lf-meta-failed ( -- term code ) mmf 2@ ;
: lf-meta-fail ( term code -- ) mmf 2! lf-meta-throw-base outcome-rejected - throw ;
: lf-must ( outcome -- )
  dup ok? if drop exit then 0 mmf mmf-code !
  outcome-sane lf-meta-throw-base swap - throw ;
: lf-made! ( flag -- ) 0= if outcome-full lf-must then ;
: lf-run+ ( run x -- run' ) run-push lf-must ;
: lf-run+! ( x addr -- ) tuck @ swap lf-run+ swap ! ;
: lf-run2 ( x y -- run ) >r run-one lf-must r> lf-run+ ;
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
: lf-defeq-approx! ( t s -- flag )
  ['] lf-meta-defeq-guarded lf-with-approx outcome-sane lf-must ;
: lf-instantiate! ( e -- e' ) lf-instantiate-mvars lf-must ;
: lf-has-open-mvar? ( e -- flag ) ['] lf-mvar-open? lf-term-holds? lf-must ;
: lf-open-mvar-free ( e -- e ) dup lf-has-open-mvar? if outcome-unsupported lf-must then ;
\ isDefEq with the elaborator's flags (TermElabM's setElabConfig: foApprox
\ and ctxApprox) added to the configuration in force, at transparency mode
\ (lf-meta-with: defeq's own configuration and mode put back however it
\ ends), an internal code such as the stuck signal made invalid. A bit a
\ caller's scope sets, as Lean's withAssignableSyntheticOpaque and
\ approxDefEq do (meta-config.fs), stays set (plan 9.4.8l, review
\ tactic-move M2: elabTermEnsuringType's, tactic-core.fs). Lean's
\ setElabConfig (Elab/Config.lean:61-62) also clears constApprox and
\ quasiPatternApprox, once, when TermElabM starts; OR-ing gives the same
\ configuration: no caller of this word holds those bits, and inside
\ TermElabM a scope's bits stay set in Lean too (review tactic-fidelity L5).
: lf-defeq-elab-at ( t s mode -- flag outcome )
  ['] lf-meta-defeq lf-defeq-flags lf-defeq-elab or rot lf-meta-with outcome-sane ;
: lf-tac-defeq ( t s -- flag outcome ) lf-tr-default lf-defeq-elab-at ;

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
: lf-found ( x true | false -- x ) 0= if outcome-invalid lf-must then ;
: lf-goal-type ( goal -- type ) lf-mvar-type lf-found ;
: lf-goal-tag ( goal -- tag ) lf-mvar-tag lf-found ;
: lf-goal-view ( goal -- view ) lf-mvar-view lf-found ;
: lf-view-local-of ( view fvar -- local ) over swap lf-view-find lf-found lf-view-local ;
: lf-fvar-user-name ( fvar -- name ) lf-mctx-view swap lf-view-local-of lf-local-name ;
: lf-goal-kind ( goal -- kind ) lf-mvar-kind lf-found ;
: lf-with-goal ( i*x goal xt -- j*x ) swap lf-goal-view lf-with-view ;

\ ---- matchConstInduct: a head's declaration, when it is an inductive type.
: mm-inductive ( d -- d true | false )
  dup lf-menv-kind lf-kind-inductive = dup 0= if nip then ;
: lf-menv-find? ( name -- d true | false )
  lf-menv-find dup outcome-invalid = if 2drop false exit then lf-must true ;
: lf-match-const-induct ( f -- d true | false )
  dup lf-term-const? 0= if drop false exit then
  lf-const-name lf-menv-find? dup if drop mm-inductive then ;

\ ---- A call's working record: a frame per call open on the slab, so
\ that a call inside another has its own (slice LA item 5), freed on both
\ paths. Rule (review tactic-move M1): xt is given no address. A claim on
\ the slab may move its block (slab.fs: an address is valid only until
\ the next claim), and a call nested in xt claims its own frame on the
\ same slab; so xt reads its frame afresh as the slab's last unit (its
\ caller's accessor, such as goal.fs's mti), never keeping the address
\ across a word that may nest a call. The frames are strictly nested,
\ so the last unit is always the innermost open call's.
: mm-frame ( slab -- )
  1 over slab-claim lf-must over slab-at swap slab-unit erase ;
: lf-with-record ( i*x slab xt -- j*x )
  over dup slab-count 2>r swap mm-frame catch 2r> swap slab-cut throw ;
\ n cells claimed on top of slab, the first's address to xt, the slab cut
\ back to its count before however xt ends.
: mm-cells ( n slab -- addr ) tuck slab-claim lf-must swap slab-at ;
: lf-with-cells ( i*x n slab xt -- j*x )
  over dup slab-count 2>r -rot mm-cells swap catch 2r> swap slab-cut throw ;
base !   \ the BASE this file was loaded with
