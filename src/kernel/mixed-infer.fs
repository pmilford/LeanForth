\ Experimental, untrusted mixed-term inference. Closed source roots only.
\ Signatures and nested dependencies are unchecked assumptions; no theorem
\ authority. One stable index/session, no raw writes, resets or concurrent
\ calls. Handles are local diagnostics. Fuel is shared by preflight,
\ traversal, specialization and transformations; bounded metadata, identity
\ scans and topological staging are additional work. A type that is no
\ visible Sort or Pi where one is needed is put in Lean's whnf first
\ (ensure_sort_core, ensure_pi_core: plan task 4.2.2c); uncertain
\ conversion is unknown.
\ Free variables (ADR 0014 Q2, plan task 4.2.2a; [kernel] code, not yet
\ through the review gate): the type inference gives back for a node is
\ closed, as in Lean's kernel (inside a chain of lambdas, an inner
\ lambda's type is over the scope's bound variables until the chain's top
\ closes it; only the enclosing lambda sees it). The terms it reads are
\ not: a source node is read under the scope (below), so the same node,
\ shared by two places (a hash-consed #0, say), stands for different
\ variables at different depths. A cache of inferred types (ADR 0014
\ Q10, plan task 4.2.7) must therefore be keyed by the opened term (a
\ closed copy) or by the node with the scope, never by the source node
\ alone. When inference enters a lambda or Pi (infer_lambda,
\ infer_pi, type_checker.cpp 125-166), the domain must be a type (S2),
\ and the binder gets a new free variable of the local context
\ (core/local-context.fs) whose type is the domain closed with the free
\ variables of the binders around it (instantiate_rev, mixed-open.fs); it
\ waits on the job's scope, which grows as binders are opened (a scope
\ the heap cannot grow is full, as the binder context was). A chain of lambdas has Lean's mk_pi over its free
\ variables of the innermost body's type as its type, built once from the
\ inside out (lf-minfer-lam), a Pi the Sort of the levels' imax, and a
\ free variable its entry's type (infer_fvar, 93-99). Inference reads its
\ source terms under the scope: a loose bound variable k is the scope's
\ free variable k places from the top, so inferring a term under the
\ scope is inferring Lean's instantiate_rev of it with the scope's free
\ variables -- the same types, from the same checks in the same order --
\ without copying each body first (Lean opens a telescope of binders at
\ once; the binders here are entered one by one, each one inference step
\ with its source node as its subject, as the derivation log records it).
\ An application's argument is closed before it is put into the Pi body
\ (not for a body without loose bound variables, which Lean's instantiate
\ gives back without reading it: ADR 0014 Amendment 6), by Lean's
\ instantiate without the audit that lf-mixed-instantiate ran
\ before free variables: the body is a type inference made or the audited
\ input holds, the argument an audited source node closed by mixed-open
\ (which checks each leaf's shape, liveness and child order), and every
\ comparison that can lead to acceptance audits both of its graphs
\ (lf-minfer-compare, through lf-mixed-convert-keeping).
\ Scratch a step no longer needs is discarded (lf-minfer-discard). As Lean, the innermost body's type of a
\ chain of lambdas goes through cheap_beta_reduce (instantiate.cpp
\ 211-230, type_checker.cpp 140; whnf.fs), since plan task 4.2.2c.
\ Rejection ([kernel] code, not yet through the review gate): a type
\ whose whnf is no Sort or Pi is Lean's typeExpected or funExpected,
\ rejected with the codes of ADR 0011's rules S1, S2, S4 and F1, which
\ Lean's ensure_sort_core and ensure_pi_core replace since plan task
\ 4.2.2c. A comparison is Lean's is_def_eq (defeq.fs): its no is the
\ step's exception, appTypeMismatch, declTypeMismatch or, for a let term's
\ value (infer_let, plan task 4.2.3; its section below), letTypeMismatch,
\ rejected (since
\ plan task 4.2.2d, which retired ADR 0011's rules D1-D5); where the port
\ cannot decide it is unknown, or exhausted or full. Like every result
\ here, a rejection holds only if the candidate signatures are the
\ constants' true types: they are unchecked assumptions at this
\ interface. Inference "aside" is Lean's infer-only mode (infer_type,
\ type_checker.cpp 360-362), for the comparison's typer (lf-minfer-typed:
\ whether a term is a proof, its type for unit-like types): no
\ comparison, an application's argument neither inferred nor compared
\ (its spine typed from its head, lf-minfer-spine), a lambda's domain and
\ a let's type and value not typed (infer_lambda 131-133, infer_let 215),
\ no universe-parameter test of a Sort or a constant, any live node read
\ (whnf results and inferred types, which the checker's own passes made
\ from the audited input). What Lean's infer-only typing still tests --
\ a Pi's domains and body are types (infer_pi), a function's type is a Pi
\ (infer_app's ensure_pi_core), a projection's structure (infer_proj) --
\ rejects aside as while deciding: Lean throws there in either mode, and
\ the exception ends the check (plan task 4.2.7d; ADR 0014 Amendment 10).
\ Environment mode (plan task 2.2.3; [kernel] code, not yet through the
\ review gate): a job started with lf-minfer-start-env, by
\ check-declaration.fs, takes a constant's type from the checked
\ environment within the check's snapshot instead of the signature index,
\ and checks a Sort's level against the declaration's universe parameters
\ when it visits the Sort: rules N1, K5, L1 and L2 at the place and in the
\ order Lean's kernel checks them (env-signature.fs). A job started with
\ lf-minfer-start, as by lf-mixed-infer and the probes, never uses it.
\ State: one inference record, lf-minfer-job (fields lf-ijob-*): fuel, frame
\ depth, index token, the scratch mark before the call, the scope (the
\ opened binders' free variables and a Pi telescope's levels), whether
\ inference runs aside, whether it runs in environment mode, a copy of a
\ reference's levels, the arguments of the spines typed aside
\ (lf-minfer-spine-cells and the count in use); a member of the checker context
\ (lib/context.fs). Lean's whnf (whnf.fs) runs on the job's frames. A
\ step's mark (lf-minfer-discard) is on scratch-marks.fs's mark stack.
\ The local context is local-context.fs's: emptied when a job starts;
\ discarding scratch (a binder domain's or an argument's inference, a
\ Pi's, a failure) drops the
\ entries of the free variables it discards with them (lf-lctx-drop), so
\ their numbers may be taken again and the entries never outnumber the
\ live nodes. A node's intermediate results wait on the job's frames, an
\ explicit stack in the heap that grows with the depth (lib/frame.fs;
\ plan task 6.2.0): no depth limit, and a stack the heap cannot grow is
\ full. Single-threaded within one context. lf-minfer-walk,
\ lf-minfer-apart and a few steps are deferred only so that words defined
\ before them can call them, and set once, at load time, and shared.
\ Stack use: see "Host stacks" at the end.
\ mixed-definition-probe.fs starts a job with
\ lf-minfer-start, calls lf-minfer-walk, lf-minfer-sort-rule,
\ lf-minfer-zero?, lf-minfer-agree, lf-minfer-verdict and lf-minfer-reject
\ directly, and reads lf-minfer-fuel afterwards; check-declaration.fs does
\ the same with lf-minfer-start-env.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/constant-term-scope.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/generation-handles.fs
require ../core/let-terms.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/projections.fs
require ../core/scratch-marks.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./env-signature.fs
require ./level-compare.fs
require ./level-make.fs
require ./level-normalize.fs
require ./level-value.fs
require ./mixed-beta.fs
require ./mixed-convert.fs
require ./mixed-head.fs
require ./mixed-open.fs
require ./mixed-signature-audit.fs
require ./mixed-signature-probe.fs
require ./reduce-nat.fs
require ./string-literals.fs
require ./whnf.fs

begin-structure /lf-ijob
  /frames +field lf-ijob-frames  \ fuel, visits in progress, the explicit stack
  field: lf-ijob-token     \ signature index token
  field: lf-ijob-binders   \ free variables on the scope
  field: lf-ijob-aside     \ true while inference runs aside (infer-only)
  field: lf-ijob-env       \ true in environment mode (lf-minfer-start-env)
  field: lf-ijob-argument  \ the argument an application's type is instantiated with
  field: lf-ijob-chain     \ for a lambda's lambda body, where the chain began, else -1
  field: lf-ijob-inner     \ true while a Pi's Pi body is entered (no cache key)
  field: lf-ijob-spine     \ cells of lf-minfer-spine-cells in use (aside spines)
  /lf-scratch +field lf-ijob-mark  \ the stores before the call (scratch-marks.fs)
end-structure
0 lf-ijob-frames 0<> [if] .( mixed-infer.fs: frames must come first) cr abort [then]
/lf-ijob context-record: lf-minfer-job
: lf-ijob-fuel ( job -- addr ) lf-ijob-frames frame-fuel ;     \ visits left
: lf-ijob-depth ( job -- addr ) lf-ijob-frames frame-depth ;   \ visits in progress
\ The scope's free variables, outermost first, and beside each its
\ domain's Sort level (Pis): as many as are opened (no fixed limit).
1 cells context-slab: lf-minfer-fvars
1 cells context-slab: lf-minfer-sorts
\ A constant's universe arguments, copied: as many as it has (no fixed
\ limit); one the heap cannot hold is full.
2 cells context-slab: lf-minfer-actual-pairs
\ The arguments of the applications that infer-only inference is typing
\ (lf-minfer-spine), outermost first, a stack: the job's lf-ijob-spine
\ cells are in use (no fixed limit; one the heap cannot hold is full).
1 cells context-slab: lf-minfer-spine-cells

\ Fields of the record. Tests read the fuel left and the scope's depth
\ (the binders opened), and mixed-definition-probe reads the fuel left.
: lf-minfer-frames ( -- frames ) lf-minfer-job lf-ijob-frames ;
: lf-minfer-fuel ( -- addr ) lf-minfer-job lf-ijob-fuel ;
: lf-minfer-depth ( -- addr ) lf-minfer-job lf-ijob-depth ;
: lf-minfer-token ( -- addr ) lf-minfer-job lf-ijob-token ;
: lf-minfer-context-depth ( -- addr ) lf-minfer-job lf-ijob-binders ;
: lf-minfer-aside ( -- addr ) lf-minfer-job lf-ijob-aside ;
\ Rejection rules run only when inference does not run aside.
: lf-minfer-deciding? ( -- flag ) lf-minfer-aside @ 0= ;
: lf-minfer-env? ( -- flag ) lf-minfer-job lf-ijob-env @ ;
\ Mode flags are registers of the checker context, never shared between
\ contexts: the aside flag here, set around one nested inference and
\ restored (lf-minfer-typed); the environment flag, set for a whole
\ job by lf-minfer-start-env and cleared by lf-minfer-start; and the keep
\ flags of the comparisons (mixed-convert's walk-arg, level-compare's
\ lf-lcrec-keep), which each call sets afresh (lf-mixed-convert-keeping,
\ lf-level-compare-keeping).

\ Helpers run on the fuel left and inference continues with what they leave.
\ They report only ok, invalid, exhausted or full, and the signature lookup
\ also unknown; outcome-sane passes any outcome on unchanged (so rejected or
\ unsupported too, once ADR 0008 step 3 lets helpers return them; still not
\ ok) and makes anything else invalid. A failed step has no type (-1).
: lf-minfer-refuel ( fuel-addr -- ) @ lf-minfer-fuel ! ;
: lf-minfer-none ( status -- type status ) -1 swap ;
\ Failures of inference itself are recorded as diagnostics at this site.
: lf-minfer-site ( -- site ) c" mixed-infer lf-mixed-infer" ;
\ Scratch that a step no longer needs once it has succeeded -- what a
\ binder domain's, an application argument's or a Pi telescope's
\ inference made beyond its Sort level or its verdict -- is discarded:
\ the terms and their local-context entries go back to a mark on the
\ scratch mark stack taken before it (lf-scratch-cut, scratch-marks.fs),
\ the levels and references stay (the Sort level may be one the step
\ made). A measure for small term stores, so that free variables (plan
\ task 4.2.2a) fit where the binder context did; it changes no result, as
\ nothing made after the mark is used again. With the caches of ADR 0014
\ Q10 on, which keep scratch until the job ends (kernel/caches.fs sets the
\ hook), and after a failure, the mark is let go and nothing discarded;
\ after a failure the job's own rollback discards everything. Every step
\ mark is used exactly once, here, whatever the outcome, so the stack
\ stays LIFO: a mark is taken just before its step's child visit and used
\ once that child (and every mark taken inside it) is done. A mark the
\ stack refuses (out of order) makes a succeeding step invalid; number 0,
\ of a mark that could not be taken, comes only with a failed step
\ (lf-minfer-call-marked).
defer lf-minfer-keeps? ( -- flag )
:noname ( -- flag ) false ; is lf-minfer-keeps?
: lf-minfer-discard ( outcome mark -- outcome )
  over ok? lf-minfer-keeps? 0= and if lf-scratch-cut else lf-scratch-drop then
  lf-scratch-settled ;
: lf-minfer-note ( n1 n2 code -- ) lf-minfer-site swap lf-diag-note ;

\ The scope: the free variables of the binders opened around the node
\ being inferred, outermost first, each with a level beside it (a Pi
\ domain's Sort level, else 0). A binder is opened once its domain is
\ checked, where Lean extends its local context (type_checker.cpp 131-136,
\ 151-155): a new entry of the local context, of the domain as its type,
\ with its place on the scope (which the derivation log reads).
\ A scope the heap cannot grow is full (plan task 6.2.0), recorded as a
\ full binder context with the depth and the room, whatever fuel is left
\ (ADR 0008); so is a full local context or term store. Every telescope
\ gives its binders back when it ends (lf-minfer-unbind), whatever the
\ outcome; their entries stay while their nodes do, and go with them when
\ scratch is discarded.
: lf-minfer-fvar-cell ( i -- addr ) cells lf-minfer-fvars slab-base + ;
: lf-minfer-sort-cell ( i -- addr ) cells lf-minfer-sorts slab-base + ;
: lf-minfer-crowded ( -- outcome )
  lf-minfer-context-depth @ lf-minfer-fvars slab-capacity lf-diag-binders-full
  lf-minfer-note outcome-full ;
: lf-minfer-scope-room? ( -- flag )
  lf-minfer-context-depth @ 1+ dup lf-minfer-fvars slab-hold ok?
  swap lf-minfer-sorts slab-hold ok? and ;
: lf-minfer-scope-push ( fvar level -- )
  lf-minfer-context-depth @ tuck lf-minfer-sort-cell ! lf-minfer-fvar-cell !
  1 lf-minfer-context-depth +! ;
: lf-minfer-placed ( fvar -- fvar ) lf-minfer-context-depth @ over lf-fvar-depth! ;
: lf-minfer-bind ( type level -- outcome )
  lf-minfer-scope-room? 0= if 2drop lf-minfer-crowded exit then
  swap lf-lctx-local ok-then? if lf-minfer-placed swap lf-minfer-scope-push outcome-ok
  else nip then ;
: lf-minfer-unbind ( base -- ) lf-minfer-context-depth ! ;
\ The free variables opened since base: their cells and their number.
: lf-minfer-opened ( base -- fvars n )
  dup lf-minfer-fvar-cell swap lf-minfer-context-depth @ swap - ;

\ How many of the scope's innermost free variables a term read under it
\ names: 1 + the largest k - d over its bound variables k under d of its
\ own binders, or 0. A scan of its own (once per path, as the passes
\ visit), of at most as many visits as the job has fuel, spending none of
\ it; one that cannot finish gives n, every free variable.
lf-walk-room context-walk2: lf-minfer-scan
: lf-minfer-scan-bvar ( first second walk -- outcome )
  nip tuck walk-context @ - over walk-arg @ max swap walk-arg ! outcome-ok ;
: lf-minfer-scan-dispatch ( first second walk tag -- outcome )
  ['] lf-minfer-scan-bvar lf-whnf-scan-step ;
: lf-minfer-scan-visit ( walk -- outcome ) ['] lf-minfer-scan-dispatch lf-term-visit ;
\ The scan keeps the largest k - d (-1 for none), so that no index
\ overflows; m is one more, at most n.
: lf-minfer-scanned ( node n -- m )
  >r -1 lf-minfer-scan walk-arg ! lf-minfer-fuel @ lf-minfer-scan walk-budget 0=
  if drop r> exit then
  0 ['] lf-minfer-scan-visit lf-minfer-scan walk-run-pair ok?
  if lf-minfer-scan walk-arg @ r@ 1- min 1+ r> drop else r> then ;
\ That number is Lean's loose_bvar_range, which Lean reads from the node
\ (expr.cpp 102-103, computed once when the node is made), as the term
\ store keeps it in the node's data word (core/terms.fs, ADR 0016 C1;
\ plan task 6.5.5): it is taken from there, at most n, and no scan runs.
\ A node without data asks the hook (the caches' memo, kernel/caches.fs;
\ by default never known), and only then is scanned.
defer lf-minfer-range ( node -- m true | false )
:noname ( node -- m true | false ) drop false ; is lf-minfer-range
: lf-minfer-word ( node -- m true | false )
  lf-term-data@ if lf-data-loose true else false then ;
: lf-minfer-loose ( node n -- m )
  over lf-minfer-word if min nip exit then
  over lf-minfer-range if min nip else lf-minfer-scanned then ;
\ Of n free variables, the innermost that node needs, at least one: the
\ pass then visits and pays for node as with all n, and gives the same
\ term, while checking and copying only those (plan task 6.2.0: a
\ binder's domain is closed in time independent of the scope's depth).
: lf-minfer-needed ( node fvars n -- node fvars' n' )
  dup 2 < if exit then
  2 pick over lf-minfer-loose 1 max tuck - cells rot + swap ;

\ Closing on the job's fuel (mixed-open.fs), which continues with what it
\ leaves: a term read under the scope, with the scope's free variables put
\ for its loose bound variables (instantiate_rev; the scope's binders);
\ ok, invalid, exhausted or full. A closing under the whole scope is a
\ function of the scope, which its innermost free variable names, so
\ mixed-open.fs keeps its results for every later closing under it
\ (lf-instantiate-scope): an argument closed once is not closed again
\ inside a larger argument, which inference closes after it (plan task
\ 6.5.5; ADR 0014, Amendment 3).
: lf-minfer-lend ( -- ) lf-minfer-fuel @ lf-open-fuel ! ;
: lf-minfer-repay ( -- ) lf-open-fuel @ lf-minfer-fuel ! ;
: lf-minfer-close ( node -- node' status )
  lf-minfer-lend 0 lf-minfer-opened lf-minfer-needed lf-instantiate-scope lf-minfer-repay
  outcome-sane ;

\ Live nodes as handles; the right one is checked first.
: lf-minfer-handle ( node -- node identity true | false )
  dup lf-term-identity dup 0= if nip then ;
: lf-minfer-handles ( left right -- left lid right rid true | false )
  lf-minfer-handle 0= if drop false exit then 2>r
  lf-minfer-handle if 2r> true else 2r> 2drop false then ;

\ Compare two types by Lean's is_def_eq (conversion, which validates both
\ graphs first), with the shared fuel, lending the comparison the typer
\ (lf-minfer-typed, below). An undecided comparison keeps the fuel it
\ left (a failed inference leaves no fuel in the end anyway).
defer lf-minfer-typer ( node frames -- type outcome )
: lf-minfer-convert ( left lid right rid -- status )
  ['] lf-minfer-typer lf-dq-typer !
  lf-minfer-fuel @ lf-mixed-convert-keeping lf-mconvert-fuel lf-minfer-refuel
  0 lf-dq-typer ! outcome-sane ;
: lf-minfer-compare ( left right -- status )
  lf-minfer-handles if lf-minfer-convert else outcome-invalid then ;
\ A Pi body with an argument put for its bound variable, as infer_app
\ does (type_checker.cpp 187: Lean's instantiate, mixed-open.fs), on the
\ job's fuel: the argument, a source term read under the scope, is first
\ closed with the scope's free variables. With the derivation log on
\ (ADR 0013) this is one instantiate step of the Pi body and the argument,
\ as before free variables; both paths run the same words.
: lf-minfer-put ( -- addr ) lf-minfer-job lf-ijob-argument ;
: lf-minfer-substitute ( body argument -- type status )
  lf-minfer-put ! lf-minfer-lend lf-minfer-put 1 lf-instantiate lf-minfer-repay
  outcome-sane ;
\ Lean's instantiate gives back a body without loose bound variables at
\ once, never reading the argument (instantiate.cpp 22: offset 0 at least
\ the body's loose_bvar_range), as for a non-dependent arrow's body. So
\ the argument is then not closed (plan task 6.5.5, agent PF): the
\ substitution runs with the argument as it is, which it never reads, as
\ no loose bound variable remains to put it for; it keeps the body by its
\ data word (mixed-open.fs) for one unit, or walks it and meets a dead
\ free variable as before.
: lf-minfer-closed-body? ( body -- flag )
  lf-term-data@ if lf-data-loose 0= else false then ;
: lf-minfer-put-closed ( body argument -- type status )
  over lf-minfer-closed-body? if lf-minfer-substitute exit then
  lf-minfer-close ok-then? if lf-minfer-substitute else nip no-result then ;
: lf-minfer-instantiate ( body argument -- type status )
  lf-log? if 2dup lf-rule-instantiate lf-log-open lf-minfer-put-closed lf-log-close
  else lf-minfer-put-closed then ;

\ A stamped symbolic Sort for an allocated level; an allocator failure (a
\ full store or a spent serial) is full and cannot yield a type.
: lf-minfer-sort ( level -- type status )
  dup lf-level-identity 0= if drop -1 outcome-invalid exit then
  lf-hterm-sort if drop outcome-ok else -1 outcome-full then ;
\ A visited Sort's type. In environment mode, while deciding, its level
\ must first use only the declaration's universe parameters (L2), checked
\ with the job's fuel (env-signature.fs).
: lf-minfer-scoped? ( -- flag ) lf-minfer-env? lf-minfer-deciding? and ;
: lf-minfer-scope-level ( level -- level status )
  dup lf-minfer-fuel @ lf-env-level-scope swap lf-minfer-fuel ! ;
: lf-minfer-sort-scope ( level -- level status )
  lf-minfer-scoped? if lf-minfer-scope-level else outcome-ok then ;
: lf-minfer-sort-type ( level -- type status )
  lf-minfer-sort-scope ok-then? 0= if no-result exit then
  lf-level-succ if lf-minfer-sort else -1 outcome-full then ;

\ A node that is a Sort, with its level; a node that is a Pi, with its
\ domain and body.
: lf-minfer-sort? ( node -- level true | false )
  lf-term-read if drop swap lf-tag-symbolic-sort = dup 0= if nip then else false then ;
: lf-minfer-pi? ( node -- domain body true | false )
  lf-term-read if rot lf-tag-pi = if true exit then 2drop then false ;

\ A constant: specialize its candidate signature to the reference's levels,
\ first copied into this record (specialization needs its input disjoint
\ from every arena and scratch area). In environment mode the signature is
\ the accepted declaration's stored type, found in the checked environment
\ (env-signature.fs: N1, K5, L1, then L2 while deciding), else the
\ candidate in the index. Success continues with the fuel the
\ specialization left; a failure leaves no fuel.
: lf-minfer-actuals ( -- addr ) 0 lf-minfer-actual-pairs slab-at ;
: lf-minfer-copy ( slot -- addr count )
  lf-cref-pairs tuck 2* cells lf-minfer-actuals swap move lf-minfer-actuals swap ;
: lf-minfer-specialized ( root identity fuel' 0 | status -- type status )
  outcome-sane dup ok? if drop lf-minfer-fuel ! drop outcome-ok
  else 0 lf-minfer-fuel ! lf-minfer-none then ;
: lf-minfer-candidate ( name pairs count -- root identity fuel' 0 | status )
  2>r lf-minfer-token @ swap 2r> lf-minfer-fuel @ lf-msp-specialize-fuel ;
: lf-minfer-stored ( name pairs count -- root identity fuel' 0 | status )
  lf-minfer-fuel @ lf-minfer-deciding? lf-env-signature ;
: lf-minfer-signature ( name pairs count -- root identity fuel' 0 | status )
  lf-minfer-env? if lf-minfer-stored else lf-minfer-candidate then ;
: lf-minfer-room? ( slot -- slot flag )
  dup lf-crec-arity @ lf-minfer-actual-pairs slab-hold ok? ;
: lf-minfer-constant ( reference -- type status )
  lf-cref-slot lf-minfer-room? 0= if drop -1 outcome-full exit then
  dup lf-crec-name @ swap lf-minfer-copy lf-minfer-signature lf-minfer-specialized ;

\ A free variable has its entry's type (infer_fvar, type_checker.cpp
\ 93-99); one that the local context does not name is malformed. A bound
\ variable k read under the scope is the scope's free variable k places
\ from the top (see the header), so it has that variable's type; one
\ beyond the scope is out of scope, invalid (preflight finds every such
\ input first).
: lf-minfer-fvar? ( node -- flag )
  dup lf-term-valid? if lf-term-tag@ lf-tag-fvar = else drop false then ;
: lf-minfer-fvar ( node -- type status )
  dup lf-fvar-live? if lf-fvar-type outcome-ok exit then
  0 lf-diag-malformed lf-minfer-note -1 outcome-invalid ;
: lf-minfer-unbound ( index binders -- type status )
  lf-diag-out-of-scope lf-minfer-note -1 outcome-invalid ;
: lf-minfer-bvar ( index -- type status )
  lf-minfer-context-depth @ 2dup < 0= if lf-minfer-unbound exit then
  swap - 1- lf-minfer-fvar-cell @ lf-minfer-fvar ;

\ Inference runs on the job's frames, an explicit stack that grows with
\ the depth (lib/frame.fs; plan task 6.2.0): a node's visit is a chain of
\ steps ( ... frames -- ... frames next ) that keep on the stack what they
\ need across a child's visit. lf-minfer-walk ( node -- type status ) runs
\ one visit to its end, as a loop of its own from what the stack then
\ holds, so that the typer and the callers outside can use it from inside
\ a step.
defer lf-minfer-walk ( node -- type status )

\ Rejection (ADR 0011, ADR 0014): a rejection replaces whatever was
\ recorded with its own record (lf-minfer-reject). The helpers report ok
\ or a failure, and a failure leaves no fuel.
: lf-minfer-reject ( n1 site code -- outcome ) 0 -rot lf-diag! outcome-rejected ;
\ The rejection of a comparison: Lean's no, (mask rejected), is recorded
\ at site with code and the mask (0 since plan task 4.2.2d); any other
\ outcome passes, among them the exception Lean's is_def_eq throws inside
\ (lf-mixed-convert-no? false: an unknown constant, ...) with its own record.
: lf-minfer-no? ( status -- flag ) outcome-rejected = lf-mixed-convert-no? and ;
: lf-minfer-verdict ( mask status site code -- status )
  2swap dup lf-minfer-no? if drop -rot lf-minfer-reject else nip nip nip then ;
: lf-minfer-take ( status addr -- status )
  over ok? if lf-minfer-refuel else drop 0 lf-minfer-fuel ! then ;
\ whnfB (ADR 0003 step 1) of a live node, with the job's fuel (for
\ check-block.fs's stand-in, until plan task 5.2.1b moves it to whnf.fs).
: lf-minfer-reduce ( node identity -- node' status )
  lf-minfer-fuel @ lf-mixed-beta nip outcome-sane lf-mbeta-fuel lf-minfer-take ;
: lf-minfer-whnf ( node -- node' status )
  dup lf-term-identity if lf-minfer-reduce else drop -1 outcome-invalid then ;
\ Lean's normalizes_to_zero on a level, with the job's fuel (S3).
: lf-minfer-zero? ( level -- flag status )
  lf-minfer-fuel @ lf-level-zero? lf-lvalue-fuel lf-minfer-take ;

\ Lean's ensure_sort_core and ensure_pi_core (type_checker.cpp 62-83;
\ ADR 0014 Q1, plan task 4.2.2c), which replace ADR 0011's rules S1, S2,
\ S4 and F1: a type that is a Sort (a Pi) as it is; otherwise its whnf
\ (whnf.fs: beta, and delta in a check of the checked environment), on
\ the job's frames and fuel, must be one. A whnf that is neither is
\ Lean's typeExpected (funExpected): rejected at site with code and the
\ reduced type, as ADR 0011's rules recorded it -- aside too (the typer),
\ where Lean's infer-only typing throws the same exception, which no step
\ of is_def_eq catches (plan task 4.2.7d; review rvKN 3: before, aside
\ said unknown). A whnf that fails passes its outcome on (unknown where
\ Lean may reduce further than LeanForth yet, whnf.fs; exhausted, full,
\ invalid).
: lf-minfer-whnf-job ( node -- node' status ) lf-minfer-frames lf-whnf-on ;
: lf-minfer-not-type ( reduced site code -- -1 status ) lf-minfer-reject no-result ;
: lf-minfer-sort-rule ( type site code -- level status )
  2>r dup lf-minfer-sort? if nip 2r> 2drop outcome-ok exit then
  lf-minfer-whnf-job ok-then? 0= if 2r> 2drop no-result exit then
  dup lf-minfer-sort? if nip 2r> 2drop outcome-ok else 2r> lf-minfer-not-type then ;
: lf-minfer-not-pi ( reduced -- outcome )
  lf-minfer-site lf-diag-function-expected lf-minfer-reject ;

\ Comparing an inferred type (left) with an expected type (right): Lean's
\ is_def_eq through conversion (defeq.fs, mixed-convert.fs), (0 ok) when
\ equal, (0 rejected) when Lean says no, which the caller reports as its
\ step's exception with lf-minfer-verdict (appTypeMismatch,
\ declTypeMismatch, check-block's constructor parameter); otherwise (0
\ outcome), the comparison's own. The 0 is where ADR 0011's rejection
\ analysis kept the mask of its rules D1-D5, each a sufficient condition
\ for Lean's no, which the port computes itself: plan task 4.2.2d retired
\ the analysis (ADR 0014 Q1), after a cross-check in which it never showed
\ apart a pair the port did not reject (or run out of fuel on).
: lf-minfer-agree ( left right -- mask status ) lf-minfer-compare 0 swap ;
\ A frame and a unit of fuel for each visit; the diagnostics of the
\ refusals are inference's.
: lf-minfer-frames-full ( -- ) lf-minfer-frames frame-room@ lf-diag-frame-limit lf-minfer-note ;
: lf-minfer-refused ( outcome -- outcome )
  dup outcome-full = if lf-minfer-frames-full exit then
  dup outcome-exhausted = if lf-minfer-fuel @ lf-minfer-site lf-diag-exhausted then ;
: lf-minfer-room ( frames -- outcome ) frame-admit dup ok? 0= if lf-minfer-refused then ;
\ A binder a caller enters itself (check-block.fs): its domain, a term
\ read under the scope, closed, as the scope's next free variable.
: lf-minfer-enter-binder ( domain -- status ) lf-minfer-close ok-then? if 0 lf-minfer-bind then ;

\ Inference's visits. lf-minfer-call asks for the visit of node,
\ continuing with cont ( type status frames -- ... ); the visit's first
\ step is the frames' visitor, lf-minfer-visit-step below.
: lf-minfer-call ( node frames cont -- ... frames next )
  over lf-minfer-room dup ok? if drop frame-opened else frame-refuse then ;
\ A step's mark on the scratch mark stack (lf-minfer-discard), its number
\ saved on the frames where the step finds it: ok; or full (the stack
\ cannot grow: recorded with its depth and room) or invalid (a store's
\ count is not valid), with number 0 saved.
: lf-minfer-stack-full ( -- ) lf-scratch-size lf-diag-work-stack-full lf-minfer-note ;
: lf-minfer-unmarked ( outcome -- outcome )
  dup outcome-full = if lf-minfer-stack-full then ;
: lf-minfer-marked ( frames -- outcome )
  >r lf-scratch-push dup ok? 0= if lf-minfer-unmarked then swap r> frame-save ;
\ The visit of node once the step's mark is taken; when it could not be,
\ the step continues at once with no result and that outcome, as after a
\ refused visit (its mark, number 0, is then only let go, and refused).
: lf-minfer-call-marked ( node outcome frames cont -- ... frames next )
  rot dup ok? if drop lf-minfer-call else frame-refuse then ;

\ Application while deciding, in three steps (infer_app, type_checker.cpp
\ 173-187; aside, lf-minfer-spine below types the whole spine): the
\ function's type must be a Pi, after whnf when it is no visible one
\ (ensure_pi_core: otherwise rejected, funExpected, or the whnf's
\ failure), the argument's type must convert to its domain (otherwise
\ unknown, or rejected when Lean says no: appTypeMismatch), and the type is the Pi
\ body instantiated with the argument. The argument waits on the stack
\ while the function's type is inferred; the body, the argument, the
\ domain and the mark taken before the argument's inference (its scratch
\ is discarded) while the argument's is.
: lf-minfer-pi-whnf ( type -- domain body true | outcome false )
  lf-minfer-whnf-job ok-then? 0= if false exit then
  dup lf-minfer-pi? if rot drop true else lf-minfer-not-pi false then ;
: lf-minfer-pi-parts ( type -- domain body true | outcome false )
  dup lf-minfer-pi? if rot drop true else lf-minfer-pi-whnf then ;
: lf-minfer-argued ( mark domain A status -- status )
  ok-then? 0= if nip swap lf-minfer-discard exit then
  swap lf-minfer-agree lf-minfer-site lf-diag-argument-apart lf-minfer-verdict
  swap lf-minfer-discard ;
: lf-minfer-applied ( body argument status -- type status )
  ok-then? if lf-minfer-instantiate else nip lf-minfer-none then ;
\ Lean's eager mode (tc 168-183): an argument eagerReduce _ _, its head
\ matched by name, is compared with the domain in eager mode (defeq.fs).
: lf-minfer-eager? ( node -- flag )
  lf-mhead-spine 2 = over lf-term-tag@ lf-tag-constant = and 0= if drop false exit then
  lf-whnf-cref lf-crec-name @ dup s" eagerReduce" lf-name-str-is?
  if lf-name-prefix@ lf-whnf-anon? else drop false then ;
: lf-minfer-app-arg ( A status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore 0 r@ frame-pick lf-minfer-eager? lf-dq-eager !
  2swap lf-minfer-argued false lf-dq-eager !
  r@ frame-restore r@ frame-restore swap rot lf-minfer-applied r> 0 ;
: lf-minfer-app-fn ( T status frames -- ... frames next )
  >r r@ frame-restore -rot ok-keep? 0= if r> 0 exit then
  lf-minfer-pi-parts 0= if nip lf-minfer-none r> 0 exit then
  r@ frame-save swap dup r@ frame-save swap r@ frame-save r@ lf-minfer-marked
  r> ['] lf-minfer-app-arg lf-minfer-call-marked ;
\ A projection (plan task 5.2.2): a projection leaf and its structure
\ term (core/projections.fs), typed by Lean's infer_proj in
\ infer-proj.fs, which sets this hook while loading; unknown before.
: lf-minfer-proj-unset ( leaf e frames -- -1 status frames 0 )
  nip nip outcome-unknown no-result rot 0 ;
defer lf-minfer-proj ( leaf e frames -- ... frames next )
' lf-minfer-proj-unset is lf-minfer-proj
: lf-minfer-app ( function argument frames -- ... frames next )
  tuck frame-save ['] lf-minfer-app-fn lf-minfer-call ;

\ Source nodes lie below the term count at the start, as the job's mark
\ records it (none when the mark could not be taken); inference that runs
\ aside (the typer) reads every live node, among them the closed copies
\ it infers, whose free variables are read through their entries.
: lf-minfer-start-terms ( -- n ) lf-minfer-job lf-ijob-mark lf-scratch-terms ;
: lf-minfer-source? ( node -- flag )
  dup 0< 0= swap lf-minfer-start-terms < and lf-minfer-aside @ or ;
: lf-minfer-read ( node -- first second tag true | false )
  dup lf-minfer-source? 0= if drop false exit then lf-term-read dup if >r rot r> then ;

\ An application aside, as Lean's infer_app in infer-only mode
\ (type_checker.cpp 188-205): the spine f a1 .. an is typed from its head
\ alone. The head's type is inferred (and keyed, as infer_type_core(f,
\ true) keys it); then, for each argument in turn, a type that is a
\ visible Pi gives its body, and one that is not first has the arguments
\ since the last such point put for its loose bound variables at once
\ (instantiate_rev), is put in whnf when it is no Pi (ensure_pi_core:
\ else rejected, funExpected) and gives its body; last, the arguments since the
\ last point are put into the type at once. The application's prefixes
\ f a1 .. ak are neither typed nor keyed, and the type is the same term
\ as one argument at a time would give (instantiation keeps a visible
\ Pi a Pi), but each node of the type is visited once per point, not
\ once per argument (ADR 0014, Amendment 9). Arguments read under the
\ scope are closed first, those the type's loose range can name (Lean's
\ instantiate never reads the others). The arguments wait in
\ lf-minfer-spine-cells, outermost first, above those of the spines being
\ typed around this one (a whnf's iota may type aside again); the frames
\ keep where they start and how many there are.
: lf-minfer-spine-cell ( i -- addr ) lf-minfer-spine-cells slab-at ;
: lf-minfer-spine-top ( -- addr ) lf-minfer-job lf-ijob-spine ;
: lf-minfer-app? ( node -- first second true | false )
  lf-minfer-read 0= if false exit then lf-tag-app = if true else 2drop false then ;
: lf-minfer-spine-count ( function -- n )
  1 swap begin lf-minfer-app? while drop swap 1+ swap repeat ;
\ The arguments below the outermost, into cells c-1, c-2, ...; the head.
: lf-minfer-spine-fill ( function c -- head )
  begin over lf-minfer-app? while
    rot 1- tuck lf-minfer-spine-cell ! rot drop repeat drop ;
\ Room for n more cells: where they start, and ok or full.
: lf-minfer-spine-room ( n -- base outcome )
  lf-minfer-spine-top @ tuck + lf-minfer-spine-cells slab-hold ;
\ The innermost of k arguments that a type's loose range can name.
: lf-minfer-spine-needs ( T k -- m ) swap lf-term-data@ if lf-data-loose min then ;
\ Cells i .. i+n-1 closed in place with the scope's free variables.
: lf-minfer-close-cell ( i -- status )
  lf-minfer-spine-cell dup @ lf-minfer-close ok-then? if swap ! outcome-ok else nip then ;
: lf-minfer-close-at ( i k -- i status ) over + lf-minfer-close-cell ;
: lf-minfer-close-cells ( i n -- status ) ['] lf-minfer-close-at ok-each nip ;
: lf-minfer-spine-subst ( T i k -- T' status )
  swap lf-minfer-spine-cell swap lf-minfer-lend lf-instantiate-rev lf-minfer-repay
  outcome-sane ;
: lf-minfer-spine-put ( T i k -- T' status )
  2 pick over lf-minfer-spine-needs >r 2dup + r@ - r> lf-minfer-close-cells
  dup ok? if drop lf-minfer-spine-subst else >r drop 2drop r> lf-minfer-none then ;
\ The k arguments before cell c put into T at once.
: lf-minfer-spine-pending ( T k c -- T' status ) over - swap lf-minfer-spine-put ;
\ One argument (cell c): T and k, the arguments not yet put, after it.
: lf-minfer-spine-step ( T k c -- T' k' outcome )
  >r over lf-minfer-pi? if nip rot drop swap 1+ r> drop outcome-ok exit then
  r> lf-minfer-spine-pending ok-then? 0= if -1 0 rot exit then
  lf-minfer-pi-parts if nip 1 outcome-ok else -1 0 rot then ;
: lf-minfer-spine-loop ( T end base -- T k outcome )
  0 -rot ?do i lf-minfer-spine-step dup ok? 0= if unloop exit then drop loop outcome-ok ;
: lf-minfer-spine-type ( T base n -- type status )
  over + dup >r swap lf-minfer-spine-loop ok-then?
  if r> lf-minfer-spine-pending else r> drop nip lf-minfer-none then ;
: lf-minfer-spined ( T status base n -- type status )
  2swap ok-then? if -rot lf-minfer-spine-type else nip nip lf-minfer-none then ;
\ The head's type is known: the spine's, and its cells given back.
: lf-minfer-spine-fn ( T status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore over >r lf-minfer-spined
  r> lf-minfer-spine-top ! r> 0 ;
: lf-minfer-spine-keep ( base n frames -- base n ) >r 2dup r@ frame-save r> frame-save ;
\ The n arguments into cells base .. base+n-1, now in use; the head.
: lf-minfer-spine-head ( function argument base n -- head )
  + dup lf-minfer-spine-top ! 1- tuck lf-minfer-spine-cell ! lf-minfer-spine-fill ;
: lf-minfer-spine ( function argument frames -- ... frames next )
  >r over lf-minfer-spine-count dup lf-minfer-spine-room ok-then?
  0= if >r 2drop drop r> no-result r> 0 exit then
  swap r@ lf-minfer-spine-keep lf-minfer-spine-head
  r> ['] lf-minfer-spine-fn lf-minfer-call ;
\ An application node: its spine aside, the node itself while deciding.
: lf-minfer-app-node ( function argument frames -- ... frames next )
  lf-minfer-aside @ if lf-minfer-spine else lf-minfer-app then ;

\ Binders, one at a time, as infer_lambda and infer_pi treat each binder
\ of a telescope (type_checker.cpp 125-166). The domain, read under the
\ scope, must be a type, its type a Sort (otherwise rejected by S2, or the
\ whnf's failure); its inference's scratch is then discarded, and the binder gets
\ a free variable whose type is the domain closed with the scope's free
\ variables (instantiate_rev), with that Sort's level beside it. The body
\ is inferred one binder deeper, and the binder goes back to the scope
\ whatever the outcome (lf-minfer-unbind).
: lf-minfer-domain-sort ( type -- level status )
  lf-minfer-site lf-diag-domain-type lf-minfer-sort-rule ;
: lf-minfer-domain-level ( mark type status -- level status )
  dup ok? if drop lf-minfer-domain-sort then rot lf-minfer-discard ;
: lf-minfer-open-binder ( domain level -- status )
  swap lf-minfer-close ok-then? if swap lf-minfer-bind else nip then ;
: lf-minfer-bound ( domain mark D status -- status )
  lf-minfer-domain-level ok-then? if lf-minfer-open-binder else nip then ;
\ For a caller that walks a telescope itself, as Lean's check_constructors
\ does (check-block.fs, plan task 5.2.1a), in a job it started: a binder
\ domain's level (its inference and Sort, scratch kept); a domain, a term
\ read under the scope (source or not), closed and opened as the next
\ binder (level 0 beside it). Two such terms compare with lf-minfer-agree
\ as their closed copies would (Lean compares closed terms,
\ inductive.cpp 456-497): the comparison is structural on equal depths,
\ and the typer closes what it infers with the whole scope.
: lf-minfer-domain ( domain -- level status )
  lf-minfer-walk dup ok? if drop lf-minfer-domain-sort then ;
: lf-minfer-push ( domain -- outcome ) lf-minfer-enter-binder ;
\ A step that keeps base below its result: x and true, or -1, the failure
\ and false.
: lf-minfer-good? ( x status -- x true | -1 status false )
  dup ok? if drop true else nip no-result false then ;
\ A lambda's type: Lean's infer_lambda opens the whole chain of lambdas
\ (fun x1 ... fun xn => b) and makes the Pi over all their free variables
\ of b's type at once (mk_pi; type_checker.cpp 125-141, without
\ cheap_beta_reduce: see the header). Here each lambda is entered on its
\ own, and the chain's type is built from the inside out the same way:
\ b's type with the chain's free variables made bound variables
\ (abstract), then for each lambda the Pi of its source domain over it --
\ a Pi of the chain, as mk_pi makes it, since a source domain holds no
\ free variable and its chain binders are bound variables already; at the
\ chain's top, the loose bound variables of binders outside the chain
\ are closed with their free variables (instantiate_rev). So a lambda
\ inside the chain has its type over the scope's bound variables, at its
\ depth, as the derivation log records it, and the chain's type is
\ Lean's, built in one pass. The job's chain field names the depth where
\ the chain began while a lambda's body is a lambda; the inner lambda
\ takes it as it starts (lf-minfer-top), so no other node sees it.
\ Aside, as Lean's infer_lambda in infer-only mode (131-133; plan task
\ 4.2.7d), no domain is typed: it is closed and opened as the next
\ binder at once (0 beside it), and only the body is inferred.
\ Steps: the domain's inference (while deciding), with the scope's depth
\ before the binder (base), the chain's top, the domain, the body and the
\ step's mark waiting on the stack; then the body's, with base, top and
\ the domain.
: lf-minfer-chain ( -- addr ) lf-minfer-job lf-ijob-chain ;
: lf-minfer-top ( base -- top )
  lf-minfer-chain dup @ -1 rot ! dup 0< if drop else nip then ;
: lf-minfer-lam? ( node -- flag ) lf-minfer-read if nip nip lf-tag-lam = else false then ;
: lf-minfer-abstract ( type top -- type' status )
  lf-minfer-lend lf-minfer-opened lf-abstract lf-minfer-repay outcome-sane ;
: lf-minfer-lam-type ( domain type status -- type status )
  lf-minfer-good? if lf-term-pi room-result
  else rot drop then ;
: lf-minfer-lam-close ( base top type status -- type status )
  2swap over = >r lf-minfer-unbind r>
  if lf-minfer-good? if lf-minfer-close then then ;
: lf-minfer-lam-end ( T status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore r@ frame-restore 2>r -rot lf-minfer-lam-type
  2r> swap 2swap lf-minfer-lam-close r> 0 ;
: lf-minfer-lam-chained ( T status frames -- type status frames 0 )
  -1 lf-minfer-chain ! lf-minfer-lam-end ;
\ The innermost body's type T, put through cheap_beta_reduce first, as
\ infer_lambda does (type_checker.cpp 140, whnf.fs; plan task 4.2.2c).
: lf-minfer-body-type ( top T -- type status )
  lf-minfer-frames lf-cheap-beta
  ok-then? if swap lf-minfer-abstract else nip no-result then ;
: lf-minfer-lam-plain ( T status frames -- type status frames 0 )
  >r 1 r@ frame-pick -rot lf-minfer-good? if lf-minfer-body-type else rot drop then
  r> lf-minfer-lam-end ;
\ The body's visit, once the binder is open and base, top and the domain
\ wait on the frames.
: lf-minfer-lam-body ( body frames -- ... frames next )
  >r dup lf-minfer-lam? if 1 r@ frame-pick lf-minfer-chain ! r> ['] lf-minfer-lam-chained
  else r> ['] lf-minfer-lam-plain then lf-minfer-call ;
: lf-minfer-lam-domain ( D status frames -- ... frames next )
  >r 2 r@ frame-pick 0 r@ frame-pick 2swap lf-minfer-bound
  dup ok? 0= if no-result 5 r@ frame-drop r> 0 exit then
  drop 1 r@ frame-pick 2 r@ frame-drop r> lf-minfer-lam-body ;
: lf-minfer-lam-check ( domain body frames -- ... frames next )
  >r r@ frame-save r@ lf-minfer-marked r> ['] lf-minfer-lam-domain lf-minfer-call-marked ;
: lf-minfer-lam-aside ( domain body frames -- ... frames next )
  >r swap 0 lf-minfer-open-binder ok-then? if r> lf-minfer-lam-body exit then
  nip no-result 3 r@ frame-drop r> 0 ;
: lf-minfer-lam-keep ( domain frames -- )
  >r lf-minfer-context-depth @ dup r@ frame-save lf-minfer-top r@ frame-save
  r> frame-save ;
: lf-minfer-lam ( domain body frames -- ... frames next )
  >r over r@ lf-minfer-lam-keep
  lf-minfer-deciding? if r> lf-minfer-lam-check else r> lf-minfer-lam-aside then ;
\ A Pi's type is Sort (mk_imax u v) for a domain in Sort u and a body in
\ Sort v: Lean's infer_pi builds the level innermost first
\ (type_checker.cpp 158-165), as these steps do (ADR 0011, Amendment
\ 1; level-make.fs). S4 (ADR 0011, Amendment 2): the body's type must be a
\ Sort too (infer_pi's ensure_sort_core on the body, 158); when it is no
\ visible Sort and its whnfB is rigid and not a Sort, Lean's kernel fails
\ with typeExpected. A full level store is full. Only the level is
\ needed, so the Pi's scratch is discarded before its Sort is made. Two
\ marks are taken at the Pi's start, one for each discard: the domain's
\ scratch goes back to the newer (A), the whole Pi's to the older (B),
\ which the domain's failure lets go.
\ Steps: the domain's inference, with the scope's depth before the binder
\ (base), mark B, the body, mark A and the domain waiting on the stack;
\ then the body's, with base and mark B.
: lf-minfer-body-sort ( type -- level status )
  lf-minfer-site lf-diag-body-type lf-minfer-sort-rule ;
: lf-minfer-imax ( v base -- level status )
  lf-minfer-sort-cell @ swap lf-level-mk-imax room-result ;
: lf-minfer-pi-level ( base type -- base level status )
  lf-minfer-body-sort lf-minfer-good? if over lf-minfer-imax then ;
: lf-minfer-pi-end ( mark base level status -- type status )
  rot lf-minfer-unbind rot lf-minfer-discard lf-minfer-good? if lf-minfer-sort then ;
: lf-minfer-pi-body ( T status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore 2swap
  lf-minfer-good? if lf-minfer-pi-level then lf-minfer-pi-end r> 0 ;
\ A step mark let go on a failure path, where the step's own failure is
\ the outcome.
: lf-minfer-let-go ( mark -- ) lf-scratch-drop drop ;
\ Lean's infer_pi opens a chain of Pis at once (type_checker.cpp
\ 144-166): an inner Pi is never inferred on its own, so never looked up
\ or kept in the inferred-type cache (type_checker.cpp 332-334, 356). The
\ chain is entered one Pi at a time here; a Pi's body that is a Pi is
\ marked as inner while it is entered (lf-minfer-inner, which the caches
\ read, kernel/caches.fs), and its own visit takes the mark off.
: lf-minfer-inner ( -- addr ) lf-minfer-job lf-ijob-inner ;
: lf-minfer-pi-node? ( node -- flag )
  lf-minfer-read if nip nip lf-tag-pi = else false then ;
: lf-minfer-pi-inner ( body -- body ) dup lf-minfer-pi-node? lf-minfer-inner ! ;
: lf-minfer-pi-domain ( D status frames -- ... frames next )
  >r r@ frame-restore r@ frame-restore 2swap lf-minfer-bound
  dup ok? 0= if no-result 1 r@ frame-pick lf-minfer-let-go 3 r@ frame-drop r> 0 exit then
  drop r@ frame-restore lf-minfer-pi-inner r> ['] lf-minfer-pi-body lf-minfer-call ;
: lf-minfer-pi ( domain body frames -- ... frames next )
  false lf-minfer-inner !
  >r lf-minfer-context-depth @ r@ frame-save r@ lf-minfer-marked
  swap r@ frame-save r@ lf-minfer-marked lf-scratch-settled
  over r@ frame-save r> ['] lf-minfer-pi-domain lf-minfer-call-marked ;

\ A let term (core/let-terms.fs; plan task 4.2.3): Lean's infer_let
\ (type_checker.cpp 208-230). A chain of let terms, each the body of the
\ last, is entered in one visit, one let after another, as Lean's loop
\ does (212-226). For each, while deciding (not aside, 215-221): the
\ declared type T, read under the scope, must be a type (ensure_sort_core:
\ rejected with S2's code, Lean's typeExpected), its scratch discarded;
\ the value v's type must be is_def_eq to T closed with the scope's free
\ variables, else rejected, Lean's letTypeMismatch (219), the scratch of
\ v's inference and the comparison discarded. Then x gets a let variable
\ of the local context (lf-lctx-let; 223) whose type and value are T and
\ v closed, on the scope (0 beside it), and the body is read one binder
\ deeper. The innermost body's type goes through cheap_beta_reduce (228)
\ and is closed over the chain's let variables as Lean's mk_pi(fvars, r,
\ true) closes it (229; local_ctx.cpp 93-125, mk_binding with
\ remove_dead_let), innermost first: a variable the term so far does not
\ mention is dropped (its abstract is the term itself, by the update
\ rule of mixed-open.fs, where Lean finds no loose bound variable 0 and
\ lower_loose_bvars changes nothing in a term with no other), any other
\ wraps it, abstracted over x, in let x : T := v (nonDep false, mk_let's
\ default). The chain's variables leave the scope whatever the outcome. A
\ let term whose second argument is no lambda is malformed (invalid).
\ Steps: the scope's depth before the chain (base) waits on the stack
\ throughout; while deciding, T's inference with v, the lambda and a step
\ mark waiting, then v's with v, the lambda, T closed and another mark;
\ then the body's.
: lf-minfer-let-fail ( outcome n frames -- -1 outcome frames 0 )
  tuck frame-drop >r r@ frame-restore lf-minfer-unbind no-result r> 0 ;
: lf-minfer-bind-let ( type value -- outcome )
  lf-minfer-scope-room? 0= if 2drop lf-minfer-crowded exit then
  lf-lctx-let ok-then? if lf-minfer-placed 0 lf-minfer-scope-push outcome-ok then ;
: lf-minfer-let-bound ( Tc v -- outcome )
  lf-minfer-close ok-then? if lf-minfer-bind-let else nip then ;
\ The innermost body's type r closed over the scope's let variable i (x
\ in cell i): the term itself, or let x : T := v; r' with r' r abstracted.
: lf-minfer-let-wrap ( r' x -- let status )
  tuck lf-fvar-type swap lf-term-lam 0= if drop -1 outcome-full exit then
  swap lf-fvar-value swap 0 lf-let-make room-result ;
: lf-minfer-let-abstract ( r i -- r' status )
  lf-minfer-fvar-cell 1 lf-minfer-lend lf-abstract lf-minfer-repay outcome-sane ;
: lf-minfer-let-close1 ( r i -- r' status )
  2dup lf-minfer-let-abstract ok-then? 0= if nip nip no-result exit then
  rot 2dup = if drop nip outcome-ok exit then
  drop swap lf-minfer-fvar-cell @ lf-minfer-let-wrap ;
: lf-minfer-let-closed ( r base -- r' status )
  >r lf-minfer-context-depth @ begin dup r@ > while
    1- tuck lf-minfer-let-close1 ok-then? 0= if nip r> drop no-result exit then swap
  repeat drop r> drop outcome-ok ;
: lf-minfer-let-type-of ( R base -- type status )
  swap lf-minfer-frames lf-cheap-beta ok-then? 0= if nip no-result exit then
  swap lf-minfer-let-closed ;
: lf-minfer-let-end ( R status frames -- type status frames 0 )
  >r r@ frame-restore -rot lf-minfer-good? if over lf-minfer-let-type-of then
  rot lf-minfer-unbind r> 0 ;
defer lf-minfer-let-one ( v lam frames -- ... frames next )
: lf-minfer-let-bind ( Tc v lam frames -- ... frames next )
  >r -rot lf-minfer-let-bound dup ok? 0= if nip 0 r> lf-minfer-let-fail exit then drop
  lf-term-second@ dup lf-let? if dup lf-let-value swap lf-let-binder r> lf-minfer-let-one exit then
  r> ['] lf-minfer-let-end lf-minfer-call ;
: lf-minfer-let-argued ( mark Tc V status -- status )
  ok-then? 0= if nip swap lf-minfer-discard exit then
  swap lf-minfer-agree lf-minfer-site lf-diag-let-value-apart lf-minfer-verdict
  swap lf-minfer-discard ;
: lf-minfer-let-value ( V status frames -- ... frames next )
  >r r@ frame-restore 0 r@ frame-pick 2swap lf-minfer-let-argued
  dup ok? 0= if 3 r> lf-minfer-let-fail exit then drop
  r@ frame-restore r@ frame-restore r@ frame-restore swap r> lf-minfer-let-bind ;
: lf-minfer-let-tc ( level status frames -- Tc status )
  >r ok-then? if drop 0 r@ frame-pick lf-term-first@ lf-minfer-close else no-result then
  r> drop ;
: lf-minfer-let-type ( D status frames -- ... frames next )
  >r r@ frame-restore -rot lf-minfer-domain-level r@ lf-minfer-let-tc
  ok-then? 0= if 2 r> lf-minfer-let-fail exit then
  r@ frame-save r@ lf-minfer-marked
  3 r@ frame-pick swap r> ['] lf-minfer-let-value lf-minfer-call-marked ;
: lf-minfer-let-check ( v lam frames -- ... frames next )
  >r swap r@ frame-save dup r@ frame-save r@ lf-minfer-marked
  swap lf-term-first@ swap r> ['] lf-minfer-let-type lf-minfer-call-marked ;
: lf-minfer-let-open ( v lam frames -- ... frames next )
  >r dup lf-term-first@ lf-minfer-close ok-then? 0= if nip nip 0 r> lf-minfer-let-fail exit then
  -rot r> lf-minfer-let-bind ;
: lf-minfer-let-bad ( v lam frames -- -1 outcome frames 0 )
  >r nip 0 lf-diag-malformed lf-minfer-note outcome-invalid 0 r> lf-minfer-let-fail ;
:noname ( v lam frames -- ... frames next )
  over lf-term-tag@ lf-tag-lam <> if lf-minfer-let-bad exit then
  lf-minfer-deciding? if lf-minfer-let-check else lf-minfer-let-open then ; is lf-minfer-let-one
: lf-minfer-let ( v lam frames -- ... frames next )
  >r lf-minfer-context-depth @ r@ frame-save r> lf-minfer-let-one ;

\ Infer an original source node; nodes made by this inference are output
\ data, never input. Constructors outside this subset are unknown, and
\ recorded as unsupported with their tag.
: lf-minfer-unsupported ( tag -- tag -1 status )
  dup 0 lf-diag-unsupported lf-minfer-note -1 outcome-unknown ;
\ A projection leaf is never a term of its own (core/projections.fs):
\ malformed.
: lf-minfer-stray ( first -- -1 status ) 0 lf-diag-malformed lf-minfer-note -1 outcome-invalid ;
: lf-minfer-leaf ( first tag -- type status )
  case lf-tag-symbolic-sort of lf-minfer-sort-type endof
    lf-tag-constant of lf-minfer-constant endof
    lf-tag-bvar of lf-minfer-bvar endof
    lf-tag-lit of drop lf-reduce-nat-type endof
    lf-tag-proj of lf-minfer-stray endof
    lf-tag-str of drop lf-str-type endof
    nip lf-minfer-unsupported rot endcase ;
: lf-minfer-other ( first second frames tag -- -1 status frames 0 tag )
  >r >r 2drop r> r> lf-minfer-unsupported 2swap 0 swap ;
: lf-minfer-binary ( first second tag frames -- ... frames next )
  swap case lf-tag-app of lf-minfer-app-node endof
    lf-tag-lam of lf-minfer-lam endof
    lf-tag-pi of lf-minfer-pi endof
    lf-tag-let of lf-minfer-let endof  lf-tag-let-nondep of lf-minfer-let endof
    lf-tag-projection of lf-minfer-proj endof
    lf-minfer-other endcase ;
: lf-minfer-dispatch ( first second tag frames -- ... frames next )
  over lf-term-binary-tag? if lf-minfer-binary else >r nip lf-minfer-leaf r> 0 then ;
: lf-minfer-visit ( node frames -- ... frames next )
  >r dup lf-minfer-fvar? lf-minfer-aside @ and if lf-minfer-fvar r> 0 exit then
  lf-minfer-read if r> lf-minfer-dispatch else -1 outcome-invalid r> 0 then ;

\ A visit's first step, the frames' visitor. The derivation log (ADR
\ 0013): with it on, the visit is one inference step (sort, variable,
\ constant, application, lambda or Pi) at the binder context's depth,
\ closed by the step it keeps for the visit's end; both paths run the
\ same visit. A visit aside records no step: Lean's infer_only is no
\ derivation, and its applications lack the comparison the log's
\ structural check requires of an application step.
: lf-minfer-logged ( node -- node ) lf-minfer-context-depth @ lf-log-infer ;
: lf-minfer-closing ( type status frames -- type status frames 0 ) >r lf-log-close r> 0 ;
: lf-minfer-logging? ( -- flag ) lf-log? 0<> lf-minfer-deciding? and ;
: lf-minfer-visit-step ( node frames -- ... frames next )
  lf-minfer-logging? if ['] lf-minfer-closing over frame-save swap lf-minfer-logged swap then
  lf-minfer-visit ;
: lf-minfer-walk-run ( node -- type status )
  lf-minfer-frames ['] lf-minfer-call frame-through drop ;
' lf-minfer-walk-run is lf-minfer-walk
\ The frames and their visitor, set up once in every context; their stack
\ is freed with the context.
\ The visitor: lf-minfer-visit-step, or the inference cache's step around
\ it (kernel/caches.fs sets the hook).
defer lf-minfer-entry ( node frames -- ... frames next )
' lf-minfer-visit-step is lf-minfer-entry
: lf-minfer-setup ( -- ) ['] lf-minfer-entry lf-minfer-frames frame-init ;
' lf-minfer-setup context-setup
: lf-minfer-release ( -- ) lf-minfer-frames frame-free ;
' lf-minfer-release context-teardown

\ Preflight before any allocation: the closed root's binder scope, then the
\ whole signature index, each continuing with the fuel the last one left.
: lf-minfer-scope ( root identity -- status )
  0 lf-minfer-fuel @ lf-constant-term-scope outcome-sane
  dup ok? if lf-cts-fuel lf-minfer-refuel then ;
: lf-minfer-index ( -- status )
  lf-minfer-token @ lf-minfer-fuel @ lf-mixed-signature-audit outcome-sane
  dup ok? if lf-msa-fuel lf-minfer-refuel then ;
: lf-minfer-preflight ( root identity -- status )
  lf-minfer-scope dup ok? if drop lf-minfer-index then ;

\ The job's scratch mark before allocation (core/scratch-marks.fs), and
\ the rollback to it after a failure: every term, level, reference and
\ local-context entry the job made goes; allocation serials never rewind.
\ LIFO: the job's mark is its oldest, taken when it starts and given back
\ only once its walk has returned, after every mark taken inside it. A
\ mark that could not be taken (a store's count not valid) is erased, so
\ the rollback refuses it and no node is a source (lf-minfer-source?):
\ the job fails at its first read. A refused rollback is invalid.
: lf-minfer-mark ( job -- ) lf-ijob-mark lf-scratch-mark drop ;
: lf-minfer-rollback ( outcome -- outcome )
  lf-minfer-job lf-ijob-mark lf-scratch-rollback lf-scratch-settled ;
: lf-minfer-idle ( job -- )
  dup lf-ijob-frames frame-reset 0 over lf-ijob-binders !
  -1 over lf-ijob-chain ! false over lf-ijob-inner ! 0 over lf-ijob-spine !
  false over lf-ijob-aside ! false swap lf-ijob-env ! ;

\ Start a job on lf-minfer-job: the index token and nonnegative fuel, no
\ frames or binders in use, rules on, not in environment mode, an empty
\ local context, and the scratch mark to roll back to. Neither preflight
\ allocates, so the stores stand the same before and after it; the
\ definition probe starts a job after its own preflight.
\ A new job empties the caches (kernel/caches.fs sets the hook), as its
\ local context starts empty, and the memo of closings (mixed-open.fs).
defer lf-minfer-fresh ( -- )
:noname ( -- ) ; is lf-minfer-fresh
: lf-minfer-start ( token fuel -- )
  lf-minfer-job tuck lf-ijob-fuel ! tuck lf-ijob-token !
  dup lf-minfer-idle lf-minfer-mark lf-lctx-reset lf-minfer-fresh lf-open-forget ;
\ Start a job in environment mode (check-declaration.fs), inside a check
\ of the checked environment: as lf-minfer-start, with no index token.
: lf-minfer-start-env ( fuel -- )
  0 swap lf-minfer-start true lf-minfer-job lf-ijob-env ! ;

\ A failure reports no type and leaves zero fuel.
: lf-minfer-failed ( status -- type identity status ) 0 lf-minfer-fuel ! -1 0 rot ;
: lf-minfer-result ( type -- type identity status )
  dup lf-term-identity if outcome-ok exit then
  drop outcome-invalid lf-minfer-rollback lf-minfer-failed ;
: lf-minfer-run ( root -- type identity status )
  lf-minfer-walk
  dup ok? if drop lf-minfer-result else nip lf-minfer-rollback lf-minfer-failed then ;

\ ( token root identity fuel -- type identity status ) Full source and global
\ index preflight precede allocation. All failures roll the stores back to
\ the job's scratch mark; serials never rewind. The input is the root's
\ graph, which preflight found closed. Every failure reports zero
\ remaining fuel conservatively.
: lf-minfer-negative ( token root identity fuel -- type identity status )
  0 lf-diag-bad-argument lf-minfer-note drop 2drop outcome-invalid lf-minfer-failed ;
: lf-mixed-infer ( token root identity fuel -- type identity status )
  dup 0< if lf-minfer-negative exit then
  >r rot r> lf-minfer-start over swap lf-minfer-preflight
  dup ok? if drop lf-minfer-run else nip lf-minfer-failed then ;

\ Lean's infer_type in infer-only mode (type_checker.cpp 360-362), the
\ typer of defeq.fs's steps 4, 11, 12 and 14 (lf-dq-typer, which
\ lf-minfer-convert lends a comparison): node, closed with the scope's
\ free variables, inferred aside on the frames' fuel, keeping what it
\ makes (the comparison's caller discards it).
: lf-minfer-typed ( node frames -- type outcome )
  >r r@ frame-fuel @ lf-minfer-fuel ! lf-minfer-aside @ >r true lf-minfer-aside !
  lf-minfer-close ok-then? if lf-minfer-walk else no-result then
  r> lf-minfer-aside ! lf-minfer-fuel @ r> frame-fuel ! ;
' lf-minfer-typed is lf-minfer-typer

\ Host stacks. Inference and conversion keep every level on their frames
\ (plan task 6.2.0), so their host-stack use does not grow with the
\ depth: a step holds a few cells while it runs, and the loops that nest
\ are few -- inference's; within its step, a comparison's (lf-minfer-agree,
\ defeq.fs); within a comparison step, the typer's inference aside, which
\ never compares (infer-only), or a whnf of its own; within the typer's
\ step, a whnf on the job's frames; and within any of them a substitution
\ pass, beta reductions that nest instantiate and shift
\ passes (lf-mbeta-*-cells), or a level comparison's normalize
\ (lf-lnorm-*-cells, level-normalize.fs), never both. lf-minfer-loop-cells
\ bounds a loop with its step's words, generously (the deepest painted
\ level of the recursive version held 9 return and 6 data cells).
128 constant lf-minfer-loop-cells
lf-mbeta-return-cells lf-lnorm-return-cells max constant lf-minfer-rs-nested
lf-mbeta-data-cells lf-lnorm-data-cells max constant lf-minfer-ds-nested
4 lf-minfer-loop-cells * lf-minfer-rs-nested + constant lf-minfer-return-cells
4 lf-minfer-loop-cells * lf-minfer-ds-nested + constant lf-minfer-data-cells
lf-minfer-data-cells lf-minfer-return-cells lf-mbeta-host?
0= [if] .( mixed-infer.fs: host stacks too small) cr abort [then]
lf-minfer-data-cells lf-minfer-return-cells context-need
