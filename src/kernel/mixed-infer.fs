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
\ An application's argument is closed before it is put into the Pi body,
\ by Lean's instantiate without the audit that lf-mixed-instantiate ran
\ before free variables: the body is a type inference made or the audited
\ input holds, the argument an audited source node closed by mixed-open
\ (which checks each leaf's shape, liveness and child order), and every
\ comparison that can lead to acceptance audits both of its graphs
\ (lf-minfer-compare, through lf-mixed-convert-keeping).
\ The rejection analysis below keeps its own binders as bound variables
\ too (see lf-minfer-close), and scratch a step no longer needs is
\ discarded (lf-minfer-discard). As Lean, the innermost body's type of a
\ chain of lambdas goes through cheap_beta_reduce (instantiate.cpp
\ 211-230, type_checker.cpp 140; whnf.fs), since plan task 4.2.2c.
\ Rejection ([kernel] code, not yet through the review gate): a type
\ whose whnf is no Sort or Pi is Lean's typeExpected or funExpected,
\ rejected with the codes of ADR 0011's rules S1, S2, S4 and F1, which
\ Lean's ensure_sort_core and ensure_pi_core replace since plan task
\ 4.2.2c. Where a comparison is undecided, rules D1-D5 (ADR 0011, ADR
\ 0008 step 3: an argument's type and the function's domain are apart)
\ may show that Lean's kernel certainly fails the same step, and the
\ outcome is then rejected, recorded with the rule; otherwise it stays
\ unknown, or exhausted or full when the analysis ran out of fuel or room
\ (ADR 0008; since plan task 4.2.2c). Like every result here, a
\ rejection holds only if the candidate signatures are the constants'
\ true types: they are unchecked assumptions at this interface. The
\ analysis only ever turns an unknown into rejected, exhausted or full,
\ and is retired by plan task 4.2.2d. The proof test P2
\ runs inference "aside": with no rule, on any live node (whnf results and
\ inferred types, which the checker's own passes made from the audited
\ input), discarding what it allocates.
\ Environment mode (plan task 2.2.3; [kernel] code, not yet through the
\ review gate): a job started with lf-minfer-start-env, by
\ check-declaration.fs, takes a constant's type from the checked
\ environment within the check's snapshot instead of the signature index,
\ and checks a Sort's level against the declaration's universe parameters
\ when it visits the Sort: rules N1, K5, L1 and L2 at the place and in the
\ order Lean's kernel checks them (env-signature.fs). A job started with
\ lf-minfer-start, as by lf-mixed-infer and the probes, never uses it.
\ State: one inference record, lf-minfer-job (fields lf-ijob-*): fuel, frame
\ depth, index token, the arena counts before the call, the scope (the
\ opened binders' free variables and a Pi telescope's levels), whether
\ inference runs aside, whether it runs in environment mode, a copy of a
\ reference's levels, and the first shortage of fuel or room the
\ rejection analysis met; a member of the checker context
\ (lib/context.fs). Lean's whnf (whnf.fs) runs on the job's frames.
\ The local context is local-context.fs's: emptied when a job starts;
\ discarding scratch (a binder domain's or an argument's inference, a
\ Pi's, test P2, a level of the rejection analysis, a failure) drops the
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
require ../core/levels.fs
require ../core/local-context.fs
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
require ./whnf.fs

begin-structure /lf-ijob
  /frames +field lf-ijob-frames  \ fuel, visits in progress, the explicit stack
  field: lf-ijob-token     \ signature index token
  field: lf-ijob-terms     \ term count before the call
  field: lf-ijob-levels    \ level count before the call
  field: lf-ijob-crefs     \ reference count before the call
  field: lf-ijob-binders   \ free variables on the scope
  field: lf-ijob-aside     \ true while inference runs aside, for test P2
  field: lf-ijob-env       \ true in environment mode (lf-minfer-start-env)
  field: lf-ijob-argument  \ the argument an application's type is instantiated with
  field: lf-ijob-chain     \ for a lambda's lambda body, where the chain began, else -1
  field: lf-ijob-short     \ the first exhausted or full the rejection analysis met, or 0
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
\ The first time the rejection analysis runs out of fuel or room, which
\ lf-minfer-agree reports (ADR 0008): the outcome, or 0.
: lf-minfer-short ( -- addr ) lf-minfer-job lf-ijob-short ;
: lf-minfer-shortage ( status -- )
  dup outcome-exhausted = over outcome-full = or lf-minfer-short @ 0= and
  if lf-minfer-short ! else drop then ;
\ Mode flags are registers of the checker context, never shared between
\ contexts: the aside flag here, set around one nested inference and
\ restored (lf-minfer-proof-free?); the environment flag, set for a whole
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
\ inference made beyond its Sort level or its verdict -- is discarded by
\ setting the term count back to the mark taken before it. A measure for
\ small term stores (the default holds 64 terms), so that free variables
\ (plan task 4.2.2a) fit where the binder context did; it changes no
\ result, as nothing made after the mark is used again. It must go when
\ the caches of ADR 0014 Q10 come, which keep scratch until the check
\ ends. After a failure the job's own rollback discards everything.
: lf-minfer-discard ( outcome mark -- outcome )
  over ok? if dup lf-term-count ! lf-lctx-drop else drop then ;
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
: lf-minfer-scan-binary ( first second walk tag -- outcome )
  over walk-context @ swap lf-tag-app <> - swap walk-children-at ;
: lf-minfer-scan-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if lf-minfer-scan-binary exit then
  lf-tag-bvar = if lf-minfer-scan-bvar else drop 2drop outcome-ok then ;
: lf-minfer-scan-visit ( walk -- outcome ) lf-terms ['] lf-minfer-scan-dispatch walk-visit ;
\ The scan keeps the largest k - d (-1 for none), so that no index
\ overflows; m is one more, at most n.
: lf-minfer-loose ( node n -- m )
  >r -1 lf-minfer-scan walk-arg ! lf-minfer-fuel @ lf-minfer-scan walk-budget 0=
  if drop r> exit then
  0 ['] lf-minfer-scan-visit lf-minfer-scan walk-run-pair ok?
  if lf-minfer-scan walk-arg @ r@ 1- min 1+ r> drop else r> then ;
\ Of n free variables, the innermost that node needs, at least one: the
\ pass then visits and pays for node as with all n, and gives the same
\ term, while checking and copying only those (plan task 6.2.0: a
\ binder's domain is closed in time independent of the scope's depth).
: lf-minfer-needed ( node fvars n -- node fvars' n' )
  dup 2 < if exit then
  2 pick over lf-minfer-loose 1 max tuck - cells rot + swap ;

\ Opening on the job's fuel (mixed-open.fs), which continues with what it
\ leaves: node with the free variables opened since base put for its
\ loose bound variables (instantiate_rev); ok, invalid, exhausted or full.
: lf-minfer-lend ( -- ) lf-minfer-fuel @ lf-open-fuel ! ;
: lf-minfer-repay ( -- ) lf-open-fuel @ lf-minfer-fuel ! ;
: lf-minfer-open ( node base -- node' status )
  lf-minfer-lend lf-minfer-opened lf-minfer-needed lf-instantiate-rev lf-minfer-repay
  outcome-sane ;
\ A term read under the scope, closed with every free variable of the
\ scope (its loose bound variables are the scope's binders).
: lf-minfer-close ( node -- node' status ) 0 lf-minfer-open ;

\ Live nodes as handles; the right one is checked first.
: lf-minfer-handle ( node -- node identity true | false )
  dup lf-term-identity dup 0= if nip then ;
: lf-minfer-handles ( left right -- left lid right rid true | false )
  lf-minfer-handle 0= if drop false exit then 2>r
  lf-minfer-handle if 2r> true else 2r> 2drop false then ;

\ Compare two types by conservative beta conversion, which validates both
\ graphs with the shared fuel. An undecided comparison keeps the fuel it
\ left, for the rejection analysis (a failed inference leaves no fuel in
\ the end anyway).
: lf-minfer-convert ( left lid right rid -- status )
  lf-minfer-fuel @ lf-mixed-convert-keeping lf-mconvert-fuel lf-minfer-refuel
  outcome-sane dup lf-minfer-shortage ;
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
: lf-minfer-put-closed ( body argument -- type status )
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

\ Inference and the rejection analysis run on the job's frames, an
\ explicit stack that grows with the depth (lib/frame.fs; plan task
\ 6.2.0): a node's visit is a chain of steps ( ... frames -- ... frames
\ next ) that keep on the stack what they need across a child's visit.
\ lf-minfer-walk ( node -- type status ) and lf-minfer-apart ( left right
\ -- mask flag ) run one visit to its end, as a loop of its own from what
\ the stack then holds, so that the analysis, test P2 and the callers
\ outside can use them from inside a step.
defer lf-minfer-walk ( node -- type status )

\ After a step that succeeded, keep x and the step's result; otherwise drop
\ x and pass the failed ( result status ) on.
: lf-minfer-step? ( x result status -- x result true | result status false )
  dup ok? if drop true else rot drop false then ;

\ Definite rejection (ADR 0011). A rule runs only once the step it decides
\ is undecided and has recorded why (not a Pi, not a Sort, terms differ):
\ a rejection replaces that record with the rule's (lf-minfer-reject); an
\ analysis that cannot decide leaves it, as the record keeps the first
\ failure. The helpers report ok or a failure, and a failure leaves no
\ fuel, so an analysis that goes on after one does nothing more.
: lf-minfer-reject ( n1 site code -- outcome ) 0 -rot lf-diag! outcome-rejected ;
\ The rejection of a comparison: (mask rejected) is recorded at site
\ with code and the mask of rules; any other outcome passes.
: lf-minfer-verdict ( mask status site code -- status )
  2swap dup outcome-rejected = if drop -rot lf-minfer-reject else nip nip nip then ;
: lf-minfer-take ( status addr -- status )
  over ok? if lf-minfer-refuel else drop dup lf-minfer-shortage 0 lf-minfer-fuel ! then ;
\ whnfB (ADR 0003 step 1) of a live node, with the job's fuel.
: lf-minfer-reduce ( node identity -- node' status )
  lf-minfer-fuel @ lf-mixed-beta nip outcome-sane lf-mbeta-fuel lf-minfer-take ;
: lf-minfer-whnf ( node -- node' status )
  dup lf-term-identity if lf-minfer-reduce else drop -1 outcome-invalid then ;
\ Lean's normalizes_to_zero on a level, with the job's fuel (S3, P2).
: lf-minfer-zero? ( level -- flag status )
  lf-minfer-fuel @ lf-level-zero? lf-lvalue-fuel lf-minfer-take ;
\ Both fields of two nodes, left first. Unchecked: both are valid.
: lf-minfer-firsts ( left right -- l1 r1 ) lf-term-first@ swap lf-term-first@ swap ;
: lf-minfer-seconds ( left right -- l2 r2 ) lf-term-second@ swap lf-term-second@ swap ;

\ Lean's ensure_sort_core and ensure_pi_core (type_checker.cpp 62-83;
\ ADR 0014 Q1, plan task 4.2.2c), which replace ADR 0011's rules S1, S2,
\ S4 and F1: a type that is a Sort (a Pi) as it is; otherwise its whnf
\ (whnf.fs: beta, and delta in a check of the checked environment), on
\ the job's frames and fuel, must be one. A whnf that is neither is
\ Lean's typeExpected (funExpected): rejected at site with code and the
\ reduced type while deciding, as ADR 0011's rules recorded it; aside
\ (test P2), where a failure only means "not known", unknown, recorded as
\ not a Sort (not a Pi) with the type. A whnf that fails passes its
\ outcome on (unknown where Lean may reduce further than LeanForth yet,
\ whnf.fs; exhausted, full, invalid).
: lf-minfer-whnf-job ( node -- node' status ) lf-minfer-frames lf-whnf-on ;
: lf-minfer-not-sort ( type -- -1 status )
  0 lf-diag-not-sort lf-minfer-note -1 outcome-unknown ;
: lf-minfer-not-type ( reduced site code -- -1 status )
  lf-minfer-deciding? if lf-minfer-reject no-result else 2drop lf-minfer-not-sort then ;
: lf-minfer-sort-rule ( type site code -- level status )
  2>r dup lf-minfer-sort? if nip 2r> 2drop outcome-ok exit then
  lf-minfer-whnf-job ok-then? 0= if 2r> 2drop no-result exit then
  dup lf-minfer-sort? if nip 2r> 2drop outcome-ok else 2r> lf-minfer-not-type then ;
: lf-minfer-not-pi ( reduced -- outcome )
  lf-minfer-deciding? if lf-minfer-site lf-diag-function-expected lf-minfer-reject
  else 0 lf-diag-not-pi lf-minfer-note outcome-unknown then ;

\ The rejection analysis below compares terms under the binders it enters
\ itself (D4), as before plan task 4.2.2a: a binder it enters gets a free
\ variable on the scope, and the bodies keep their loose bound variables
\ for those binders, innermost the scope's top, as inference reads a term
\ under the scope. A term of the analysis is closed with the scope's free
\ variables (lf-minfer-close), as D4's domains need and P2 does; terms
\ read under binders that a caller opened itself (check-block.fs) close
\ the same way. Comparing and reducing such terms needs no closing.

\ P2, "known not to be a proof": node's type T and T's type infer, and the
\ latter's whnfB is Sort l with l not zero under every assignment, so
\ Lean's is_prop of T is false (fact 6). Inference runs aside on the
\ closed node, its free variables those of the local context; every
\ failure means "not known". The arena counts and the aside flag are
\ restored afterwards.
: lf-minfer-type2 ( node -- type status )
  lf-minfer-walk dup ok? if drop lf-minfer-walk then ;
: lf-minfer-nonzero? ( level -- flag ) lf-minfer-zero? ok? if 0= else drop false then ;
\ A failure means "not known"; one for want of fuel or room is kept for
\ lf-minfer-agree (lf-minfer-shortage).
: lf-minfer-unknown ( status -- false ) lf-minfer-shortage false ;
: lf-minfer-sorted-free? ( type -- flag )
  lf-minfer-whnf ok-then? 0= if lf-minfer-unknown exit then
  lf-minfer-sort? if lf-minfer-nonzero? else false then ;
: lf-minfer-free? ( node -- flag )
  lf-minfer-close ok-then? 0= if lf-minfer-unknown exit then
  lf-minfer-type2 ok-then? if lf-minfer-sorted-free? else lf-minfer-unknown then ;
\ The arena counts, kept on the data stack around work whose allocations
\ are discarded (the return stack has less room for recursion).
: lf-minfer-counts ( -- terms levels crefs )
  lf-term-count @ lf-level-count @ lf-cref-count @ ;
: lf-minfer-counts! ( terms levels crefs -- )
  lf-cref-count ! lf-level-count ! dup lf-term-count ! lf-lctx-drop ;
: lf-minfer-proof-free? ( node -- flag )
  >r lf-minfer-counts lf-minfer-aside @ r> true lf-minfer-aside !
  lf-minfer-free? swap lf-minfer-aside ! >r lf-minfer-counts! r> ;
: lf-minfer-free2? ( left right -- flag )
  swap lf-minfer-proof-free? if lf-minfer-proof-free? else drop false then ;

\ D1-D5: whether an inferred type (left) and an expected type (right),
\ both well typed in the local context, are apart, so that Lean's
\ is_def_eq is certainly false: (mask true), mask being the rules used
\ from the pair down to the pair that decided, or (0 false). The pair is
\ closed at the start; below a D4 level it is open for the analysis's own
\ binders (see lf-minfer-close). Each level reduces both sides; see
\ lf-minfer-apart-call for its cost.
1 constant lf-rule-d1
2 constant lf-rule-d2
4 constant lf-rule-d3
8 constant lf-rule-d4
16 constant lf-rule-d5
defer lf-minfer-apart ( left right -- mask flag )
: lf-minfer-holds ( flag bit -- mask flag ) over and swap ;
: lf-minfer-via ( mask flag bit -- mask' flag ) over if rot or swap else drop then ;
: lf-minfer-whnf2 ( left right -- left' right' true | false )
  swap lf-minfer-whnf ok-then? 0= if 2drop false exit then
  swap lf-minfer-whnf ok-then? if true else 2drop false then ;
: lf-minfer-kinds ( left right -- left right kl kr )
  2dup swap lf-mhead-kind swap lf-mhead-kind ;
\ D1: two Sorts whose levels Lean's is_equivalent calls different (fact 5,
\ ADR 0011 Amendment 1); no precondition, as quick_is_def_eq decides two
\ Sorts at once.
: lf-minfer-sorts-apart ( left right -- mask flag )
  lf-minfer-firsts lf-minfer-fuel @ lf-level-inequivalent? lf-lcmp-fuel lf-minfer-take
  ok? and lf-rule-d1 lf-minfer-holds ;
\ Each level of the analysis is a visit on the job's frames: a frame and
\ a unit of fuel, as an inference visit takes; with neither left (no fuel,
\ or a stack the heap cannot grow), the pair is not shown apart. A level's
\ steps ( ... frames -- ... frames next ) end with ( mask flag frames 0 );
\ lf-minfer-apart-call asks for a level's visit of a pair, continuing with
\ cont ( mask flag frames -- ... ). The diagnostics of the refusals are
\ inference's (lf-minfer-room).
: lf-minfer-frames-full ( -- ) lf-minfer-frames frame-room@ lf-diag-frame-limit lf-minfer-note ;
: lf-minfer-refused ( outcome -- outcome )
  dup outcome-full = if lf-minfer-frames-full exit then
  dup outcome-exhausted = if lf-minfer-fuel @ lf-minfer-site lf-diag-exhausted then ;
: lf-minfer-room ( frames -- outcome ) frame-admit dup ok? 0= if lf-minfer-refused then ;
defer lf-minfer-apart-step ( left right frames -- ... frames next )
: lf-minfer-apart-call ( left right frames cont -- ... frames next )
  over lf-minfer-room dup ok? 0= if lf-minfer-shortage 2>r 2drop 0 false 2r> exit then
  drop ['] lf-minfer-apart-step frame-open ;
\ D3 and D5, two variables with arguments (is_def_eq_app, 878-895, needs
\ the same head and number): a different number of arguments, or
\ different variables known not to be proofs, are apart (D3); the same
\ variable and number are apart when some argument pair is (D5), the
\ pairs compared last argument first, each a level of its own. A head is
\ a free variable (of inference's binders) or a bound one (of the
\ analysis's): the same variable when both tag and number are.
: lf-minfer-count ( node -- count ) lf-mhead-spine nip ;
: lf-minfer-head ( node -- head ) lf-mhead-spine drop ;
: lf-minfer-variable ( node -- index tag )
  lf-minfer-head dup lf-term-first@ swap lf-term-tag@ ;
: lf-minfer-same-head? ( left right -- flag )
  lf-minfer-variable rot lf-minfer-variable rot = >r = r> and ;
: lf-minfer-d5 ( left right mask -- mask' true ) nip nip lf-rule-d5 or true ;
\ count argument pairs left, from left right down their functions; left,
\ right and count wait on the stack while the last pair is compared.
defer lf-minfer-args-apart ( left right count frames -- ... frames next )
: lf-minfer-args-back ( mask flag frames -- ... frames next )
  >r r@ frame-restore r@ frame-restore r@ frame-restore   ( mask flag left right count )
  >r 2swap r> swap if drop lf-minfer-d5 r> 0 exit then
  nip >r lf-minfer-firsts r> 1- r> ['] lf-minfer-args-apart ;
: lf-minfer-args-step ( left right count frames -- ... frames next )
  over 0= if >r drop 2drop 0 false r> 0 exit then
  >r r@ frame-save 2dup r@ frame-save r@ frame-save
  lf-minfer-seconds r> ['] lf-minfer-args-back lf-minfer-apart-call ;
' lf-minfer-args-step is lf-minfer-args-apart
: lf-minfer-heads ( left right -- head head' ) lf-minfer-head swap lf-minfer-head swap ;
: lf-minfer-heads-apart ( left right -- mask flag )
  lf-minfer-heads lf-minfer-free2? lf-rule-d3 lf-minfer-holds ;
: lf-minfer-arity? ( left right -- left right count true | false )
  2dup lf-minfer-count swap lf-minfer-count over = if true else drop 2drop false then ;
\ P4 (plan task 5.2.1a): once inductive types can be in the environment,
\ Lean's last route, is_def_eq_unit_like (type_checker.cpp 1119-1130,
\ called at 1203), makes two terms equal when the left one's type, after
\ whnf, is a structure whose one constructor has no field (PUnit) and
\ their types are equal -- also after is_def_eq_app has failed. So two
\ variable-headed terms are shown apart (D3, D5) only when the left one's
\ type, inferred aside, has after whnfB a head that is no constant: Lean's
\ whnf leaves such a type as it is (ADR 0011 fact 3), so it is no
\ structure. A type headed by a constant, or one that cannot be inferred,
\ leaves the pair undecided.
: lf-minfer-type-kind ( node -- kind )
  lf-minfer-walk ok-then? 0= if lf-minfer-shortage lf-head-none exit then
  lf-minfer-whnf ok-then? if lf-mhead-kind else lf-minfer-shortage lf-head-none then ;
: lf-minfer-kind-aside ( node -- kind )
  >r lf-minfer-counts lf-minfer-aside @ r> true lf-minfer-aside !
  lf-minfer-type-kind swap lf-minfer-aside ! >r lf-minfer-counts! r> ;
: lf-minfer-unit-free? ( node -- flag )
  lf-minfer-kind-aside dup lf-head-constant <> swap lf-head-none <> and ;
: lf-minfer-vars-apart ( left right frames -- ... frames next )
  >r over lf-minfer-unit-free? 0= if 2drop 0 false r> 0 exit then
  lf-minfer-arity? 0= if lf-rule-d3 true r> 0 exit then
  >r 2dup lf-minfer-same-head?
  if r> r> lf-minfer-args-apart else r> drop lf-minfer-heads-apart r> 0 then ;
\ D4, two Pis or two lambdas (is_def_eq_binding, 752-779; ADR 0003
\ Amendment 1, owner answers G6 and G7): when the domains are equal by the
\ cautious comparison, the pair is apart when the bodies are, the variable
\ having the right (expected) side's domain (B2): a new free variable of
\ that domain, closed, on the scope (Lean's is_def_eq_binding, 766-772),
\ which the bodies' loose bound variable 0 now stands for; otherwise when
\ the domains are apart. A binder that cannot be entered (no room or fuel)
\ is not apart.
: lf-minfer-enter-binder ( domain -- status )
  lf-minfer-close ok-then? if 0 lf-minfer-bind then dup lf-minfer-shortage ;
\ The result of D4's comparison, of the bodies with the scope's depth
\ before their binder (base) waiting on the stack, or of the domains.
: lf-minfer-d4 ( mask flag frames -- mask' flag frames 0 ) >r lf-rule-d4 lf-minfer-via r> 0 ;
: lf-minfer-bodies-back ( mask flag frames -- mask' flag frames 0 )
  >r r@ frame-restore lf-minfer-unbind r> lf-minfer-d4 ;
: lf-minfer-bodies-apart ( left right frames -- ... frames next )
  >r lf-minfer-context-depth @ -rot dup lf-term-first@ lf-minfer-enter-binder ok?
  if rot r@ frame-save lf-minfer-seconds r> ['] lf-minfer-bodies-back lf-minfer-apart-call
  else 2drop lf-minfer-unbind 0 false r> lf-minfer-d4 then ;
: lf-minfer-binders-apart ( left right frames -- ... frames next )
  >r 2dup lf-minfer-firsts lf-minfer-compare
  dup ok? if drop r> lf-minfer-bodies-apart exit then
  outcome-unknown = if lf-minfer-firsts r> ['] lf-minfer-d4 lf-minfer-apart-call exit then
  2drop 0 false r> lf-minfer-d4 ;
\ One level: two Sorts by D1; otherwise P1 (both rigid) and P3 (not
\ exactly one a lambda) on the shapes, P2 on both sides (no proof
\ irrelevance), then D2 for different shapes among Sort, Pi and bound
\ variable, D3/D5 for two bound variables, D4 for two binders. Kinds
\ that are no shape (a constant: K1; lf-head-applied, lf-head-none) are
\ never apart.
: lf-minfer-one-lam? ( kl kr -- flag ) lf-head-lam = swap lf-head-lam = xor ;
: lf-minfer-shapes? ( kl kr -- flag )
  2dup lf-minfer-one-lam? 0= -rot lf-mhead-shape? swap lf-mhead-shape? and and ;
: lf-minfer-shapes-apart ( left right kl kr frames -- ... frames next )
  >r 2dup <> if 2drop 2drop lf-rule-d2 true r> 0 exit then
  drop lf-head-var = if r> lf-minfer-vars-apart else r> lf-minfer-binders-apart then ;
: lf-minfer-rigid-apart ( left right kl kr frames -- ... frames next )
  >r 2dup lf-minfer-shapes? 0= if 2drop 2drop 0 false r> 0 exit then
  2over lf-minfer-free2? if r> lf-minfer-shapes-apart else 2drop 2drop 0 false r> 0 then ;
: lf-minfer-sorts? ( kl kr -- flag ) lf-head-sort = swap lf-head-sort = and ;
: lf-minfer-apart-visit ( left right frames -- ... frames next )
  >r lf-minfer-whnf2 0= if 0 false r> 0 exit then lf-minfer-kinds
  2dup lf-minfer-sorts? if 2drop lf-minfer-sorts-apart r> 0 else r> lf-minfer-rigid-apart then ;
\ A level's first step: it keeps the arena counts (terms on top) and the
\ step that restores them when the level returns, discarding the nodes,
\ levels and references it made.
: lf-minfer-counts-save ( frames -- )
  >r lf-minfer-counts r@ frame-save r@ frame-save r> frame-save ;
: lf-minfer-restored ( mask flag frames -- mask flag frames 0 )
  >r r@ frame-restore r@ frame-restore r@ frame-restore lf-minfer-counts! r> 0 ;
: lf-minfer-apart-begin ( left right frames -- ... frames next )
  dup lf-minfer-counts-save ['] lf-minfer-restored over frame-save lf-minfer-apart-visit ;
' lf-minfer-apart-begin is lf-minfer-apart-step
: lf-minfer-apart-run ( left right -- mask flag )
  lf-minfer-frames ['] lf-minfer-apart-call frame-through drop ;
' lf-minfer-apart-run is lf-minfer-apart

\ Compare an inferred type (left) with an expected type (right), in
\ Lean's order: (0 ok) when equal; (mask rejected) when the comparison is
\ undecided and D1-D5 show the pair apart; else (0 outcome), the
\ comparison's own. The analysis begins at the scope's current depth.
: lf-minfer-mismatch ( left right -- mask flag )
  lf-minfer-deciding? 0= if 2drop 0 false exit then
  0 lf-minfer-short ! lf-minfer-apart ;
\ A pair the analysis did not show apart is unknown -- or exhausted (full)
\ when the analysis ran out of fuel (room) first, or had none to begin
\ with: with more it might have shown the pair apart, so by ADR 0008's
\ order the limit decides (an exhaustion recorded as such, replacing the
\ comparison's note). CLI2's finding of 2026-11-04: before, such a check
\ was unknown.
: lf-minfer-ran-out ( -- status )
  lf-minfer-fuel @ lf-minfer-site lf-diag-fuel 0 -rot lf-diag! outcome-exhausted ;
: lf-minfer-undecided ( -- status )
  lf-minfer-deciding? 0= if outcome-unknown exit then
  lf-minfer-short @ dup outcome-exhausted = if drop lf-minfer-ran-out exit then
  ?dup if exit then lf-minfer-fuel @ 0> if outcome-unknown else lf-minfer-ran-out then ;
: lf-minfer-agree ( left right -- mask status )
  2dup lf-minfer-compare dup outcome-unknown <> if nip nip 0 swap exit then
  drop lf-minfer-mismatch if outcome-rejected else lf-minfer-undecided then ;

\ Inference's visits. lf-minfer-call asks for the visit of node,
\ continuing with cont ( type status frames -- ... ); the visit's first
\ step is the frames' visitor, lf-minfer-visit-step below.
: lf-minfer-call ( node frames cont -- ... frames next )
  over lf-minfer-room dup ok? if drop frame-opened else frame-refuse then ;

\ Application, in three steps (infer_app, type_checker.cpp 173-187): the
\ function's type must be a Pi, after whnf when it is no visible one
\ (ensure_pi_core: otherwise rejected, funExpected, or the whnf's
\ failure), the argument's type must convert to its domain (otherwise
\ unknown, or rejected by D1-D5: appTypeMismatch), and the type is the Pi
\ body instantiated with the argument. The argument waits on the stack
\ while the function's type is inferred; the body, the argument, the
\ domain and the term count before the argument's inference (its scratch
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
: lf-minfer-app-arg ( A status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore 2swap lf-minfer-argued
  r@ frame-restore r@ frame-restore swap rot lf-minfer-applied r> 0 ;
: lf-minfer-app-fn ( T status frames -- ... frames next )
  >r r@ frame-restore -rot lf-minfer-step? 0= if r> 0 exit then
  lf-minfer-pi-parts 0= if nip lf-minfer-none r> 0 exit then
  r@ frame-save swap dup r@ frame-save swap r@ frame-save lf-term-count @ r@ frame-save
  r> ['] lf-minfer-app-arg lf-minfer-call ;
: lf-minfer-app ( function argument frames -- ... frames next )
  tuck frame-save ['] lf-minfer-app-fn lf-minfer-call ;

\ Source nodes lie below the term count at the start; inference that runs
\ aside (test P2) reads every live node, among them the closed copies P2
\ infers, whose free variables are read through their entries.
: lf-minfer-source? ( node -- flag )
  dup 0< 0= swap lf-minfer-job lf-ijob-terms @ < and lf-minfer-aside @ or ;
: lf-minfer-read ( node -- first second tag true | false )
  dup lf-minfer-source? 0= if drop false exit then lf-term-read dup if >r rot r> then ;

\ Binders, one at a time, as infer_lambda and infer_pi treat each binder
\ of a telescope (type_checker.cpp 125-166). The domain, read under the
\ scope, must be a type, its type a Sort (otherwise unknown, or rejected
\ by S2); its inference's scratch is then discarded, and the binder gets
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
\ and the analysis closes what it infers with the whole scope.
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
\ Steps: the domain's inference, with the scope's depth before the
\ binder (base), the chain's top, the domain, the body and the term
\ count waiting on the stack; then the body's, with base, top and the
\ domain.
: lf-minfer-chain ( -- addr ) lf-minfer-job lf-ijob-chain ;
: lf-minfer-top ( base -- top )
  lf-minfer-chain dup @ -1 rot ! dup 0< if drop else nip then ;
: lf-minfer-lam? ( node -- flag ) lf-minfer-read if nip nip lf-tag-lam = else false then ;
: lf-minfer-abstract ( type top -- type' status )
  lf-minfer-lend lf-minfer-opened lf-abstract lf-minfer-repay outcome-sane ;
: lf-minfer-lam-type ( domain type status -- type status )
  lf-minfer-good? if lf-term-pi if outcome-ok else -1 outcome-full then
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
: lf-minfer-lam-domain ( D status frames -- ... frames next )
  >r 2 r@ frame-pick 0 r@ frame-pick 2swap lf-minfer-bound
  dup ok? 0= if no-result 5 r@ frame-drop r> 0 exit then
  drop 1 r@ frame-pick 2 r@ frame-drop
  dup lf-minfer-lam? if 1 r@ frame-pick lf-minfer-chain ! r> ['] lf-minfer-lam-chained
  else r> ['] lf-minfer-lam-plain then lf-minfer-call ;
: lf-minfer-lam ( domain body frames -- ... frames next )
  >r lf-minfer-context-depth @ dup r@ frame-save lf-minfer-top r@ frame-save
  over r@ frame-save r@ frame-save lf-term-count @ r@ frame-save
  r> ['] lf-minfer-lam-domain lf-minfer-call ;
\ A Pi's type is Sort (mk_imax u v) for a domain in Sort u and a body in
\ Sort v: Lean's infer_pi builds the level innermost first
\ (type_checker.cpp 158-165), as these steps do (ADR 0011, Amendment
\ 1; level-make.fs). S4 (ADR 0011, Amendment 2): the body's type must be a
\ Sort too (infer_pi's ensure_sort_core on the body, 158); when it is no
\ visible Sort and its whnfB is rigid and not a Sort, Lean's kernel fails
\ with typeExpected. A full level store is full. Only the level is
\ needed, so the Pi's scratch is discarded before its Sort is made.
\ Steps: the domain's inference, with the scope's depth before the binder
\ (base), the term count, the body and the domain waiting on the stack;
\ then the body's, with base and the count.
: lf-minfer-body-sort ( type -- level status )
  lf-minfer-site lf-diag-body-type lf-minfer-sort-rule ;
: lf-minfer-imax ( v base -- level status )
  lf-minfer-sort-cell @ swap lf-level-mk-imax if outcome-ok else -1 outcome-full then ;
: lf-minfer-pi-level ( base type -- base level status )
  lf-minfer-body-sort lf-minfer-good? if over lf-minfer-imax then ;
: lf-minfer-pi-end ( mark base level status -- type status )
  rot lf-minfer-unbind rot lf-minfer-discard lf-minfer-good? if lf-minfer-sort then ;
: lf-minfer-pi-body ( T status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore 2swap
  lf-minfer-good? if lf-minfer-pi-level then lf-minfer-pi-end r> 0 ;
: lf-minfer-pi-domain ( D status frames -- ... frames next )
  >r r@ frame-restore 1 r@ frame-pick 2swap lf-minfer-bound
  dup ok? 0= if no-result 3 r@ frame-drop r> 0 exit then
  drop r@ frame-restore r> ['] lf-minfer-pi-body lf-minfer-call ;
: lf-minfer-pi ( domain body frames -- ... frames next )
  >r lf-minfer-context-depth @ r@ frame-save lf-term-count @ r@ frame-save
  r@ frame-save dup r@ frame-save r> ['] lf-minfer-pi-domain lf-minfer-call ;

\ Infer an original source node; nodes made by this inference are output
\ data, never input. Constructors outside this subset are unknown, and
\ recorded as unsupported with their tag.
: lf-minfer-unsupported ( tag -- tag -1 status )
  dup 0 lf-diag-unsupported lf-minfer-note -1 outcome-unknown ;
: lf-minfer-leaf ( first tag -- type status )
  case lf-tag-symbolic-sort of lf-minfer-sort-type endof
    lf-tag-constant of lf-minfer-constant endof
    lf-tag-bvar of lf-minfer-bvar endof
    nip lf-minfer-unsupported rot endcase ;
: lf-minfer-other ( first second frames tag -- -1 status frames 0 tag )
  >r >r 2drop r> r> lf-minfer-unsupported 2swap 0 swap ;
: lf-minfer-binary ( first second tag frames -- ... frames next )
  swap case lf-tag-app of lf-minfer-app endof
    lf-tag-lam of lf-minfer-lam endof
    lf-tag-pi of lf-minfer-pi endof
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
\ same visit.
: lf-minfer-logged ( node -- node ) lf-minfer-context-depth @ lf-log-infer ;
: lf-minfer-closing ( type status frames -- type status frames 0 ) >r lf-log-close r> 0 ;
: lf-minfer-visit-step ( node frames -- ... frames next )
  lf-log? if ['] lf-minfer-closing over frame-save swap lf-minfer-logged swap then
  lf-minfer-visit ;
: lf-minfer-walk-run ( node -- type status )
  lf-minfer-frames ['] lf-minfer-call frame-through drop ;
' lf-minfer-walk-run is lf-minfer-walk
\ The frames and their visitor, set up once in every context; their stack
\ is freed with the context.
: lf-minfer-setup ( -- ) ['] lf-minfer-visit-step lf-minfer-frames frame-init ;
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

\ The three arena counts before allocation, and their rollback; allocation
\ serials never rewind.
: lf-minfer-mark ( job -- )
  lf-term-count @ over lf-ijob-terms ! lf-level-count @ over lf-ijob-levels !
  lf-cref-count @ swap lf-ijob-crefs ! ;
: lf-minfer-rollback ( -- )
  lf-minfer-job dup lf-ijob-terms @ lf-term-count ! dup lf-ijob-levels @ lf-level-count !
  dup lf-ijob-crefs @ lf-cref-count ! lf-ijob-terms @ lf-lctx-drop ;
: lf-minfer-idle ( job -- )
  dup lf-ijob-frames frame-reset 0 over lf-ijob-binders !
  -1 over lf-ijob-chain !
  false over lf-ijob-aside ! false swap lf-ijob-env ! ;

\ Start a job on lf-minfer-job: the index token and nonnegative fuel, no
\ frames or binders in use, rules on, not in environment mode, an empty
\ local context, and the arena counts to roll back to. Neither preflight
\ allocates, so the counts are the same before and after it; the
\ definition probe starts a job after its own preflight.
: lf-minfer-start ( token fuel -- )
  lf-minfer-job tuck lf-ijob-fuel ! tuck lf-ijob-token !
  dup lf-minfer-idle lf-minfer-mark lf-lctx-reset ;
\ Start a job in environment mode (check-declaration.fs), inside a check
\ of the checked environment: as lf-minfer-start, with no index token.
: lf-minfer-start-env ( fuel -- )
  0 swap lf-minfer-start true lf-minfer-job lf-ijob-env ! ;

\ A failure reports no type and leaves zero fuel.
: lf-minfer-failed ( status -- type identity status ) 0 lf-minfer-fuel ! -1 0 rot ;
: lf-minfer-result ( type -- type identity status )
  dup lf-term-identity if outcome-ok exit then
  drop lf-minfer-rollback outcome-invalid lf-minfer-failed ;
: lf-minfer-run ( root -- type identity status )
  lf-minfer-walk
  dup ok? if drop lf-minfer-result else nip lf-minfer-rollback lf-minfer-failed then ;

\ ( token root identity fuel -- type identity status ) Full source and global
\ index preflight precede allocation. All failures restore three arena counts;
\ serials never rewind. The input is the root's graph, which preflight
\ found closed. Every failure reports zero remaining fuel conservatively.
: lf-minfer-negative ( token root identity fuel -- type identity status )
  0 lf-diag-bad-argument lf-minfer-note drop 2drop outcome-invalid lf-minfer-failed ;
: lf-mixed-infer ( token root identity fuel -- type identity status )
  dup 0< if lf-minfer-negative exit then
  >r rot r> lf-minfer-start over swap lf-minfer-preflight
  dup ok? if drop lf-minfer-run else nip lf-minfer-failed then ;

\ Host stacks. Inference and the analysis keep every level on the job's
\ frames (plan task 6.2.0), so their host-stack use does not grow with the
\ depth: a step holds a few cells while it runs, and the loops that nest
\ are few -- inference's; within its step, the analysis's (lf-minfer-agree);
\ within an analysis step, an inference aside (test P2, the unit check),
\ which never runs the analysis again (it has no rule); and within any of
\ them conversion, whose beta reductions nest instantiate and shift
\ passes (lf-mbeta-*-cells), or a level comparison's normalize
\ (lf-lnorm-*-cells, level-normalize.fs), never both. lf-minfer-loop-cells
\ bounds a loop with its step's words, generously (the deepest painted
\ level of the recursive version held 9 return and 6 data cells).
128 constant lf-minfer-loop-cells
lf-mbeta-return-cells lf-lnorm-return-cells max constant lf-minfer-rs-nested
lf-mbeta-data-cells lf-lnorm-data-cells max constant lf-minfer-ds-nested
3 lf-minfer-loop-cells * lf-minfer-rs-nested + constant lf-minfer-return-cells
3 lf-minfer-loop-cells * lf-minfer-ds-nested + constant lf-minfer-data-cells
lf-minfer-data-cells lf-minfer-return-cells lf-mbeta-host?
0= [if] .( mixed-infer.fs: host stacks too small) cr abort [then]
lf-minfer-data-cells lf-minfer-return-cells context-need
