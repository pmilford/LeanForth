\ Experimental, untrusted mixed-term inference. Closed source roots only.
\ Signatures and nested dependencies are unchecked assumptions; no theorem
\ authority. One stable index/session, no raw writes, resets or concurrent
\ calls. Handles are local diagnostics. Fuel is shared by preflight,
\ traversal, specialization and transformations; bounded metadata, identity
\ scans and topological staging are additional work. Only a directly visible
\ Pi is applied; uncertain conversion is unknown.
\ Free variables (ADR 0014 Q2, plan task 4.2.2a; [kernel] code, not yet
\ through the review gate): inference only ever infers closed terms, as
\ Lean's kernel does. A telescope of lambdas or Pis is opened as Lean's
\ infer_lambda and infer_pi open it (type_checker.cpp 125-166): each
\ domain, opened with the free variables of the binders before it
\ (instantiate_rev, mixed-open.fs), must be a type (S2) and then gets a
\ new free variable of the local context (core/local-context.fs); the
\ body, opened with all of them, is inferred; a lambda's type is then
\ mk_pi of them over the body's type, a Pi's the Sort of the levels'
\ imax. A free variable's type is its entry's (infer_fvar, 93-99); a loose
\ bound variable is malformed. The opened binders' free variables wait on
\ the job's scope, at most lf-depth-limit (more is full, as the binder
\ context was). The rejection analysis below keeps its own binders as
\ bound variables (see lf-minfer-closed), and scratch a step no longer
\ needs is discarded (lf-minfer-discard). Lean then also applies
\ cheap_beta_reduce to a lambda body's type (instantiate.cpp 211-230,
\ type_checker.cpp 140); that would change inferred
\ types, so it comes with the ports that need it (plan task 4.2.2c), not
\ with this change of representation, which changes no outcome.
\ Definite rejection (ADR 0011, ADR 0008 step 3; [kernel] code, not yet
\ through the review gate): where a step is undecided, rules F1 (a
\ function's type is no Pi), S2 (a binder domain is no type), S4 (a Pi's
\ body is no type) and D1-D5 (an argument's type and the function's domain
\ are apart) may show that
\ Lean's kernel certainly fails the same step, and the outcome is then
\ rejected, recorded with the rule; otherwise it stays unknown. Like every
\ result here, a rejection holds only if the candidate signatures are the
\ constants' true types: they are unchecked assumptions at this interface.
\ The analysis only ever turns an unknown into rejected: when it cannot decide,
\ or runs out of fuel or room, the step stays unknown. The proof test P2
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
\ inference runs aside, whether it runs in environment mode, and a copy of
\ a reference's levels; a member of the checker context (lib/context.fs).
\ The local context is local-context.fs's: emptied when a job starts and
\ only appended to during it, so a free variable's number is unique within
\ the job; discarding scratch (a failure, test P2, the rejection analysis)
\ leaves the entries of discarded free variables dead, never reused. A
\ node's intermediate results stay on the data stack. Single-threaded
\ within one context.
\ lf-minfer-walk and lf-minfer-apart are deferred only for the mutual
\ recursion and set once, at load time, and shared.
\ Stack use: the recursion runs on the host stacks, a bounded number of
\ cells per level of inference or of the rejection analysis (the two share
\ the frame limit), at most lf-depth-limit levels, and a conversion,
\ reduction or level evaluation at the deepest level nests beta's passes,
\ a level comparison Lean's normalize (see the need stated at the end);
\ a host stack overflow throws and never yields a result.
\ mixed-definition-probe.fs starts a job with
\ lf-minfer-start, calls lf-minfer-walk, lf-minfer-sort-rule,
\ lf-minfer-zero?, lf-minfer-agree, lf-minfer-verdict and lf-minfer-reject
\ directly, and reads lf-minfer-fuel afterwards; check-declaration.fs does
\ the same with lf-minfer-start-env.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/constant-term-scope.fs
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

begin-structure /lf-ijob
  field: lf-ijob-fuel      \ visits left
  field: lf-ijob-depth     \ active frames, at most lf-depth-limit
  field: lf-ijob-token     \ signature index token
  field: lf-ijob-terms     \ term count before the call
  field: lf-ijob-levels    \ level count before the call
  field: lf-ijob-crefs     \ reference count before the call
  field: lf-ijob-binders   \ free variables on the scope
  field: lf-ijob-aside     \ true while inference runs aside, for test P2
  field: lf-ijob-env       \ true in environment mode (lf-minfer-start-env)
  field: lf-ijob-argument  \ the argument an application's type is instantiated with
  field: lf-ijob-apart     \ the scope's depth where the rejection analysis began
  lf-depth-limit cells +field lf-ijob-fvars   \ the scope's free variables, outermost
                                               \ first
  lf-depth-limit cells +field lf-ijob-sorts   \ beside each, its domain's Sort level (Pis)
  lf-cref-argument-capacity 2* cells +field lf-ijob-actuals
end-structure
/lf-ijob context-record: lf-minfer-job

\ Fields of the record. Tests read the fuel left and the scope's depth
\ (the binders opened), and mixed-definition-probe reads the fuel left.
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
  over ok? if lf-term-count ! else drop then ;
: lf-minfer-note ( n1 n2 code -- ) lf-minfer-site swap lf-diag-note ;

\ The scope: the free variables of the binders opened around the node
\ being inferred, outermost first, each with a level beside it (a Pi
\ domain's Sort level, else 0). A binder is opened once its domain is
\ checked, where Lean extends its local context (type_checker.cpp 131-136,
\ 151-155): a new entry of the local context, of the domain as its type.
\ More than lf-depth-limit open binders is full, recorded as a full binder
\ context, whatever fuel is left (ADR 0008); so is a full local context or
\ term store. Every telescope gives its binders back when it ends
\ (lf-minfer-unbind), whatever the outcome; their entries stay until the
\ next job starts, so that a number is never reused within a job.
: lf-minfer-fvar-cell ( i -- addr ) cells lf-minfer-job lf-ijob-fvars + ;
: lf-minfer-sort-cell ( i -- addr ) cells lf-minfer-job lf-ijob-sorts + ;
: lf-minfer-crowded ( -- outcome )
  lf-minfer-context-depth @ lf-depth-limit lf-diag-binders-full lf-minfer-note
  outcome-full ;
: lf-minfer-scope-push ( fvar level -- )
  lf-minfer-context-depth @ tuck lf-minfer-sort-cell ! lf-minfer-fvar-cell !
  1 lf-minfer-context-depth +! ;
: lf-minfer-bind ( type level -- outcome )
  lf-minfer-context-depth @ lf-depth-limit < 0= if 2drop lf-minfer-crowded exit then
  swap lf-lctx-local ok-then? if swap lf-minfer-scope-push outcome-ok else nip then ;
: lf-minfer-unbind ( base -- ) lf-minfer-context-depth ! ;
\ The free variables opened since base: their cells and their number.
: lf-minfer-opened ( base -- fvars n )
  dup lf-minfer-fvar-cell swap lf-minfer-context-depth @ swap - ;

\ Opening and closing on the job's fuel (mixed-open.fs), which continues
\ with what they leave: node with the free variables opened since base
\ put for its loose bound variables (instantiate_rev), and the Pi over
\ them of a type (mk_pi). Both report ok, invalid, exhausted or full.
: lf-minfer-lend ( -- ) lf-minfer-fuel @ lf-open-fuel ! ;
: lf-minfer-repay ( -- ) lf-open-fuel @ lf-minfer-fuel ! ;
: lf-minfer-open ( node base -- node' status )
  lf-minfer-lend lf-minfer-opened lf-instantiate-rev lf-minfer-repay outcome-sane ;
: lf-minfer-close ( type base -- pi status )
  lf-minfer-lend lf-minfer-opened lf-mk-pi lf-minfer-repay outcome-sane ;

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
  outcome-sane ;
: lf-minfer-compare ( left right -- status )
  lf-minfer-handles if lf-minfer-convert else outcome-invalid then ;
\ A Pi body with an argument put for its bound variable, as infer_app
\ does (type_checker.cpp 187: Lean's instantiate, mixed-open.fs), on the
\ job's fuel. The argument is closed, as every term inference meets is.
: lf-minfer-put ( -- addr ) lf-minfer-job lf-ijob-argument ;
: lf-minfer-instantiate ( body argument -- type status )
  lf-minfer-put ! lf-minfer-lend lf-minfer-put 1 lf-instantiate lf-minfer-repay
  outcome-sane ;

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

\ The level of an inferred Sort. Any other type is unknown, not a judgment,
\ and recorded as not a Sort.
: lf-minfer-not-sort ( node -- -1 status )
  0 lf-diag-not-sort lf-minfer-note -1 outcome-unknown ;
: lf-minfer-sort-level ( node -- level status )
  dup lf-term-read 0= if drop -1 outcome-invalid exit then
  drop swap lf-tag-symbolic-sort = if nip outcome-ok else drop lf-minfer-not-sort then ;

\ A constant: specialize its candidate signature to the reference's levels,
\ first copied into this record (specialization needs its input disjoint
\ from every arena and scratch area). In environment mode the signature is
\ the accepted declaration's stored type, found in the checked environment
\ (env-signature.fs: N1, K5, L1, then L2 while deciding), else the
\ candidate in the index. Success continues with the fuel the
\ specialization left; a failure leaves no fuel.
: lf-minfer-actuals ( -- addr ) lf-minfer-job lf-ijob-actuals ;
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
: lf-minfer-constant ( reference -- type status )
  lf-cref-slot dup lf-crec-name @ swap lf-minfer-copy lf-minfer-signature
  lf-minfer-specialized ;

\ A free variable has its entry's type (infer_fvar, type_checker.cpp
\ 93-99); one that the local context does not name is malformed. A bound
\ variable never reaches inference, which only meets closed terms (Lean
\ refuses any other, 326-327): it is malformed too, recorded with its
\ index and the binders open.
: lf-minfer-fvar? ( node -- flag )
  dup lf-term-valid? if lf-term-tag@ lf-tag-fvar = else drop false then ;
: lf-minfer-fvar ( node -- type status )
  dup lf-fvar-live? if lf-fvar-type outcome-ok exit then
  0 lf-diag-malformed lf-minfer-note -1 outcome-invalid ;
: lf-minfer-bvar ( index -- type status )
  lf-minfer-context-depth @ lf-diag-out-of-scope lf-minfer-note -1 outcome-invalid ;

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
  over ok? if lf-minfer-refuel else drop 0 lf-minfer-fuel ! then ;
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

\ Rules S1, S2 and F1 on a type that is no visible Sort or Pi: when rules
\ run, the type's whnfB whose head kind passes test ( kind -- flag ).
: lf-minfer-reduced ( type -- node true | false )
  lf-minfer-deciding? if lf-minfer-whnf ok-then? if true exit then then drop false ;
: lf-minfer-head-rule ( type test -- node true | false )
  swap lf-minfer-reduced if tuck lf-mhead-kind swap execute dup 0= if nip then
  else drop false then ;
\ S1, S2: the level of a type's Sort (lf-minfer-sort-level); when that is
\ undecided and the whnfB is rigid and not a Sort (Lean's ensure_sort_core
\ fails: typeExpected), rejected at site with code and the reduced type.
: lf-minfer-not-type ( site code type -- -1 status )
  ['] lf-mhead-not-sort? lf-minfer-head-rule
  if -rot lf-minfer-reject else 2drop outcome-unknown then no-result ;
: lf-minfer-sort-rule ( type site code -- level status )
  2>r dup lf-minfer-sort-level dup outcome-unknown =
  if 2drop 2r> rot lf-minfer-not-type else 2r> 2drop rot drop then ;
\ F1: a function's type that is no visible Pi is rejected when its whnfB
\ is rigid and not a Pi (Lean's ensure_pi_core fails: funExpected).
: lf-minfer-not-pi ( type -- outcome )
  dup 0 lf-diag-not-pi lf-minfer-note ['] lf-mhead-not-pi? lf-minfer-head-rule
  if lf-minfer-site lf-diag-function-expected lf-minfer-reject else outcome-unknown then ;

\ The rejection analysis below compares terms under the binders it enters
\ itself (D4), as before plan task 4.2.2a: a binder it enters gets a free
\ variable on the scope, above the scope's depth where the analysis
\ began, and the bodies keep their loose bound variables for those
\ binders, innermost the scope's top. A term of the analysis is closed by
\ putting those free variables for them (instantiate_rev), as P2 and D4's
\ domains need. Comparing and reducing such terms needs no closing.
: lf-minfer-apart-base ( -- addr ) lf-minfer-job lf-ijob-apart ;
: lf-minfer-closed ( node -- node' status ) lf-minfer-apart-base @ lf-minfer-open ;

\ P2, "known not to be a proof": node's type T and T's type infer, and the
\ latter's whnfB is Sort l with l not zero under every assignment, so
\ Lean's is_prop of T is false (fact 6). Inference runs aside on the
\ closed node, its free variables those of the local context; every
\ failure means "not known". The arena counts and the aside flag are
\ restored afterwards.
: lf-minfer-type2 ( node -- type status )
  lf-minfer-walk dup ok? if drop lf-minfer-walk then ;
: lf-minfer-sort? ( node -- level true | false )
  lf-term-read if drop swap lf-tag-symbolic-sort = dup 0= if nip then else false then ;
: lf-minfer-nonzero? ( level -- flag ) lf-minfer-zero? ok? if 0= else drop false then ;
: lf-minfer-sorted-free? ( type -- flag )
  lf-minfer-whnf ok-then? 0= if drop false exit then
  lf-minfer-sort? if lf-minfer-nonzero? else false then ;
: lf-minfer-free? ( node -- flag )
  lf-minfer-closed ok-then? 0= if drop false exit then
  lf-minfer-type2 ok-then? if lf-minfer-sorted-free? else drop false then ;
\ The arena counts, kept on the data stack around work whose allocations
\ are discarded (the return stack has less room for recursion).
: lf-minfer-counts ( -- terms levels crefs )
  lf-term-count @ lf-level-count @ lf-cref-count @ ;
: lf-minfer-counts! ( terms levels crefs -- )
  lf-cref-count ! lf-level-count ! lf-term-count ! ;
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
\ binders (see lf-minfer-closed). Each level reduces both sides; see
\ lf-minfer-apart-frame for its cost.
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
\ D3 and D5, two variables with arguments (is_def_eq_app, 878-895, needs
\ the same head and number): a different number of arguments, or
\ different variables known not to be proofs, are apart (D3); the same
\ variable and number are apart when some argument pair is (D5). A head is
\ a free variable (of inference's binders) or a bound one (of the
\ analysis's): the same variable when both tag and number are.
: lf-minfer-count ( node -- count ) lf-mhead-spine nip ;
: lf-minfer-head ( node -- head ) lf-mhead-spine drop ;
: lf-minfer-variable ( node -- index tag )
  lf-minfer-head dup lf-term-first@ swap lf-term-tag@ ;
: lf-minfer-same-head? ( left right -- flag )
  lf-minfer-variable rot lf-minfer-variable rot = >r = r> and ;
: lf-minfer-d5 ( left right mask -- mask' true ) nip nip lf-rule-d5 or true ;
: lf-minfer-args-apart ( left right count -- mask flag )
  0 ?do 2dup lf-minfer-seconds lf-minfer-apart if lf-minfer-d5 unloop exit then
    drop lf-minfer-firsts loop 2drop 0 false ;
: lf-minfer-heads ( left right -- head head' ) lf-minfer-head swap lf-minfer-head swap ;
: lf-minfer-heads-apart ( left right -- mask flag )
  lf-minfer-heads lf-minfer-free2? lf-rule-d3 lf-minfer-holds ;
: lf-minfer-arity? ( left right -- left right count true | false )
  2dup lf-minfer-count swap lf-minfer-count over = if true else drop 2drop false then ;
: lf-minfer-vars-apart ( left right -- mask flag )
  lf-minfer-arity? 0= if lf-rule-d3 true exit then
  >r 2dup lf-minfer-same-head?
  if r> lf-minfer-args-apart else r> drop lf-minfer-heads-apart then ;
\ D4, two Pis or two lambdas (is_def_eq_binding, 752-779; ADR 0003
\ Amendment 1, owner answers G6 and G7): when the domains are equal by the
\ cautious comparison, the pair is apart when the bodies are, the variable
\ having the right (expected) side's domain (B2): a new free variable of
\ that domain, closed, on the scope (Lean's is_def_eq_binding, 766-772),
\ which the bodies' loose bound variable 0 now stands for; otherwise when
\ the domains are apart. A binder that cannot be entered (no room or fuel)
\ is not apart.
: lf-minfer-enter-binder ( domain -- status )
  lf-minfer-closed ok-then? if 0 lf-minfer-bind then ;
: lf-minfer-bodies-apart ( left right -- mask flag )
  lf-minfer-context-depth @ -rot dup lf-term-first@ lf-minfer-enter-binder ok?
  if lf-minfer-seconds lf-minfer-apart else 2drop 0 false then rot lf-minfer-unbind ;
: lf-minfer-binders-apart ( left right -- mask flag )
  2dup lf-minfer-firsts lf-minfer-compare case
    outcome-ok of lf-minfer-bodies-apart endof
    outcome-unknown of lf-minfer-firsts lf-minfer-apart endof
    >r 2drop 0 false r> endcase lf-rule-d4 lf-minfer-via ;
\ One level: two Sorts by D1; otherwise P1 (both rigid) and P3 (not
\ exactly one a lambda) on the shapes, P2 on both sides (no proof
\ irrelevance), then D2 for different shapes among Sort, Pi and bound
\ variable, D3/D5 for two bound variables, D4 for two binders. Kinds
\ that are no shape (a constant: K1; lf-head-applied, lf-head-none) are
\ never apart.
: lf-minfer-one-lam? ( kl kr -- flag ) lf-head-lam = swap lf-head-lam = xor ;
: lf-minfer-shapes? ( kl kr -- flag )
  2dup lf-minfer-one-lam? 0= -rot lf-mhead-shape? swap lf-mhead-shape? and and ;
: lf-minfer-shapes-apart ( left right kl kr -- mask flag )
  2dup <> if 2drop 2drop lf-rule-d2 true exit then
  drop lf-head-var = if lf-minfer-vars-apart else lf-minfer-binders-apart then ;
: lf-minfer-rigid-apart ( left right kl kr -- mask flag )
  2dup lf-minfer-shapes? 0= if 2drop 2drop 0 false exit then
  2over lf-minfer-free2? if lf-minfer-shapes-apart else 2drop 2drop 0 false then ;
: lf-minfer-sorts? ( kl kr -- flag ) lf-head-sort = swap lf-head-sort = and ;
: lf-minfer-apart-visit ( left right -- mask flag )
  lf-minfer-whnf2 0= if 0 false exit then lf-minfer-kinds
  2dup lf-minfer-sorts? if 2drop lf-minfer-sorts-apart else lf-minfer-rigid-apart then ;

\ Compare an inferred type (left) with an expected type (right), in
\ Lean's order: (0 ok) when equal; (mask rejected) when the comparison is
\ undecided and D1-D5 show the pair apart; else (0 outcome), the
\ comparison's own. The analysis begins at the scope's current depth.
: lf-minfer-mismatch ( left right -- mask flag )
  lf-minfer-deciding? 0= if 2drop 0 false exit then
  lf-minfer-context-depth @ lf-minfer-apart-base ! lf-minfer-apart ;
: lf-minfer-agree ( left right -- mask status )
  2dup lf-minfer-compare dup outcome-unknown <> if nip nip 0 swap exit then
  drop lf-minfer-mismatch if outcome-rejected else outcome-unknown then ;

\ Application: the function's type must be a visible Pi (otherwise unknown,
\ or rejected by F1), the argument's type must convert to its domain
\ (otherwise unknown, or rejected by D1-D5: appTypeMismatch), and the type
\ is the Pi body instantiated with the argument.
: lf-minfer-pi-parts ( type -- domain body true | outcome false )
  dup lf-term-read 0= if drop outcome-invalid false exit then
  rot lf-tag-pi = if rot drop true else 2drop lf-minfer-not-pi false then ;
: lf-minfer-argument ( domain argument -- status )
  lf-term-count @ -rot lf-minfer-walk ok-then? 0= if nip swap lf-minfer-discard exit then
  swap lf-minfer-agree lf-minfer-site lf-diag-argument-apart lf-minfer-verdict
  swap lf-minfer-discard ;
: lf-minfer-apply ( domain body argument -- type status )
  rot over lf-minfer-argument ok-then?
  if lf-minfer-instantiate else nip lf-minfer-none then ;
: lf-minfer-app ( function argument -- type status )
  swap lf-minfer-walk lf-minfer-step? 0= if exit then
  lf-minfer-pi-parts if rot lf-minfer-apply else nip lf-minfer-none then ;

\ Binders, a telescope at a time, as infer_lambda and infer_pi walk one
\ (type_checker.cpp 125-166): while the body is a binder of the same tag,
\ the next domain, opened with the free variables of the binders before it
\ in the telescope (base is the scope's depth where it starts), must be a
\ type, its type a Sort (otherwise unknown, or rejected by S2); then it
\ gets a free variable on the scope with that Sort's level, and its
\ inference's scratch is discarded. The body, opened with all of them, is
\ then inferred, and the binders go back to the scope whatever the
\ outcome (lf-minfer-unbind). The words that call lf-minfer-walk keep
\ their state on the data stack and call no other word between their
\ visits, so that every nested level holds few cells of the return stack
\ (see "Host stacks" at the end).
: lf-minfer-domain-sort ( type -- level status )
  lf-minfer-site lf-diag-domain-type lf-minfer-sort-rule ;
: lf-minfer-domain-level ( mark type status -- level status )
  dup ok? if drop lf-minfer-domain-sort then rot lf-minfer-discard ;
: lf-minfer-open-domain ( base tag body domain -- base tag body domain' status )
  2over drop lf-minfer-open ;
: lf-minfer-bound ( domain level status -- status )
  ok-then? if lf-minfer-bind else nip then ;
: lf-minfer-more? ( body tag -- flag )
  over lf-term-valid? if swap lf-term-tag@ = else 2drop false then ;
: lf-minfer-fields ( node -- first second ) dup lf-term-first@ swap lf-term-second@ ;
: lf-minfer-binders ( base tag domain body -- base tag body status )
  begin swap lf-minfer-open-domain ok-then? 0= if exit then
    lf-term-count @ over lf-minfer-walk lf-minfer-domain-level lf-minfer-bound
    dup ok? 0= if exit then drop 2dup swap lf-minfer-more?
  while lf-minfer-fields repeat outcome-ok ;
\ A telescope that failed gives its binders back and no type. A step that
\ keeps base below its result: x and true, or -1, the failure and false.
: lf-minfer-escape ( base tag status -- -1 status ) nip swap lf-minfer-unbind no-result ;
: lf-minfer-good? ( x status -- x true | -1 status false )
  dup ok? if drop true else nip no-result false then ;
\ A lambda's type is the Pi over the telescope's free variables (mk_pi) of
\ its body's type (type_checker.cpp 139-141, without cheap_beta_reduce;
\ see the header).
: lf-minfer-lam ( domain body -- type status )
  lf-minfer-context-depth @ lf-tag-lam 2swap lf-minfer-binders ok-then?
  0= if lf-minfer-escape exit then nip over lf-minfer-open lf-minfer-good?
  if lf-minfer-walk lf-minfer-good? if over lf-minfer-close then then
  rot lf-minfer-unbind ;
\ A Pi's type is Sort (mk_imax u1 (mk_imax u2 ... v)) for domains in Sort
\ ui and a body in Sort v: Lean's infer_pi builds the level innermost
\ first (type_checker.cpp 158-165; ADR 0011, Amendment 1; level-make.fs).
\ S4 (ADR 0011, Amendment 2): the body's type must be a Sort too (infer_pi's
\ ensure_sort_core on the body, 158); when it is no visible Sort and its
\ whnfB is rigid and not a Sort, Lean's kernel fails with typeExpected. A
\ full level store is full. Only the level is needed, so the telescope's
\ scratch is discarded before the Sort is made.
: lf-minfer-body-sort ( type -- level status )
  lf-minfer-site lf-diag-body-type lf-minfer-sort-rule ;
: lf-minfer-imax-step ( v i -- v' i true | false )
  tuck lf-minfer-sort-cell @ swap lf-level-mk-imax if swap true else drop false then ;
: lf-minfer-imax ( v base -- level status )
  >r lf-minfer-context-depth @ begin 1- dup r@ < 0= while
    lf-minfer-imax-step 0= if r> drop -1 outcome-full exit then
  repeat drop r> drop outcome-ok ;
: lf-minfer-pi-level ( base type -- base level status )
  lf-minfer-body-sort lf-minfer-good? if over lf-minfer-imax then ;
: lf-minfer-pi-end ( mark base level status -- type status )
  rot lf-minfer-unbind rot lf-minfer-discard lf-minfer-good? if lf-minfer-sort then ;
: lf-minfer-pi ( domain body -- type status )
  lf-term-count @ -rot lf-minfer-context-depth @ lf-tag-pi 2swap lf-minfer-binders
  ok-then? 0= if lf-minfer-escape rot drop exit then nip over lf-minfer-open
  lf-minfer-good? if lf-minfer-walk lf-minfer-good? if lf-minfer-pi-level then then
  lf-minfer-pi-end ;

\ Infer a node: a source node, or one this job made from source nodes by
\ opening binders (or, aside, any live node). Constructors outside this
\ subset are unknown, and recorded as unsupported with their tag.
: lf-minfer-unsupported ( tag -- tag -1 status )
  dup 0 lf-diag-unsupported lf-minfer-note -1 outcome-unknown ;
: lf-minfer-leaf ( first tag -- type status )
  case lf-tag-symbolic-sort of lf-minfer-sort-type endof
    lf-tag-constant of lf-minfer-constant endof
    lf-tag-bvar of lf-minfer-bvar endof
    nip lf-minfer-unsupported rot endcase ;
: lf-minfer-binary ( first second tag -- type status )
  case lf-tag-app of lf-minfer-app endof
    lf-tag-lam of lf-minfer-lam endof
    lf-tag-pi of lf-minfer-pi endof
    nip nip lf-minfer-unsupported rot endcase ;
: lf-minfer-dispatch ( first second tag -- type status )
  dup lf-term-binary-tag? if lf-minfer-binary else nip lf-minfer-leaf then ;
\ Since plan task 4.2.2a inference reads the opened bodies and domains it
\ makes itself (as Lean's infer_lambda does), so every live node can be
\ read, as before only aside (test P2). A free variable is read through
\ its entry.
: lf-minfer-read ( node -- first second tag true | false )
  lf-term-read dup if >r rot r> then ;
: lf-minfer-visit ( node -- type status )
  dup lf-minfer-fvar? if lf-minfer-fvar exit then
  lf-minfer-read if lf-minfer-dispatch else -1 outcome-invalid then ;

\ Each visit costs one unit of fuel and holds one of at most
\ lf-depth-limit frames. No fuel left is exhausted and no free frame is
\ full (with neither, the fuel decides); both spend nothing and are
\ recorded as diagnostics.
: lf-minfer-frames-full ( -- )
  lf-minfer-depth @ lf-depth-limit lf-diag-frame-limit lf-minfer-note ;
: lf-minfer-refused ( outcome -- outcome )
  dup outcome-full = if lf-minfer-frames-full
  else lf-minfer-fuel @ lf-minfer-site lf-diag-exhausted then ;
: lf-minfer-room ( -- outcome )
  lf-minfer-fuel @ lf-minfer-depth @ lf-depth-limit < visit-outcome
  dup ok? 0= if lf-minfer-refused then ;
: lf-minfer-enter ( -- ) -1 lf-minfer-fuel +! 1 lf-minfer-depth +! ;
: lf-minfer-in-frame ( node -- type status )
  lf-minfer-room ok-then? 0= if no-result exit then
  lf-minfer-enter lf-minfer-visit -1 lf-minfer-depth +! ;
' lf-minfer-in-frame is lf-minfer-walk

\ Each level of the rejection analysis takes a frame and a unit of fuel
\ like an inference visit (with neither left, the pair is not shown
\ apart), and discards the nodes, levels and references it made.
: lf-minfer-apart-frame ( left right -- mask flag )
  lf-minfer-room ok? 0= if 2drop 0 false exit then
  lf-minfer-enter >r >r lf-minfer-counts r> r> lf-minfer-apart-visit
  2>r lf-minfer-counts! 2r> -1 lf-minfer-depth +! ;
' lf-minfer-apart-frame is lf-minfer-apart

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
  lf-ijob-crefs @ lf-cref-count ! ;
: lf-minfer-idle ( job -- )
  0 over lf-ijob-depth ! 0 over lf-ijob-binders ! 0 over lf-ijob-apart !
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

\ Host stacks. Each level of the recursion holds at most 8 return-stack
\ and 6 data-stack cells: stack painting on Gforth 0.7.3 and 1.0 (which
\ agree) along inference's five paths, an application's argument and
\ function, a binder's body and domain, and a Pi's body, at every depth
\ that ends ok (7 and 5; 2026-11-02), and along the rejection analysis's
\ two recursive paths, a D4 telescope (7 and 3) and D5 arguments (8 and 5:
\ the ?DO loop adds two return cells), which share the frame limit with
\ inference (the D5 depth 0-8 white-box, the D4 depth 1-7 through the
\ definition probe; 2026-11-02). Since free variables (plan task 4.2.2a,
\ painted on Gforth 1.0, 2026-11-03, as the cells per level between
\ depths 10 and 50): an argument chain 7 and 4, a Pi's domain chain 6 and
\ 6 (a telescope keeps its state on the data stack, so that its domains
\ are inferred with few return cells), lambdas in arguments 6 and 3.5 per
\ frame, D4 6 and 4, D5 8 and 5; a function chain 10 and 5, of which the
\ instantiate pass that the deepest application nests accounts for the
\ part above 8 (its depth grows with the chain's; it is no more than
\ beta's nesting, below). Opening and closing a binder (mixed-open.fs)
\ nests one pass of at most lf-depth-limit frames, fewer cells than beta's
\ three. At any level a comparison runs
\ conversion, whose beta reductions nest instantiate and shift passes
\ (lf-mbeta-*-cells, whose slack also covers the entry words of
\ conversion, of the definition probe and of the analysis's leaf steps:
\ test P2, which nests inference within the same frame limit, a
\ reduction, and level-value's evaluation for normalizes_to_zero, in S3
\ and P2, whose depth limit of 64 levels at about 8 return cells each
\ needs fewer cells than beta). A level comparison -- of two Sorts or of
\ constants' levels in conversion, or by rule D1 -- runs Lean's
\ normalize instead, never inside beta's passes: lf-lnorm-*-cells
\ (level-normalize.fs: 7 return and 3 data cells per node of the level
\ graph, 6.5 and 2.5 measured, plus the name order; 576 and 384 cells for
\ level graphs and names 64 deep). So the deepest level nests the larger
\ of beta's need and normalize's; tests/core/infer-deep.fs runs the
\ deepest normalize the level store allows at the deepest inference.
\ The frame that hands over from inference to the analysis, from the
\ inference frame whose argument is compared to the analysis's first
\ frame (in-frame, visit, dispatch, binary, app, apply, argument, agree,
\ mismatch, apart-frame), holds 9 return cells, one more than a level
\ (painted on both hosts, review of 2026-11-02), and either slack holds
\ the extra cell. There is at most one such frame on any path: inference
\ within the analysis (P2) runs aside, with no rule, so it never hands
\ over again. So a check nests at most lf-depth-limit levels of
\ inference or analysis plus the larger nested need, beta's at these
\ limits: 1,728 return and 1,344 data cells (Gforth 0.7.3 has 1,920 and
\ 2,048). Loading stops when the host's stacks are smaller, and the need
\ is stated for the job pool (context-need).
8 constant lf-minfer-rs-level   \ return-stack cells per level
6 constant lf-minfer-ds-level   \ data-stack cells per level
\ At the deepest level: beta's passes or a level comparison, never both.
lf-mbeta-return-cells lf-lnorm-return-cells max constant lf-minfer-rs-nested
lf-mbeta-data-cells lf-lnorm-data-cells max constant lf-minfer-ds-nested
: lf-minfer-need ( cells-per-level nested-cells -- cells ) swap lf-depth-limit * + ;
lf-minfer-rs-level lf-minfer-rs-nested lf-minfer-need constant lf-minfer-return-cells
lf-minfer-ds-level lf-minfer-ds-nested lf-minfer-need constant lf-minfer-data-cells
lf-minfer-data-cells lf-minfer-return-cells lf-mbeta-host?
0= [if] .( mixed-infer.fs: host stacks too small for lf-depth-limit) cr abort [then]
lf-minfer-data-cells lf-minfer-return-cells context-need
