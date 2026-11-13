\ The scope check and abstraction of a metavariable assignment for the
\ front end's unifier (plan FE1c; ADR 0021 D6): ports of Lean 4.35.0's
\ checkAssignment (Lean/Meta/ExprDefEq.lean, with CheckAssignment and
\ CheckAssignmentQuick, which give the same verdicts) and of
\ mkLambdaFVars xs v (etaReduce := true) as processAssignment uses it
\ (Lean/MetavarContext.lean, mkBinding).
\ lf-meta-pattern! ( mvar addr n -- ) names ?m and the xi, the n free
\ variables in cells at addr (kept while the next words run);
\ lf-meta-check-assignment ( v -- v' flag outcome ): may ?m := fun x1
\ .. xn => v be made? invalid for a stale ?m; false (Lean's none) when ?m
\ occurs in an xi's type, else v with its metavariables instantiated is
\ walked:
\ - a free variable is in ?m's scope when ?m's own local context holds it
\   (lf-mvar-sees?); else it must be one of the xi (else the
\   check fails, "out of scope");
\ - a metavariable: ?m itself fails (the occurs check); with an xi in
\   ?m's own scope (Lean's hasCtxLocals) every other one fails; a
\   delayed one fails when ?m occurs in its pending metavariable; one
\   whose scope, less the xi, is a prefix of ?m's is fine and its type
\   must not hold ?m (typeOccursCheck); any other fails when it is
\   read-only (another depth) or synthetic opaque, and also without
\   ctxApprox;
\ - the parts of any other node, the first failure counting.
\ Never a guess: unsupported for what Lean does by changing the context
\ or the value: an out-of-scope let variable (Lean puts in its value), a
\ metavariable whose scope is wider with ctxApprox (Lean makes a new one
\ of a narrower scope), ?f x1 .. xk with an xi out of scope under
\ ctxApprox (Lean assigns ?f a constant function), and a failure inside
\ a beta-redex (Lean retries it beta-reduced).
\ lf-meta-mk-lambda ( addr n v -- lam outcome ): mkLambdaFVars xs v with
\ etaReduce, the innermost binder first: fun x => f x with x not in f is
\ f; else a lambda over the free variable's type (head-beta reduced),
\ abstracted (instantiate.fs). Unsupported, as Lean then changes the
\ metavariable context or adds let binders: a metavariable of v or of
\ an xi's type whose scope holds an xi (elimMVarDeps), and a let
\ variable in the local context between the first xi and the last.
\ The xi must be live free variables, not let variables, in the order of
\ the local context (processAssignment's are). Both words take the
\ local context to be one prefix of a growing list (mvars.fs, FE1b),
\ until per-goal contexts come (plan FE1g-1).
\ lf-meta-ctx-approx! ( flag -- ) sets ctxApprox (Lean's Meta.Config).
\ Outcomes: ok; unsupported as above; full when a store or the heap has
\ no room; invalid for a stale leaf. Untrusted.
\ State: the record ac (the walk, ?m, the xi and two flags), a member of
\ the checker context (ADR 0009); one check at a time.

require ../lib/lib.fs
require ../core/terms.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../core/let-terms.fs
require ./dag-walk.fs
require ./mvars.fs
require ./instantiate.fs
require ./meta-spine.fs
require ./term-eqv.fs

begin-structure /ac
  field: ac-target    \ ?m
  field: ac-xs        \ the xi: the address of their cells
  field: ac-n         \ and how many
  field: ac-locals    \ hasCtxLocals: an xi in ?m's scope
  field: ac-hit       \ typeOccursCheck: ?m in a metavariable's type
  field: ac-approx    \ ctxApprox
  /dw +field ac-walk
end-structure
/ac context-record: ac
: lf-meta-ctx-approx! ( flag -- ) ac ac-approx ! ;

\ Scopes: each metavariable's own local context (mvars.fs, lctx-views.fs).
: ac-x ( i -- x ) cells ac ac-xs @ + @ ;
: ac-xs? ( fvar -- flag ) false ac ac-n @ 0 ?do over i ac-x = or loop nip ;
: ac-m ( -- mvar ) ac ac-target @ ;
: ac-view ( mvar -- view ) lf-mvar-view 0= if lf-view-empty then ;
\ ?n's context less the xi is a sub-prefix of ?m's (isSubPrefixOf with
\ exceptFVars).
: ac-prefix? ( mvar -- flag )
  ac-view ac-m ac-view ac ac-xs @ ac ac-n @ lf-view-sub-prefix-except? ;
: ac-sees-x? ( mvar -- flag )
  false ac ac-n @ 0 ?do over i ac-x lf-mvar-sees? or loop nip ;

\ ---- Images: 0 fine, 1 out of scope, 2 failed (Lean's two exceptions).
0 constant ac-fine  1 constant ac-scope-fail  2 constant ac-fail
: ac-wk ( -- walk ) ac ac-walk ;
: ac-refuse-with ( outcome -- 0 ) ac-wk dw-refuse 0 ;
: ac-refuse ( -- 0 ) outcome-unsupported ac-refuse-with ;
: ac-fvar ( fvar -- image )
  dup lf-fvar-live? 0= if drop outcome-invalid ac-refuse-with exit then
  ac-m over lf-mvar-sees? if drop ac-fine exit then
  dup lf-fvar-let? if drop ac-refuse exit then
  ac-xs? if ac-fine else ac-scope-fail then ;
\ Whether ?m occurs in a term, its assignments followed (mvars.fs); a
\ check that fails ends the walk with its outcome.
: ac-occurs-in ( term -- flag )
  ac-m swap lf-mvar-occurs? dup ok? if drop else ac-refuse-with drop false then ;
: ac-typed ( mvar -- ) lf-mvar-type if ac-occurs-in if true ac ac-hit ! then then ;
: ac-other ( mvar -- image )
  lf-mvar-assignable? 0= if ac-fail exit then ac ac-approx @ if ac-refuse
  else ac-fail then ;
: ac-pending ( mvar -- flag ) lf-mvar-delayed if 2drop ac-occurs-in else false then ;
: ac-mvar ( mvar -- image )
  dup ac-m = if drop ac-fail exit then  dup lf-mvar-value if 2drop ac-refuse exit then
  ac ac-locals @ if drop ac-fail exit then  dup ac-pending if drop ac-fail exit then
  dup ac-prefix? if ac-typed ac-fine else ac-other then ;
: ac-leaf ( node -- image )
  dup lf-term-tag@ case lf-tag-fvar of ac-fvar endof  lf-tag-mvar of ac-mvar endof
    >r drop ac-fine r> endcase ;

\ Nodes: one with no free variable and no metavariable is fine without a
\ visit of its parts; a let's parts in Lean's order (type, value, body).
: ac-binary? ( node -- flag ) lf-term-tag@ lf-term-binary-tag? ;
: ac-ground? ( node -- flag ) lf-term-data@ if lf-data-fvar? 0= else false then ;
: ac-inner? ( node -- flag ) dup ac-binary? if ac-ground? 0= else drop false then ;
: ac-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: ac-parts ( node walk -- child true | false )
  over lf-term-first@ over ac-undone if nip nip true exit then
  swap lf-term-second@ swap ac-undone ;
: ac-pending-child ( node walk -- child true | false )
  over ac-inner? if ac-parts else 2drop false then ;
: ac-first-fail ( i1 i2 -- image ) over if drop else nip then ;
: ac-img ( node -- image ) ac-wk dw-image ;
: ac-let ( let -- image )
  dup lf-let-binder ac-inner? 0= if lf-let-value ac-img exit then
  dup lf-let-type ac-img
  over lf-let-value ac-img ac-first-fail swap lf-let-body ac-img ac-first-fail ;
: ac-pair ( node -- image )
  dup lf-let? if ac-let exit then
  dup lf-term-first@ ac-img swap lf-term-second@ ac-img ac-first-fail ;

\ Applications: a failure under a lambda head Lean retries beta-reduced;
\ ?f x1 .. xk with a variable out of scope, under ctxApprox, it solves
\ with a constant function.
: ac-beta? ( node -- flag ) lf-meta-head lf-term-tag@ lf-tag-lam = ;
: ac-fvar? ( t -- flag ) lf-term-tag@ lf-tag-fvar = ;
: ac-fvar-args? ( node -- flag )
  true swap begin dup lf-meta-app? while dup lf-term-second@ ac-fvar? rot and swap
  lf-term-first@ repeat drop ;
: ac-delayed? ( mvar -- flag ) lf-mvar-delayed dup if nip nip nip then ;
: ac-mvar-spine? ( node -- flag )
  ac ac-approx @ 0= if drop false exit then
  dup lf-meta-head dup lf-term-tag@ lf-tag-mvar =
  if ac-delayed? 0= swap ac-fvar-args? and else 2drop false then ;
: ac-app ( node image -- image )
  dup 0= if nip exit then  over ac-beta? if 2drop ac-refuse exit then
  dup ac-scope-fail = if over ac-mvar-spine? if 2drop ac-refuse exit then then nip ;
: ac-build ( node walk -- image )
  drop dup ac-inner? 0= if dup ac-binary? if drop ac-fine else ac-leaf then exit then
  dup ac-pair over lf-meta-app? if ac-app else nip then ;
: ac-walk-set ( pending build -- walk )
  ac-wk tuck dw-build ! tuck dw-pending ! lf-term-base lf-term-count @ + over dw-size ! ;

\ ---- checkAssignment.
: ac-xs! ( mvar addr n -- ) ac tuck ac-n ! tuck ac-xs ! ac-target ! ;
: ac-x-occurs? ( -- flag outcome )
  false ac ac-n @ 0 ?do ac-m i ac-x lf-fvar-type lf-mvar-occurs? ok-then? 0=
    if nip unloop false swap exit then or loop outcome-ok ;
: ac-locals? ( -- flag ) ac-m ac-sees-x? ;
: ac-solid? ( v -- flag )
  dup ac-binary? if ac-ground? exit then lf-term-tag@
  dup lf-tag-fvar <> swap lf-tag-mvar <> and ;
: ac-verdict ( v image outcome -- v' flag outcome )
  dup ok? 0= if nip false swap exit then drop 0= ac ac-hit @ 0= and outcome-ok ;
: ac-run ( v -- v' flag outcome )
  lf-instantiate-mvars ok-then? 0= if -1 false rot exit then
  ac-locals? ac ac-locals !  false ac ac-hit !
  dup ['] ac-pending-child ['] ac-build ac-walk-set dw-run ac-verdict ;
: lf-meta-pattern! ( mvar addr n -- ) ac-xs! ;
: lf-meta-check-assignment ( v -- v' flag outcome )
  ac-m lf-mvar-live? 0= if false outcome-invalid exit then
  ac-x-occurs? ok-then? 0= if false swap exit then if false outcome-ok exit then
  dup ac-solid? if true outcome-ok else ac-run then ;

\ ---- mkLambdaFVars xs v (etaReduce), from the last xi to the first.
: ac-set ( addr n -- ) ac tuck ac-n ! ac-xs ! ;
\ hasLetDeclsInBetween: a let local of the current context (Lean's
\ isLet: not a have) between the first xi and the last; an xi the
\ context lacks counts as one (unsupported).
: ac-place ( fvar -- i true | false ) lf-mctx-view swap lf-view-find ;
: ac-let-at? ( i -- flag ) lf-mctx-view swap lf-view-local lf-local-fvar lf-fvar-let? ;
: ac-ranks ( -- lo hi true | false )
  0 ac-x ac-place 0= if false exit then
  ac ac-n @ 1- ac-x ac-place if true else drop false then ;
: ac-let-between? ( -- flag )
  ac ac-n @ 2 < if false exit then ac-ranks 0= if true exit then
  false -rot swap 1+ ?do i ac-let-at? or loop ;
\ elimMVarDeps would act: a metavariable whose scope holds an xi (a node
\ whose data word is known holds no metavariable).
: ac-dep-inner? ( node -- flag )
  dup ac-binary? if lf-term-data@ dup if nip then 0= else drop false then ;
: ac-dep-pending ( node walk -- child true | false )
  over ac-dep-inner? if ac-parts else 2drop false then ;
: ac-dep-leaf ( node -- 0|1 )
  dup lf-term-tag@ lf-tag-mvar = if ac-sees-x? 1 and else drop 0 then ;
: ac-dep-build ( node walk -- 0|1 )
  drop dup ac-dep-inner? if
  dup lf-term-first@ ac-img swap lf-term-second@ ac-img or exit then
  dup ac-binary? if drop 0 else ac-dep-leaf then ;
: ac-deps? ( term -- flag outcome )
  ['] ac-dep-pending ['] ac-dep-build ac-walk-set dw-run swap 0<> swap ;
: ac-types-deps? ( -- flag outcome )
  false ac ac-n @ 0 ?do i ac-x lf-fvar-type ac-deps? ok-then? 0=
    if nip unloop false swap exit then or loop outcome-ok ;
: ac-unported? ( v -- flag outcome )
  ac-let-between? if drop true outcome-ok exit then
  ac-deps? ok-then? 0= if false swap exit then if true outcome-ok
  else ac-types-deps? then ;

\ One binder: fun x => f x, x not in f, is f; else a lambda.
: ac-eta ( e x -- e' flag outcome )
  over lf-meta-app? 0= if drop false outcome-ok exit then
  over lf-term-second@ over <> if drop false outcome-ok exit then
  over lf-term-first@ lf-mvar-occurs? ok-then? 0= if false swap exit then
  if false else lf-term-first@ true then outcome-ok ;
: ac-lam ( e i -- lam outcome )
  dup ac-x lf-fvar-type lf-meta-head-beta ok-then? 0= if nip nip no-result exit then
  -rot cells ac ac-xs @ + 1 lf-meta-abstract ok-then? 0= if nip no-result exit then
  lf-term-lam if outcome-ok else -1 outcome-full then ;
: ac-binder ( e i -- e' outcome )
  2dup ac-x ac-eta ok-then? 0= if >r 2drop drop r> no-result exit then
  if nip nip outcome-ok else drop ac-lam then ;
: ac-binders ( v -- lam outcome )
  ac ac-n @ begin dup 0> while 1- tuck ac-binder ok-then? 0=
  if nip no-result exit then swap
  repeat drop outcome-ok ;
: lf-meta-mk-lambda ( addr n v -- lam outcome )
  over 0= if nip nip outcome-ok exit then
  >r ac-set r@ ac-unported? ok-then? 0= if r> drop no-result exit then
  if r> drop -1 outcome-unsupported else r> ac-binders then ;
