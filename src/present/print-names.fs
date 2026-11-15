\ Names for the term printer: structured names as text, Lean's hygienic
\ names, and capture-free display names for binders, chosen as Lean's
\ delaborator does (pp.safeShadowing). Untrusted presentation code.
\ Requires print-job.fs and the core modules loaded below.
\ State: one paired walk record in the context, lf-pp-scan-walk, for the
\ scans that ask whether a body mentions a binder.

require ./print-job.fs
require ../core/levels.fs
require ../core/level-scope.fs
require ../core/tagged-sort-boundary.fs
require ../core/symbolic-session.fs
require ../core/generation-handles.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs

lf-walk-room context-walk2: lf-pp-scan-walk
\ The front end's leaves, free variables and metavariables (plan FE1g-1),
\ which are themselves: equal only to their own node, holding no bound
\ variable; term-printer.fs prints them through lf-pp-open-leaf.
: lf-pp-identity-tag? ( tag -- flag ) dup lf-tag-fvar = swap lf-tag-mvar = or ;

\ A structured name as text, components joined by dots, sent to xt
\ ( c-addr u -- ), from the first component on without recursion: the
\ component k from the root is found by walking up from the name, so a
\ name of n components takes n*n/2 steps. A name of more than
\ lf-name-default components prints nothing and marks the pool full (the
\ print then ends full), as a name the pool has no room for does. Unchecked:
\ the ID is valid and the name storage passed lf-name-storage-valid?, so
\ every prefix chain ends at the anonymous name, which gives nothing.
: lf-pp-part ( id xt -- )
  >r dup lf-name-str?
  if lf-name-text r> execute else lf-name-payload r> lf-pp-number-to then ;
: lf-pp-dot-to ( xt -- ) s" ." rot execute ;
\ Component k from the root (0 the first) of a name of n components.
: lf-pp-part-at ( id n k xt -- ) >r - 1- lf-name-ancestor r> lf-pp-part ;
: lf-pp-parts-to ( id n xt -- )
  over 0 ?do i if dup lf-pp-dot-to then 2 pick 2 pick i 3 pick lf-pp-part-at loop
  drop 2drop ;
: lf-pp-too-deep ( id n xt -- ) 2drop drop true lf-pjob lf-pjob-full ! ;
: lf-pp-name-to ( id xt -- )
  over lf-name-depth swap over lf-name-default >
  if lf-pp-too-deep else lf-pp-parts-to then ;

\ Hygienic names (Lean's macro scopes, such as a._@._internal._hyg.0)
\ print as the part before _@, as Lean's delaborator prints them.
: lf-pp-skip-nums ( id -- id' ) begin dup lf-name-num? while lf-name-prefix@ repeat ;
: lf-pp-hygienic? ( id -- flag ) lf-pp-skip-nums s" _hyg" lf-name-str-is? ;
: lf-pp-erase ( id -- id' )
  begin dup s" _@" lf-name-str-is? 0= over and while lf-name-prefix@ repeat lf-name-prefix@ ;
: lf-pp-hygienic ( name kind -- flag ) drop lf-pp-hygienic? ;
: lf-pp-unhygienic ( id -- id' ) dup lf-pp-hygienic? if lf-pp-erase then ;

\ A binder's suggested name, placed in the pool: its recorded name with
\ macro scopes erased; a for the anonymous name, as Lean; x when the side
\ table has no name for the binder.
: lf-pp-base ( id -- )
  lf-pp-unhygienic ?dup if ['] lf-pp-put lf-pp-name-to else s" a" lf-pp-put then ;
: lf-pp-suggest ( node -- ) lf-pres-binder@ if drop lf-pp-base else s" x" lf-pp-put then ;

\ Does any binder in scope from bottom index from upwards show this text?
\ A from beyond the scope (only after a forbidden reset from a sink) is
\ the top of the scope: no binder.
: lf-pp-shows? ( c-addr u i -- c-addr u flag ) lf-pp-bind-at lf-pp-text 2over compare 0= ;
: lf-pp-any? ( c-addr u from -- flag ) lf-pp-depth ['] lf-pp-shows? any-in? nip nip ;
: lf-pp-taken? ( mark -- flag ) lf-pp-pending 0 lf-pp-any? ;

\ Scans of a body with the print's fuel. In the body, bound variable i at
\ binder depth d (inside the body) is the body's own binder when i = d and
\ binder j = i - d - 1 of the scope (innermost first) when i > d. A scan
\ stops at the first hit. The walk (lib/walk.fs) stops only at an outcome
\ that is not ok, so a hit is reported as rejected, used here as a stop
\ signal that carries an answer, not as a verdict: lf-pp-hit? turns it
\ into a true flag beside ok as soon as the walk returns, so no public
\ word reports it. Invalid, exhausted and full pass through as failures.
: lf-pp-hit ( flag -- outcome ) if outcome-rejected else outcome-ok then ;
: lf-pp-hit? ( outcome -- flag outcome )
  dup outcome-rejected = if drop true outcome-ok else false swap then ;
: lf-pp-scan-binary ( first second walk tag -- outcome )
  over walk-context @ swap lf-term-inner if swap walk-children-at else drop 2drop
  outcome-full then ;
: lf-pp-leaf-tag? ( tag -- flag )
  dup lf-tag-sort = over lf-tag-symbolic-sort = or over lf-tag-constant = or
  over lf-tag-proj = or over lf-pp-identity-tag? or swap lf-literal-tag? or ;
: lf-pp-scan-other ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if lf-pp-scan-binary exit then
  lf-pp-leaf-tag? if drop 2drop outcome-ok else drop 2drop outcome-invalid then ;
\ Variable i mentions bound variable k of the body's context (walk-arg).
: lf-pp-var-is ( i walk -- outcome ) dup walk-context @ swap walk-arg @ + = lf-pp-hit ;
\ A scan's dispatch: a bound variable goes to var ( i walk -- outcome ),
\ every other node to lf-pp-scan-other.
: lf-pp-scan-dispatch ( first second walk tag var -- outcome )
  over lf-tag-bvar = if nip rot drop execute else drop lf-pp-scan-other then ;
: lf-pp-loose-dispatch ( first second walk tag -- outcome )
  ['] lf-pp-var-is lf-pp-scan-dispatch ;
: lf-pp-loose-visit ( walk -- outcome ) ['] lf-pp-loose-dispatch lf-term-visit ;
\ Variable i mentions a binder of the scope that shows the text pending at
\ mark (walk-arg). A variable beyond the scope is left to the printer.
: lf-pp-outer ( i d -- j true | false ) - 1- dup 0< if drop false else true then ;
: lf-pp-shows-pending? ( j mark -- flag )
  lf-pp-pending rot lf-pp-entry lf-pp-text compare 0= ;
: lf-pp-var-shows ( i walk -- outcome )
  tuck walk-context @ lf-pp-outer 0= if drop outcome-ok exit then
  dup lf-pp-depth < 0= if 2drop outcome-ok exit then
  swap walk-arg @ lf-pp-shows-pending? lf-pp-hit ;
: lf-pp-uses-dispatch ( first second walk tag -- outcome )
  ['] lf-pp-var-shows lf-pp-scan-dispatch ;
: lf-pp-uses-visit ( walk -- outcome ) ['] lf-pp-uses-dispatch lf-term-visit ;
: lf-pp-scan ( term arg xt -- flag outcome )
  >r lf-pp-scan-walk dup lf-pp-lend walk-arg !
  0 r> lf-pp-scan-walk walk-run-pair lf-pp-scan-walk lf-pp-repay lf-pp-hit? ;
\ Does term mention its context's bound variable k (0 = innermost)?
: lf-pp-loose? ( term k -- flag outcome ) ['] lf-pp-loose-visit lf-pp-scan ;
\ Does body (under one new binder) mention a binder in scope that shows
\ the name pending at mark?
: lf-pp-uses? ( body mark -- flag outcome ) ['] lf-pp-uses-visit lf-pp-scan ;

\ Choosing a binder's display name (Lean's getUnusedName with
\ pp.safeShadowing): keep the suggestion when no binder in scope shows it,
\ or when none from bottom index from upwards (a fun's earlier binders)
\ shows it and the body uses no binder in scope that shows it; otherwise
\ append _1, _2, ... until no binder in scope shows the result. The name is
\ left pending in the pool from mark; lf-pp-bind brings it into scope.
: lf-pp-suffix ( mark base-length k -- )
  >r + lf-pp-used ! s" _" lf-pp-put r> ['] lf-pp-put lf-pp-number-to ;
: lf-pp-retry? ( mark -- flag ) lf-pp-taken? lf-pp-full? 0= and ;
: lf-pp-fresh ( mark -- )
  dup lf-pp-pending nip 0
  begin 1+ >r 2dup r@ lf-pp-suffix over lf-pp-retry? while r> repeat r> drop 2drop ;
: lf-pp-clash? ( mark from -- flag ) swap lf-pp-pending rot lf-pp-any? ;
: lf-pp-shadow? ( mark body from -- flag outcome )
  rot tuck swap lf-pp-clash? if 2drop false outcome-ok else lf-pp-uses? >r 0= r> then ;
: lf-pp-kept? ( body from mark -- mark flag outcome )
  dup lf-pp-taken? 0= if nip nip true outcome-ok exit then
  dup >r -rot lf-pp-shadow? r> -rot ;
: lf-pp-renamed ( mark flag -- mark ) 0= if dup lf-pp-fresh then ;
: lf-pp-choose ( node body from -- mark outcome )
  rot lf-pp-used @ swap lf-pp-suggest lf-pp-kept?
  dup ok? if drop lf-pp-renamed lf-pp-pool-outcome else nip then ;
