\ The checked environment's answers to inference (plan task 2.2.3; ADR
\ 0011 rules N1, K5, L1, L2; ADR 0012 E2, E5). Inference in environment
\ mode (kernel/mixed-infer.fs, run by kernel/check-declaration.fs) asks
\ here where Lean's kernel asks its environment, and in Lean's order:
\ - at a constant, as infer_constant does (type_checker.cpp 101-120): the
\   lookup within the check's snapshot (lf-env-lookup: N1 rejects, K5
\   gives unknown or unsupported), the number of universe arguments (L1),
\   each argument within the checked declaration's universe parameters
\   (L2, check_level), then the constant's stored type with its own
\   parameters replaced by the arguments, all at once
\   (instantiate_type_lparams; lf-mixed-level-substitute). The stored type
\   is the accepted slot's own input term, never a copy;
\ - at a Sort, L2 on its level, as infer_type_core's Sort case does.
\ Deciding, a constant that passes is recorded as a dependency of the
\ check's candidate (lf-env-depend, which also joins its axiom set and
\ provenance). Aside (inference's proof test P2), as in Lean's
\ infer_only mode, L2 is skipped and nothing is recorded: a failure
\ there only means "not known". The lookup and the arity test cost no
\ fuel (Lean's lookup is a map access); L2 costs one unit per level node
\ visited, the specialization what lf-mixed-level-substitute charges.
\ [kernel] code: experimental, not through the review gate.
\ State: the walk record lf-envsig-walker (L2 on one level) and the
\ request record lf-envsig-request (one constant), both members of the
\ checker context (lib/context.fs). The environment is read only within
\ the check's snapshot (environment.fs).

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/levels.fs
require ../core/terms.fs
require ./environment.fs
require ./mixed-level-substitute.fs

lf-level-walk-room context-walk: lf-envsig-walker

begin-structure /lf-esreq
  field: lf-esreq-name      \ the constant's name ID
  field: lf-esreq-pairs     \ address of its universe arguments, (index identity) pairs
  field: lf-esreq-count     \ their number
  field: lf-esreq-fuel      \ fuel left
  field: lf-esreq-deciding  \ false while inference runs aside
end-structure
/lf-esreq context-record: lf-envsig-request

\ L2 on a level: every parameter it names is one of the checked
\ declaration's (lf-env-param?: ok, rejected, or invalid without a
\ check's snapshot). The audit validated the level graph before.
: lf-envsig-param ( first second walk -- outcome ) 2drop lf-env-param? ;
: lf-envsig-succ ( first second walk -- outcome ) nip walk-child ;
: lf-envsig-zero ( first second walk -- outcome ) drop 2drop outcome-ok ;
: lf-envsig-dispatch ( first second walk tag -- outcome )
  dup lf-level-binary-tag? if drop walk-children exit then
  case lf-level-tag-param of lf-envsig-param endof
    lf-level-tag-succ of lf-envsig-succ endof
    lf-level-tag-zero of lf-envsig-zero endof walk-bad-tag endcase ;
: lf-envsig-visit ( walk -- outcome ) lf-levels ['] lf-envsig-dispatch walk-visit ;
: lf-envsig-site ( -- site ) c" env-signature lf-env-level-scope" ;
: lf-envsig-walk ( level -- outcome )
  ['] lf-envsig-visit lf-envsig-walker walk-run
  lf-envsig-walker lf-envsig-site lf-diag-walk ;
\ L2 on one level with the given fuel: the fuel left, and ok; rejected for
\ a parameter the checked declaration does not declare; invalid without a
\ check's snapshot, for negative fuel or a malformed level; exhausted;
\ full.
: lf-env-level-scope ( level fuel -- fuel' outcome )
  lf-envsig-walker walk-budget 0= if drop 0 outcome-invalid exit then
  lf-envsig-walk lf-envsig-walker walk-fuel @ swap ;

\ The request's fields.
: lf-envsig-fuel ( -- addr ) lf-envsig-request lf-esreq-fuel ;
: lf-envsig-count ( -- n ) lf-envsig-request lf-esreq-count @ ;
: lf-envsig-deciding? ( -- flag ) lf-envsig-request lf-esreq-deciding @ ;

\ L1, then (deciding) L2 on each universe argument, then (deciding) the
\ dependency; each ( d -- d outcome ) for the accepted slot d found.
: lf-envsig-arity ( d -- d outcome ) lf-envsig-count over lf-env-arity? ;
: lf-envsig-level ( level -- outcome )
  lf-envsig-fuel @ lf-env-level-scope swap lf-envsig-fuel ! ;
: lf-envsig-argument ( k -- outcome )
  lf-envsig-request lf-esreq-pairs @ swap lf-cref-pair@ drop lf-envsig-level ;
: lf-envsig-arguments ( -- outcome )
  lf-envsig-count 0 ?do i lf-envsig-argument dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
: lf-envsig-scoped ( d -- d outcome )
  lf-envsig-deciding? if lf-envsig-arguments else outcome-ok then ;
: lf-envsig-record ( d -- d outcome )
  lf-envsig-deciding? if dup lf-env-depend else outcome-ok then ;

\ The stored type of a declaration -- an accepted slot's, or one the
\ check declares itself -- a live input term, with the declaration's own
\ parameters replaced by the request's arguments; on success also the
\ fuel left, for inference to go on with.
: lf-envsig-root ( decl -- root identity true | false )
  lf-idecl-type @ dup lf-term-identity if true else drop false then ;
: lf-envsig-actuals ( -- pairs count fuel )
  lf-envsig-request dup lf-esreq-pairs @ over lf-esreq-count @ rot lf-esreq-fuel @ ;
: lf-envsig-left ( root identity 0 | status -- root identity fuel' 0 | status )
  dup ok? if drop lf-mls-fuel @ outcome-ok then ;
: lf-envsig-instantiate ( decl -- root identity fuel' 0 | status )
  dup lf-envsig-root 0= if drop outcome-invalid exit then
  rot lf-idecl-params@ drop lf-envsig-actuals lf-mixed-level-substitute lf-envsig-left ;
: lf-envsig-type ( d -- root identity fuel' 0 | status )
  lf-env-accepted ok-then? if lf-slot-decl lf-envsig-instantiate then ;

\ Constants a check declares itself before it uses them (plan task
\ 5.2.1a): an inductive block's own type while its constructors are
\ checked, as Lean's add_inductive declares the types first
\ (inductive.cpp, declare_inductive_types). The hook gives the input
\ declaration of such a name; it is set once, while loading, by
\ check-block.fs, which answers only during a block's check. Such a
\ constant is found before the environment is asked, gets L1 and (while
\ deciding) L2 as any other, and is no dependency.
defer lf-envsig-local ( name -- decl true | false )
:noname ( name -- false ) drop false ; is lf-envsig-local
: lf-envsig-arity-local ( decl -- decl outcome )
  lf-envsig-count over lf-idecl-arity @ 2dup = if 2drop outcome-ok
  else lf-env-arity-rejected then ;
: lf-envsig-own ( decl -- root identity fuel' 0 | status )
  lf-envsig-arity-local ok-then? 0= if exit then
  lf-envsig-scoped ok-then? 0= if exit then lf-envsig-instantiate ;
: lf-envsig-run ( -- root identity fuel' 0 | status )
  lf-envsig-request lf-esreq-name @ dup lf-envsig-local if nip lf-envsig-own exit then
  lf-env-lookup ok-then? 0= if exit then
  lf-envsig-arity ok-then? 0= if exit then lf-envsig-scoped ok-then? 0= if exit then
  lf-envsig-record ok-then? 0= if exit then lf-envsig-type ;

\ The type of the constant named name with count universe arguments at
\ pairs, for the check in this context, deciding or aside, with fuel:
\ (root identity fuel' ok) for the stored type specialized; rejected by
\ N1, L1 or L2 (each recorded by the environment); unknown or unsupported
\ by K5; full for a full dependency list or store; exhausted; invalid
\ without a check's snapshot or for a stored type that is not live. The
\ arguments must be valid level pairs, any number of them.
: lf-env-signature ( name pairs count fuel deciding -- root identity fuel' 0 | status )
  lf-envsig-request >r r@ lf-esreq-deciding ! r@ lf-esreq-fuel ! r@ lf-esreq-count !
  r@ lf-esreq-pairs ! r> lf-esreq-name ! lf-envsig-run ;
