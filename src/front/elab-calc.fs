\ Lean's calc, the elaborator's part (plan row 9.4.8z12, small tactics
\ 2): a port of Lean 4.35.0's src/lean/Lean/Elab/Calc.lean, the steps
\ calc a ~ b := p, _ ~ c := q, .. made one proof of a ~ z by Trans.trans,
\ for the calc tactic (tactics/calc.fs). Every word throws on failure
\ (meta-must.fs); a Lean error at the step running (tactic-run.fs).
\ - lf-calc-relation? ( e -- r a b true | false ): getCalcRelation? (:21):
\   e an application of two arguments at least, r its function without
\   the last two (taken to be the relation's, explicit, as Lean assumes);
\   lf-calc-rel? ( e -- flag ) its test alone; lf-calc-rel, lf-calc-lhs,
\   lf-calc-rhs ( e -- x ) the parts of one.
\ - lf-calc-trans ( result rtype step stype -- x y true | x code false ): mkCalcTrans
\   (:35): r a b of rtype, s _ c of stype instantiated; u and v their
\   relations' sorts (getRelUniv, :28: the sort that ends r's type, which
\   is the sort of r a b, rtype itself, as inferType of r a b instantiates
\   r's type with a b: the level of rtype and of stype); α β γ the types
\   of a b c and their levels u1 u2 u3; w a new level metavariable and t a
\   new natural metavariable of α → γ → Sort w; then trySynthInstance of
\   Trans.{u,v,w,u1,u2,u3} α β γ r s t (t is Trans's out-parameter).
\   Found: true, x Trans.trans.{the same} α β γ r s t self a b c result
\   step and y its type instantiated and head-beta reduced, which must be
\   a relation (else false with code 511, Lean's "invalid 'calc' step,
\   step result is not a relation", x that type). Not found (or stuck):
\   false with code 510, "invalid 'calc' step, failed to synthesize
\   `Trans` instance", x the type sought.
\ - lf-elab-calc-steps ( i n -- val type ): elabCalcSteps (:107) of the n
\   steps that are step i's arguments in pairs (a relation term T, then
\   its proof e), in the current context, in the elaborator's
\   configuration (elab-decl.fs's lf-elab-configured; a failure of the
\   elaborator stops the step as tactic-core.fs's lf-tac-elab-fail does):
\   T by Term.elabType (no synthesis after it), from the second step on
\   with its first hole ascribed the type of the right side before it
\   (annotateFirstHoleWithType, :63: the leaf a binop tree's left
\   operands lead to, when it is _; a step that is _ alone is not
\   supported yet, 99), a relation (else 512, "invalid 'calc' step,
\   relation expected", with T); from the second step on, its left side
\   isDefEqGuarded to the right side before it (else 513, "invalid
\   'calc' step, left-hand side is", with both sides and their types); e
\   by Term.elabTermEnsuringType against T; from the second step on,
\   synthesizeSyntheticMVarsUsingDefault and lf-calc-trans of the chain
\   so far and the step (its code at the step); after the last step,
\   synthesizeSyntheticMVarsUsingDefault again. One step is its proof.
\ Not ported: throwCalcFailure (:139: the chain's type and the goal's,
\ after a coercion was not found; the tactic answers 131, not supported
\ yet, as the elaborator does for every coercion) and the term form
\ (elabCalc, :178; no LeanForth form).
\ Lean call list: getCalcRelation? -> lf-calc-relation?; getRelUniv ->
\ lf-level!; inferType, getLevel, instantiateMVars, headBeta ->
\ lf-infer!, lf-level!, lf-instantiate!, lf-meta-head-beta;
\ mkFreshLevelMVar, mkFreshExprMVar -> lf-level-mvar-new, lf-mvar-new;
\ mkConst, mkAppN -> lf-mk-const, lf-mk-app-cells; trySynthInstance ->
\ lf-try-synth; elabType, elabTermEnsuringType -> lf-elab-type,
\ lf-elab-ensuring; isDefEqGuarded -> lf-meta-defeq-guarded;
\ synthesizeSyntheticMVarsUsingDefault -> lf-elab-synthesize-default.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: ecl-trans-frames and ecl-step-frames (a frame per call open,
\ meta-must.fs's lf-with-record), in the checker context (ADR 0009);
\ the ascription a step's first hole is given is in its syntax node.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/bounds.fs
require ../lib/slab.fs
require ./syntax.fs
require ./mvars.fs
require ./meta-spine.fs
require ./instantiate.fs
require ./synth.fs
require ./elab-pending.fs
require ./elab-term.fs
require ./elab-decl.fs
require ./tactic-api.fs

510 lfa-lean s" invalid 'calc' step, failed to synthesize `Trans` instance"
  lfa-code: lfa-e-calc-trans
511 lfa-lean s" invalid 'calc' step, step result is not a relation"
  lfa-code: lfa-e-calc-not-rel
512 lfa-lean s" invalid 'calc' step, relation expected" lfa-code: lfa-e-calc-relation
513 lfa-lean s" invalid 'calc' step, left-hand side is" lfa-code: lfa-e-calc-lhs

\ ---- getCalcRelation?: r a b of r a b.
: lf-calc-rhs ( e -- b ) lf-term-second@ ;
: lf-calc-lhs ( e -- a ) lf-term-first@ lf-term-second@ ;
: lf-calc-rel ( e -- r ) lf-term-first@ lf-term-first@ ;
: lf-calc-rel? ( e -- flag ) lf-meta-args# 1 > ;
: ecl-parts ( e -- r a b ) dup lf-calc-rel swap lf-meta-args2 ;
: lf-calc-relation? ( e -- r a b true | false )
  dup lf-calc-rel? if ecl-parts true exit then drop false ;
\ One the caller made sure of (Lean's unreachable!): else a fault.
: ecl-relation ( e -- r a b )
  dup lf-calc-rel? 0= if outcome-invalid lf-must then ecl-parts ;

\ ---- mkCalcTrans: a frame of the levels, then Trans.trans's arguments.
\ The layout is Trans.trans's: its six levels from ecf-u and its twelve
\ arguments from ecf-alpha lie in adjacent cells in Lean's order, read as
\ arrays by ecl-levels and ecl-applied (keep the fields in that order).
begin-structure /ecf
  field: ecf-u  field: ecf-v  field: ecf-w  field: ecf-u1  field: ecf-u2  field: ecf-u3
  field: ecf-alpha  field: ecf-beta  field: ecf-gamma
  field: ecf-r  field: ecf-s  field: ecf-t  field: ecf-self
  field: ecf-a  field: ecf-b  field: ecf-c  field: ecf-result  field: ecf-step
end-structure
/ecf context-slab: ecl-trans-frames
: ecf ( -- addr ) ecl-trans-frames slab-last ;
: ecf! ( x xt -- ) ecf swap execute ! ;   \ xt a field of the frame
: ecl-chain! ( result rtype -- )
  dup lf-level! ['] ecf-u ecf! ecl-relation ecf ecf-a cell-pair! ['] ecf-r ecf!
  ['] ecf-result ecf! ;
: ecl-step! ( step stype -- )
  lf-instantiate! dup lf-level! ['] ecf-v ecf! ecl-relation ['] ecf-c ecf! drop
  ['] ecf-s ecf! ['] ecf-step ecf! ;
\ α β γ the types of a b c, u1 u2 u3 their levels, each in Lean's order.
: ecl-types ( -- α β γ )
  ecf ecf-a @ lf-infer! ecf ecf-b @ lf-infer! ecf ecf-c @ lf-infer! ;
: ecl-types! ( -- ) ecl-types ecf ecf-alpha cell-triple! ;
: ecl-sorts ( -- u1 u2 u3 )
  ecf ecf-alpha @ lf-level! ecf ecf-beta @ lf-level! ecf ecf-gamma @ lf-level! ;
: ecl-levels! ( -- ) ecl-sorts ecf ecf-u1 cell-triple! ;
\ w, then t : α → γ → Sort w.
: ecl-arrow ( dom body -- pi ) lf-term-pi lf-made! ;
: ecl-sort ( level -- sort ) lf-term-symbolic-sort lf-made! ;
: ecl-t-type ( -- type )
  ecf ecf-alpha @ ecf ecf-gamma @ ecf ecf-w @ ecl-sort ecl-arrow ecl-arrow ;
: ecl-fresh! ( -- )
  lf-level-mvar-new lf-must ['] ecf-w ecf! ecl-t-type mv-natural lf-mvar-new lf-must
  ['] ecf-t ecf! ;
\ A constant at the six levels, applied to the first n arguments.
: ecl-levels ( -- u v w u1 u2 u3 ) ecf ecf-u 6 0 do dup i cells + @ swap loop drop ;
: ecl-applied ( c-addr u n -- e )
  >r ecl-levels 6 lf-mk-const ecf ecf-alpha r> lf-mk-app-cells ;
: ecl-relation-result ( e type -- x y true | x code false )
  dup lf-calc-rel? if true else nip lfa-e-calc-not-rel false then ;
: ecl-result ( -- x y true | x code false )
  s" Trans.trans" 12 ecl-applied dup lf-infer! lf-instantiate! lf-meta-head-beta lf-must
  ecl-relation-result ;
: ecl-synth ( -- x y true | x code false )
  s" Trans" 6 ecl-applied dup lf-try-synth lf-must lf-synth-some =
  if ['] ecf-self ecf! drop ecl-result else drop lfa-e-calc-trans false then ;
: ecl-frame! ( result rtype step stype -- ) ecl-step! ecl-chain! ecl-types! ecl-levels! ;
: ecl-trans ( result rtype step stype -- x y true | x code false )
  ecl-frame! ecl-fresh! ecl-synth ;
: lf-calc-trans ( result rtype step stype -- x y true | x code false )
  ecl-trans-frames ['] ecl-trans lf-with-record ;

\ ---- The step's errors: 512 with T; 513 with both sides; a code of
\ lf-calc-trans with its term (510's with useDiagnosticMsg's hint).
: ecl-no-relation ( type -- )
  ['] lf-tac-indented. lf-tac-detail lfa-e-calc-relation lf-tac-stop ;
: ecl-type-of. ( e -- outcome )
  s"  : " lf-pp-emit lf-infer ok-then? if lf-tac-term. then ;
: ecl-typed. ( e -- outcome ) dup lf-tac-indented. ['] ecl-type-of. ok-with nip ;
: ecl-but. ( prev -- outcome )
  s\" \nbut previous right-hand side is\n" lf-pp-emit ecl-typed. ;
: ecl-sides. ( prev lhs -- outcome ) ecl-typed. ['] ecl-but. ok-with nip ;
: ecl-lhs-fail ( lhs prev -- )
  swap 2 ['] ecl-sides. lf-tac-detail-n lfa-e-calc-lhs lf-tac-stop ;
: ecl-hinted. ( term -- outcome ) lf-tac-indented. ['] lf-tac-diagnostics. ok-and ;
: ecl-detail ( code -- xt )
  lfa-e-calc-trans = if ['] ecl-hinted. else ['] lf-tac-indented. then ;
: ecl-trans-fail ( term code -- ) tuck ecl-detail lf-tac-detail lf-tac-stop ;

\ ---- The elaborator's words (lf-elab-calc-steps runs in its
\ configuration), a failure stopping the step.
: ecl-type ( node -- type ) lf-elab-type lf-tac-elab-must ;
: ecl-ensuring ( node type -- proof ) lf-elab-ensuring lf-tac-elab-must ;
: ecl-defaults ( -- ) lf-elab-synthesize-default lf-tac-elab-must ;

\ ---- annotateFirstHoleWithType: the leaf the left operands lead to,
\ when the term is an operator's and the leaf is _ (a step _ alone: 99).
: ecl-op? ( node -- flag ) syn-kind@ syn-k-binop syn-k-binrel syn-k-rightact one-of3? ;
: ecl-first-leaf ( node -- leaf ) begin dup ecl-op? while syn-b@ repeat ;
: ecl-plain-hole? ( node -- flag ) syn-kind@ syn-k-hole = ;
: ecl-annotate ( node type -- node )
  over ecl-plain-hole? if lf-tac-unported then
  over ecl-first-leaf dup ecl-plain-hole? if syn-ascribe! else 2drop then ;

\ ---- elabCalcSteps: a frame of the step, the chain so far and the
\ right side before.
begin-structure /ecs
  field: ecs-i  field: ecs-result  field: ecs-rtype  field: ecs-prev
end-structure
/ecs context-slab: ecl-step-frames
: ecs ( -- addr ) ecl-step-frames slab-last ;
: ecl-node ( k -- node ) ecs ecs-i @ swap lf-tac-arg ;
: ecl-proved ( type k -- proof ) 2* 1+ ecl-node swap ecl-ensuring ;
\ T's type, its sides; the first step's T as written, a later one's
\ with its first hole ascribed the type of the right side before it.
: ecl-sides ( type -- type lhs rhs )
  dup lf-calc-rel? 0= if ecl-no-relation then dup lf-meta-args2 ;
: ecl-term ( k -- node ) 2* ecl-node ;
: ecl-later ( k -- node ) ecl-term ecs ecs-prev @ lf-infer! ecl-annotate ;
: ecl-first ( -- )
  0 ecl-term ecl-type ecl-sides nip ecs ecs-prev ! dup ecs ecs-rtype !
  0 ecl-proved ecs ecs-result ! ;
: ecl-lhs ( lhs -- )
  ecs ecs-prev @ 2dup lf-meta-defeq-guarded lf-must if 2drop else ecl-lhs-fail then ;
: ecl-chain ( proof type -- )
  ecl-defaults ecs ecs-result @ ecs ecs-rtype @ 2swap lf-calc-trans
  0= if ecl-trans-fail then ecs ecs-rtype ! ecs ecs-result ! ;
\ Step k's T, its left side the right side before, which its own right
\ side then becomes (nothing reads it before the next step); its proof.
: ecl-sided ( k -- k type )
  dup ecl-later ecl-type ecl-sides swap ecl-lhs ecs ecs-prev ! ;
: ecl-next ( k -- ) ecl-sided tuck swap ecl-proved swap ecl-chain ;
: ecl-steps ( i n -- val type )
  swap ecs ecs-i ! ecl-first 1 ?do i ecl-next loop ecl-defaults
  ecs ecs-result @ ecs ecs-rtype @ ;
: ecl-framed ( i n -- val type ) ecl-step-frames ['] ecl-steps lf-with-record ;
: lf-elab-calc-steps ( i n -- val type ) ['] ecl-framed lf-elab-configured ;

base !   \ the BASE this file was loaded with
