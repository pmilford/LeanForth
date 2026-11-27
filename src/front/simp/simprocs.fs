\ Simp's simprocs (simp group 4, pass 2; plan .claude/work/briefs/
\ simp-group-4-architect.md sections 1 and 3): Lean 4.35.0's default
\ simprocs, each found by its record's name (front/simp-set-data.fs's
\ simp-proc-name), and SimprocEntry.try (src/lean/Lean/Meta/Tactic/Simp/
\ Simproc.lean:195).
\ - lf-simproc: ( xt x n pre? dsimproc? "decl" "name" -- ): the port of
\   Lean's simproc name (pre? its arrow, dsimproc? builtin_dsimproc: a
\   result with no proof): xt ( e x -- e' h step ) run on a term whose
\   head is the constant decl with n arguments, which every ported
\   simproc tests first (isAppOfArity, let_expr: a key's root may be
\   another head, GT.gt's keys are LT.lt's), any other term continue; x
\   is the port's own (an operation's number).
\ - lf-simproc-try ( e p extra -- e' h step ): simproc record p on e
\   less its last extra arguments, which are put back after
\   (Step.addExtraArgs, Types.lean:928): the port's step, or its
\   family's guard's; a port whose phase or kind is not the record's is
\   unsupported (data of another Lean).
\ - A port's step is simp/types.fs's; its continue is Lean's .continue
\   none (no builtin simproc of Lean 4.35.0 answers .continue (some r):
\   BuiltinSimprocs/*.lean), so simprocCore tries the next candidate.
\ - lf-simp-eval-prop ( p flag -- e h step ): evalPropStep (BuiltinSimprocs/
\   Util.lean:19): True or False, done, by eq_true_of_decide or
\   eq_false_of_decide p d (Eq.refl b), d mkDecide p's instance.
\ - Guards, for a simproc whose action is not ported: unsupported exactly
\   where Lean's simproc may fire, else continue, never a step of its own.
\   Every simproc of Init's default set has a row by its name (review of
\   simp group 4, B1): a port (simprocs/core.fs, simprocs/nat.fs), a
\   named guard below (reduceCtorEq, Core.lean:88, sp-ctor-guard; Nat's
\   Diff family, Nat.lean:268-365, sp-diff-guard; crude ports for Char's
\   two digit simprocs and BitVec's two shift-shift and two
\   shift-by-literal simprocs, which fire on any operand), or a row of
\   simprocs/guards.fs's table, each citing Lean's declaration: sp-lit-
\   rows (sp-lit-guard) for a simproc whose body answers .continue unless
\   every explicit operand passes its fromExpr? (getNatValue?,
\   getOfNatValue?, getIntValue?, getFinValue?, getBitVecValue?,
\   getCharValue?, getStringValue?; Meta/LitValues.lean): unsupported
\   when every explicit argument that is no proof has a literal's form
\   (sp-may-lit?: a raw literal, a metavariable or annotation, or a
\   literal's head constant), else continue; sp-crude- rows (sp-crude)
\   unsupported whenever its keys match. A name with no row (another
\   Lean's simproc) is unsupported whenever its keys match.
\ Throws as meta-must.fs's words do. Untrusted: a simproc only proposes
\ a step whose proof the kernel checks. State: none of its own; the
\ port table sp-ports is laid while loading, before any context is made
\ (lib/context.fs's context-sealed?), and only read after.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/name-table.fs
require ../../lib/context.fs
require ../../lib/texts.fs
require ../../core/terms.fs
require ../../core/input.fs
require ../../core/nat-ops.fs
require ../simp-set-data.fs
require ../fun-info.fs
require ../nat-offset.fs
require ./types.fs

\ ---- The ports, by Lean's name: an entry's data, then its head's name.
begin-structure /sp
  field: sp-xt   field: sp-x   field: sp-n   field: sp-pre   field: sp-dsimp
end-structure
name-table: sp-ports
: sp-laid ( xt x n pre? dsimproc? -- )
  2>r rot , swap , , 2r> swap , , ;
\ Rows are laid only while the modules load (review B3), as the tactic
\ registry's (tactic-run.fs's lfr-open): runs read them in place.
: sp-open ( -- ) context-sealed? abort" simprocs: a port after context-new" ;
: sp-row ( xt x n pre? dsimproc? c-addr u "name" -- )
  sp-open parse-name sp-ports name-entry 2>r sp-laid 2r> counted, ;
: lf-simproc: ( xt x n pre? dsimproc? "decl" "name" -- ) parse-name sp-row ;
\ A guard's row: any head (n -1, no decl), its xt ( e x -- e h step ).
: sp-guard-row ( xt pre? dsimproc? "name" -- ) 2>r 0 -1 2r> 0 0 sp-row ;
: sp-data ( entry -- addr ) name-entry-data ;
: sp-decl ( entry -- c-addr u ) sp-data /sp + count ;
\ The record's phase and kind are the port's.
: sp-phase? ( p entry -- flag ) sp-data sp-pre @ swap simp-proc-post? = 0= ;
: sp-kind? ( p entry -- flag ) sp-data sp-dsimp @ swap simp-proc-dsimproc? = ;
: sp-fitting ( p entry -- entry )
  2dup sp-phase? >r tuck sp-kind? r> and 0= if lf-unported then ;
: sp-any? ( entry -- flag ) sp-data sp-n @ 0< ;
: sp-shaped? ( e entry -- flag )
  dup sp-any? if 2drop true exit then dup sp-data sp-n @ swap sp-decl lf-meta-app-of? ;
: sp-call ( e entry -- e' h step )
  2dup sp-shaped? 0= if drop lf-simp-pass exit then
  sp-data dup sp-x @ swap sp-xt @ execute ;

\ ---- Literal forms (the families' fromExpr? read no other heads).
texts-begin texts+ OfNat.ofNat Neg.neg Char.ofNat Char.ofNatAux BitVec.ofNat
texts+ BitVec.ofNatLT BitVec.ofFin Int.ofNat Int.negSucc Fin.mk List.cons List.nil
texts+ String.mk Nat.zero Nat.succ
texts-end constant sp-lit-heads
lf-tag-lit lf-tag-str lf-tag-mvar lf-tag-annotation 4 lf-tags constant sp-lit-tags
: sp-lit-head? ( a -- flag )
  lf-meta-head dup lf-mvar? swap ['] lf-meta-const-named? sp-lit-heads texts-find 0<> or ;
: sp-may-lit? ( a -- flag ) dup lf-term-tag@ sp-lit-tags lf-tag-in? swap sp-lit-head? or ;

\ ---- The literal families' guard: argument i of e, of the m whose
\ binder kinds getFunInfoNArgs gives (fun-info.fs), checked when it is
\ explicit and no proof (beyond m: checked).
: sp-explicit? ( m i -- flag )
  tuck > if lf-meta-param 0= swap lf-binder-default = and else drop true then ;
: sp-arg-lit? ( e m i -- e m flag )
  2dup sp-explicit? if 2 pick swap lf-meta-app-arg sp-may-lit? else drop true then ;
: sp-lits? ( e -- flag )
  dup lf-meta-head over lf-meta-args# lf-meta-fun-info lf-must
  over lf-meta-args# ['] sp-arg-lit? all? nip nip ;
: sp-lit-guard ( e -- e h step ) dup sp-lits? if lf-unported then lf-simp-pass ;
: sp-crude ( e -- e h step ) lf-unported lf-simp-pass ;
: sp-lit-port ( e x -- e h step ) drop sp-lit-guard ;
: sp-crude-port ( e x -- e h step ) drop sp-crude ;
\ The table's rows (simprocs/guards.fs), by phase and kind: post
\ dsimprocs, post simprocs, a pre dsimproc.
: sp-lit-d: ( "name" -- ) ['] sp-lit-port false true sp-guard-row ;
: sp-lit-s: ( "name" -- ) ['] sp-lit-port false false sp-guard-row ;
: sp-lit-d-pre: ( "name" -- ) ['] sp-lit-port true true sp-guard-row ;
: sp-crude-d: ( "name" -- ) ['] sp-crude-port false true sp-guard-row ;

\ ---- SimprocEntry.try.
: sp-entry ( p -- entry | 0 ) simp-proc-name sp-ports name-table-find ;
: sp-apply ( e p -- e' h step )
  dup sp-entry ?dup if sp-fitting sp-call else drop sp-crude then ;
: sp-run ( e p extra -- e extra e0' h step ) swap >r 2dup lf-term-fns r> sp-apply ;
: sp-extra ( e extra e0' h step -- e' h step )
  dup lf-simp-continue = if 2drop 2drop lf-simp-pass exit then >r lf-simp-extra-args r> ;
: lf-simproc-try ( e p extra -- e' h step ) sp-run sp-extra ;

\ ---- evalPropStep (Util.lean:19).
: sp-decided ( flag -- c-addr u )
  if s" eq_true_of_decide" else s" eq_false_of_decide" then ;
: sp-bool ( flag -- b ) if s" Bool.true" else s" Bool.false" then lf-mk-const0 ;
: sp-prop ( flag -- c ) if s" True" else s" False" then lf-mk-const0 ;
: sp-eval-proof ( p flag -- h )
  >r r@ sp-decided lf-mk-const0 swap dup lf-mk-decide lf-term-second@
  r> sp-bool lf-mk-eq-refl 3 lf-mk-app-n ;
: lf-simp-eval-prop ( p flag -- e h step ) dup sp-prop -rot sp-eval-proof lf-simp-done ;

\ ---- Nat's Diff family (Nat.lean:268-365): both sides NatOffsets
\ (NatOffset.fromExpr?, 168: a literal, or asOffset's addition of a
\ literal, HAdd.hAdd, Add.add, Nat.add, or Nat.succ) may fire; else
\ continue.
: sp-addition? ( a -- flag )
  dup 6 s" HAdd.hAdd" lf-meta-app-of? over 4 s" Add.add" lf-meta-app-of? or
  swap 2 s" Nat.add" lf-meta-app-of? or ;
: sp-add-of-lit? ( a -- flag )
  dup sp-addition? if lf-term-second@ sp-may-lit? else drop false then ;
: sp-offset? ( a -- flag )
  dup sp-may-lit? swap sp-add-of-lit? or ;   \ (Nat.succ: a literal's head)
: sp-diff-guard ( e x -- e h step )
  drop dup lf-meta-args2 sp-offset? swap sp-offset? and if lf-unported then lf-simp-pass ;

\ ---- reduceCtorEq (Core.lean:88): Eq _ lhs rhs with both sides
\ constructor applications (constructorApp'?, CtorRecognizer.lean:97:
\ isOffset?, then the head with litToCtor, then the head of whnf, at
\ reducible and instances transparency) of different constructors gives
\ False: unsupported; the same constructor, or a side with none:
\ continue. A literal other than Nat's (litToCtor's Int, Fin and others)
\ is a constructor not known here, unsupported beside any other.
-1 constant sp-unknown   -2 constant sp-succ   -3 constant sp-zero
: sp-nat-ctor ( lit -- c ) 0 lf-lit-u> if sp-succ else sp-zero then ;
: sp-named-ctor ( name -- c )
  dup lf-nat-succ-name? if drop sp-succ exit then
  dup lf-nat-zero-name? if drop sp-zero then ;
\ (A term's constants are declared: lf-menv-find refuses any other.)
: sp-ctor-name ( name -- c )
  dup lf-menv-find lf-must lf-menv-kind lf-kind-constructor =
  if sp-named-ctor else drop 0 then ;
: sp-head-ctor ( a -- c )
  dup lf-lit-leaf? if sp-nat-ctor exit then
  dup lf-meta-head-name if sp-ctor-name ?dup if nip exit then then
  sp-may-lit? sp-unknown and ;
: sp-offset ( a -- a c true | a false )
  dup lf-meta-offset lf-must if nip 0<> sp-succ and true else 2drop false then ;
: sp-whnf-ctor ( a -- c ) ['] lf-whnf! lf-tr-instances lf-meta-at sp-head-ctor ;
: sp-ctor-of ( a -- c )
  sp-offset if nip exit then dup sp-head-ctor ?dup if nip exit then sp-whnf-ctor ;
: sp-ctors-fire? ( c1 c2 -- flag )
  2dup <> over sp-unknown = or >r 0<> swap 0<> and r> and ;
: sp-ctor-guard ( e x -- e h step )
  drop dup lf-meta-args2 sp-ctor-of swap sp-ctor-of sp-ctors-fire? if lf-unported then
  lf-simp-pass ;

' sp-ctor-guard 0 3 false false lf-simproc: Eq reduceCtorEq
' sp-diff-guard 0 3 false false lf-simproc: Eq Nat.reduceEqDiff
' sp-diff-guard 0 4 false false lf-simproc: BEq.beq Nat.reduceBeqDiff
' sp-diff-guard 0 4 false false lf-simproc: bne Nat.reduceBneDiff
' sp-diff-guard 0 4 false false lf-simproc: LE.le Nat.reduceLeDiff
' sp-diff-guard 0 6 false false lf-simproc: HSub.hSub Nat.reduceSubDiff
' sp-crude-port 0 3 false false lf-simproc: Eq Char.Nat.reduceDigitCharEq
' sp-crude-port 0 3 false false lf-simproc: Eq Char.Nat.reduceEqDigitChar
\ BitVec.lean:447-465 (reduceShiftShift: (x <<< i) <<< j to x <<< (i + j)
\ for any x) and :94-98, :221-230 (reduceShiftWithBitVecLit: x <<< i, i a
\ literal, for any x).
' sp-crude-port 0 6 false false
lf-simproc: HShiftLeft.hShiftLeft BitVec.reduceShiftLeftShiftLeft
' sp-crude-port 0 6 false false
lf-simproc: HShiftRight.hShiftRight BitVec.reduceShiftRightShiftRight
' sp-crude-port 0 6 false true
lf-simproc: HShiftLeft.hShiftLeft BitVec.reduceHShiftLeft'
' sp-crude-port 0 6 false true
lf-simproc: HShiftRight.hShiftRight BitVec.reduceHShiftRight'

base !   \ the BASE this file was loaded with
