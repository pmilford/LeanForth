\ Nat values and offsets of the front end's unifier (plan FE1c; ADR 0021
\ D6): ports of Lean 4.35.0's evalNat, isOffset? and mkOffset
\ (Lean/Meta/Offset.lean) with mkNatLit and mkNatAdd (Lean/Expr.lean).
\ - lf-meta-eval-nat ( e -- n flag outcome ): evalNat, left to right: a
\   literal, Nat.zero, OfNat.ofNat _ n (instOfNatNat _), Nat.succ a,
\   Nat.add a b, Add.add _ instAddNat a b and HAdd.hAdd _ _ _ (instHAdd _
\   instAddNat) a b (the instances matched by shape, as Lean's
\   Structural tests do); anything else has no value (flag false).
\ - lf-meta-offset ( e -- s k flag outcome ): isOffset?: e is s + k, k
\   counted through Nat.succ and additions whose second argument has a
\   value (Nat.add, and Add.add and HAdd.hAdd with Nat's own instance);
\   flag false when e is no addition or successor at all.
\ - lf-meta-mk-offset ( e k -- e' outcome ): mkOffset: e for k = 0, the
\   literal k when e's value is 0, else e + k (mkNatAdd: HAdd.hAdd.{0,0,0}
\   Nat Nat Nat (instHAdd.{0} Nat instAddNat) e k); a literal k is
\   OfNat.ofNat.{0} Nat k (instOfNatNat k) (lf-meta-nat-lit, mkNatLit).
\ - lf-meta-nat ( -- term outcome ): the constant Nat.
\ - lf-meta-ctor-if-lit ( e -- e' outcome ): toCtorIfLit (WHNF.lean:23)
\   for a natural literal: 0 is Nat.zero, v > 0 Nat.succ of the raw
\   literal v - 1 (unsupported beyond a cell); any other term is itself
\   (a string literal is front/whnf.fs's).
\ - lf-meta-cleanup-offset ( e -- e' outcome ): cleanupNatOffsetMajor
\   (WHNF.lean:216): for isOffset? e = (s, k), s when k = 0, Nat.succ s
\   when k = 1, else Nat.succ (s + (k - 1)) (mkNatAdd, mkNatLit); e when
\   it is no offset. Both are reduceRec's clean-up of a major premise.
\ The shapes it matches use term-eqv.fs's lf-meta-app-of? and
\ lf-meta-nth-arg.
\ Values are unsigned cells (below 2^64 on a 64-bit host), added and
\ compared unsigned. Never a guess: unsupported for a literal, a sum or
\ an offset beyond a cell, an operation Lean's evalNat also evaluates that is not
\ ported (subtraction, multiplication, division, modulo and power:
\ Nat.sub, Sub.sub, HSub.hSub and the others, by name and number of
\ arguments), an instance of Add.add or HAdd.hAdd in an offset that is
\ not Nat's own node for node (Lean then asks isDefEq at instances
\ transparency). A constant's name is made in the context's name store
\ when it has none yet, as Lean's mkNatLit and mkNatAdd name constants
\ without asking the environment (in a fed context above the input's
\ marks; a text's run has its own names, S1 merge B).
\ Outcomes: ok; unsupported as above; full when a store or the heap has
\ no room; invalid for a level store whose first level is not zero.
\ Untrusted. State: the record no (the value so far and the
\ universe-argument pairs of a constant being made) and the slab
\ no-stack (the terms still to evaluate), in the checker context (ADR
\ 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/texts.fs
require ../core/terms.fs
require ../core/names.fs
require ../core/compact-names.fs
require ../core/levels.fs
require ../core/literals.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/generation-handles.fs
require ../core/mvar-leaves.fs
require ./meta-spine.fs
require ./term-eqv.fs

begin-structure /no
  field: no-acc           \ evalNat: the value so far
  field: no-e             \ isOffset?: the term not yet taken apart
  field: no-off           \ and the offset so far
  field: no-out           \ isOffset?: the outcome that ended a layer
  field: no-k             \ a constant being made: its number of universe arguments
  6 cells +field no-pairs \ and its (level, identity) pairs, up to three
end-structure
/no context-record: no
1 cells context-slab: no-stack

\ ---- Constants by name, their universe arguments all zero.
: no-split ( c-addr u -- c-addr i rest u' )
  2dup s" ." search if 2>r r@ - 2r> 1 /string else 2drop 0 -1 then ;
: no-seek ( prefix c-addr i -- name outcome )
  lf-name-str room-result ;
: no-name ( c-addr u -- name outcome )
  0 -rot begin no-split 2>r no-seek ok-then? 0= if 2r> 2drop no-result exit then
  2r> dup 0< until 2drop outcome-ok ;
: no-pair ( i -- addr ) 2* cells no no-pairs + ;
: no-zero? ( -- flag ) 0 lf-level-tag@ lf-level-tag-zero = ;
: no-zeros ( k -- outcome )
  no-zero? 0= if drop outcome-invalid exit then
  0 ?do 0 lf-level-identity 0=
  if unloop outcome-invalid exit then 0 i no-pair 2! loop outcome-ok ;
: no-ref ( name -- term outcome )
  lf-name-generation @ 0 no-pair no no-k @ lf-cref-new 0= if -1 outcome-full exit then
  lf-cterm-new lf-made-term ;
: no-const ( c-addr u k -- term outcome )
  no no-k ! no-name ok-then? 0= if no-result exit then
  no no-k @ no-zeros dup ok? if drop no-ref else nip no-result then ;
: no-app ( f a outcome -- t outcome )
  dup ok? 0= if nip nip no-result exit then
  drop lf-term-app room-result ;
: lf-meta-nat ( -- term outcome ) s" Nat" 0 no-const ;
: no-lit ( u -- term outcome ) lf-hterm-cell lf-made-term ;

\ ---- mkNatLit and mkNatAdd.
: no-app-nat ( f outcome -- t outcome )
  ok-then? if lf-meta-nat no-app else no-result then ;
: no-ofnat ( -- f outcome ) s" OfNat.ofNat" 1 no-const no-app-nat ;
: no-inst-lit ( lit -- t outcome )
  s" instOfNatNat" 0 no-const ok-then? if swap outcome-ok no-app else nip no-result then ;
: lf-meta-nat-lit ( u -- term outcome )
  no-lit ok-then? 0= if no-result exit then
  no-ofnat ok-then? 0= if nip no-result exit then
  over outcome-ok no-app ok-then? 0= if nip no-result exit then swap no-inst-lit no-app ;
: no-inst-hadd ( -- t outcome )
  s" instHAdd" 1 no-const no-app-nat ok-then? 0= if no-result exit then
  s" instAddNat" 0 no-const no-app ;
: no-hadd3 ( -- f outcome ) s" HAdd.hAdd" 3 no-const no-app-nat no-app-nat no-app-nat ;
: no-hadd-inst ( -- f outcome )
  no-hadd3 ok-then? 0= if no-result exit then no-inst-hadd no-app ;
: no-add ( a b -- t outcome )
  swap no-hadd-inst ok-then? 0= if nip nip no-result exit then
  swap outcome-ok no-app ok-then? 0= if nip no-result exit then swap outcome-ok no-app ;

\ ---- Shapes (Lean's match_expr), by term-eqv.fs's lf-meta-app-of?.
: no-inst-addnat? ( t -- flag ) 0 s" instAddNat" lf-meta-app-of? ;
: no-inst-hadd? ( t -- flag )
  dup 2 s" instHAdd" lf-meta-app-of?
  if 1 2 lf-meta-nth-arg no-inst-addnat? else drop false then ;
: no-inst-ofnat? ( t -- flag ) 1 s" instOfNatNat" lf-meta-app-of? ;
\ evalNat's other operations, by their number of arguments (Lean's
\ match_expr arms of Nat.sub, Sub.sub, HSub.hSub and the like): tables of
\ lib/texts.fs, one per count (review F10 of 2026-11-18).
texts-begin texts+ Nat.sub Nat.mul Nat.div Nat.mod Nat.pow
texts-end constant no-ops2
texts-begin texts+ Sub.sub Mul.mul Div.div Mod.mod NatPow.pow
texts-end constant no-ops4
texts-begin texts+ Pow.pow
texts-end constant no-ops5
texts-begin texts+ HSub.hSub HMul.hMul HDiv.hDiv HMod.hMod HPow.hPow
texts-end constant no-ops6
: no-ops ( n -- table | 0 )
  case 2 of no-ops2 endof 4 of no-ops4 endof 5 of no-ops5 endof 6 of no-ops6 endof
    0 swap endcase ;
: no-unported? ( t -- flag )
  lf-meta-head-args no-ops ?dup if ['] lf-meta-const-named? swap texts-find 0<>
  else drop false then ;
\ The last two arguments of an addition.
: no-sides ( e -- a b ) dup lf-term-first@ lf-term-second@ swap lf-term-second@ ;

\ ---- evalNat: the terms to evaluate on no-stack, the first argument on
\ top; each value adds to no-acc. A step's code: 0 go on, 1 no value.
: no-push ( t -- outcome ) no-stack slab-push ;
: no-pop ( -- t ) no-stack slab-pop ;
: no-add-acc ( u -- outcome )
  no no-acc @ 2dup + tuck u> if 2drop outcome-unsupported exit then
  nip no no-acc ! outcome-ok ;
: no-push-arg ( t i n -- outcome ) lf-meta-nth-arg no-push ;
\ An addition's two summands, the first on top.
: no-push-sides ( t -- code outcome )
  no-sides swap >r no-push dup ok? if drop r> no-push else r> drop then 0 swap ;
: no-lit-step ( lit -- code outcome )
  dup lf-lit-small? if lf-lit-cell no-add-acc 0 swap
  else drop 0 outcome-unsupported then ;
: no-succ-step ( t -- code outcome )
  0 1 no-push-arg dup ok? if drop 1 no-add-acc then 0 swap ;
: no-ofnat-step ( t -- code outcome )
  dup 2 3 lf-meta-nth-arg no-inst-ofnat?
  if 1 3 no-push-arg 0 swap else drop 1 outcome-ok then ;
: no-addc-step ( t -- code outcome )
  dup 1 4 lf-meta-nth-arg no-inst-addnat? if no-push-sides else drop 1 outcome-ok then ;
: no-hadd-step ( t -- code outcome )
  dup 3 6 lf-meta-nth-arg no-inst-hadd? if no-push-sides else drop 1 outcome-ok then ;
\ An operation not ported whose last argument or the one before holds a
\ free variable has no value either: Lean's evalNat (Offset.lean:28-60)
\ fails at a free variable or an instance guard it reaches (branch
\ s2-tactics: n * 0); it skips type arguments, so this assumes the free
\ variable is not only in one of an operand's (as in S2's inputs).
: no-fvar-operand? ( t -- flag )
  dup lf-term-second@ lf-meta-has-fvar? swap lf-term-first@ lf-term-second@
    lf-meta-has-fvar?
  or ;
: no-unported-step ( t -- code outcome )
  no-fvar-operand? if 1 outcome-ok else 0 outcome-unsupported then ;
: no-sum-step ( t -- code outcome )
  dup 4 s" Add.add" lf-meta-app-of? if no-addc-step exit then
  dup 6 s" HAdd.hAdd" lf-meta-app-of? if no-hadd-step exit then
  dup no-unported? if no-unported-step else drop 1 outcome-ok then ;
: no-app-step ( t -- code outcome )
  dup lf-meta-succ? if no-succ-step exit then
  dup 2 s" Nat.add" lf-meta-app-of? if no-push-sides exit then
  dup 3 s" OfNat.ofNat" lf-meta-app-of? if no-ofnat-step else no-sum-step then ;
: no-step ( t -- code outcome )
  dup lf-term-tag@ lf-tag-lit = if no-lit-step exit then
  dup 0 s" Nat.zero" lf-meta-app-of? if drop 0 outcome-ok exit then
  dup lf-meta-app? if no-app-step else drop 1 outcome-ok then ;
: no-none ( outcome -- 0 false outcome ) 0 swap false swap ;
: no-run ( -- n flag outcome )
  begin no-stack slab-count 0> while no-pop no-step ok-then? 0= if no-none exit then
    if outcome-ok no-none exit then repeat no no-acc @ true outcome-ok ;
: lf-meta-eval-nat ( e -- n flag outcome )
  0 no no-acc ! no-stack slab-clear no-push dup ok? if drop no-run else no-none then ;

\ ---- isOffset?: one layer of no-e at a time, the offset in no-off. A
\ layer's code: none, Nat.succ a, an addition a + b, an addition whose
\ instance is not Nat's node for node (Lean asks isDefEq: unsupported),
\ or a failure, its outcome in no-out.
0 constant no-plain  1 constant no-succ-at  2 constant no-sum-at
3 constant no-foreign  4 constant no-failed
: no-want ( n -- inst outcome ) 4 = if s" instAddNat" 0 no-const else no-inst-hadd then ;
: no-inst-arg ( e n -- arg ) dup 3 - swap lf-meta-nth-arg ;
: no-inst-ok? ( e n -- flag outcome )
  tuck no-inst-arg swap no-want ok-then? if lf-meta-eqv else nip false swap then ;
: no-fail ( outcome -- 0 0 code ) no no-out ! 0 0 no-failed ;
: no-inst-layer ( e n -- a b code )
  over swap no-inst-ok? dup ok? 0= if nip nip no-fail exit then drop
  if no-sides no-sum-at else drop 0 0 no-foreign then ;
: no-layer ( e -- a b code )
  dup lf-meta-succ? if 0 1 lf-meta-nth-arg 0 no-succ-at exit then
  dup 2 s" Nat.add" lf-meta-app-of? if no-sides no-sum-at exit then
  dup 4 s" Add.add" lf-meta-app-of? if 4 no-inst-layer exit then
  dup 6 s" HAdd.hAdd" lf-meta-app-of? if 6 no-inst-layer else 0 no-plain then ;
\ v more for the offset: false when it passes a cell.
: no-off+ ( v -- flag )
  no no-off @ over + tuck u> if drop false else no no-off ! true then ;
: no-go ( a -- true outcome ) no no-e ! true outcome-ok ;
\ Nat.succ a: one more, unsupported past a cell.
: no-succ-layer ( a -- go? outcome )
  1 no-off+ if no-go else drop false outcome-unsupported then ;
\ An addition a + b: b's value adds to the offset and a goes on; with
\ none, the layer is no offset.
: no-add-layer ( a b -- go? outcome )
  lf-meta-eval-nat ok-then2? 0= if nip false swap exit then
  0= if 2drop false outcome-ok exit then
  no-off+ if no-go else drop false outcome-unsupported then ;
: no-end-outcome ( code -- outcome )
  no-foreign = if outcome-unsupported else no no-out @ then ;
: no-off-end ( a b code -- go? outcome )
  nip nip dup no-plain = if drop false outcome-ok exit then no-end-outcome false swap ;
: no-off-step ( -- go? outcome )
  no no-e @ no-layer dup no-succ-at = if 2drop no-succ-layer exit then
  dup no-sum-at = if drop no-add-layer else no-off-end then ;
: no-off-loop ( -- outcome )
  begin no-off-step ok-then? 0= if exit then 0= until outcome-ok ;
: lf-meta-offset ( e -- s k flag outcome )
  no no-e ! 0 no no-off ! no-off-step dup ok? if over if drop no-off-loop then then
  no no-e @ no no-off @ 2swap ;

\ ---- mkOffset.
: lf-meta-mk-offset ( e k -- e' outcome )
  dup 0= if drop outcome-ok exit then
  over lf-meta-eval-nat ok-then2? 0= if nip nip no-result exit then
  swap 0= and if nip lf-meta-nat-lit exit then
  lf-meta-nat-lit ok-then? if no-add else nip no-result then ;

\ ---- reduceRec's clean-up of a major premise (WHNF.lean:247-248, plan S2
\ merge B): toCtorIfLit (23) and cleanupNatOffsetMajor (216).
\ mkNatSucc: Nat.succ e.
: no-succ ( e -- t outcome )
  s" Nat.succ" 0 no-const ok-then? if swap outcome-ok no-app else nip no-result then ;
: no-lit-ctor ( lit -- e outcome )
  dup lf-lit-small? 0= if drop outcome-unsupported no-result exit then
  lf-lit-cell ?dup 0= if s" Nat.zero" 0 no-const exit then
  1- no-lit ok-then? if no-succ else no-result then ;
: lf-meta-ctor-if-lit ( e -- e' outcome )
  dup lf-lit-leaf? if no-lit-ctor else outcome-ok then ;
: no-plus ( s k -- t outcome )
  lf-meta-nat-lit ok-then? if no-add else nip no-result then ;
: no-cleanup ( s k -- e' outcome )
  ?dup 0= if outcome-ok exit then
  1- ?dup if no-plus ok-then? 0= if no-result exit then then no-succ ;
\ isOffset? none leaves (e, 0) (lf-meta-offset), which no-cleanup keeps.
: lf-meta-cleanup-offset ( e -- e' outcome )
  lf-meta-offset ok-then3? if drop no-cleanup else no-result then ;

base !   \ the BASE this file was loaded with
