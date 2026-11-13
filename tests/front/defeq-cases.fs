\ LeanForth's side of tests/front/check_defeq.py (plan FE1c): the
\ variables of tests/front/whnf-cases.fs and, made after them in this
\ order, the metavariables ?r : Nat, ?t : Nat -> Nat and ?y : Nat -> Nat
\ -> Nat, the free variables j : Nat, e c : a = b, u : Nat -> Nat, v w :
\ PUnit.{1}, i : a = b -> Nat, the synthetic opaque ?o : Nat, the free
\ variable d : Nat -> PUnit.{1} and the level metavariable ?lu, as
\ tests/front/defeq-cases.lean makes them (names unique without case:
\ Gforth's are case-insensitive). One line per case: "true", then both
\ sides with their metavariables instantiated, or "false", or "stuck"
\ (the stuck signal, lf-meta-stuck), or "unsupported" or the outcome's
\ name. Each case runs under a mark that is rolled back after it, so no
\ case sees another's assignments; eq-dq uses the elaborator's
\ configuration (foApprox, ctxApprox: Lean's run_meta), meta-dq Meta's
\ default, deep-dq the elaborator's one depth deeper (withNewMCtxDepth),
\ red-dq, inst-dq and impl-dq reducible, instances and implicit
\ transparency; stuck-dq and dstuck-dq the elaborator's with
\ isDefEqStuckEx, at this depth and one deeper; guard-dq
\ lf-meta-defeq-guarded (isDefEqGuarded) with isDefEqStuckEx.
\ Test support only: printing recurses on the host stack, which the
\ small cases allow.

\ Every module first: a context member declared after menv-load (in
\ whnf-cases.fs) would move the context under the loaded slice.
require ../../src/front/defeq.fs
require ../../src/front/defeq-delta.fs
require ./whnf-cases.fs
require ./depth.fs

\ Literals print their value.
action-of .t constant .t-plain
:noname ( t -- )
  dup lf-term-tag@ lf-tag-lit = if lf-lit-cell 0 u.r exit then .t-plain execute ; is .t
: nlit ( u -- t ) lf-hterm-cell must drop ;

nat nat tpi constant nat>nat
nat mv-natural lf-mvar-new made constant ?r  ?r char r named
nat>nat mv-natural lf-mvar-new made constant ?t  ?t char t named
nat nat>nat tpi mv-natural lf-mvar-new made constant ?y  ?y char y named
nat char j local constant fj
: eqab ( -- t ) lv1 1 s" Eq" cn nat app fa app fb app ;
eqab char e local constant fe
eqab char c local constant fc
nat>nat char u local constant fu
: punit ( -- t ) lv1 1 s" PUnit" cn ;
punit char v local constant fv
punit char w local constant fw
eqab nat tpi char i local constant fi
nat mv-opaque lf-mvar-new made constant ?o  ?o char o named
nat punit tpi char d local constant fd
lf-level-mvar-new made constant lvu
lvu lf-level-succ must constant lvu1

: defeq-show ( t s flag outcome -- )
  dup lf-meta-stuck = if 2drop 2drop ." stuck" cr exit then
  dup ok? 0= if nip nip nip .outcome cr exit then drop
  if ." true " swap lf-instantiate-mvars drop .t space lf-instantiate-mvars drop .t
  else 2drop ." false" then cr ;
variable dq-xt  ' lf-meta-defeq dq-xt !
: dq-case ( t s -- )
  lf-mctx-mark drop >r 2dup dq-xt @ execute defeq-show r> lf-mctx-rollback drop
  lf-tr-default lf-defeq-mode! ;
: eq-dq ( t s -- ) lf-defeq-elab lf-defeq-flags! dq-case ;
: meta-dq ( t s -- ) lf-meta-default lf-defeq-flags! dq-case ;
: deep-dq ( t s -- ) lf-defeq-elab lf-defeq-flags! false lf-mctx-depth{ drop >r dq-case
  r> }lf-mctx-depth drop ;
: red-dq ( t s -- ) lf-tr-reducible lf-defeq-mode! eq-dq ;
: inst-dq ( t s -- ) lf-tr-instances lf-defeq-mode! eq-dq ;
: impl-dq ( t s -- ) lf-tr-implicit lf-defeq-mode! eq-dq ;
: stuck-flags ( -- ) lf-defeq-elab lf-defeq-stuck or lf-defeq-flags! ;
: stuck-dq ( t s -- ) stuck-flags dq-case ;
: dstuck-dq ( t s -- ) stuck-flags false lf-mctx-depth{ drop >r dq-case r> }lf-mctx-depth drop ;
: guard-dq ( t s -- )
  ['] lf-meta-defeq-guarded dq-xt ! stuck-dq ['] lf-meta-defeq dq-xt ! ;
