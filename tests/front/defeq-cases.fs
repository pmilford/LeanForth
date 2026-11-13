\ LeanForth's side of tests/front/check_defeq.py (plan FE1c): the
\ variables of tests/front/whnf-cases.fs and, made after them in this
\ order, the metavariables ?r : Nat, ?t : Nat -> Nat and ?y : Nat -> Nat
\ -> Nat, the free variables j : Nat, e c : a = b, u : Nat -> Nat, v w :
\ PUnit.{1}, i : a = b -> Nat, and the synthetic opaque ?o : Nat, as
\ tests/front/defeq-cases.lean makes them (names unique without case:
\ Gforth's are case-insensitive). One line per case: "true", then both
\ sides with their metavariables instantiated, or "false", or
\ "unsupported" or the outcome's name. Each case runs under a mark that
\ is rolled back after it, so no case sees another's assignments; eq-dq
\ uses the elaborator's configuration (foApprox, ctxApprox: Lean's
\ run_meta), meta-dq Meta's default, deep-dq the elaborator's one depth
\ deeper (withNewMCtxDepth), red-dq, inst-dq and impl-dq reducible,
\ instances and implicit transparency.
\ Test support only: printing recurses on the host stack, which the
\ small cases allow.

\ Every module first: a context member declared after menv-load (in
\ whnf-cases.fs) would move the context under the loaded slice.
require ../../src/front/defeq.fs
require ./whnf-cases.fs

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

: defeq-show ( t s flag outcome -- )
  dup ok? 0= if nip nip nip .outcome cr exit then drop
  if ." true " swap lf-instantiate-mvars drop .t space lf-instantiate-mvars drop .t
  else 2drop ." false" then cr ;
: dq-case ( t s -- )
  lf-mctx-mark drop >r 2dup lf-meta-defeq defeq-show r> lf-mctx-rollback drop
  lf-tr-default lf-defeq-mode! ;
: eq-dq ( t s -- ) lf-defeq-elab lf-defeq-flags! dq-case ;
: meta-dq ( t s -- ) 0 lf-defeq-flags! dq-case ;
: deep-dq ( t s -- ) lf-defeq-elab lf-defeq-flags! lf-mctx-deeper dq-case
  lf-mctx-shallower ;
: red-dq ( t s -- ) lf-tr-reducible lf-defeq-mode! eq-dq ;
: inst-dq ( t s -- ) lf-tr-instances lf-defeq-mode! eq-dq ;
: impl-dq ( t s -- ) lf-tr-implicit lf-defeq-mode! eq-dq ;
