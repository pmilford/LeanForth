\ Lean's Meta.check (plan S2, branch s2-tactics; docs/design/S2_INTERFACE.md
\ 5): whether a term is type correct, after Lean 4.35.0's Meta/Check.lean
\ (check 331, checkAux 290, checkApp 272) and InferType.lean's
\ ensureType (getLevel). The rewrite tactic checks its motive with it
\ (Meta/Tactic/Rewrite.lean:63), at transparency all.
\ - lf-meta-check ( e mode -- outcome ): e checked at transparency mode
\   (the configured one given back however it ends), each node once
\   (Lean's checkCache, by node: the term store shares equal nodes):
\   an application: its function, its argument, then checkApp: the
\   function's type, put through whnf, is a pi whose domain is
\   definitionally equal to the argument's type (else not type correct:
\   invalid, the application kept for the message); a pi: each binder's
\   type a type (ensureType: its type a sort) and checked, the body under a
\   new free variable, ensureType of it when it is no pi (forallTelescope's
\   end), then checked; a lambda: the same without the body's ensureType
\   (lambdaLetTelescope); a constant: as many universe arguments as its
\   declaration has parameters (checkConstant; an unknown constant is
\   invalid); any other leaf: nothing.
\ - lf-meta-check-bad ( -- e ): the application whose argument did not
\   fit, or whose function had no pi type, after an invalid answer; -1
\   for any other failure.
\ Not supported yet (unsupported): a let and a projection inside the term
\ (checkLambdaLet's let case and checkProj, which no motive of the proof
\ set holds; plan S5).
\ The walk keeps its work on a heap stack (no host recursion, plan task
\ 6.2.0) and spends one unit of the declaration's budget a step
\ (meta-config.fs, --elab-fuel): exhausted when none is left. Outcomes:
\ ok; invalid as above, or what inferType, whnf or getLevel answers;
\ full when a store, the memo or the heap has no room; exhausted;
\ unsupported as above. Untrusted: only the kernel's check of the
\ finished proof decides anything.
\ Example: fun _a : Nat => _a = n + 1 is type correct at all (HAdd.hAdd's
\ out-parameter Type unfolds); fun _a : Nat => @Eq Nat _a Nat.zero.succ
\ applied wrongly, @Eq Nat Nat, is invalid, the application kept.
\ State: the record mck (the bad application, the memo of nodes checked)
\ and the slab mck-todo (the work: node and kind), in the checker context
\ (ADR 0009); the memo's blocks are freed with the context.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/memo.fs
require ../core/terms.fs
require ../core/local-context.fs
require ../core/constant-term-boundary.fs
require ../core/let-terms.fs
require ./meta-config.fs
require ./meta-spine.fs
require ./instantiate.fs
require ./whnf.fs
require ./infer.fs
require ./defeq.fs

0 constant mck-k-check    \ check the node
1 constant mck-k-ensure   \ ensureType: its type is a sort
2 constant mck-k-app      \ checkApp of the application
3 constant mck-k-body     \ a pi's body: ensureType unless a pi, then check
begin-structure /mck
  field: mck-bad          \ the application that did not fit, or -1
  /memo +field mck-seen   \ the nodes checked
end-structure
/mck context-record: mck
:noname ( -- ) mck mck-seen memo-free ; context-teardown
2 cells context-slab: mck-todo
: lf-meta-check-bad ( -- e ) mck mck-bad @ ;

\ ---- The memo: a set of nodes.
: mck-ready ( -- outcome )
  mck mck-seen dup memo-live? if memo-clear outcome-ok else 1 0 rot memo-init then ;
: mck-seen? ( e -- flag ) 0 mck mck-seen memo-at 0<> ;
: mck-saw ( e -- outcome ) 0 mck mck-seen memo-claim nip ;

\ ---- The work, the last pushed done first.
: mck-push ( x kind -- outcome ) mck-todo slab-2push ;
: mck-todo+ ( x kind -- flag ) mck-push ok? ;
: mck-full ( x -- outcome ) drop outcome-full ;
\ An application: its function, its argument, then checkApp.
: mck-app ( e -- outcome )
  dup mck-k-app mck-todo+ if dup lf-term-second@ mck-k-check mck-todo+ else false then
  if lf-term-first@ mck-k-check mck-push else mck-full then ;
\ A binder: its type a type and checked, then the body under a new free
\ variable (kind: a pi's body or a lambda's).
: mck-open ( binder -- body outcome )
  dup lf-term-first@ lf-lctx-local ok-then? if lf-meta-open else nip no-result then ;
: mck-domain+ ( binder -- outcome )
  lf-term-first@ dup mck-k-check mck-todo+ if mck-k-ensure mck-push else mck-full then ;
: mck-binder ( e kind -- outcome )
  over mck-open ok-then? 0= if nip nip exit then
  swap mck-todo+ if mck-domain+ else mck-full then ;
: mck-ensure ( e -- outcome ) lf-get-level nip ;
: mck-pi-body ( b -- outcome )
  dup lf-term-pi? if mck-k-check mck-push exit then
  dup mck-k-check mck-todo+ if mck-ensure else mck-full then ;
\ checkConstant: the universe arguments the declaration takes.
: mck-arity ( d e -- outcome ) lf-meta-arity? if outcome-ok else outcome-invalid then ;
: mck-const ( e -- outcome ) dup lf-meta-const-decl ok-then? if swap mck-arity else nip
  then ;
\ A projection, and a smart-unfolding marker (core/annotations.fs: Lean
\ checks mdata's term, not ported), answer unsupported.
lf-tag-projection lf-tag-annotation 2 lf-tags constant mck-unported
: mck-leaf ( e -- outcome )
  mck-unported lf-term-in? if outcome-unsupported else outcome-ok then ;
: mck-node ( e -- outcome )
  dup lf-term-tag@ case lf-tag-app of mck-app endof
    lf-tag-pi of mck-k-body mck-binder endof  lf-tag-lam of mck-k-check mck-binder endof
    lf-tag-constant of mck-const endof  drop dup mck-leaf swap endcase ;
\ (A node checked spends one unit of the budget.)
: mck-check ( e -- outcome )
  dup mck-seen? if drop outcome-ok exit then
  lf-meta-spend? 0= if drop outcome-exhausted exit then
  dup lf-let? if drop outcome-unsupported exit then
  dup mck-saw dup ok? if drop mck-node else nip then ;

\ ---- checkApp: the function's type made a pi by whnf, its domain
\ isDefEq the argument's type.
: mck-fn-type ( f -- type outcome )
  lf-infer ok-then? if lf-meta-whnf else no-result then ;
: mck-pi-domain ( type -- d outcome )
  dup lf-term-pi? if lf-term-first@ outcome-ok else drop outcome-invalid no-result then ;
: mck-domain ( e -- d outcome )
  lf-term-first@ mck-fn-type ok-then? if mck-pi-domain else no-result then ;
: mck-fits? ( d e -- flag outcome )
  lf-term-second@ lf-infer ok-then? 0= if nip false swap exit then
  lf-meta-defeq outcome-sane ;
: mck-bad! ( e -- outcome ) mck mck-bad ! outcome-invalid ;
: mck-fits ( flag e -- outcome ) swap if drop outcome-ok else mck-bad! then ;
: mck-no-domain ( e outcome -- outcome )
  dup outcome-invalid = if drop mck-bad! else nip then ;
: mck-app-check ( e -- outcome )
  dup mck-domain ok-then? 0= if mck-no-domain exit then
  over mck-fits? ok-then? if swap mck-fits else nip then ;

\ ---- The loop (lib/slab.fs's worklist drain).
: mck-step ( e kind -- flag outcome )
  case mck-k-check of mck-check endof  mck-k-ensure of mck-ensure endof
    mck-k-app of mck-app-check endof  mck-k-body of mck-pi-body endof
    nip outcome-invalid swap endcase true swap ;
: mck-run ( -- outcome ) mck-todo ['] mck-step slab-2all? nip ;
: mck-checking ( e -- outcome )
  -1 mck mck-bad ! mck-todo slab-clear mck-ready dup ok? 0= if nip exit then drop
  mck-check dup ok? if drop mck-run then ;
: lf-meta-check ( e mode -- outcome ) ['] mck-checking swap lf-meta-at ;
base !   \ the BASE this file was loaded with
