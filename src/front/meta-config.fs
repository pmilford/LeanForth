\ The Meta layer's configuration (plan S1; docs/design/S1_INTERFACE.md §2
\ and §8): what Lean 4.35.0's Meta layer reads with getConfig
\ (Lean/Meta/Basic.lean, Config, lines 121-171), its transparency
\ (TransparencyMode), the front end's work budget, and the stuck signal.
\ Every word of the Meta layer (level-defeq.fs, defeq.fs, whnf.fs) reads
\ its configuration here.
\ - Flags (lf-defeq-flags), Lean's Config fields: lf-defeq-fo (foApprox),
\   lf-defeq-ctx (ctxApprox), lf-defeq-quasi (quasiPatternApprox),
\   lf-defeq-const (constApprox), lf-defeq-stuck (isDefEqStuckEx),
\   lf-defeq-univ (univApprox) and lf-defeq-opaque (assignSyntheticOpaque).
\   lf-meta-default is Lean's default Config (univApprox only),
\   lf-defeq-elab the elaborator's (run_meta and TermElabM add foApprox and
\   ctxApprox). univApprox acts only while postponed level constraints are
\   processed, which the front end answers unsupported (level-defeq.fs):
\   the flag is kept, it changes no answer yet. assignSyntheticOpaque is
\   read by the tactics' comparison of types (S1 §10, branch s1-elab).
\   lf-defeq-flags! sets them; lf-meta-flag? ( bit -- flag ) reads one.
\ - Transparency, numbered as Lean's TransparencyMode constructors:
\   lf-tr-all, lf-tr-default (the default), lf-tr-reducible,
\   lf-tr-instances, lf-tr-none, lf-tr-implicit; lf-defeq-mode! sets it,
\   lf-defeq-mode reads it. A configuration scope (Lean's withConfig,
\   withTransparency) saves lf-meta-config ( -- flags mode ) and gives it
\   back with lf-meta-config! ( flags mode -- ).
\ - The budget (S1 §8, Lean's maxHeartbeats): the steps of elaboration,
\   synthesis, unification and whnf one declaration may take, default
\   lf-meta-default-budget (100,000,000, as --fuel's); lf-meta-budget! sets
\   it, lf-meta-spend? spends one step and is false, spending nothing, once
\   none is left: the caller answers exhausted.
\ - lf-meta-stuck (16): Lean's isDefEqStuck exception
\   (isDefEqStuckExceptionId, Basic.lean:33 and 652), an internal code
\   beside ADR 0008's outcomes 0-6. It is raised only under lf-defeq-stuck,
\   at Lean's sites (level-defeq.fs: LevelDefEq.lean:169; defeq.fs:
\   ExprDefEq.lean:2118 and 2182), and caught only where Lean catches it
\   (defeq.fs: isDefEqAppFallback and lf-meta-defeq-guarded; later
\   trySynthInstance, synthInstance and synthPendingImp). Every mark rolls
\   back on it and passes it on, as checkpointDefEq does. It is never
\   stored or printed: outcome-sane makes it invalid, and every exit of
\   the Meta layer to the elaborator or a tactic applies outcome-sane.
\ State: one context record, mcfg (ADR 0009). Untrusted front-end code.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs

0 constant lf-tr-all   1 constant lf-tr-default   2 constant lf-tr-reducible
3 constant lf-tr-instances   4 constant lf-tr-none   5 constant lf-tr-implicit
6 constant lf-tr-modes

1 constant lf-defeq-fo   2 constant lf-defeq-ctx   4 constant lf-defeq-quasi
8 constant lf-defeq-const   16 constant lf-defeq-stuck   32 constant lf-defeq-univ
64 constant lf-defeq-opaque
lf-defeq-univ constant lf-meta-default
lf-meta-default lf-defeq-fo or lf-defeq-ctx or constant lf-defeq-elab
16 constant lf-meta-stuck
100000000 constant lf-meta-default-budget

begin-structure /mcfg
  field: mcfg-flags    \ Lean's Config flags (the bits above)
  field: mcfg-mode     \ the transparency
  field: mcfg-budget   \ steps left in this declaration
end-structure
/mcfg context-record: mcfg
: lf-defeq-flags! ( flags -- ) mcfg mcfg-flags ! ;
: lf-defeq-mode! ( mode -- ) mcfg mcfg-mode ! ;
: lf-meta-budget! ( n -- ) mcfg mcfg-budget ! ;
:noname ( -- )
  lf-meta-default lf-defeq-flags! lf-tr-default lf-defeq-mode!
  lf-meta-default-budget lf-meta-budget! ; context-setup

: lf-defeq-flags ( -- flags ) mcfg mcfg-flags @ ;
: lf-meta-flag? ( bit -- flag ) lf-defeq-flags and 0<> ;
: lf-defeq-mode ( -- mode ) mcfg mcfg-mode @ ;
: lf-meta-config ( -- flags mode ) lf-defeq-flags lf-defeq-mode ;
: lf-meta-config! ( flags mode -- ) lf-defeq-mode! lf-defeq-flags! ;
: lf-meta-budget ( -- n ) mcfg mcfg-budget @ ;
: lf-meta-spend? ( -- flag )
  lf-meta-budget dup 0> if 1- lf-meta-budget! true else drop false then ;

base !   \ the BASE this file was loaded with
