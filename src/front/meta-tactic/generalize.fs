\ Generalizing terms of a goal (plan row TB2, piece E, slice E1;
\ docs/design/TACTIC_PATTERNS.md section 1): Lean 4.35.0's
\ Meta/Tactic/Generalize.lean, MVarId.generalize (:136, generalizeCore
\ :28-76) with no equation names, as rcases' generalizeExceptFVar asks it
\ (Elab/Tactic/RCases.lean:404). Each word throws on failure
\ (meta-must.fs), as Lean's do.
\ Public words:
\   lf-goal-generalize ( goal args -- fvars goal' )  in goal's context
\       (checkNotAssigned first): args a run of pairs of cells, a term e
\       and a name (0: none); the goal's type instantiated becomes
\       (x1 : T1) -> .. -> (xn : Tn) -> type, built from the last
\       argument out, each ei's occurrences abstracted by kabstract at
\       transparency instances (kabstract.fs), Ti ei's type instantiated,
\       xi the name given or x (made inaccessible as Lean's
\       mkFreshUserName); that type checked type correct (meta-check.fs at
\       the transparency in force); goal' a new synthetic opaque goal of
\       it with goal's tag in goal's context, goal assigned goal' e1 .. en,
\       and the n binders introduced (introNP: goal.fs's
\       lf-goal-intro-names, a given name accessible, x inaccessible);
\       fvars the new free variables, a run
\ Not supported yet (thrown unsupported): a type that is not type correct
\ (Lean's "result is not type correct", plan E5), and equation names
\ (hName, generalize h : e = x: no form yet).
\ Lean call list: instantiateMVars -> lf-instantiate!; inferType ->
\ lf-infer!; kabstract -> lf-meta-kabstract under lf-meta-at;
\ mkForall -> lf-term-pi, lf-pres-binder!; isTypeCorrect ->
\ lf-meta-check; mkFreshExprSyntheticOpaqueMVar -> lf-goal-fresh;
\ assign -> lf-mvar-assign; introNP -> lf-goal-intro-names.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mgz-frames (a frame per call open, meta-must.fs's
\ lf-with-record), in the checker context (ADR 0009); no other. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../present/binder-table.fs
require ../../author/declarations.fs
require ../goals.fs
require ../meta-config.fs
require ../infer.fs
require ../kabstract.fs
require ../meta-check.fs
require ../tactic-run.fs
require ../meta-must.fs
require ./goal.fs

begin-structure /mgz
  field: mgz-goal        \ the goal
  field: mgz-args        \ its arguments, a run of pairs
end-structure
/mgz context-slab: mgz-frames
: mgz ( -- frame ) mgz-frames slab-last ;
: mgz-n ( -- n ) mgz mgz-args @ run-count 2/ ;
: mgz-arg ( k -- e name ) 2* mgz mgz-args @ swap 2dup run@ -rot 1+ run@ ;
\ (xi : Ti) -> type with ei abstracted (kabstract at instances).
: mgz-kab ( type e -- body ) lf-meta-kabstract lf-must drop ;
: mgz-abstract ( type e -- body ) ['] mgz-kab lf-tr-instances lf-meta-at ;
: mgz-name ( name -- name' ) ?dup 0= if s" x" lfa-intern then ;
: mgz-forall ( type e name -- type' )
  >r lf-instantiate! dup lf-infer! lf-instantiate! -rot mgz-abstract lf-term-pi lf-made!
  dup r> mgz-name lf-binder-default lf-pres-binder! lf-must ;
: mgz-target ( -- t )
  mgz mgz-goal @ lf-goal-type lf-instantiate! mgz-n 0 ?do mgz-n 1- i - mgz-arg mgz-forall loop ;
: mgz-checked ( t -- t )
  dup lf-defeq-mode lf-meta-check dup outcome-invalid = if drop lf-tac-unported then
  lf-must ;
\ The new goal applied to e1 .. en, then the n binders introduced.
: mgz-applied ( goal' -- e ) mgz-n 0 ?do i mgz-arg drop lf-mk-app loop ;
: mgz-names ( -- names ) 0 mgz-n 0 ?do i mgz-arg nip run-push lf-must loop ;
: mgz-run ( -- fvars goal' )
  mgz-target mgz-checked mgz mgz-goal @ lf-goal-fresh dup mgz-applied mgz mgz-goal @ swap
  lf-mvar-assign lf-must mgz-names mgz-n lf-goal-intro-names swap ;
: mgz-framed ( goal args -- fvars goal' ) mgz mgz-args ! mgz mgz-goal ! mgz-run ;
: mgz-in ( goal args -- fvars goal' ) mgz-frames ['] mgz-framed lf-with-record ;
: lf-goal-generalize ( goal args -- fvars goal' )
  over lf-goal-not-assigned drop over ['] mgz-in lf-with-goal ;
base !   \ the BASE this file was loaded with
