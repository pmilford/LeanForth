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
\   lf-goal-generalize-eq ( goal args h -- fvars goal' )  the same of one
\       argument (args one pair, e and x) with the equation name h
\       (generalize h : e = x, generalizeCore's hName path :51-78): the
\       type (x : T) -> type' made and checked as above, its binder
\       opened (forallBoundedTelescope 1: x a local of type T) and
\       closed again over (h : e = x) -> type' (mkEq, mkForall,
\       mkForallFVars), goal' a new goal of it, goal assigned
\       goal' e (Eq.refl e) (mkEqRefl), the two binders introduced with
\       their names (introNP); fvars x and h. With one argument x's type
\       is e's own, so isDefEq holds and the equation is an Eq (mkHEq
\       serves several arguments of which a later one's type depends on
\       an earlier one). Another count of pairs is thrown unsupported.
\   lf-goal-generalize-hyp ( goal args h hyps -- fvars goal' )
\       MVarId.generalizeHyp (:148-156) of one argument: hyps a run of
\       free variables of goal's context; those whose type instantiated
\       holds e (kabstract at instances leaves a loose bound variable)
\       reverted (preserveOrder, revert.fs's lf-goal-revert-kept), the
\       goal generalized (h 0: lf-goal-generalize, else
\       lf-goal-generalize-eq), the reverted introduced again with their
\       names (introNP, goal.fs's lf-goal-intro-kept); none reverted is
\       generalize alone, as Lean's (hyps empty: the trivial case)
\ Not supported yet (thrown unsupported): a type that is not type correct
\ (Lean's "result is not type correct", plan E5).
\ Lean call list: instantiateMVars -> lf-instantiate!; inferType ->
\ lf-infer!; kabstract -> lf-meta-kabstract under lf-meta-at;
\ mkForall -> lf-term-pi, lf-pres-binder!; isTypeCorrect ->
\ lf-meta-check; mkFreshExprSyntheticOpaqueMVar -> lf-goal-fresh;
\ assign -> lf-mvar-assign; introNP -> lf-goal-intro-names;
\ forallBoundedTelescope -> lf-with-local-decl and lf-meta-instantiate1;
\ mkEq, mkEqRefl -> lf-mk-eq, lf-mk-eq-refl; mkForallFVars ->
\ lf-mk-forall-fvars (telescope.fs); revert -> lf-goal-revert-kept;
\ introNP of the reverted -> lf-goal-intro-kept.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mgz-frames, mgq-frames and mgh-frames (a frame per call open,
\ meta-must.fs's lf-with-record), in the checker context (ADR 0009); no
\ other. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/bounds.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../core/local-context.fs
require ../../present/binder-table.fs
require ../../author/declarations.fs
require ../goals.fs
require ../meta-config.fs
require ../infer.fs
require ../kabstract.fs
require ../meta-check.fs
require ../tactic-run.fs
require ../meta-must.fs
require ../instantiate.fs
require ../app-builder.fs
require ../telescope.fs
require ./goal.fs
require ./revert.fs

begin-structure /mgz
  field: mgz-goal        \ the goal
  field: mgz-args        \ its arguments, a run of pairs
end-structure
/mgz context-slab: mgz-frames
: mgz ( -- frame ) mgz-frames slab-last ;
: mgz-n ( -- n ) mgz mgz-args @ run-count 2/ ;
: mgz-arg ( k -- e name ) mgz mgz-args @ swap run-pair@ ;
\ (xi : Ti) -> type with ei abstracted (kabstract at instances).
: mgz-kab ( type e -- body ) lf-meta-kabstract lf-must drop ;
: mgz-abstract ( type e -- body ) ['] mgz-kab lf-tr-instances lf-meta-at ;
: mgz-name ( name -- name' ) ?dup 0= if s" x" lfa-intern then ;
: mgz-forall ( type e name -- type' )
  >r lf-instantiate! dup lf-infer! lf-instantiate! -rot mgz-abstract lf-term-pi lf-made!
  dup r> mgz-name lf-binder-default lf-pres-binder! lf-must ;
: mgz-target ( -- t )
  mgz mgz-goal @ lf-goal-type lf-instantiate! mgz-n 0 ?do mgz-n 1- i - mgz-arg
  mgz-forall loop ;
: mgz-checked ( t -- t ) dup lf-defeq-mode lf-meta-check
  dup outcome-invalid = if drop outcome-unsupported then lf-must ;
\ The new goal applied to e1 .. en, then the n binders introduced.
: mgz-applied ( goal' -- e ) mgz-n 0 ?do i mgz-arg drop lf-mk-app loop ;
: mgz-names ( -- names ) 0 mgz-n 0 ?do i mgz-arg nip lf-run+ loop ;
: mgz-run ( -- fvars goal' )
  mgz-target mgz-checked mgz mgz-goal @ lf-goal-fresh dup mgz-applied mgz mgz-goal @ swap
  lf-mvar-assign lf-must mgz-names mgz-n lf-goal-intro-names swap ;
: mgz-framed ( goal args -- fvars goal' ) mgz mgz-goal cell-pair! mgz-run ;
: mgz-in ( goal args -- fvars goal' ) mgz-frames ['] mgz-framed lf-with-record ;
: lf-goal-generalize ( goal args -- fvars goal' )
  over lf-goal-not-assigned drop over ['] mgz-in lf-with-goal ;

\ ---- generalize h : e = x (generalizeCore's hName path), one argument:
\ inside an mgz frame of the goal and the pair, an mgq frame of h and x.
begin-structure /mgq
  field: mgq-h           \ the equation's name
  field: mgq-x           \ x, a local while the binder is open
end-structure
/mgq context-slab: mgq-frames
: mgq ( -- frame ) mgq-frames slab-last ;
: mgq-e ( -- e ) 0 mgz-arg drop lf-instantiate! ;
\ (h : e = x) -> type, then closed over x (mkForallFVars #[x]).
: mgq-arrow ( type -- t )
  mgq-e mgq mgq-x @ lf-mk-eq swap lf-term-pi lf-made! mgq mgq-h @ lf-binder-named ;
: mgq-closed ( t0 x -- t )
  dup mgq mgq-x ! swap lf-term-second@ swap lf-meta-instantiate1 lf-must mgq-arrow
  mgq mgq-x 1 lf-mk-forall-fvars ;
\ forallBoundedTelescope 1: x a local of the binder's type, named x.
: mgq-binder ( t0 -- t0 type name bi )
  dup lf-term-first@ 0 mgz-arg nip mgz-name lf-binder-default ;
: mgq-target ( t0 -- t ) mgq-binder ['] mgq-closed lf-with-local-decl ;
\ goal assigned goal' e (Eq.refl e); the names x, h.
: mgq-applied ( goal' -- e ) mgz-applied mgq-e lf-mk-eq-refl lf-mk-app ;
: mgq-assign ( goal' -- goal' )
  dup mgq-applied mgz mgz-goal @ swap lf-mvar-assign lf-must ;
: mgq-names ( -- names ) mgz-names mgq mgq-h @ lf-run+ ;
: mgq-one ( -- ) mgz-n 1 <> if lf-unported then ;
: mgq-new ( -- goal' ) mgz-target mgz-checked mgq-target mgz mgz-goal @ lf-goal-fresh ;
: mgq-run ( -- fvars goal' )
  mgq-one mgq-new mgq-assign mgq-names 2 lf-goal-intro-names swap ;
: mgq-framed ( goal args h -- fvars goal' ) mgq mgq-h ! mgz mgz-goal cell-pair! mgq-run ;
: mgq-nested ( goal args h -- fvars goal' ) mgq-frames ['] mgq-framed lf-with-record ;
: mgq-in ( goal args h -- fvars goal' ) mgz-frames ['] mgq-nested lf-with-record ;
: lf-goal-generalize-eq ( goal args h -- fvars goal' )
  >r over lf-goal-not-assigned r> swap ['] mgq-in lf-with-goal ;

\ ---- generalizeHyp of one argument (four cells: Lean's mvarId args hyps
\ and the argument's hName, kept in an mgh frame).
begin-structure /mgh
  field: mgh-args        \ the argument, one pair
  field: mgh-h           \ the equation's name, 0 for none
  field: mgh-kept        \ the hypotheses that hold e, a run
  field: mgh-locals      \ their locals once reverted (revert-kept's run)
end-structure
/mgh context-slab: mgh-frames
: mgh ( -- frame ) mgh-frames slab-last ;
: mgh-e ( -- e ) mgh mgh-args @ 0 run@ lf-instantiate! ;
: mgh-kab ( type e -- flag ) lf-meta-kabstract lf-must nip ;
: mgh-holds? ( fvar -- flag )
  lf-fvar-type lf-instantiate! mgh-e ['] mgh-kab lf-tr-instances lf-meta-at ;
: mgh-keep ( fvar -- ) dup mgh-holds? if mgh mgh-kept lf-run+! else drop then ;
: mgh-filter ( hyps -- ) dup run-count 0 ?do dup i run@ mgh-keep loop drop ;
: mgh-gen ( goal -- fvars goal' )
  mgh mgh-args @ mgh mgh-h @ ?dup if lf-goal-generalize-eq else lf-goal-generalize then ;
: mgh-revert ( goal -- goal' ) mgh mgh-kept @ lf-goal-revert-kept mgh mgh-locals ! ;
: mgh-again ( fvars goal -- fvars goal' )
  mgh mgh-locals @ dup run-count lf-goal-intro-kept drop ;
: mgh-run ( goal -- fvars goal' ) mgh-revert mgh-gen mgh-again ;
: mgh-framed ( goal args h hyps -- fvars goal' )
  >r mgh mgh-h ! mgh mgh-args ! r> mgh-filter mgh-run ;
: lf-goal-generalize-hyp ( goal args h hyps -- fvars goal' )
  mgh-frames ['] mgh-framed lf-with-record ;
base !   \ the BASE this file was loaded with
