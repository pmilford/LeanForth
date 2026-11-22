\ The dite of Lean's by_cases (plan row TB2, tactic batch 2b): the term
\ refine if h : p then ?pos else ?neg elaborates to (Init/ByCases.lean:
\ 25-28, the macro; the if-then-else notation's dite, Init/Prelude.lean),
\ for tactics/by-cases.fs. Each word throws on failure (meta-must.fs).
\ Public words:
\   lf-mk-decidable ( p -- t )  Decidable p
\   lf-decidable-instance ( p -- inst )  the instance of Decidable p that
\       by_cases' open Classical in finds: instance search (synth.fs's
\       lf-synth-instance?), else Classical.propDecidable p, the scoped
\       instance of priority low that open Classical adds, tried last
\       (Classical.propDecidable depends on the axioms propext,
\       Classical.choice and Quot.sound, which the checker's axiom report
\       then lists)
\   lf-goal-by-cases ( goal name p inst -- pos neg )  in goal's context
\       (checkNotAssigned first) two new synthetic opaque goals of goal's
\       target instantiated (refine's getMainTarget), pos in the context
\       with a new local name : p, tagged pos, neg with name : Not p,
\       tagged neg (Lean's named holes ?pos and ?neg); goal assigned
\       @dite.{u} T p inst (fun name : p => pos) (fun name : Not p =>
\       neg), T the target and u its level (getLevel), each fun made by
\       telescope.fs's lf-mk-lambda-fvars (elimMVar: fun h => ?n h, ?n
\       delayed-assigned the goal)
\ Not ported: the macro scopes Lean's tags pos and neg carry (the macro's
\ hygiene; by-case: erases them, as Lean's case does, so only their
\ printing differs); an instance of priority low or lower, which Lean
\ tries only after Classical.propDecidable (none in Init: the instances'
\ priorities in the elaboration data are 100 and up).
\ Lean call list: getMainTarget -> lf-goal-target (assert.fs);
\ withLocalDecl -> lf-local-decl-new, lf-with-view; mkFreshExprMVar
\ (syntheticOpaque, named) -> lf-goal-new; mkLambdaFVars ->
\ lf-mk-lambda-fvars; mkApp -> lf-mk-app-n; getLevel -> lf-level!;
\ synthInstance? -> lf-synth-instance?; assign -> lf-mvar-assign.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mbc-frames (a frame per call open, meta-must.fs's lf-with-record),
\ in the checker context (ADR 0009); no other. Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../present/binder-table.fs
require ../mvars.fs
require ../lctx-views.fs
require ../goals.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs
require ../synth.fs
require ./assert.fs

: lf-mk-decidable ( p -- t ) s" Decidable" lf-mk-const0 swap lf-mk-app ;
: mbc-classical ( p -- inst ) s" Classical.propDecidable" lf-mk-const0 swap lf-mk-app ;
: lf-decidable-instance ( p -- inst )
  dup lf-mk-decidable lf-synth-instance? if nip else drop mbc-classical then ;

begin-structure /mbc
  field: mbc-goal        \ the goal
  field: mbc-name        \ the hypothesis' name
  field: mbc-p           \ the proposition
  field: mbc-inst        \ its Decidable instance
  field: mbc-fvar        \ the branch's variable (mkLambdaFVars' cell)
end-structure
/mbc context-slab: mbc-frames
: mbc ( -- frame ) mbc-frames slab-last ;

\ ---- A branch: fun name : type => ?g, ?g a new goal of the target
\ tagged tag, in goal's context with the new local.
: mbc-target ( -- T ) mbc mbc-goal @ lf-goal-target drop ;
: mbc-bind ( tag -- g fun )
  mbc-target swap lf-mctx-view lf-goal-new lf-must dup mbc mbc-fvar 1 lf-mk-lambda-fvars ;
: mbc-local ( type -- view )
  mbc mbc-name @ lf-binder-default lf-local-decl-new swap mbc mbc-fvar ! ;
: mbc-branch ( type c-addr u -- g fun )
  lfa-intern swap mbc-local ['] mbc-bind swap lf-with-view ;

\ ---- @dite.{u} T p inst (fun h => pos) (fun h => neg), applied a branch
\ at a time.
: mbc-dite ( T -- f ) >r s" dite" r> lf-level! lf-mk-const1 ;
: mbc-head ( -- e )
  mbc-target dup mbc-dite swap lf-mk-app mbc mbc-p @ lf-mk-app mbc mbc-inst @ lf-mk-app ;
: mbc-pos ( e -- pos e' ) mbc mbc-p @ s" pos" mbc-branch rot swap lf-mk-app ;
: mbc-neg ( pos e -- pos neg e' )
  mbc mbc-p @ lf-mk-not s" neg" mbc-branch rot swap lf-mk-app ;
: mbc-run ( goal -- pos neg )
  lf-goal-not-assigned >r mbc-head mbc-pos mbc-neg r> swap lf-mvar-assign lf-must ;
: mbc-framed ( goal name p inst -- pos neg )
  mbc mbc-inst ! mbc mbc-p ! mbc mbc-name ! dup mbc mbc-goal !
  dup ['] mbc-run lf-with-goal ;
: lf-goal-by-cases ( goal name p inst -- pos neg )
  mbc-frames ['] mbc-framed lf-with-record ;
base !   \ the BASE this file was loaded with
