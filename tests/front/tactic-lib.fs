\ Unit tests of the tactic library (plan slice a2-i; design
\ docs/design/TACTIC_PLUGINS.md 2.1-2.3): src/front/meta-must.fs,
\ telescope.fs and the app-builder.fs words that tests/front/check_whnf.py
\ (the builders against pinned Lean's AppBuilder) cannot reach, over the
\ S2 slice in an authoring run (new nodes are store nodes, so binders are
\ named in the presentation table), by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. every outcome: lf-must's code per outcome (none for ok, invalid for a
\    value outside the vocabulary), lf-meta-catch's hand-back (each
\    outcome as thrown, never ok; another code passed on), commitWhen's
\    true, false and THROW, the builders' invalid, rejected and
\    unsupported, mkAppM's instance binders found and not found (part 4,
\    with the slice's elaboration data); 2. malformed input: a value outside the outcomes, too
\    many levels or arguments, a goal or variable outside any context, an
\    unknown constant; 3. stack effects (each T{ }T checks the depth);
\ 5. resources: a store's false thrown full; 6. state and rollback: the
\    metavariable context, the current view, the local context and the
\    library's frame slabs put back on both paths; 7. regression pins:
\    the telescope's kinds and names, mkLambdaFVars's binder and
\    elimMVar's delayed case (intro's fun x => ?n x).
\ Nothing here accepts a theorem: only the kernel's check does.
include ../support/heap-watch.fs
require ../support/tester.fs
require ../../src/main.fs
decimal

\ Room as the command line gives it (a new context's term store is small).
4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
: library ( -- c-addr u ) s" tests/front/s2-slice.ndjson" ;
T{ library true lfc-library-open -> outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" tactic-lib: not made" ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: zero ( -- t ) s" Nat.zero" lf-mk-const0 ;
: decl ( c-addr u -- d ) lfa-intern lf-menv-find made ;
: name= ( id c-addr u -- flag ) lfa-intern = ;
\ (Each part below that needs no earlier term starts a new run.)
: refl-d ( -- d ) s" Eq.refl" decl ;   \ Eq.refl.{u} {α : Sort u} (a : α)
\ A free variable of the type, its local named and pushed on the view.
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
\ The THROW code of a word that may throw, its inputs gone either way.
: code1 ( x xt -- code ) catch dup if nip then ;

\ ---- 1. meta-must.fs: lf-must, the codes, lf-made!.
T{ outcome-ok ' lf-must code1 -> 0 }T
T{ outcome-invalid ' lf-must code1 outcome-unknown ' lf-must code1 -> -4201 -4203 }T
T{ outcome-rejected ' lf-must code1 outcome-unsupported ' lf-must code1
   outcome-full ' lf-must code1 outcome-exhausted ' lf-must code1 -> -4204 -4205 -4206 -4202 }T
T{ 99 ' lf-must code1 -1 ' lf-must code1 -> -4201 -4201 }T   \ outside the vocabulary
T{ -4200 lf-meta-thrown? -4201 lf-meta-thrown? -4206 lf-meta-thrown? -4207 lf-meta-thrown?
   lf-author-throw lf-meta-thrown? -> false true true false false }T
T{ -4205 lf-meta-outcome -4201 lf-meta-outcome -> outcome-unsupported outcome-invalid }T
T{ true ' lf-made! code1 false ' lf-made! code1 -> 0 -4206 }T
\ A throwing face: the outcome word's result, else its failure thrown.
T{ nat lf-infer! lf-sort? nat dup lf-whnf! = nat dup lf-whnf-d! = -> true true true }T
T{ nat lf-infer! lf-level! lf-level-tag@ lf-level-tag-succ = -> true }T   \ Nat : Type
T{ -1 ' lf-infer! code1 -> -4201 }T   \ no term

\ ---- lf-meta-catch: outcome code calling throwing words.
: sum-prod ( a b -- a+b a*b ) 2dup + -rot * ;
: fails-unsupported ( a b -- c ) 2drop outcome-unsupported lf-must 0 ;
: fails-full ( a -- b c ) drop outcome-full lf-must 0 0 ;
T{ 3 4 ' sum-prod 2 2 lf-meta-catch -> 7 12 outcome-ok }T
T{ 3 4 ' fails-unsupported 2 1 lf-meta-catch -> -1 outcome-unsupported }T
T{ 5 ' fails-full 1 2 lf-meta-catch -> -1 -1 outcome-full }T
: other ( -- ) 77 throw ;
: author-fails ( -- ) lfa-e-tac-meta lfa-fail ;
: passed-on ( xt -- code ) 0 0 ['] lf-meta-catch catch nip nip nip ;
T{ ' other passed-on ' author-fails passed-on -> 77 lf-author-throw }T
lf-tac-forget

\ ---- lf-commit-when: kept on true; rolled back on false and on a THROW,
\ which passes on; no mark left open.
variable mv
: fresh-mv ( -- ) nat mv-natural lf-mvar-new made mv ! ;
: assigned? ( -- flag ) mv @ lf-mvar-value dup if nip then ;
: assign-then ( flag -- flag ) mv @ zero lf-mvar-assign made ;
: assign-fail ( -- flag ) true assign-then drop outcome-rejected lf-must true ;
T{ fresh-mv true ' assign-then lf-commit-when assigned? lf-mctx-marks -> true true 0 }T
T{ fresh-mv false ' assign-then lf-commit-when assigned? lf-mctx-marks -> false false 0 }T
T{ fresh-mv ' assign-fail ' lf-commit-when code1 assigned? lf-mctx-marks -> -4204 false 0 }T

\ ---- lf-with-goal: the goal's context current while xt runs, the
\ current one put back after it, also after a THROW; a goal of no
\ context (no metavariable) refused, invalid.
lf-mctx-view constant view0
nat s" x" binder constant fx
lf-mctx-view constant view1
nat 0 view1 lf-goal-new made constant goal1
view0 lf-mctx-view!
: view-in ( -- view ) lf-mctx-view ;
: view-fails ( -- ) outcome-full lf-must ;
: with-fails ( goal xt -- code ) ['] lf-with-goal catch dup if nip nip then ;
T{ goal1 ' view-in lf-with-goal lf-mctx-view -> view1 view0 }T
T{ goal1 ' view-fails with-fails lf-mctx-view -> -4206 view0 }T
T{ nat ' view-in with-fails lf-mctx-view -> -4201 view0 }T

\ ---- 2. telescope.fs: binder kinds, the declaration's first.
: fresh-pi ( -- pi ) nat nat lf-term-pi lf-made! ;   \ sharing is off: a new node
: named-pi ( kind -- pi ) >r fresh-pi dup s" y" lfa-intern r> lf-pres-binder! made ;
T{ refl-d lf-menv-type refl-d 0 lf-binder-kind-at -> lf-binder-implicit true }T
T{ refl-d lf-menv-type lf-term-second@ refl-d 1 lf-binder-kind-at -> lf-binder-default true }T
T{ lf-binder-instance named-pi -1 0 lf-binder-kind-at -> lf-binder-instance true }T
T{ lf-binder-strict named-pi refl-d 9 lf-binder-kind-at -> lf-binder-strict true }T
T{ fresh-pi -1 0 lf-binder-kind-at fresh-pi lf-binder-of -> false false }T
T{ lf-binder-implicit named-pi lf-binder-of rot s" y" name= -> lf-binder-implicit true true }T
\ An unrecorded binder's name is the anonymous one (0); a recorded one's.
T{ fresh-pi lf-binder-name lf-binder-default named-pi lf-binder-name s" y" name= -> 0 true }T

\ ---- lf-with-local-decl: a new local in a new current view; both put
\ back after xt, also after a THROW.
nat constant nat0
lf-lctx-count @ constant count0
: sees-x ( fvar -- type flag ) dup lf-fvar-type swap lf-mctx-view swap lf-view-find dup if nip then ;
: local-ok ( -- type flag n view )
  nat0 s" z" lfa-intern lf-binder-default ['] sees-x lf-with-local-decl lf-lctx-count @
  lf-mctx-view ;
T{ local-ok -> nat0 true count0 view0 }T
: local-fails ( fvar -- ) drop outcome-unsupported lf-must ;
: local-thrown ( -- code n view )
  nat0 s" z" lfa-intern lf-binder-default ['] local-fails ['] lf-with-local-decl catch
  dup if nip nip nip nip then lf-lctx-count @ lf-mctx-view ;
T{ local-thrown -> -4205 count0 view0 }T

\ ---- lf-forall-meta-telescope-reducing: a metavariable per binder,
\ natural for {α} and (a), synthetic for an instance binder, named as the
\ binder; Eq.refl's body Eq ?α ?a ?a; a type that is no pi as it is; an
\ unrecorded pi's kind refused (unsupported) with the frame dropped.
create kinds 8 cells allot
: kind+ ( k mvar kind -- k+1 ) drop lf-mvar-kind drop over cells kinds + ! 1+ ;
: telescope-of ( d -- n body ) 0 over lf-menv-type rot ['] kind+ lf-forall-meta-telescope-reducing ;
T{ refl-d telescope-of 3 s" Eq" lf-meta-app-of? kinds 2@ swap -> 2 true mv-natural mv-natural }T
: tag-of ( acc mvar kind -- acc ) drop lf-mvar-tag drop swap drop ;
T{ 0 refl-d lf-menv-type refl-d ' tag-of lf-forall-meta-telescope-reducing drop s" a" name= -> true }T
T{ 0 nat0 -1 ' 2drop lf-forall-meta-telescope-reducing nat0 = -> 0 true }T
: refused ( -- code n )
  0 fresh-pi -1 ['] 2drop ['] lf-forall-meta-telescope-reducing catch dup if nip nip nip nip then
  tl-frames slab-count ;
T{ refused -> -4205 0 }T

\ ---- lf-mk-lambda-fvars, lf-mk-forall-fvars: over x (a local of view1).
create xs 2 cells allot
: succ-x ( -- e ) s" Nat.succ" lf-mk-const0 fx lf-mk-app ;
: in-view1 ( i*x xt -- j*x ) view1 lf-mctx-view! catch view0 lf-mctx-view! throw ;
: lam-x ( -- t ) fx xs ! succ-x xs 1 lf-mk-lambda-fvars ;
: pi-x ( -- t ) fx xs ! succ-x xs 1 lf-mk-forall-fvars ;
: binder? ( t -- name kind first flag ) dup lf-binder-of drop rot lf-term-first@ ;
T{ ' lam-x in-view1 dup lf-term-lam? swap lf-term-second@ lf-term-second@ lf-term-bvar? -> true true }T
T{ ' lam-x in-view1 binder? fx lf-fvar-type = rot s" x" name= -> lf-binder-default true true }T
T{ ' pi-x in-view1 lf-term-pi? -> true }T
T{ succ-x xs 0 lf-mk-lambda-fvars succ-x lf-term-second@ swap lf-term-second@ = -> true }T
\ Malformed: a variable outside the current view (invalid), a let
\ variable (unsupported).
: outside ( -- code ) succ-x xs 1 ['] lf-mk-lambda-fvars catch dup if nip nip nip then ;
T{ fx xs ! outside -> -4201 }T
nat zero lf-lctx-let made constant flet
T{ flet xs ! flet lf-mctx-view swap s" w" lfa-intern 0 lf-local-new made lf-view-push made
   lf-mctx-view! outside view0 lf-mctx-view! -> -4205 }T

\ ---- elimMVar's case (intro's fun x => ?n x): an unassigned synthetic
\ opaque metavariable whose context ends with x becomes ?n x, ?n new in
\ the context before x, of type (x : Nat) -> Nat, delayed-assigned [x]
\ := the metavariable; a natural one is assigned ?n x instead; one that
\ does not see x stays as it is; a local after x is refused.
variable goal
: new-in-view1 ( kind -- ) nat swap view1 lf-mvar-new-at made goal ! ;
: lam-goal ( -- lam ) fx xs ! goal @ xs 1 lf-mk-lambda-fvars ;
: aux ( lam -- aux ) lf-term-second@ lf-term-first@ ;
: delayed-on ( aux -- pending n ) lf-mvar-delayed drop nip ;
T{ mv-opaque new-in-view1 ' lam-goal in-view1 dup lf-term-second@ lf-term-second@ lf-term-bvar?
   swap aux delayed-on swap goal @ = -> true 1 true }T
T{ ' lam-goal in-view1 aux dup lf-mvar-view drop lf-view-count swap lf-mvar-type drop lf-term-pi?
   -> 0 true }T
T{ mv-natural new-in-view1 ' lam-goal in-view1 drop goal @ lf-mvar-value nip -> true }T
T{ nat mv-natural lf-mvar-new made goal ! ' lam-goal in-view1 lf-term-second@ goal @ = -> true }T
: view2 ( -- ) view1 lf-mctx-view! nat s" y" binder drop ;
: after-x ( -- code ) mv-opaque new-in-view1 view2 nat mv-opaque lf-mctx-view lf-mvar-new-at made
  goal ! ['] lam-goal catch view0 lf-mctx-view! ;
T{ after-x -> -4205 }T
\ A metavariable that sees y but not x, abstracted over [x, y] (Lean
\ reverts y alone): refused, unsupported.
view1 lf-mctx-view! nat s" y" binder constant fy  lf-mctx-view constant view-xy
view0 fy s" y" lfa-intern 0 lf-local-new made lf-view-push made constant view-y
view0 lf-mctx-view!
: lam-xy ( -- e ) fx xs ! fy xs cell+ ! goal @ xs 2 lf-mk-lambda-fvars ;
: partial-xs ( -- code )
  nat mv-opaque view-y lf-mvar-new-at made goal ! view-xy lf-mctx-view! ['] lam-xy catch
  view0 lf-mctx-view! ;
T{ partial-xs -> -4205 }T
\ mkLambdaFVars leaves no metavariable that sees x (Lean's elimMVarDeps
\ reverts it): a delayed-assigned one (?n of fun y => ?n y, which ?g of
\ context x, y gives; ?n's context holds x), or one inside e
\ (Nat.succ ?g, ?g in view1), is refused, unsupported; one that does not
\ see x stays (above).
: lam-y ( -- e ) fy xs ! goal @ xs 1 lf-mk-lambda-fvars ;
: delayed-e ( -- code )
  nat mv-opaque view-xy lf-mvar-new-at made goal ! view-xy lf-mctx-view! lam-y aux goal !
  view1 lf-mctx-view! ['] lam-goal catch view0 lf-mctx-view! ;
T{ delayed-e -> -4205 }T
: succ-goal ( -- e ) fx xs ! s" Nat.succ" lf-mk-const0 goal @ lf-mk-app xs 1 lf-mk-lambda-fvars ;
: inner-e ( -- code ) mv-natural new-in-view1 view1 lf-mctx-view! ['] succ-goal catch
  view0 lf-mctx-view! ;
T{ inner-e -> -4205 }T

\ HAdd.hAdd {α β γ} [self : HAdd α β γ] : α → β → γ (a new run).
lf-author-begin
T{ s" HAdd.hAdd" decl telescope-of drop kinds 2 cells + 2@ swap -> 6 mv-natural mv-synthetic }T

\ ---- 3. app-builder.fs over the S2 slice: mkEqMPR and mkEqMP (mkAppM
\ of Eq.mpr and Eq.mp; pinned Lean for mkEqMPR: @Eq.mpr.{1} Nat Nat (Eq.refl.{2}
\ Type Nat) k, check_whnf.py's run); too many levels or arguments
\ (invalid); an unknown constant (invalid) and a mismatch (rejected),
\ the frame slab and the metavariable context put back.
lf-author-begin
: refl-nat ( -- h ) nat lf-mk-eq-refl ;
T{ refl-nat zero lf-mk-eq-mpr 4 s" Eq.mpr" lf-meta-app-of? -> true }T
\ (The S2 slice has no Eq.mp: mkAppM's getConstVal fails, invalid.)
: mp-code ( -- code ) refl-nat zero ['] lf-mk-eq-mp catch dup if nip nip then ;
T{ mp-code -> -4201 }T
T{ refl-nat zero lf-mk-eq-mpr lf-meta-head lf-const-slot lf-cref-pairs nip -> 1 }T
lf-author-begin
: seventeen ( -- x1..x17 17 ) 17 0 do 0 loop 17 ;
: many-levels ( -- code ) s" Nat" seventeen ['] lf-mk-const catch dup if >r 20 0 do drop loop r> then ;
T{ many-levels -> -4201 }T
: no-such ( -- code ) s" No.such" zero 1 ['] lf-mk-app-m catch dup if nip nip nip nip then ;
T{ no-such abm-frames slab-count lf-mctx-marks -> -4201 0 0 }T
: mismatch ( -- code ) s" Nat.succ" refl-nat 1 ['] lf-mk-app-m catch dup if nip nip nip nip then ;
T{ mismatch abm-frames slab-count lf-mctx-marks -> -4204 0 0 }T
\ mkAppM at transparency all keeps it (withAtLeastTransparency).
: refl-zero ( -- e ) s" Eq.refl" zero 1 lf-mk-app-m ;
T{ ' refl-zero lf-tr-all lf-meta-at 2 s" Eq.refl" lf-meta-app-of? -> true }T
\ mkCongrArg: a dependent function is no arrow (rejected). (A congrFun
\ proof fused through congrArg? is check_whnf.py's, against pinned Lean.)
: refl-fun ( -- f ) s" Eq.refl" nat lf-infer! lf-level! lf-mk-const1 nat lf-mk-app ;
nat0 zero zero lf-mk-eq s" h" binder constant fh
: dependent ( -- code ) refl-fun fh ['] lf-mk-congr-arg catch dup if nip nip then ;
T{ dependent -> -4204 }T
T{ nat dup lf-whnf-r! = -> true }T

\ ---- 4. mkAppM's instance binders (AppBuilder.lean's mkAppMFinal), with
\ the S2 slice's elaboration data read, so that instance search
\ (synth.fs's lf-synth-instance) is the lf-meta-synth hook, and the
\ stores given the command line's room (lfc-rooms). Pinned Lean 4.35.0
\ (pp.all, mkAppM in run_meta over a local k : Nat): HAdd.hAdd #[k, k]
\ is @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k k;
\ Append.append #[Nat, Nat] is "failed to synthesize Append.{1} Type"
\ (rejected), the frame and context put back. HAdd.hAdd #[Nat, Nat]
\ (Lean: "failed to synthesize HAdd Type Type ?γ") tries a candidate the
\ slice's data leaves out (synth.fs's error 119): unsupported,
\ never rejected nor a term.
T{ s" tests/front/s2-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms -> outcome-ok outcome-ok }T
lf-author-begin
nat s" k" binder constant fk
: inst-nat ( -- e ) s" instHAdd" 0 lf-mk-const1 nat lf-mk-app s" instAddNat" lf-mk-const0 lf-mk-app ;
: hadd-lean ( -- e ) s" HAdd.hAdd" 0 0 0 3 lf-mk-const nat nat nat inst-nat fk fk 6 lf-mk-app-n ;
: hadd-kk ( -- e ) s" HAdd.hAdd" fk fk 2 lf-mk-app-m ;
T{ hadd-kk hadd-lean lf-meta-eqv abm-frames slab-count lf-mctx-marks -> true outcome-ok 0 0 }T
: types2 ( c-addr u -- code ) nat nat 2 ['] lf-mk-app-m catch dup if >r 2drop 2drop drop r> then ;
T{ s" Append.append" types2 abm-frames slab-count lf-mctx-marks -> -4204 0 0 }T
T{ s" HAdd.hAdd" types2 lf-synth-error abm-frames slab-count -> -4205 119 0 }T
lf-author-begin
.( tactic-lib.fs: all tests passed) cr
bye
