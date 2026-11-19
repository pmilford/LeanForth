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
\ A wrong cell count is LeanForth's fault, thrown invalid when xt ends:
\ never a cell of the caller's eaten silently (review F8 of a2-i).
\ (by-count: a THROW's five cells dropped, xt's two inputs among them.)
: by-count ( i*x xt in out -- code ) ['] lf-meta-catch catch dup if >r 2drop 2drop drop r> then ;
T{ 111 222 333 ' sum-prod 3 2 by-count -> 111 -4201 }T
T{ 3 4 ' sum-prod 2 1 by-count -> -4201 }T
T{ 3 4 ' sum-prod 2 2 by-count -> 7 12 outcome-ok 0 }T
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
: sees-x ( fvar -- type flag ) dup lf-fvar-type swap lf-mctx-view swap lf-view-has? ;
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
\ mkBinding head-beta reduces a binder's type (a2-i; pinned Lean 4.35.0,
\ run_meta: mkLambdaFVars #[j] j over j : (fun y : Nat => Nat) k is
\ fun j : Nat => j, (lam Nat.{} #0)).
: beta-type ( -- t ) nat nat lf-term-lam lf-made! zero lf-mk-app ;
: lam-j ( -- lam ) beta-type s" j" binder dup xs ! xs 1 lf-mk-lambda-fvars view0 lf-mctx-view! ;
T{ lam-j dup lf-term-first@ s" Nat" lf-meta-const-named? swap lf-term-second@ lf-term-bvar?
   -> true true }T
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
\ Expr.eq?: Eq α a b's arguments in order; none for another term.
: eq-ab ( -- a b e ) zero zero 2dup lf-mk-eq ;
: sides= ( a b α a' b' -- α b=b' a=a' ) rot >r rot = -rot = r> -rot ;
: eq-taken ( -- b=b' a=a' nat? flag ) eq-ab lf-eq? >r sides= rot s" Nat" lf-meta-const-named? r> ;
T{ eq-taken -> true true true true }T
T{ nat lf-eq? refl-nat lf-eq? -> false false }T
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
\ An instance binder in this run, which has no elaboration data: no class
\ is known, so instance search refuses the goal (110, invalid), never a
\ term; the frame and context put back (part 4 has the data).
: hadd-code ( -- code ) s" HAdd.hAdd" zero zero 2 ['] lf-mk-app-m catch dup if >r 2drop 2drop
  drop r> then ;
T{ hadd-code lf-synth-error abm-frames slab-count lf-mctx-marks -> -4201 110 0 0 }T
: refl-zero ( -- e ) s" Eq.refl" zero 1 lf-mk-app-m ;
T{ ' refl-zero lf-tr-all lf-meta-at 2 s" Eq.refl" lf-meta-app-of? -> true }T
\ mkCongrArg: a dependent function is no arrow (rejected). (A congrFun
\ proof fused through congrArg? is check_whnf.py's, against pinned Lean.)
: refl-fun ( -- f ) s" Eq.refl" nat lf-infer! lf-level! lf-mk-const1 nat lf-mk-app ;
nat0 zero zero lf-mk-eq s" h" binder constant fh
: dependent ( -- code ) refl-fun fh ['] lf-mk-congr-arg catch dup if nip nip then ;
T{ dependent -> -4204 }T
T{ nat dup lf-whnf-r! = -> true }T

\ ---- 5. Slice 9.4.8l-I's shared words (plan 9.4.8l-I).
\ The configuration scopes: each sets only its own part on the
\ configuration in force and gives it back on both paths.
: config@ ( -- flags mode ) lf-meta-config ;
: config-fails ( -- ) outcome-full lf-must ;
lf-meta-default lf-tr-instances lf-meta-config!
lf-defeq-fo lf-defeq-ctx or lf-defeq-quasi or constant approx-bits
T{ ' config@ lf-with-reducible config@ -> lf-meta-default lf-tr-reducible lf-meta-default
   lf-tr-instances }T
T{ ' config@ lf-with-assignable-opaque config@
   -> lf-meta-default lf-defeq-opaque or lf-tr-instances lf-meta-default lf-tr-instances }T
T{ ' config@ lf-with-approx -> lf-meta-default approx-bits or lf-tr-instances }T
: both ( -- flags mode ) ['] config@ lf-with-assignable-opaque ;
T{ ' both lf-with-approx -> lf-meta-default approx-bits or lf-defeq-opaque or lf-tr-instances }T
T{ ' config-fails ' lf-with-reducible code1 config@ -> -4206 lf-meta-default lf-tr-instances }T
T{ ' config-fails ' lf-with-assignable-opaque code1 config@
   -> -4206 lf-meta-default lf-tr-instances }T
T{ ' config-fails ' lf-with-approx code1 config@ -> -4206 lf-meta-default lf-tr-instances }T
lf-defeq-elab lf-tr-default lf-meta-config!
\ lf-with-record: a frame erased for each call, nested calls their own,
\ every frame freed when xt ends or throws (a frame xt leaves above its
\ own too). xt reads its frame as the slab's last unit (review
\ tactic-move M1): a nested call that grows the slab past its block (5000
\ units) moves it, and the outer call's frame, read afresh, still holds
\ what it wrote before and takes what it writes after.
create rec-slab /slab allot  2 cells 10000 rec-slab slab-init drop
: rec ( -- frame ) rec-slab slab-last ;
: rec-sum ( x -- x' n ) rec @ + rec-slab slab-count ;
: rec-dirty ( -- ) 7 rec ! ;
: rec-fails ( -- ) rec-dirty outcome-full lf-must ;
: rec-depth ( -- n ) rec-slab slab-count ;
: rec-nested ( -- n m ) rec-dirty rec-slab ['] rec-depth lf-with-record rec-slab
  slab-count ;
: rec-leaks ( -- ) 2 rec-slab slab-claim 2drop ;
T{ 5 rec-slab ' rec-sum lf-with-record rec-slab slab-count -> 5 1 0 }T
T{ rec-slab ' rec-dirty lf-with-record 0 rec-slab ' rec-sum lf-with-record -> 0 1 }T
T{ rec-slab ' rec-fails ' lf-with-record catch nip nip rec-slab slab-count -> -4206 0 }T
T{ rec-slab ' rec-nested lf-with-record rec-slab slab-count -> 2 1 0 }T
T{ rec-slab ' rec-leaks lf-with-record rec-slab slab-count -> 0 }T
: rec-grows ( -- ) 9 rec ! 5000 rec-slab slab-claim lf-must drop ;
: rec-outer ( -- before after cap-grew? n )
  rec-slab slab-capacity rec-dirty rec-slab ['] rec-grows lf-with-record rec @
  8 rec ! rec @ rot rec-slab slab-capacity < rec-slab slab-count ;
T{ rec-slab ' rec-outer lf-with-record rec-slab slab-count -> 7 8 true 1 0 }T
rec-slab slab-free
\ lf-term-holds-with?: the test reads its context x, which is not left.
: same? ( x leaf -- x flag ) over = ;
nat s" w" binder constant fw   nat s" v" binder constant fv
zero fw lf-mk-app constant zero-x
T{ zero-x fw ' same? lf-term-holds-with? zero-x fv ' same? lf-term-holds-with?
   -> true outcome-ok false outcome-ok }T
\ lf-local-decl-new: a new variable of the type and its local, pushed on
\ a new view; the current view not changed.
lf-mctx-view constant view-q  nat constant ty-q
ty-q s" q" lfa-intern lf-binder-default lf-local-decl-new constant view-q' constant fq
T{ fq lf-fvar-type ty-q = view-q' lf-view-count view-q lf-view-count 1+ = lf-mctx-view view-q =
   -> true true true }T
T{ view-q' fq lf-view-find nip view-q fq lf-view-find -> true false }T
\ appendTag on names: succ ++ zero, and an anonymous parent's tag as it is.
T{ s" succ" lfa-intern s" zero" lfa-intern lf-name-append-tag s" succ.zero" name= -> true }T
T{ 0 s" zero" lfa-intern lf-name-append-tag s" zero" name= -> true }T
\ matchEq?: an Eq's three arguments, also after whnf (a beta-redex
\ (fun p => p) (0 = 0)); no Eq after whnf, false.
zero zero lf-mk-eq constant zz
: prop-id ( -- f ) s" True" lf-mk-const0 lf-infer! 0 lf-term-bvar lf-made! lf-term-lam lf-made! ;
: zero? ( t -- flag ) zero lf-meta-eqv made ;
: zero-sides ( α a b true -- f f true ) >r zero? swap zero? rot drop r> ;
T{ zz lf-match-eq? zero-sides -> true true true }T
T{ prop-id zz lf-mk-app lf-match-eq? zero-sides -> true true true }T
T{ nat lf-match-eq? zero-x ' lf-match-eq? code1 -> false 0 false }T

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
\ lf-defeq-elab-at: isDefEq at the transparency asked for, the
\ configuration in force put back (with the slice's
\ elaboration data, which holds the reducibility attributes): id Nat is Nat at default, not at
\ reducible (id is no reducible definition); lf-tac-defeq at default.
: id-nat ( -- t ) s" id" nat 1 lf-mk-app-m ;
T{ id-nat nat lf-tr-default lf-defeq-elab-at id-nat nat lf-tr-reducible lf-defeq-elab-at config@
   -> true outcome-ok false outcome-ok lf-defeq-elab lf-tr-default }T
T{ id-nat nat lf-tac-defeq -> true outcome-ok }T
\ lf-tac-with-synth (Term.withSynthesize, review tactic-move M3): the
\ stack passes through xt; the pending list is set aside while xt runs
\ (none seen inside) and put back however xt ends; a problem xt leaves
\ that no instance fills (Append Type: the elaborator records Lean's
\ "failed to synthesize", 125) stops the run, as the runner's mapping of
\ an invalid outcome gives it (93; the elaborator's own code is not
\ carried, plan 9.4.8l), and the window is closed with the problem left.
: type0 ( -- t ) nat lf-infer! ;
: append-type ( -- mvar )
  s" Append" type0 lf-level! lf-mk-const1 type0 lf-mk-app mv-synthetic lf-mvar-new made ;
: pends ( -- n ) lf-elab-pending# ;
: sum-pends ( a b -- a+b n ) + pends ;
: pend-append ( -- ) append-type lf-elab-pend drop ;
: pend-throws ( -- ) pend-append -77 throw ;
T{ lf-elab-pending-reset pend-append 3 4 ' sum-pends lf-tac-with-synth pends -> 7 0 1 }T
T{ lf-elab-pending-reset lf-elab-error-reset ' pend-append ' lf-tac-with-synth catch nip lf-author-code
   lf-elab-error drop pends -> lf-author-throw 93 125 1 }T
lf-tac-forget
T{ lf-elab-pending-reset pend-append ' pend-throws ' lf-tac-with-synth catch nip lf-author-code pends
   -> -77 0 2 }T
lf-elab-pending-reset lf-elab-error-reset
lf-author-begin

\ ---- 6. tactic-msg.fs's branches that a well-formed proof never takes
\ (S2 coverage debt, paid by slice 9.4.8l-I): a term that does not print
\ (no term: an instantiation refused) cuts the message at once, each part
\ after it left out and its outcome kept; a type whose own type cannot be
\ inferred gives the plain form; isDefEq of the two sorts out of fuel
\ gives the plain form; a detail while an error is recorded is left out.
create text 4096 allot  variable text#
: grab ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
2variable settings
: sunk ( i*x xt -- j*x c-addr u )   \ what xt prints, the printer put back
  lf-print-settings settings 2! 0 text# ! ['] grab lf-print-unicode lf-print-setup
  execute settings 2@ lf-print-setup text text# @ ;
: has. ( e type expected -- outcome c-addr u ) ['] lf-has-type-but-expected. sunk ;
: has-type ( -- c-addr u ) s\"   Nat.zero\nhas type\n  " ;
T{ zero -1 nat has. has-type compare -> outcome-invalid 0 }T
T{ zero nat -1 has. s\"   Nat.zero\nhas type\n  Nat\nbut is expected to have type\n  " compare
   -> outcome-invalid 0 }T
T{ -1 nat nat has. s"   " compare -> outcome-invalid 0 }T
\ (Nat.zero's sort Nat, against 0 = 0's Prop: named; x : (fun y => y) Nat
\ against Nat.zero's Nat: equal, so plain, also when isDefEq runs out.)
T{ zero zero zero zero lf-mk-eq has. s\" of sort `Nat`" search nip nip -> outcome-ok true }T
: id-type ( -- f ) nat lf-infer! 0 lf-term-bvar lf-made! lf-term-lam lf-made! ;
id-type nat lf-mk-app s" x" binder constant fx-beta
: plain-x ( -- c-addr u ) s\"   Nat.zero\nhas type\n  x\nbut is expected to have type\n  Nat.zero" ;
T{ zero fx-beta zero has. plain-x compare -> outcome-ok 0 }T
T{ 1 lf-defeq-fuel! zero fx-beta zero has. plain-x compare 0 lf-defeq-fuel! -> outcome-ok 0 }T
T{ 1 lf-defeq-fuel! fx-beta lf-infer! nat lf-tac-defeq nip ok? 0 lf-defeq-fuel! -> false }T
: shout. ( x -- outcome ) drop s" late" lf-pp-emit outcome-ok ;
: detail# ( -- n ) lfa-detail slab-count ;
T{ ' author-fails catch detail# 0 ' shout. lf-tac-inline detail# = -> lf-author-throw true }T
lf-tac-forget
T{ lf-author-code -> 0 }T

\ ---- 7. The goal words of commit C2 (plan 9.4.8l-I), called directly:
\ lf-goal-intro-n (names, _, a binder with no name, n > 1, kinds given or
\ read, no binder 94 with the goal, the context and the frames put back
\ on both paths), lf-goal-checked-assign (assigned; 98 for a variable
\ outside the context and for a goal assigned already, with Lean's text;
\ 93 for an open metavariable), lf-goal-refl (Eq.refl; 97 with Lean's
\ text; 93 for no Eq), lf-tac-detail-n (n cells dropped once an error is
\ recorded). Errors thrown outside a tactic run are authoring errors at
\ the current token.
lf-author-begin
: goal-of ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: pi-named ( dom body c-addr u kind -- t )
  >r lfa-intern >r lf-term-pi lf-made! dup r> r> lf-pres-binder! made ;
: nat2 ( -- t ) nat nat nat s" b" lf-binder-default pi-named s" a" lf-binder-default pi-named ;
create names 2 cells allot  create kinds2 2 cells allot  create xs2 2 cells allot
: names! ( n0 n1 -- ) names cell+ ! names ! ;
: local-at ( view k -- local ) over lf-view-count + 2 - lf-view-local ;
: intro-code ( goal names kinds2 n -- code ) xs2 ['] lf-goal-intro-n catch dup if >r 2drop 2drop
  drop r> else nip then ;
lf-mctx-view constant view-c2
: prop ( -- t ) 0 lf-term-symbolic-sort lf-made! ;
: frames0? ( -- flag ) mti-frames slab-count 0= lf-mctx-view view-c2 = and ;
nat2 goal-of constant g2
s" x" lfa-intern 0 names!
g2 names 0 2 xs2 lf-goal-intro-n constant g2'
: new-local ( k -- local ) g2' lf-goal-view swap local-at ;
T{ g2' lf-goal-type nat lf-meta-eqv made g2 lf-goal-assigned? frames0? -> true true true }T
T{ 0 new-local dup lf-local-name s" x" name= swap lf-local-flags -> true 0 }T
T{ 1 new-local dup lf-local-name s" b" name= swap lf-local-flags -> true lf-local-inaccessible }T
T{ 0 new-local lf-local-fvar xs2 @ = 1 new-local lf-local-fvar xs2 cell+ @ = -> true true }T
\ Kinds given (an alternative's fields): the local's flags carry them.
lf-binder-implicit kinds2 !  lf-binder-default kinds2 cell+ !  s" y" lfa-intern 0 names!
nat2 goal-of names kinds2 2 xs2 lf-goal-intro-n lf-goal-view constant v-k
T{ v-k 0 local-at lf-local-flags v-k 1 local-at lf-local-flags
   -> lf-binder-implicit lf-local-inaccessible }T
\ A goal whose type is a metavariable assigned a pi: introN instantiates it.
nat lf-infer! mv-natural lf-mvar-new made constant m-ty
T{ m-ty prop prop s" d" lf-binder-default pi-named lf-mvar-assign -> outcome-ok }T
0 0 names!
T{ m-ty goal-of names 0 1 xs2 lf-goal-intro-n lf-goal-type prop lf-meta-eqv made frames0? -> true true }T
\ A binder with no name: a, inaccessible; with no kind known either: 99.
: bare ( -- t ) nat prop lf-term-pi lf-made! ;
0 0 names!
T{ bare goal-of names kinds2 1 xs2 lf-goal-intro-n lf-goal-view 1 local-at dup lf-local-name
   s" a" name= swap lf-local-flags lf-local-inaccessible and 0<> -> true true }T
T{ bare goal-of names 0 1 intro-code lf-author-code frames0? -> lf-author-throw 99 true }T
lf-tac-forget
\ No binder (Nat, or Prop -> Nat's second): 94 with the goal; the
\ context and the frames put back.
: detail$ ( -- c-addr u ) 0 lfa-detail slab-at lfa-detail slab-count ;
: detail-has? ( c-addr u -- flag ) detail$ 2swap search nip nip ;
T{ nat goal-of names 0 1 intro-code lf-author-code frames0? -> lf-author-throw 94 true }T
T{ s" ⊢ Nat" detail-has? -> true }T
lf-tac-forget
T{ prop nat s" c" lf-binder-default pi-named goal-of names 0 2 intro-code lf-author-code frames0?
   -> lf-author-throw 94 true }T
lf-tac-forget
\ checkedAssign: assigned; assigned again or a variable outside the
\ context: 98 with the term, Lean's line and the goal; an open
\ metavariable: 93's unsupported.
: assign-code ( goal e -- code ) ['] lf-goal-checked-assign catch dup if nip nip then ;
nat goal-of constant ga
T{ ga zero assign-code ga lf-goal-assigned? -> 0 true }T
T{ ga zero assign-code lf-author-code -> lf-author-throw 98 }T
T{ s" occurs-check failure" detail-has? -> true }T
lf-tac-forget
T{ nat goal-of nat lf-lctx-local made assign-code lf-author-code -> lf-author-throw 98 }T
T{ s\" this is often due to an occurs-check failure\n\n" detail-has? -> true }T
lf-tac-forget
T{ nat goal-of nat mv-natural lf-mvar-new made assign-code -> -4205 }T
\ MVarId.refl: 0 = 0 closed by Eq.refl; r = s, two variables: 97 with
\ Lean's text; Nat: no Eq, 93's unsupported.
zero zero lf-mk-eq goal-of constant gr
T{ gr lf-goal-refl gr lf-mvar-value drop 2 s" Eq.refl" lf-meta-app-of? -> true }T
nat s" r" binder constant fr  nat s" s" binder constant fs
T{ fr fs lf-mk-eq goal-of ' lf-goal-refl code1 lf-author-code -> lf-author-throw 97 }T
T{ s\" r\nis not definitionally equal to the right-hand side\n  s\n\n" detail-has? -> true }T
lf-tac-forget
T{ nat goal-of ' lf-goal-refl code1 -> -4205 }T
\ checkNotAssigned first (review tactic-move M3): an assigned goal is
\ refused, invalid, before its type is read, by introN (Nat: no binder,
\ else 94) and by refl (Nat: no Eq, else 93's unsupported).
nat goal-of constant g-done
T{ g-done zero lf-mvar-assign -> outcome-ok }T
lf-mctx-view constant view-g
T{ g-done names 0 1 intro-code lf-author-code mti-frames slab-count lf-mctx-view view-g =
   -> -4201 0 0 true }T
T{ g-done ' lf-goal-refl code1 lf-author-code mrf-frames slab-count -> -4201 0 0 }T
\ lf-tac-detail-n: n cells printed, or dropped while an error is recorded.
: pair. ( a b -- outcome ) + 11 = if s" eleven" lf-pp-emit then outcome-ok ;
T{ 5 6 2 ' pair. lf-tac-detail-n s" eleven" detail-has? -> true }T
lf-tac-forget
T{ ' author-fails catch 7 8 9 3 ' shout. lf-tac-detail-n -> lf-author-throw }T
lf-tac-forget
\ lf-tac-failed: an error at the step running, with xt's detail of 0.
: zero. ( x -- outcome ) 0= if s" given 0" lf-pp-emit then outcome-ok ;
T{ ' zero. lfa-e-tac-form ' lf-tac-failed catch nip nip lf-author-code s" given 0" detail-has?
   -> lf-author-throw 99 true }T
lf-tac-forget
\ lf-tac-inline while an error is recorded: neither the detail nor the end
\ of the message's line (lfa-err-inline) changes (review tactic-move M3).
: inline@ ( -- n ) lfa-error lfa-err-inline @ ;
T{ ' zero. lfa-e-tac-form ' lf-tac-failed catch nip nip inline@ detail# 0 ' shout. lf-tac-inline
   detail# = swap inline@ = -> lf-author-throw true true }T
T{ inline@ detail# < -> true }T
lf-tac-forget
\ ---- 8. MVarId.rewrite (meta-tactic/rewrite.fs's lf-goal-rewrite, plan
\ 9.4.8l-I commit C3), called directly over a : Nat, b : Nat, h : a = b:
\ a = a rewritten to b = b, the proof congrArg's, of type (a = a) = (b =
\ b), no new goal, the goal not assigned; each error of its own with
\ Lean's text: no occurrence 215, a motive not type correct 216 (pa : P
\ b in @Eq (a = b) h h), a dependent one 217 (the term Eq.refl a, whose
\ type holds a), no equality 218 (a value, a proof), a pattern that is a
\ metavariable 219; not supported yet, 99: an Iff, symm, an instance
\ binder; an assigned goal invalid. Every frame and the current view put
\ back. A rewrite inside an open frame of its own slab (a nested call)
\ leaves the outer frame's fields as they were, also when it fails.
lf-author-begin
nat s" a" binder constant fa   nat s" b" binder constant fb
fa fb lf-mk-eq s" h" binder constant fhab
\ (the rules of the failing cases below: t : True, hm : ?m = b,
\ hi : True <-> True, hx : [x : Nat] -> a = b)
s" True" lf-mk-const0 s" t" binder constant ft
nat mv-natural lf-mvar-new made fb lf-mk-eq s" hm" binder constant fhm
s" Iff" lf-mk-const0 s" True" lf-mk-const0 lf-mk-app s" True" lf-mk-const0 lf-mk-app
  s" hi" binder constant fhi
nat fa fb lf-mk-eq s" x" lf-binder-instance pi-named s" hx" binder constant fhx
\ (and rules with a binder: hs : forall x, Nat.succ x = b, whose x the
\ pattern assigns; hu : forall x : Nat, a = b, whose x stays a new goal)
create rw-xs 1 cells allot
: nat-succ ( t -- t' ) s" Nat.succ" lf-mk-const0 swap lf-mk-app ;
nat s" x" binder constant fx-rw   fx-rw rw-xs !
fx-rw nat-succ fb lf-mk-eq rw-xs 1 lf-mk-forall-fvars s" hs" binder constant fhs
fa fb lf-mk-eq rw-xs 1 lf-mk-forall-fvars s" hu" binder constant fhu
\ (hq : ?T, ?T : ?S, ?S : Type: a rule whose type has no level known)
type0 mv-natural lf-mvar-new made mv-natural lf-mvar-new made s" hq" binder constant fhq
lf-mctx-view constant view-rw
: aa ( -- t ) fa fa lf-mk-eq ;
: rw-target ( goal heq -- new proof goals ) over lf-goal-type swap false lf-goal-rewrite ;
: rw-code ( goal e heq symm? -- code )
  ['] lf-goal-rewrite catch ?dup if >r 2drop 2drop r> else drop 2drop 0 then ;
: rw-of ( goal heq -- code ) over lf-goal-type swap false rw-code ;
: rw-put-back? ( -- flag ) mrw-frames slab-count 0= lf-mctx-view view-rw = and ;
aa goal-of constant g-aa
: rw-aa ( -- app? typed? new? n )
  g-aa fhab rw-target run-count >r dup 6 s" congrArg" lf-meta-app-of? swap lf-infer!
  aa fb fb lf-mk-eq lf-mk-eq lf-meta-eqv made rot fb fb lf-mk-eq lf-meta-eqv made r> ;
T{ rw-aa -> true true true 0 }T
T{ g-aa lf-goal-assigned? rw-put-back? -> false true }T
\ A rule's new metavariables: assigned by the pattern (Nat.succ a =
\ Nat.succ a to b = b), no goal; one the rewrite leaves, a goal (Lean's
\ newMVarIds).
fa nat-succ dup lf-mk-eq goal-of constant g-ss
T{ g-ss fhs rw-target run-count nip swap fb dup lf-mk-eq lf-meta-eqv made -> 0 true }T
T{ g-aa fhu rw-target run-count nip nip rw-put-back? -> 1 true }T
\ 215, with the pattern, the target and the goal.
T{ zero zero lf-mk-eq goal-of fhab rw-of lf-author-code rw-put-back? -> lf-author-throw 215 true }T
T{ s\" a\nin the target expression\n  Nat.zero = Nat.zero\n\n" detail-has? -> true }T
lf-tac-forget
\ 216: fun _a => @Eq (_a = b) h h is not type correct (Lean's case
\ (h : n + 0 = n) : h = h by rw [Nat.add_zero], which no LeanForth text
\ reaches yet: a hypothesis used as a term).
T{ fhab fhab lf-mk-eq goal-of fhab rw-of lf-author-code rw-put-back? -> lf-author-throw 216 true }T
T{ s\" fun _a ↦ h = h\nError: Application type mismatch in the application\n" detail-has? -> true }T
lf-tac-forget
\ A motive Meta.check refuses with no application kept (Nat.zero given a
\ universe argument it has no parameter for: checkConstant): 216 with the
\ motive alone.
s" Nat.zero" 0 1 lf-mk-const constant zero-u
T{ fa zero-u lf-mk-eq goal-of fhab rw-of lf-author-code -> lf-author-throw 216 }T
T{ s\" fun _a ↦ _a = Nat.zero\n\na b : Nat" detail-has? -> true }T
lf-tac-forget
\ 217: Eq.refl a's type a = a depends on a.
T{ g-aa fa lf-mk-eq-refl fhab false rw-code lf-author-code rw-put-back? -> lf-author-throw 217 true }T
lf-tac-forget
\ 218: a value (a : Nat), a proof (t : True).
T{ g-aa fa rw-of lf-author-code -> lf-author-throw 218 }T
T{ s"  `a` is a value of type" detail-has? -> true }T
lf-tac-forget
T{ g-aa ft rw-of lf-author-code rw-put-back? -> lf-author-throw 218 true }T
T{ s"  `t` is a proof of" detail-has? -> true }T
lf-tac-forget
\ (a type whose level is not known: not a proof, as Lean's isProp says)
T{ g-aa fhq rw-of lf-author-code -> lf-author-throw 218 }T
T{ s"  `hq` is a value of type" detail-has? -> true }T
lf-tac-forget
\ 219: ?m = b.
T{ g-aa fhm rw-of lf-author-code rw-put-back? -> lf-author-throw 219 true }T
T{ s" in this equality" detail-has? -> true }T
lf-tac-forget
\ 99: an Iff (True <-> True), symm, an instance binder ([x : Nat] -> a = b).
T{ g-aa fhi rw-of lf-author-code rw-put-back? -> lf-author-throw 99 true }T
lf-tac-forget
T{ g-aa aa fhab true rw-code lf-author-code rw-put-back? -> lf-author-throw 99 true }T
lf-tac-forget
T{ g-aa fhx rw-of lf-author-code rw-put-back? -> lf-author-throw 99 true }T
lf-tac-forget
\ An assigned goal: invalid.
aa goal-of constant g-done2
T{ g-done2 fa lf-mk-eq-refl lf-mvar-assign -> outcome-ok }T
T{ g-done2 fhab rw-of lf-author-code rw-put-back? -> -4201 0 true }T
\ Inside an open frame of mrw-frames: the outer frame's fields kept
\ across a nested rewrite that succeeds and one that fails.
: rw-nested ( -- n kept? code kept? )
  4242 mrw mrw-goal ! g-aa fhab rw-target 2drop drop mrw-frames slab-count
  mrw mrw-goal @ 4242 = zero zero lf-mk-eq goal-of fhab rw-of mrw mrw-goal @ 4242 = ;
T{ mrw-frames ' rw-nested lf-with-record rw-put-back? -> 1 true lf-author-throw true true }T
lf-tac-forget

\ ---- 9. Eliminators (meta-tactic/elim.fs, plan 9.4.8l-I commit C4),
\ called directly over n : Nat, l : List Nat, b : Bool, p : Prop, α :
\ Type, x : α, f : Nat -> Nat, s : Lean.Syntax, the main goal n = n:
\ lf-elim-for (the data's Nat.recAux; Nat.casesOn for cases, the slice's
\ data holding no cases eliminator, where all of Init's names
\ Nat.casesAuxOn: Init/Data/Nat/Basic.lean:48; List.rec; 205 with each
\ hint and the goal, its explanation naming induction or cases; 209 for
\ a nested type under induction only), lf-elim-info
\ (Nat.rec's alternatives; index targets 99), lf-elim-app (Nat.rec's
\ application, its goals tagged t.zero and t.succ, the motive; a target
\ of another type 99; no pi left 93; an instance binder 99; a binder of
\ no known kind 99), lf-elim-set-motive (the motive assigned; 212).
\ Every frame put back.
lf-author-begin
: list-nat ( -- t ) s" List" 0 lf-mk-const1 nat lf-mk-app ;
nat s" n" binder constant fn9   list-nat s" l" binder constant fl9
s" Bool" lf-mk-const0 s" b" binder constant fb9
prop s" p" binder constant fp9   type0 s" α" binder constant fal9
fal9 s" x" binder constant fx9   nat nat lf-term-pi lf-made! s" f" binder constant ff9
s" Lean.Syntax" lf-mk-const0 s" s" binder constant fs9
fn9 fn9 lf-mk-eq goal-of constant g9
T{ 0 g9 run-push made lf-goals! -> outcome-ok }T
: elim-name? ( target induction? c-addr u -- flag ) 2>r lf-elim-for lf-menv-name 2r> name= ;
T{ fn9 true s" Nat.recAux" elim-name? fn9 false s" Nat.casesOn" elim-name? -> true true }T
T{ fl9 true s" List.rec" elim-name? -> true }T
: elim-code-of ( target induction? -- code ) ['] lf-elim-for catch dup if nip nip then ;
: elim-code ( target -- code ) true elim-code-of ;
T{ fp9 elim-code lf-author-code -> lf-author-throw 205 }T
T{ s" by_cases" detail-has? s" ⊢ n = n" detail-has? -> true true }T
T{ s" Explanation: the `induction` tactic is for constructor-based reasoning as well as for "
   detail-has? s" applying custom induction principles with a 'using' clause or a " detail-has?
   s" registered '@[induction_eliminator]' theorem. The above type" detail-has? -> true true true }T
lf-tac-forget
\ (cases, induction? false: Lean's tacticName in the explanation, Induction.lean:775-778;
\ the header stays error 205's, induction's, until cases is ported: plan 9.4.8l W)
T{ fp9 false elim-code-of lf-author-code -> lf-author-throw 205 }T
T{ s" Explanation: the `cases` tactic is for constructor-based reasoning as well as for "
   detail-has? s" applying custom cases principles with a 'using' clause or a " detail-has?
   s" registered '@[cases_eliminator]' theorem. The above type" detail-has?
   s" induction" detail-has? s" by_cases" detail-has? -> true true true false true }T
lf-tac-forget
T{ fal9 elim-code lf-author-code s" Type universes" detail-has? -> lf-author-throw 205 true }T
lf-tac-forget
T{ fx9 elim-code lf-author-code s" Consider" detail-has? s" Type universes" detail-has?
   -> lf-author-throw 205 false false }T
T{ s" registered theorem." detail-has? -> true }T
lf-tac-forget
T{ ff9 elim-code lf-author-code -> lf-author-throw 205 }T
lf-tac-forget
T{ fs9 elim-code lf-author-code s" a nested inductive type" detail-has? -> lf-author-throw 209 true }T
T{ s" Hint: Consider using the `cases` tactic instead" detail-has? -> true }T
lf-tac-forget
\ (cases takes a nested type, as Lean's getElimNameInfo does: never 209;
\ the slice holds no Lean.Syntax.casesOn, so its lookup is refused, the
\ library's invalid)
T{ fs9 false elim-code-of -> -4201 }T
\ getElimExprInfo: Nat.rec {motive} (zero) (succ) (t): zero with no field,
\ succ with two, both explicit; Eq.refl's conclusion is no motive applied
\ to a target (99).
s" Nat.rec" decl lf-elim-info constant nat-info
T{ nat-info lf-elim-decl s" Nat.rec" decl = nat-info lf-elim-alts# -> true 2 }T
T{ nat-info 0 lf-elim-alt-name s" zero" name= nat-info 0 lf-elim-alt-fields
   nat-info 0 lf-elim-alt-pos -> true 0 1 }T
T{ nat-info 1 lf-elim-alt-name s" succ" name= nat-info 1 lf-elim-alt-fields
   nat-info 1 lf-elim-alt-pos -> true 2 2 }T
T{ nat-info s" succ" lfa-intern lf-elim-alt-find nat-info s" one" lfa-intern lf-elim-alt-find
   -> 1 true false }T
T{ nat-info 1 lf-elim-alt-kinds swap 2@ -> 2 lf-binder-default lf-binder-default }T
T{ refl-d ' lf-elim-info code1 lf-author-code -> lf-author-throw 99 }T
lf-tac-forget
\ mkElimApp: @Nat.rec ?motive ?zero ?succ n, the alternatives' goals in
\ order with the goal's tag appended, the motive synthetic opaque.
: frames9? ( -- flag ) mea-frames slab-count mes-frames slab-count or 0= ;
nat-info fn9 s" t" lfa-intern lf-elim-app constant motive9 constant alts9 constant f9
T{ f9 4 s" Nat.rec" lf-meta-app-of? f9 lf-term-second@ fn9 = alts9 run-count frames9?
   -> true true 2 true }T
T{ alts9 0 run@ lf-goal-tag s" t.zero" name= alts9 1 run@ lf-goal-tag s" t.succ" name=
   motive9 lf-goal-kind -> true true mv-opaque }T
\ (List.rec's {α} an implicit binder: a natural metavariable, which the
\ target's type assigns Nat)
s" List.rec" decl lf-elim-info fl9 0 lf-elim-app drop run-count swap lf-term-first@ lf-term-first@
  lf-term-first@ lf-term-first@ lf-term-second@ constant alpha9 constant alts#9
T{ alts#9 alpha9 lf-instantiate! nat lf-meta-eqv made frames9? -> 2 true true }T
: app-code ( info target -- code ) 0 ['] lf-elim-app catch dup if >r 2drop drop r> else
  nip nip nip then ;
T{ nat-info fb9 app-code lf-author-code frames9? -> lf-author-throw 99 true }T
lf-tac-forget
\ (an information that counts one binder more than Nat.rec has: no pi
\ for it, 93)
: one-more ( info -- info' )
  0 over lf-elim-decl run-push made over mel-binders 1+ run-push made
  swap dup run-count 2 ?do dup i run@ rot swap run-push made swap loop drop ;
T{ nat-info one-more fn9 app-code lf-author-code frames9? -> lf-author-throw 93 true }T
lf-tac-forget
\ (an implicit binder: an instance one refused, 99, as is a binder whose
\ kind is not known)
: hadd-info ( -- info ) 0 s" HAdd.hAdd" decl run-push made ;
: implicit-run ( k -- code )
  hadd-info mea mea-info ! fresh-pi swap ['] mea-implicit catch ?dup if nip nip else drop 0 then ;
: implicit-at ( k -- code ) mea-frames ['] implicit-run lf-with-record ;
T{ 3 implicit-at lf-author-code -> lf-author-throw 99 }T
lf-tac-forget
T{ 1 implicit-at -> 0 }T
: kind-code ( info k -- code ) ['] mel-kind catch dup if nip nip then ;
T{ hadd-info 99 kind-code lf-author-code -> lf-author-throw 99 }T
lf-tac-forget
\ setMotiveArg: fun x => x = x assigned to the motive; a motive of type
\ Nat -> Prop against the goal Nat (fun x => Nat : Nat -> Type): 212 with
\ the motive.
T{ g9 motive9 fn9 lf-elim-set-motive motive9 lf-mvar-value drop lf-term-lam? frames9?
   -> true true }T
nat prop lf-term-pi lf-made! mv-natural lf-mvar-new made constant motive-p
: motive-code ( goal motive target -- code ) ['] lf-elim-set-motive catch dup if nip nip nip then ;
T{ nat goal-of motive-p fn9 motive-code lf-author-code frames9? -> lf-author-throw 212 true }T
T{ s" ↦ Nat" detail-has? -> true }T
lf-tac-forget
\ generalizeVars (tactics/induction.fs's tind-independent, in a step
\ record whose context is the current one): hm : m = m holds m, so m is
\ refused (99); no hypothesis holds n.
nat s" m" binder constant fm9   fm9 fm9 lf-mk-eq s" hm" binder drop
: indep ( target i -- code )
  drop lf-mctx-view tb tb-view ! ['] tind-independent catch ?dup if nip else drop 0 then ;
T{ fm9 0 ' indep lf-tac-in-record lf-author-code -> lf-author-throw 99 }T
lf-tac-forget
T{ fn9 0 ' indep lf-tac-in-record -> 0 }T
\ The target: a term that is no free variable, or a let variable,
\ refused (99).
T{ zero ' tind-fvar code1 lf-author-code -> lf-author-throw 99 }T
lf-tac-forget
nat zero lf-lctx-let made constant flet9
T{ flet9 lf-meta-fvar? flet9 ' tind-fvar code1 lf-author-code fn9 tind-fvar fn9 =
   -> true lf-author-throw 99 true }T
lf-tac-forget
\ The branches no proof text reaches: 205's message cut when the type
\ does not print; a head constant that names no declaration, or no
\ inductive type (no recursor); a declaration with no inductive data
\ (93); mkElimApp past the last alternative (an information of Nat.rec
\ that lists zero alone: succ's binder an implicit argument).
T{ -1 true ' mel-major. sunk 2drop -1 false ' mel-major. sunk 2drop
   -> outcome-invalid outcome-invalid }T
T{ s" No.such.type" lfa-intern 0 lf-mk-const-id mel-inductive s" Nat.add" lf-mk-const0
   mel-inductive -> false false }T
: simple-code ( -- code ) nat s" Nat.add" decl ['] mel-simple catch dup if nip nip then ;
T{ simple-code lf-author-code -> lf-author-throw 93 }T
lf-tac-forget
: first-cells ( info n -- info' ) 0 swap 0 ?do over i run@ run-push made loop nip ;
T{ nat-info 7 first-cells fn9 0 lf-elim-app drop run-count nip frames9? -> 1 true }T
\ tactic-alts.fs, in a step record: Lean's orList of the alternatives not
\ written (none here: tal-js empty) for none, two and three; a field past
\ the kinds the eliminator gives (99); a field that is not explicit takes
\ no name; a target the goal depends on is not cleared (tryClear).
: alt+ ( info c-addr u -- info' ) lfa-intern run-push made 0 run-push made 0 run-push made ;
: expected-in ( info i -- c-addr u ) drop tal tal-info ! tal-js slab-clear ['] tal-expected. sunk ;
: expected ( info -- c-addr u ) 0 ['] expected-in lf-tac-in-record ;
T{ nat-info 4 first-cells expected s" There are no unhandled alternatives" compare -> 0 }T
T{ nat-info expected s" Expected `zero` or `succ`" compare -> 0 }T
T{ nat-info s" c" alt+ expected s" Expected `zero`, `succ`, or `c`" compare -> 0 }T
: kind-in ( info i -- code ) drop tal tal-info ! 0 tal tal-k ! 0 ['] tal-kind code1 ;
T{ nat-info 0 ' kind-in lf-tac-in-record lf-author-code -> lf-author-throw 99 }T
lf-tac-forget
T{ lf-binder-implicit tal-name-for -> 0 }T
: cleared-in ( target i -- goal ) drop tal tal-target ! tal-cleared lf-goals 0 run@ ;
T{ fn9 0 ' cleared-in lf-tac-in-record g9 = -> true }T

\ ---- 10. A mutual type (209, Lean's text and hint): FE6.Even of
\ tests/front/several.ndjson, a library of its own.
T{ s" tests/front/several.ndjson" true lfc-library-open -> outcome-ok }T
lf-author-begin
s" FE6.Even" lf-mk-const0 s" Nat.zero" lf-mk-const0 lf-mk-app s" e" binder constant fe10
T{ fe10 elim-code lf-author-code s" `FE6.Even` because it is mutually inductive" detail-has?
   -> lf-author-throw 209 true }T
lf-tac-forget
\ (cases takes it: FE6.Even.casesOn, Lean's mkCasesOnName; review
\ tactic-move-c4 B1)
T{ fe10 false s" FE6.Even.casesOn" elim-name? -> true }T
.( tactic-lib.fs: all tests passed) cr
bye
