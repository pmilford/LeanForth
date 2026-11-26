\ Simp's main loop on a term and on a goal's target (plan row FE9, simp
\ slice SL1a-1 of docs/design/TACTIC_SIMP.md): Lean 4.35.0's simpImpl,
\ simpLoop, simpStep, congr, congrDefault and simpAppUsingCongr
\ (src/lean/Lean/Meta/Tactic/Simp/Main.lean:531-720, Types.lean:732-765)
\ with simp only's methods (Rewrite.lean:536-547: rewritePre, then the
\ simpMatch refusals; rewritePost; no simproc, no decide, no ground), and
\ simpTargetCore (Main.lean:781, Types.lean:1008).
\ - lf-simp ( e max -- e' h ): Simp.main of e with simp/theorems.fs's set
\   and maxSteps max (lf-simp-max-steps, Lean's default 100000), at
\   reducible transparency with the elaborator's flags (withSimpContext,
\   Types.lean:963). The result as simp/types.fs's.
\ - lf-simp-steps ( -- n ): the steps the last lf-simp took (numSteps).
\ - lf-goal-simp-target ( goal max -- goal' | 0 ): simpTargetCore in the
\   goal's context: a result True closes the goal with of_eq_true h
\   (mkOfEqTrue's shortcuts) or True.intro (0); a proof h replaces the
\   target (replaceTargetEq); a different term with none, replaceTargetDefEq;
\   else goal itself (the caller's "no progress").
\ The loop (simpLoop): the cache first, then the step check, numSteps >
\ maxSteps before the increment; pre (rewritePre); reduceStep; simpStep;
\ post (rewritePost); a changed result simplified again; each result
\ cached. The cache (lib/memo.fs) is keyed by the term's node, Lean's
\ ExprMap by structure: a hit here is one in Lean too, never the other
\ way (nodes are shared only with hash-consing on, which the authoring
\ words turn off, and keep binder names apart), so the results are
\ Lean's but LeanForth may take more steps: beyond maxSteps the answer is
\ unsupported, never Lean's error "`simp` failed: maximum number of steps
\ exceeded" (Main.lean:684), which it cannot tell apart.
\ reduceStep (Main.lean:213) instantiates a metavariable head and
\ beta-reduces a lambda head; what else it does is unsupported here, never
\ skipped: a projection or let node, a raw natural literal, a head that a
\ structure's projection function, a recursor, a quotient's, a matcher
\ or an auxiliary definition is (iota and unfold?, which simpMatch shares).
\ simpStep: an application by congr; a constant by reduce; a sort or
\ literal as it is; a metavariable instantiated; a free variable as it is
\ (a let one unsupported: reduceFVar's implementation-detail rule); a
\ lambda by simpLambda (funext); a pi by simpForall: an arrow by
\ simpArrow (implies_congr), a proposition's body under its variable
\ (forall_congr), no proposition dsimp'd (the guard below); a let,
\ projection or annotation unsupported. Without +contextual (simp only's
\ default) no binder adds a rule, so the cache is kept throughout.
\ congr: a head with @[congr] lemmas (simp-data.fs's simp-congr-lemmas)
\ or with a congruence kind other than fixed and eq (congr-thms.fs) is
\ unsupported (SL2); else simpAppUsingCongr: the head, then each argument
\ (getFunInfoNArgs): an instance one kept (mkCongrFun'), one with no
\ forward dependency simplified (mkCongr'), a dependent one simplified
\ when whnfD of its function's type is an arrow, else dsimp'd and kept.
\ The dsimp guard: dsimp (SL1b) is not ported, so an argument it would
\ visit is kept only when dsimp would give it back: a sort, a constant
\ that is no structure projection function, or a free variable that is
\ no let, at which no rfl theorem of the set is a candidate; anything
\ else unsupported. isProof terms are not visited (simpImpl). Depth:
\ Lean's maxRecDepth counts from where the tactic runs, which LeanForth
\ does not know, so more than sm-depth-max visits in progress is
\ unsupported (never Lean's error).
\ Machine: visits on lib/frame.fs's frames (no host recursion), each
\ visit's results ( e h ) below them; a visit's own values in an
\ activation record of the slab sm-acts, the newest the visit running.
\ Throws as meta-must.fs's words do; a THROW resets the frames and the
\ activations. Untrusted: the kernel checks every proof at end NAME.
\ State: the frames sm-frames, the records sm (steps, maximum) and
\ sm-cache, the slabs sm-acts and sm-xs (the binder visits' variables);
\ one simp at a time (a busy record refuses a nested call,
\ unsupported). The binder visits' locals are dropped when the walk
\ ends, a throw included (lf-with-new-locals).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/memo.fs
require ../../lib/frame.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../meta-tactic/goal.fs
require ../congr-thms.fs
require ../telescope.fs
require ./types.fs
require ./theorems.fs
require ./rewrite.fs

100000 constant lf-simp-max-steps
384 constant sm-depth-max

begin-structure /sm  field: sm-steps  field: sm-max  end-structure
/sm context-record: sm
/memo context-record: sm-cache
:noname ( -- ) sm-cache memo-free ; context-teardown
' frame-return context-frames: sm-frames   \ its visitor: frame-open never runs it
begin-structure /sa
  field: sa-e   \ the visit's term: simpLoop's e, or the application
  field: sa-h   \ a proof kept across a child's visit
  field: sa-n   \ the application's arguments
  field: sa-i   \ its next argument
  2 cells +field sa-r   \ the result so far ( e h ), a pair
  2 cells +field sa-scope   \ a binder visit's view and term mark on entry
  field: sa-xs   \ and its first variable's place in sm-xs
end-structure
/sa context-slab: sm-acts
1 cells context-slab: sm-xs   \ the binder visits' free variables, oldest first
: sa ( -- addr ) sm-acts slab-last ;
: sm-push ( e -- ) 1 sm-acts slab-claim lf-must drop sa dup /sa erase sa-e ! ;
: sm-pop ( -- ) sm-acts slab-drop ;
: lf-simp-steps ( -- n ) sm sm-steps @ ;

\ ---- Visits: opened with their continuation (frame-open), refused as
\ the frames refuse (fuel, room) or beyond sm-depth-max.
: sm-open ( x frames cont xt -- x frames xt )
  >r over frame-admit lf-must over frame-depth @ sm-depth-max > if lf-unported then
  r> frame-open ;
: sm-call ( x cont xt -- x frames xt ) >r >r sm-frames r> r> sm-open ;
: sm-done ( e h -- e h frames 0 ) sm-frames 0 ;

\ ---- The cache and the steps (Main.lean:672-686).
: sm-cached ( e -- e' h true | e false )
  dup 0 sm-cache memo-at ?dup if nip 2@ true else false then ;
: sm-remember ( e' h e -- e' h ) >r 2dup r> 0 sm-cache memo-claim lf-must 2! ;
: sm-count ( -- ) sm sm-steps @ sm sm-max @ > if lf-unported then 1 sm sm-steps +! ;
: sm-act-e ( -- e ) sa sa-e @ ;
: sm-i ( -- i ) sa sa-i @ ;   : sm-n ( -- n ) sa sa-n @ ;
: sm-finish ( e' h -- e' h frames 0 ) sm-act-e sm-remember sm-pop sm-done ;

\ ---- reduceStep (Main.lean:213): the steps not ported refused.
: sm-head-decl ( e -- d true | false )
  lf-meta-head dup lf-term-const? if lf-const-name lf-menv-find? else drop false then ;
: sm-kind-iota? ( d -- flag )
  lf-menv-kind dup lf-kind-recursor = swap lf-kind-quotient = or ;
: sm-decl-iota? ( d -- flag )   \ reduceRecMatcher? may fire
  dup sm-kind-iota? if drop true exit then
  dup lf-menv-matcher? lf-must if drop true exit then lf-menv-aux-recursor? lf-must ;
: sm-struct-proj? ( d -- flag )   \ reduceProjFn? unfolds a structure's
  dup lf-menv-proj-fn? lf-must if lf-menv-proj-class? lf-must 0= else drop false then ;
: sm-iota-check ( app? d -- ) swap if sm-decl-iota? if lf-unported then else drop then ;
: sm-head-check ( e -- )
  dup lf-term-app? swap sm-head-decl 0= if drop exit then
  dup sm-struct-proj? if lf-unported then sm-iota-check ;
\ zeta, proj, mdata and foldRawNatLit's nodes.
lf-tag-let lf-tag-let-nondep lf-tag-projection lf-tag-annotation lf-tag-lit 5 lf-tags
  constant sm-odd-tags
: sm-odd-tag? ( tag -- flag ) sm-odd-tags lf-tag-in? ;
: sm-reduce-step ( e -- e' )
  dup lf-meta-head dup lf-mvar? if drop lf-instantiate! exit then
  lf-term-lam? if lf-meta-head-beta lf-must exit then
  dup lf-term-tag@ sm-odd-tag? if lf-unported then dup sm-head-check ;

\ ---- isOfNatNatLit, isOfScientificLit, isCharLit (Main.lean:39-64).
: sm-raw? ( e -- flag ) lf-tag-lit lf-term-tag? ;
: sm-of-nat? ( e -- flag )
  dup lf-meta-head-args >r s" OfNat.ofNat" lf-meta-const-named? r@ 3 = and
  if 1 r> lf-meta-nth-arg sm-raw? else r> 2drop false then ;
: sm-char? ( e -- flag )
  dup 1 s" Char.ofNat" lf-meta-app-of? if lf-term-second@ sm-raw? else drop false then ;
: sm-scientific? ( e -- flag )
  dup 5 s" OfScientific.ofScientific" lf-meta-app-of? 0= if drop false exit then
  dup lf-term-second@ sm-raw? swap 2 5 lf-meta-nth-arg sm-raw? and ;
: sm-literal? ( e -- flag )
  dup sm-of-nat? if drop true exit then
  dup sm-char? if drop true exit then sm-scientific? ;

\ ---- The dsimp guard.
: sm-plain-const? ( c -- flag ) lf-const-name lf-menv-find lf-must sm-struct-proj? 0= ;
: sm-stable-node? ( a -- flag )
  dup lf-sort? if drop true exit then
  dup lf-term-tag@ case lf-tag-constant of sm-plain-const? endof
    lf-tag-fvar of lf-fvar-let? 0= endof nip false swap endcase ;
: sm-rfl-free? ( a -- flag )
  dup lf-simp-pre lf-simp-rfl-match? swap lf-simp-post lf-simp-rfl-match? or 0= ;
: sm-kept? ( a -- flag ) dup sm-stable-node? 0= if drop false exit then sm-rfl-free? ;
: sm-dsimp ( a -- a ) dup sm-kept? 0= if lf-unported then ;

\ ---- simpAppUsingCongr (Types.lean:732): the head, then each argument.
0 constant sm-way-simp   1 constant sm-way-inst   2 constant sm-way-dsimp
: sm-prefix ( -- p ) sm-act-e sm-n sm-i - 1- lf-term-fns ;
: sm-arg ( -- a ) sm-prefix lf-term-second@ ;
: sm-fr! ( e h -- ) sa sa-r 2! ;
: sm-fr@ ( -- e h ) sa sa-r 2@ ;
: sm-next ( e h -- ) sm-fr! 1 sa sa-i +! ;
: sm-arrow? ( -- flag ) sm-prefix lf-term-first@ lf-infer! lf-whnf-d! lf-arrow? ;
: sm-dep-way ( -- way ) sm-arrow? 0= sm-way-dsimp and ;   \ sm-way-simp is 0
: sm-info ( -- m ) sm-act-e lf-meta-head sm-n lf-meta-fun-deps lf-must ;
: sm-way ( -- way )
  sm-info sm-i > 0= if sm-dep-way exit then
  sm-i lf-param-instance? lf-must if sm-way-inst exit then
  sm-i lf-param-fwd-deps? if sm-dep-way else sm-way-simp then ;
: sm-fun-only ( a -- ) >r sm-prefix sm-fr@ r> lf-simp-congr-fun sm-next ;
: sm-more? ( -- flag ) sm-i sm-n < ;
defer sm-simp-arg ( a -- a frames xt )
: sm-kept ( way -- ) sm-arg swap sm-way-dsimp = if sm-dsimp then sm-fun-only ;
: sm-app-args ( -- ... frames next )
  begin sm-more? while sm-way dup sm-way-simp = if drop sm-arg sm-simp-arg exit then
  sm-kept repeat sm-fr@ sm-pop sm-done ;
: sm-app-simped ( ae ah frames -- ... )
  drop 2>r sm-prefix sm-fr@ 2r> lf-simp-congr sm-next sm-app-args ;
: sm-app-head ( fe fh frames -- ... ) drop sm-fr! sm-app-args ;

\ ---- The visits: simpImpl, simpLoop, simpStep.
defer sm-simp-call ( e cont -- e frames xt )
: sm-app-open ( e -- ... )
  dup sm-push dup lf-meta-args# sa sa-n ! lf-meta-head ['] sm-app-head sm-simp-call ;
\ congr (Main.lean:637): simp/congr.fs's (simp/goal.fs loads it), else
\ unsupported.
defer sm-congr ( e -- ... )
' lf-unported is sm-congr
: sm-app ( e -- ... ) dup sm-literal? if lf-simp-none sm-done exit then sm-congr ;
lf-tag-sort lf-tag-symbolic-sort lf-tag-lit lf-tag-str 4 lf-tags constant sm-plain-tags
: sm-fvar ( e -- e ) dup lf-fvar-let? if lf-unported then ;
: sm-leaf-of ( e tag -- e' )
  case lf-tag-constant of sm-reduce-step endof   lf-tag-mvar of lf-instantiate! endof
    lf-tag-fvar of sm-fvar endof   dup sm-plain-tags lf-tag-in? 0= if lf-unported then
  endcase ;
: sm-leaf ( e -- e h ) dup lf-term-tag@ sm-leaf-of lf-simp-none ;

\ ---- Binders (Main.lean:257-412): simpLambda, simpForall, simpArrow
\ without +contextual, where withNewLemmas runs its body as it is (simp
\ only's discharger is well behaved, Rewrite.lean:662). A binder visit
\ opens its variables on the view (lf-binder-local), keeps the view and
\ the term mark of its entry in its activation and puts them back when
\ it returns; a throw leaves them to lf-simp's lf-with-new-locals.
: sm-scope ( -- ) lf-locals-mark sa sa-scope 2! sm-xs slab-count sa sa-xs ! ;
: sm-unscope ( -- ) sa sa-scope 2@ lf-locals-back sa sa-xs @ sm-xs slab-cut ;
: sm-xs-n ( -- addr n ) sa sa-xs @ dup sm-xs slab-at swap sm-xs slab-since ;
\ withLocalDecl: a local of type dom on sm-xs, pi's body opened with it.
: sm-local ( pi dom -- body )
  over swap lf-binder-local dup sm-xs slab-push lf-must lf-meta-open lf-must ;
: sm-bind ( pi -- body ) dup lf-term-first@ sm-dsimp sm-local ;   \ the domain dsimp'd
: sm-binder-done ( e' h -- e' h frames 0 ) sm-unscope sm-pop sm-done ;
\ mkAppM c (fun x => h): funext, forall_congr.
: sm-under ( h addr c-addr u -- h' ) 2>r 1 lf-mk-lambda-fvars 2r> rot 1 lf-mk-app-m ;
\ simpLambda: lambdaTelescopeDSimp, the body, Result.addLambdas
\ (Types.lean:942: funext per variable, the newest first; a lambda opens
\ one at least).
: sm-funexts ( h -- h' )
  sa sa-xs @ sm-xs slab-count 1- do i sm-xs slab-at s" funext" sm-under -1 +loop ;
: sm-lam-done ( e' h frames -- ... )
  drop dup lf-simp-none? 0= if sm-funexts then
  swap sm-xs-n lf-mk-lambda-fvars swap sm-binder-done ;
: sm-lam ( e -- ... )
  dup sm-push sm-scope begin dup lf-term-lam? while sm-bind repeat
  ['] sm-lam-done sm-simp-call ;
\ simpForall's body under x (Main.lean:403), mkForallCongr. A domain
\ that is a proposition is simplified first (377); its proof would take
\ forall_prop_domain_congr, not ported (unsupported).
: sm-forall-done ( e' h frames -- ... )
  drop swap sm-xs-n lf-mk-forall-fvars swap
  dup lf-simp-none? 0= if sm-xs-n drop s" forall_congr" sm-under then sm-binder-done ;
: sm-forall-open ( e -- ... )
  dup sm-push sm-scope sm-bind ['] sm-forall-done sm-simp-call ;
: sm-domain ( e cont -- ... ) >r dup sm-push lf-term-first@ r> sm-simp-call ;
: sm-dom-done ( d' h frames -- ... )
  drop lf-simp-none? 0= if lf-unported then drop sm-act-e sm-pop sm-forall-open ;
: sm-prop-dom ( e -- ... ) ['] sm-dom-done sm-domain ;
\ simpArrow (333, 363): both sides, then mkImpCongr (Types.lean:616): the
\ pi updated (its binder kept), implies_congr when a side has a proof.
: sm-imp-e ( q' -- e' ) sm-fr@ drop swap sm-act-e lf-meta-rebuilt lf-must ;
: sm-imp-h ( q' hq -- h )
  lf-simp-proof >r s" implies_congr" sm-fr@ lf-simp-proof r> 2 lf-mk-app-m ;
: sm-imp-none? ( hq -- flag ) lf-simp-none? sm-fr@ nip lf-simp-none? and ;
: sm-arrow-done ( q' hq frames -- ... )
  drop over sm-imp-e -rot dup sm-imp-none? if 2drop lf-simp-none else sm-imp-h then
  sm-pop sm-done ;
: sm-arrow-dom ( p' hp frames -- ... )
  drop sm-fr! sm-act-e lf-term-second@ ['] sm-arrow-done sm-simp-call ;
: sm-arrow ( e -- ... ) ['] sm-arrow-dom sm-domain ;
: sm-prop? ( e -- flag ) lf-meta-is-prop lf-must ;
: sm-pi ( e -- ... )   \ simpForall; no proposition: dsimp e
  dup lf-arrow? if sm-arrow exit then
  dup sm-prop? 0= if sm-dsimp lf-simp-none sm-done exit then
  dup lf-term-first@ sm-prop? if sm-prop-dom exit then sm-forall-open ;
: sm-step ( e frames -- ... )
  drop dup lf-term-app? if sm-app exit then
  dup lf-term-lam? if sm-lam exit then
  dup lf-term-pi? if sm-pi exit then sm-leaf sm-done ;
defer sm-loop-call ( e cont -- e frames xt )
: sm-joined-h ( e2 h2 frames -- e h ) drop sa sa-h @ -rot lf-simp-trans ;
: sm-trans-cache ( e2 h2 frames -- ... ) sm-joined-h sm-finish ;
: sm-again ( e h -- ... ) sa sa-h ! ['] sm-trans-cache sm-loop-call ;
: sm-post-continue ( e3 h3 -- ... )
  over sm-act-e lf-eqv! if sm-finish else sm-again then ;
: sm-joined ( e2 h2 e3 h3 -- e3 h ) 2>r nip 2r> lf-simp-trans ;
: sm-post ( e2 h2 -- ... )
  over lf-simp-post false lf-simp-rewrite? if sm-joined then sm-post-continue ;
: sm-stepped ( e2 h2 frames -- ... ) sm-joined-h sm-post ;
: sm-step-call ( e -- e frames xt ) ['] sm-stepped ['] sm-step sm-call ;
: sm-pre-continue ( e1 h1 -- ... )
  sa sa-h ! dup sm-reduce-step 2dup lf-eqv!
  if drop sm-step-call else nip ['] sm-trans-cache sm-loop-call then ;
: sm-pre ( e -- e1 h1 true | e false )
  dup lf-simp-pre false lf-simp-rewrite? if rot drop true else false then ;
: sm-loop ( e frames -- ... )
  drop sm-cached if sm-done exit then
  sm-count dup sm-push sm-pre if sm-again else lf-simp-none sm-pre-continue then ;
:noname ( e cont -- e frames xt ) ['] sm-loop sm-call ; is sm-loop-call
: sm-proof? ( e -- flag )
  dup lf-meta-proof-quick lf-must dup lf-lb-undef =
  if drop lf-infer! lf-meta-is-prop lf-must else nip lf-lb-true = then ;
: sm-simp ( e frames -- ... )
  drop dup sm-proof? if lf-simp-none sm-done exit then ['] frame-return sm-loop-call ;
:noname ( e cont -- e frames xt ) ['] sm-simp sm-call ; is sm-simp-call
:noname ( a -- a frames xt ) ['] sm-app-simped sm-simp-call ; is sm-simp-arg

\ ---- Simp.main: the run.
: sm-cache-ready ( -- )
  sm-cache memo-live? if sm-cache memo-clear else 1 2 sm-cache memo-init lf-must then ;
: sm-ready ( max -- )
  sm-frames frame-busy? if lf-unported then
  sm sm-max ! 0 sm sm-steps ! sm-acts slab-clear sm-xs slab-clear sm-cache-ready
  sm-frames frame-reset max-n sm-frames frame-budget drop ;
: sm-root ( e frames cont -- e frames xt ) nip sm-simp-call ;
: sm-walk ( e -- e' h ) sm-frames ['] sm-root frame-through drop ;
: sm-scoped ( e -- e' h true ) ['] sm-walk lf-with-new-locals true ;
\ A throw rolls back to the mark before the walk: the metavariable depths
\ its congruence lemmas opened (simp/congr.fs) close with it.
: sm-marked ( e -- e' h ) ['] sm-scoped lf-commit-when drop ;
: sm-guarded ( e -- e' h )
  ['] sm-marked catch ?dup if sm-frames frame-reset sm-acts slab-clear throw then ;
: lf-simp ( e max -- e' h )
  sm-ready ['] sm-guarded lf-defeq-flags lf-defeq-elab or lf-tr-reducible lf-meta-with ;

\ ---- simpTargetCore (Main.lean:781) and applySimpResultToTarget.
: sm-true? ( e -- flag ) s" True" lf-meta-const-named? ;
: sm-close ( goal h -- 0 )
  dup lf-simp-none? if drop s" True.intro" lf-mk-const0 else lf-mk-of-eq-true then
  lf-mvar-assign lf-must 0 ;
: sm-target-done ( goal target e' h -- goal' | 0 )
  over sm-true? if nip nip sm-close exit then
  dup lf-simp-none? 0= if rot drop lf-goal-replace-target-eq exit then
  drop tuck lf-eqv! if drop else lf-goal-replace-target-defeq then ;
: sm-target ( goal max -- goal' | 0 )
  >r dup lf-goal-type lf-instantiate! dup r> lf-simp sm-target-done ;
: lf-goal-simp-target ( goal max -- goal' | 0 ) over ['] sm-target lf-with-goal ;

base !   \ the BASE this file was loaded with
