\ Simp's congruence (plan row FE9, simp slice SL2 of
\ docs/design/TACTIC_SIMP.md): Lean 4.35.0's congr, congrDefault,
\ trySimpCongrTheorem?, processCongrHypothesis and visitFn
\ (src/lean/Lean/Meta/Tactic/Simp/Main.lean:531-648) and
\ tryAutoCongrTheorem? (Types.lean:807), as further visits of
\ simp/main.fs's walk, which they plug into (its hook sm-congr).
\ - congr: an application whose head is a constant with @[congr] lemmas
\   (simp-data.fs's simp-congr-lemmas, in Lean's order) tries each in
\   turn; the first that answers is the result; none, congrDefault.
\ - trySimpCongrTheorem?, one metavariable depth deeper (withNewMCtxDepth,
\   held across the visits and closed, everything in it rolled back, when
\   the lemma answers or fails; the result instantiated before): the
\   lemma at fresh levels, its type's forallMetaTelescopeReducing; its
\   left side unified with the application (mkMetaConfig); then each
\   hypothesis (processCongrHypothesis): its type's binders opened as
\   locals, the left side of its equation simplified, the right side's
\   head unified with that result abstracted over the right side's
\   arguments, and the hypothesis with the proof abstracted over the
\   locals; "modified" when a result has a proof, or below a binder
\   differs; none unmodified; then synthesizeArgs (rewrite.fs's
\   lf-simp-synthesize), and the right side and the proof instantiated,
\   none when either keeps an assignable metavariable. Not supported
\   yet: an Iff lemma or hypothesis (propext, mkIffOfEq), more arguments
\   than the lemma's left side takes (congrArgs), binderNameHint.
\ - congrDefault: when the kinds (congr-thms.fs) are all fixed or eq, or
\   their number is not the application's, simpAppUsingCongr (main.fs);
\   else tryAutoCongrTheorem?: an eq argument simplified, a fixed one
\   dsimp'd (main.fs's guard), a cast or subsingleton instance kept;
\   nothing changed, the application as it is; no proof and no cast, the
\   head over the new arguments; else the automatic theorem's proof
\   (Types.lean:868-905): the library's realized theorem f.congr_simp
\   at f's levels (format 4.1's records, simp-data.fs's simp-realized;
\   mkCongrSimpForConst?, used when its kinds are the computed ones),
\   applied to each argument as its kind asks: fixed and cast the
\   argument, eq the argument, its new value and its proof (Eq.refl
\   when none), subsingletonInst the argument and the new instance (the
\   old one when its type is the new class, else trySynthInstance's);
\   the result the theorem's right side. Not supported yet: a head that
\   is no constant or has no realized theorem (Lean's mkCongrSimpCore?,
\   or the theorem realized in the user's file), kinds other than the
\   theorem's, a cast argument (removeUnnecessaryCasts), an instance not
\   found (Lean then takes congrArgs). Lean builds the theorem before
\   the arguments are visited and, when it cannot, retries with cast and
\   subsingleton kinds fixed; LeanForth assumes the first build
\   succeeds (both kinds leave a proof or an instance as it is). Then
\   visitFn: the head simplified, and the result's proof extended
\   through it (Result.mkEqTrans).
\ Throws as meta-must.fs's words do; a throw leaves the depth and the
\ locals to lf-simp's mark and lf-with-new-locals. Untrusted: the kernel
\ checks every proof. State: the slabs sc-acts (a lemma attempt's
\ record per visit open) and sc-args (an automatic congruence's
\ arguments), in the checker context; the lemma's metavariables and a
\ hypothesis's locals on main.fs's sm-xs.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/context.fs
require ../../lib/find.fs
require ../../core/terms.fs
require ../congr-thms.fs
require ../synth.fs
require ../app-builder.fs
require ../simp-data.fs
require ../telescope.fs
require ./types.fs
require ./rewrite.fs
require ./main.fs

\ ---- tryAutoCongrTheorem?: per argument its kind, new argument and
\ proof; the flags simplified, hasProof, hasCast in the activation's sa-h.
begin-structure /sca
  field: sca-kind          \ the argument's kind (congr-thms.fs)
  2 cells +field sca-r     \ its result ( a h ), a pair: h lf-simp-none or a proof
end-structure
/sca context-slab: sc-args
1 constant sc-simplified   2 constant sc-has-proof   4 constant sc-has-cast
: sa-flags ( a -- a' ) sa-h ;   \ the activation's proof cell, a bit set here
: sc-flag! ( bit -- ) sa sa-flags @ or sa sa-flags ! ;
: sc-flag? ( bit -- flag ) sa sa-flags @ and 0<> ;
: sc-arg ( i -- addr ) sa sa-xs @ + sc-args slab-at ;
: sc-result! ( a h i -- ) sc-arg sca-r 2! ;
: sc-claim ( kind a -- )
  1 sc-args slab-claim lf-must sc-args slab-at >r lf-simp-none r@ sca-r 2! r> sca-kind ! ;
: sc-fill ( -- )
  sc-args slab-count sa sa-xs !
  sm-n 0 ?do i lf-congr-kind sm-act-e sm-n i lf-term-arg sc-claim loop ;
: sc-kind ( i -- kind ) sc-arg sca-kind @ ;
: sc-new ( i -- a ) sc-arg sca-r 2@ drop ;
: sc-head-over ( -- e ) sm-act-e lf-meta-head sm-n 0 ?do i sc-new lf-mk-app loop ;
: sc-cut ( -- ) sa sa-xs @ sc-args slab-cut ;

\ visitFn (531) of r1 = ( e1 h1 ), kept in sa-r: the head simplified; a
\ new head applied to e1's arguments (congrFun per argument with a proof).
: sc-e1 ( -- e1 ) sm-fr@ drop ;
: sc-fn-result ( f' hf -- e2 h2 )
  over sc-e1 lf-meta-head lf-eqv! if 2drop sc-e1 lf-simp-none exit then
  2>r sc-e1 dup lf-meta-args# 2r> lf-simp-extra-args ;
: sc-fn-done ( f' hf frames -- ... )
  drop sc-fn-result sm-fr@ nip -rot lf-simp-trans sc-cut sm-pop sm-done ;
: sc-visit-fn ( e1 h1 -- ... ) sm-fr! sc-e1 lf-meta-head ['] sc-fn-done sm-simp-call ;
\ The automatic theorem's proof, its values pushed on sm-xs from base.
: sc-v+ ( x -- ) sm-xs slab-push lf-must ;
: sc-vals ( base -- addr n ) dup sm-xs slab-at swap sm-xs slab-since ;
: sc-old ( i -- a ) >r sm-act-e sm-n r> lf-term-arg ;
: sc-kind<> ( addr i -- addr flag ) 2dup cells + @ swap sc-kind <> ;
: sc-kinds= ( addr n -- flag )
  dup sm-n <> if 2drop false exit then
  ['] sc-kind<> find-index dup if nip then 0= ;
: sc-head ( -- f ) sm-act-e lf-meta-head ;
\ mkCongrSimpForConst?: f.congr_simp, when the library realized it with
\ the kinds computed.
: sc-realized ( -- r )
  sc-head dup lf-term-const? 0= if lf-unported then lf-const-name lf-menv-data-decl
  0= if lf-unported then simp-realized lf-must 0= if lf-unported then ;
: sc-thm-of ( r -- c )
  dup simp-realized-kinds sc-kinds= 0= if lf-unported then simp-realized@
  lf-menv-of-data lf-must lf-menv-name sc-head lf-const-levels lf-mk-const-id ;
: sc-eq-vals ( i -- )
  dup sc-old dup sc-v+ swap sc-arg sca-r 2@ over sc-v+ lf-simp-proof' sc-v+ ;
\ subsingletonInst: the class the theorem's next binder asks for, the
\ values so far in place.
: sc-cls ( base type -- base type cls )
  2dup swap sc-vals lf-meta-instantiate-forall lf-must lf-term-first@ ;
: sc-new-inst ( old cls -- inst )
  over lf-infer! over lf-defeq! if drop exit then
  nip lf-try-synth lf-must lf-synth-some <> if lf-unported then ;
: sc-sub-vals ( base type i -- base type )
  sc-old dup sc-v+ >r sc-cls r> swap sc-new-inst sc-v+ ;
: sc-arg-val ( base type i -- base type )
  dup sc-kind case lf-ck-eq of sc-eq-vals endof   lf-ck-subsingleton of sc-sub-vals endof
    swap sc-old sc-v+ endcase ;
: sc-vals-all ( base type -- base type ) sm-n 0 ?do i sc-arg-val loop ;
: sc-rhs ( base type -- e )
  swap sc-vals lf-meta-instantiate-forall lf-must lf-simp-sides nip ;
: sc-auto-rhs ( base c -- e ) lf-infer! sc-vals-all sc-rhs ;
: sc-applied ( base c -- p ) over sc-vals lf-mk-app-cells swap sm-xs slab-cut ;
: sc-auto-proof ( -- e' h )
  sm-xs slab-count sc-realized sc-thm-of 2dup sc-auto-rhs -rot sc-applied ;
: sc-auto-finish ( -- ... )
  sc-simplified sc-flag? 0= if sm-act-e lf-simp-none sc-visit-fn exit then
  sc-has-cast sc-flag? if lf-unported then
  sc-has-proof sc-flag? if sc-auto-proof sc-visit-fn exit then
  sc-head-over lf-simp-none sc-visit-fn ;
defer sc-auto-args ( -- ... )
: sc-eq-done ( a' h frames -- ... )
  drop dup lf-simp-none? 0= if sc-has-proof sc-flag! then
  over sm-arg lf-eqv! 0= if sc-simplified sc-flag! then
  sm-i sc-result! 1 sa sa-i +! sc-auto-args ;
: sc-kept ( kind -- )
  dup lf-ck-cast = if sc-has-cast sc-flag! then
  lf-ck-fixed = if sm-arg sm-dsimp drop then 1 sa sa-i +! ;
:noname ( -- ... )
  begin sm-more? while sm-i sc-kind dup lf-ck-eq = if drop sm-arg ['] sc-eq-done
  sm-simp-call exit then sc-kept repeat sc-auto-finish ; is sc-auto-args
: sc-auto ( e -- ... )
  dup sm-push lf-meta-args# sa sa-n ! 0 sa sa-h ! sc-fill sc-auto-args ;

\ ---- congrDefault (545).
: sc-kinds? ( e -- plain? ) dup lf-meta-head lf-congr-simp-kinds lf-must
  dup lf-congr-plain? swap rot lf-meta-args# <> or ;
: sc-default ( e -- ... ) dup sc-kinds? if sm-app-open else sc-auto then ;

\ ---- trySimpCongrTheorem? (586): a record per attempt.
begin-structure /sc
  field: sc-c        \ the lemma's record (simp-data.fs)
  field: sc-end      \ past the function's last record
  field: sc-scope    \ the depth's scope (lf-mctx-depth{)
  field: sc-thm      \ the lemma's constant at fresh levels
  field: sc-type     \ its conclusion, an Eq
  field: sc-k        \ the next hypothesis, an index of the record's places
  field: sc-mod      \ modified
  field: sc-dead     \ the left side or a hypothesis failed: none
  field: sc-hxs      \ the hypothesis's locals' place in sm-xs
  field: sc-htype    \ its equation, below them
  field: sc-lhs      \ its left side, instantiated
end-structure
/sc context-slab: sc-acts
: sc ( -- addr ) sc-acts slab-last ;
: sc-push ( c n -- ) 1 sc-acts slab-claim lf-must drop sc dup /sc erase
  >r over + r@ sc-end ! r> sc-c ! ;
: sc-pop ( -- ) sc-acts slab-drop ;
: sc-reset ( -- ) 0 sc sc-k ! false sc sc-mod ! false sc sc-dead ! ;
: sc-refuse ( flag -- ) outcome-unsupported and lf-must ;   \ not supported yet when flag
: sc-mvars ( -- addr n ) sa sa-xs @ dup sm-xs slab-at swap sc sc-hxs @ swap - ;
: sc-new-x ( acc mvar kind -- acc ) drop sm-xs slab-push lf-must ;
: sc-hyps ( -- addr n ) sc sc-c @ simp-congr-hyps ;
: sc-decl ( -- d ) sc sc-c @ simp-congr@ drop lf-menv-of-data lf-must ;
\ The attempt's scope: the depth, and the metavariables' place.
: sc-open ( -- )
  false lf-mctx-depth{ lf-must sc sc-scope ! sm-xs slab-count dup sa sa-xs ! sc sc-hxs ! ;
: sc-close ( -- ) sc sc-scope @ }lf-mctx-depth lf-must sa sa-xs @ sm-xs slab-cut ;
: sc-telescope ( -- )
  sc-decl dup lf-meta-const-fresh lf-must dup sc sc-thm ! lf-infer!
  dup sr-hint? sc-refuse 0 swap rot ['] sc-new-x
  lf-forall-meta-telescope-reducing nip sm-xs slab-count sc sc-hxs ! sc sc-type ! ;
: sc-sides ( -- lhs rhs ) sc sc-type @ lf-simp-sides ;
\ An Iff, or more arguments than the left side takes: not supported yet.
\ (Every hypothesis's place is among the binders: the data's check,
\ error 37, simp-data.fs.)
: sc-shape ( -- )
  sc sc-type @ lf-eq-app? 0= sc-refuse
  sc-sides drop lf-meta-args# sm-act-e lf-meta-args# <> sc-refuse ;
: sc-unifies? ( -- flag ) sc-sides drop sm-act-e ['] lf-defeq! lf-with-simp-meta ;

\ processCongrHypothesis (552): the binders of the hypothesis's type
\ opened as locals (forallTelescopeReducing, the transparency in force),
\ its equation's left side simplified; then the right side's head (its
\ arguments, Lean's zs, not supported yet) unified with the result, and
\ the hypothesis with the proof over the locals.
: sc-h ( -- mvar ) sc-hyps drop sc sc-k @ cells + @ sa sa-xs @ + sm-xs slab-at @ ;
: sc-open-pi ( pi -- body ) dup lf-term-first@ sm-local ;
: sc-reduced ( t -- t' pi? )
  dup lf-whnf! dup lf-term-pi? if nip true else drop false then ;
: sc-forall ( t -- body )
  begin dup lf-term-pi? if sc-open-pi true else sc-reduced then 0= until ;
: sc-hxs-n ( -- addr n ) sc sc-hxs @ dup sm-xs slab-at swap sm-xs slab-since ;
: sc-m ( -- m ) sc sc-htype @ lf-simp-sides nip lf-meta-head-args 0<> sc-refuse ;
: sc-m-ok? ( e' -- flag ) sc-m swap ['] lf-defeq! lf-with-simp-meta ;
: sc-h-ok? ( e' h -- flag )
  lf-simp-proof sc-hxs-n lf-mk-lambda-fvars sc-h swap lf-defeq! ;
: sc-assigned? ( e' h -- e' h flag ) over sc-m-ok? dup if drop 2dup sc-h-ok? then ;
: sc-modified? ( e' h -- flag )
  lf-simp-none? 0= swap sc sc-lhs @ lf-eqv! 0= sc-hxs-n nip 0> and or ;
\ A failed hypothesis ends the walk of the hypotheses (Lean's throw,
\ caught as none); dead or not modified, the lemma answers none.
: sc-alive ( ok -- ) 0= sc sc-dead @ or sc sc-dead ! ;
: sc-mod-or ( flag -- ) sc sc-mod @ or sc sc-mod ! ;
: sc-live? ( -- flag ) sc sc-mod @ sc sc-dead @ 0= and ;
: sc-hyp-close ( -- ) sa sa-scope 2@ lf-locals-back sc sc-hxs @ sm-xs slab-cut ;
: sc-hyp-open ( -- ... )
  lf-locals-mark sa sa-scope 2! sc-h lf-infer! lf-instantiate! sc-forall dup sc sc-htype !
  lf-simp-sides drop lf-instantiate! dup sc sc-lhs ! ;

\ The lemma's end: its result, or none and the next lemma (the
\ function's last tried, congrDefault).
defer sc-try ( -- ... )
: sc-fail ( -- ... ) sc-close 1 sc sc-c +! sc-try ;
: sc-proof ( -- p ) sc sc-thm @ sc-mvars lf-mk-app-cells ;
: sc-result ( -- e' h ) sc-sides nip lf-instantiate! sc-proof lf-instantiate! ;
: sc-closed? ( e' h -- flag ) lf-meta-has-assignable? swap lf-meta-has-assignable? or 0= ;
: sc-answer ( -- e' h true | x x false )
  sc-live? if sc-mvars lf-simp-synthesize sc-result 2dup sc-closed? else 0 0 false then ;
: sc-hyps-done ( -- ... )
  sc-answer if sc-close sc-pop sm-pop sm-done else 2drop sc-fail then ;
defer sc-next-hyp ( -- ... )
: sc-hyp-done ( e' h frames -- ... )
  drop sc-assigned? sc-alive sc-modified? sc-mod-or sc-hyp-close
  1 sc sc-k +! sc-next-hyp ;
: sc-more-hyps? ( -- flag ) sc sc-k @ sc-hyps nip < sc sc-dead @ 0= and ;
:noname ( -- ... )
  sc-more-hyps? 0= if sc-hyps-done exit then
  sc-hyp-open ['] sc-hyp-done sm-simp-call ; is sc-next-hyp
:noname ( -- ... )
  sc sc-c @ sc sc-end @ < 0= if sc-pop sm-act-e sm-pop sc-default exit then
  sc-reset sc-open sc-telescope sc-shape sc-unifies? sc-alive sc-next-hyp ; is sc-try

\ ---- congr (637), simp/main.fs's sm-congr once this file is loaded:
\ f's @[congr] lemmas, records c .. c+n-1 (n = 0: none, also for a
\ constant the data does not hold, such as a text declaration).
: sc-congr-run ( f -- c n )
  dup lf-term-const? 0= if drop 0 0 exit then
  lf-const-name lf-menv-data-decl if simp-congr-lemmas lf-must else 0 0 then ;
: sc-lemmas ( e c n -- ... ) rot sm-push sc-push sc-try ;
: sc-congr ( e -- ... )
  dup lf-meta-head sc-congr-run ?dup if sc-lemmas else drop sc-default then ;
' sc-congr is sm-congr

base !   \ the BASE this file was loaded with
