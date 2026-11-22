\ Term builders of the tactic library (docs/design/TACTIC_PLUGINS.md 2.2;
\ plan slice a2-i): Lean 4.35.0's mkConst and mkAppN (Expr.lean) and
\ Meta/AppBuilder.lean, each word making the term the Lean function
\ makes, node for node. Every word throws on failure (meta-must.fs):
\ Lean's throwAppBuilderException and throwAppTypeMismatch as rejected,
\ a step not ported as unsupported, no room as full.
\ Public words (stack effect; the Lean function, AppBuilder.lean line):
\   lf-mk-const ( c-addr u l1..ln n -- e )  mkConst name [l1, ..., ln]
\   lf-mk-const0 ( c-addr u -- e ), lf-mk-const1 ( c-addr u l -- e )
\   lf-mk-const-id ( name l1..ln n -- e )  the same of a name ID
\       (Expr.constLevels! is core/constant-term-boundary.fs's lf-const-levels)
\   lf-mk-app ( f a -- e ), lf-mk-app-n ( f a1..an n -- e )  mkApp, mkAppN
\   lf-mk-eq ( a b -- e )                 mkEq (40)
\   lf-mk-eq-refl ( a -- h )              mkEqRefl (65)
\   lf-mk-eq-symm ( h -- h' )             mkEqSymm (98)
\   lf-mk-eq-trans ( h1 h2 -- h )         mkEqTrans (110)
\   lf-mk-expected-prop-hint ( h p -- h' ) mkExpectedPropHint (29)
\   lf-mk-expected-type-hint ( e type -- e' ) mkExpectedTypeHint (35):
\                                         id.{u} type e, u type's level
\   lf-mk-absurd ( e hp hnp -- e' )       mkAbsurd (77): absurd.{u} p e hp
\                                         hnp, p hp's type, u e's level
\   lf-mk-false-elim ( e h -- e' )        mkFalseElim (83): False.elim.{u} e h
\   lf-binder-named ( t name -- t )       a binder node t named name, of the
\                                         default kind (present/binder-table.fs;
\                                         see below: not for name 0 nor an input
\                                         node); assert.fs's pi
\   lf-mk-congr-arg ( f h -- h' )         mkCongrArg (212), with congrArg?
\                                         (199) fusing nested congrArg
\   lf-mk-app-m ( c-addr u x1..xn n -- e ) mkAppM (345), lf-mk-app-m-of
\                                         ( d x1..xn n -- e ) of a declaration
\   lf-mk-eq-mp ( h p -- e ), lf-mk-eq-mpr ( h p -- e )  mkEqMP, mkEqMPR
\                                         (444-447)
\   lf-mk-app-opt-m ( c-addr u x1..xn mask n -- e ) mkAppOptM (402): n
\                                         entries (at most abl-most - 1, the
\                                         mask stored beside them), entry i
\                                         some x(i+1) when bit i of mask is
\                                         set, else none (that cell ignored)
\   lf-mk-decide ( p -- e )               mkDecide (570): Decidable.decide p
\                                         with its instance synthesized
\   lf-eq? ( t -- α a b true | false )     Expr.eq?: Eq α a b's arguments
\   lf-match-eq? ( t -- α a b true | false ) matchEq? (MatchUtil.lean:28):
\                                         the same after whnf when t is no Eq
\   lf-match-not? ( t -- p true | false ), lf-match-ne? ( t -- α a b true
\       | false ), lf-match-heq? ( t -- α a β b true | false )  matchNot?,
\       matchNe?, matchHEq? (MatchUtil.lean:62, 71, 31): t, else t after
\       whnf, is Not p or p -> False; Ne α a b or a negated equation; HEq
\   lf-meta-has-mvar? ( e -- flag outcome ) Expr.hasMVar: a term or level
\                                         metavariable reached (core/reach.fs)
\ Levels pass on the stack (never through a global); at most abl-most
\ levels or arguments a call. AppBuilder's private infer is inferType then
\ whnfD. mkAppM walks the constant's type in a new metavariable depth
\ (withNewMCtxDepth): an implicit binder a natural metavariable, an
\ instance binder a synthetic one filled at the end by instance search
\ (synth.fs's lf-synth-instance!, through defeq.fs's lf-meta-synth hook;
\ none found: Lean's "failed to synthesize", error 122, thrown
\ rejected), an explicit one
\ the next argument, which isDefEq at default transparency at least must
\ fit (else rejected); whnfD where the type shows no pi (none: rejected,
\ too many arguments); the result instantiated must reach no assignable
\ metavariable (rejected) nor any other one (unsupported: the level
\ metavariables' assignability is not told apart). Binder kinds come
\ from telescope.fs's lf-binder-kind-at (the declaration's, until whnf).
\ mkAppOptM walks the same way, each binder taking the next entry: none a
\ new metavariable (synthetic for an instance binder, filled as
\ mkAppM's), some x, which plain isDefEq (the transparency in force) must
\ fit; entries left at a type whnfD makes no pi: rejected.
\ Not ported yet: mkCongr,
\ mkCongrFun, mkEqNDRec, mkOfEqTrue, mkEqTrue (the simp core, which
\ brings their first callers).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: abl-cells (one call's levels or arguments, read before any other
\ builder runs) and abm-frames (a frame per mkAppM open, meta-must.fs's
\ lf-with-record), in the checker
\ context (ADR 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/reach.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/tagged-sort-boundary.fs
require ../present/binder-table.fs
require ../author/declarations.fs
require ./mvars.fs
require ./meta-config.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./term-eqv.fs
require ./term-find.fs
require ./instantiate.fs
require ./meta-must.fs
require ./synth.fs
require ./telescope.fs

16 constant abl-most     \ levels or arguments a builder call takes
0 constant abl-level-zero   \ the zero level's node (core/levels.fs)
abl-most cells context-record: abl-cells
\ x1 .. xn kept in order (x1 first) in abl-cells.
: abl-stored ( x1..xn n -- addr n )
  dup abl-most u> if outcome-invalid lf-must then
  dup 0 ?do dup 1- i - cells abl-cells + rot swap ! loop abl-cells swap ;

\ ---- mkConst, mkApp, mkAppN.
: abl-const-at ( name addr n -- e )
  2>r lf-name-generation @ 2r> lf-meta-const-at lf-must ;
: lf-mk-const ( c-addr u l1..ln n -- e ) abl-stored 2>r lfa-intern 2r> abl-const-at ;
: lf-mk-const-id ( name l1..ln n -- e ) abl-stored abl-const-at ;
: lf-mk-const0 ( c-addr u -- e ) 0 lf-mk-const ;
: lf-mk-const1 ( c-addr u l -- e ) 1 lf-mk-const ;
: lf-mk-app ( f a -- e ) lf-term-app lf-made! ;
: abl-fold ( f addr n -- e ) 0 ?do dup i cells + @ >r swap r> lf-mk-app swap loop drop ;
: lf-mk-app-n ( f a1..an n -- e ) abl-stored abl-fold ;
: abl-app2 ( a b f -- e ) >r swap r> swap lf-mk-app swap lf-mk-app ;   \ mkApp2 f a b

\ ---- Shapes and AppBuilder's helpers.
: abl-fail ( -- ) outcome-rejected lf-must ;   \ throwAppBuilderException
: abl-decl ( c-addr u -- d ) lfa-intern lf-menv-find lf-must ;   \ getConstVal's
: abl-infer-d ( e -- type ) lf-infer! lf-whnf-d! ;
\ Expr.eq?: Eq α a b's three arguments.
: abl-eq-app? ( t -- flag ) 3 s" Eq" lf-meta-app-of? ;
: lf-eq? ( t -- α a b true | false )
  dup abl-eq-app? 0= if drop false exit then
  dup lf-term-second@ >r lf-term-first@ lf-meta-args2 r> true ;
: abl-eq ( t -- α a b ) lf-eq? 0= if abl-fail then ;
: abl-refl? ( h -- flag ) lf-meta-head s" Eq.refl" lf-meta-const-named? ;   \ isAppOf
: abl-refl-arg? ( h -- a true | h false )   \ isRefl?
  dup 2 s" Eq.refl" lf-meta-app-of? if lf-term-second@ true else false then ;
\ A constant at one level, by name ID; the constant at α's level
\ (getLevel α); c.{u} α a b for an Eq α a b.
: abl-const-named ( level name -- c )
  swap abl-cells ! lf-name-generation @ abl-cells 1 lf-meta-const-at lf-must ;
: abl-const-of ( α c-addr u -- c ) lfa-intern swap lf-level! swap abl-const-named ;
: abl-eq-app ( α a b c-addr u -- e )
  2>r rot dup 2r> abl-const-of swap lf-mk-app -rot 2 lf-mk-app-n ;
: abl-bvar0 ( -- e ) 0 lf-term-bvar lf-made! ;
\ Expr.beta f #[x]: a lambda's body opened with x, else f applied to x.
: abl-beta1 ( f x -- e ) over lf-term-lam? if lf-meta-open lf-must else lf-mk-app then ;
\ The binder's name and default kind in the presentation table. Not for
\ the anonymous name (0), and not for an input node (a node made with no
\ scratch tier open, as in a test over an export, keeps its binder in
\ its own record, which no builder writes): those stay unrecorded, and a
\ telescope refuses an unrecorded pi's kind (telescope.fs).
: lf-binder-named ( t name -- t )
  over lf-term-input? if drop exit then
  ?dup if over swap lf-binder-default lf-pres-binder! lf-must then ;
: abl-lam-x ( dom body -- e ) lf-term-lam lf-made! s" x" lfa-intern lf-binder-named ;

\ ---- mkEq, mkEqRefl, mkEqSymm, mkEqTrans, mkExpectedPropHint.
: abl-typed ( a c-addr u -- a c' )   \ c.{u} T, T a's type of level u
  2>r dup lf-infer! dup 2r> abl-const-of swap lf-mk-app ;
: lf-mk-eq ( a b -- e ) swap s" Eq" abl-typed swap lf-mk-app swap lf-mk-app ;
: lf-mk-eq-refl ( a -- h ) s" Eq.refl" abl-typed swap lf-mk-app ;
: lf-mk-eq-symm ( h -- h' )
  dup abl-refl? if exit then
  dup abl-infer-d abl-eq s" Eq.symm" abl-eq-app swap lf-mk-app ;
\ Eq.trans.{u} α a b c h1 h2.
: abl-trans ( h1 h2 α a b c -- h )
  >r s" Eq.trans" abl-eq-app r> lf-mk-app abl-app2 ;
: lf-mk-eq-trans ( h1 h2 -- h )
  over abl-refl? if nip exit then dup abl-refl? if drop exit then
  over abl-infer-d over abl-infer-d >r abl-eq r> abl-eq >r 2drop r> abl-trans ;
: lf-mk-expected-prop-hint ( h p -- h' )
  s" id" abl-level-zero lf-mk-const1 swap lf-mk-app swap lf-mk-app ;

\ ---- mkExpectedTypeHint (35), mkAbsurd (77), mkFalseElim (83): the
\ constant at the level of the type it proves (getLevel).
: lf-mk-expected-type-hint ( e type -- e' )
  dup s" id" abl-const-of swap lf-mk-app swap lf-mk-app ;
: lf-mk-false-elim ( e h -- e' )
  swap dup s" False.elim" abl-const-of swap lf-mk-app swap lf-mk-app ;
: abl-absurd ( e hp -- f )   \ absurd.{u} p e hp, p hp's type
  over s" absurd" abl-const-of over lf-infer! lf-mk-app rot lf-mk-app swap lf-mk-app ;
: lf-mk-absurd ( e hp hnp -- e' ) -rot abl-absurd swap lf-mk-app ;

\ ---- mkCongrArg (a loop: congrArg? fuses a nested congrArg).
\ congrArg?: congrArg's α, f and h; congrFun's made into one.
: abl-arg ( t i -- a ) 6 lf-meta-nth-arg ;
: abl-from-arg ( h -- α f h1 ) dup 0 abl-arg over 4 abl-arg rot 5 abl-arg ;
: abl-from-fun ( h -- α' f' h1 )   \ α' := ∀ x : α, β x; f' := fun f : α' => f a
  dup 0 abl-arg over 1 abl-arg abl-bvar0 abl-beta1 lf-term-pi lf-made! s" x" lfa-intern
  lf-binder-named over 5 abl-arg abl-bvar0 swap lf-mk-app over swap lf-term-lam lf-made!
  s" f" lfa-intern lf-binder-named rot 4 abl-arg ;
: abl-congr-arg? ( h -- α f h1 true | h false )
  dup 6 s" congrArg" lf-meta-app-of? if abl-from-arg true exit then
  dup 6 s" congrFun" lf-meta-app-of? if abl-from-fun true exit then false ;
\ fun x : α => f (f1 x), then mkCongrArg of it and h1.
: abl-fused ( f α f1 h1 -- f' h1 )
  >r abl-bvar0 abl-beta1 rot swap abl-beta1 abl-lam-x r> ;
\ fType.arrow?: a pi whose body has no loose bound variable.
: abl-arrow ( t -- α β )
  dup lf-term-pi? 0= if abl-fail then dup lf-term-second@ lf-meta-loose lf-must
  0> if abl-fail then dup lf-term-first@ swap lf-term-second@ ;
: abl-levels ( α β -- u v ) swap lf-level! swap lf-level! ;
: abl-congr-head ( α β -- c )   \ congrArg.{u, v} α β
  2dup abl-levels 2>r s" congrArg" 2r> 2 lf-mk-const -rot 2 lf-mk-app-n ;
\ (hType, then fType, inferred first, as Lean's; arrow? checked before eq?)
: abl-congr-plain ( f h -- h' )
  dup abl-infer-d >r over abl-infer-d abl-arrow abl-congr-head r> abl-eq >r nip r>
  2 lf-mk-app-n abl-app2 ;
: abl-congr-step ( f h -- f' h' true | h' false )
  abl-refl-arg? if lf-mk-app lf-mk-eq-refl false exit then
  abl-congr-arg? if abl-fused true exit then abl-congr-plain false ;
: lf-mk-congr-arg ( f h -- h' ) begin abl-congr-step 0= until ;


\ ---- Expr.hasMVar (core/reach.fs's tables, made for the question and freed).
: lf-meta-has-mvar? ( term -- flag outcome )
  lf-reach-open 0= if drop false outcome-full exit then
  lf-reach-term lf-reach-sweep lf-reach-holes? lf-reach-close outcome-ok ;

\ ---- mkAppM and mkAppOptM: a frame per call open.
begin-structure /abm
  field: abm-app         \ the application so far
  field: abm-type        \ the rest of its type
  field: abm-d           \ the declaration whose binder kinds are read, or -1
  field: abm-k           \ binders passed
  field: abm-i           \ explicit arguments (mkAppOptM: entries) used
  field: abm-n           \ explicit arguments (mkAppOptM: entries) given
  abl-most cells +field abm-xs
  field: abm-insts#      \ instance metavariables made
  abl-most cells +field abm-insts
  field: abm-opt         \ true: mkAppOptM's entries, abm-mask their somes
  field: abm-mask        \ bit i set: entry i is some x, else none
end-structure
/abm context-slab: abm-frames
: abm ( -- addr ) abm-frames slab-last ;
: abm-xs! ( addr n frame -- ) 2dup abm-n ! abm-xs swap cells move ;
: abm-open ( d addr n frame -- ) dup >r abm-xs! r> abm-d ! ;
: abm-done? ( -- flag ) abm abm-i @ abm abm-n @ < 0= ;
: abm-x ( -- x ) abm abm-i @ cells abm abm-xs + @ ;
: abm-enter ( pi x -- )
  abm abm-app @ over lf-mk-app abm abm-app ! lf-meta-open lf-must abm abm-type !
  1 abm abm-k +! ;
: abm-inst+ ( mvar -- )
  abm abm-insts# @ dup abl-most < 0= if outcome-full lf-must then
  cells abm abm-insts + ! 1 abm abm-insts# +! ;
: abm-hole ( pi kind -- )
  2dup lf-binder-mvar swap lf-binder-instance = if dup abm-inst+ then abm-enter ;
\ isDefEq at default transparency at least (withAtLeastTransparency).
: abl-defeq-d ( t s -- flag ) ['] lf-defeq! lf-tr-default lf-with-at-least ;
: abm-explicit ( pi -- )
  dup lf-term-first@ abm-x lf-infer! abl-defeq-d 0= if abl-fail then
  abm-x abm-enter 1 abm abm-i +! ;
: abm-kind ( pi -- kind ) abm abm-d lf-walk-kind ;
\ mkAppOptMAux (370): some x, which plain isDefEq must fit; none, a new
\ metavariable, synthetic for an instance binder.
: abo-some? ( -- flag ) abm abm-mask @ abm abm-i @ rshift 1 and ;
: abo-some ( pi -- )
  dup lf-term-first@ abm-x lf-infer! lf-defeq! 0= if abl-fail then abm-x abm-enter ;
: abo-entry ( pi -- )
  abo-some? if abo-some else dup abm-kind abm-hole then 1 abm abm-i +! ;
: abm-binder ( pi -- )
  abm abm-opt @ if abo-entry exit then
  dup abm-kind dup lf-binder-default = if drop abm-explicit else abm-hole then ;
: abm-reduce ( -- )
  abm abm-type @ lf-whnf-d! dup lf-term-pi? 0= if abl-fail then
  abm abm-type ! -1 abm abm-d ! ;
: abm-step ( -- ) abm abm-type @ dup lf-term-pi? if abm-binder else drop abm-reduce then ;
\ mkAppMFinal: the instances (synthInstance: none is Lean's "failed to
\ synthesize", synth.fs's lf-synth-instance!), the result instantiated
\ and closed.
: abm-synth ( mvar -- ) dup lf-mvar-type drop lf-synth-instance! lf-mvar-assign lf-must ;
: abm-synths ( -- ) abm abm-insts# @ 0 ?do abm abm-insts i cells + @ abm-synth loop ;
: abl-assignable? ( leaf -- flag )
  dup lf-mvar? if lf-mvar-assignable? else drop false then ;
: abl-closed ( e -- e )
  dup ['] abl-assignable? lf-term-holds? lf-must if abl-fail then
  dup lf-meta-has-mvar? lf-must if outcome-unsupported lf-must then ;
: abm-run ( -- e )
  abm abm-d @ lf-meta-const-fresh lf-must dup abm abm-app ! lf-infer! abm abm-type !
  begin abm-done? 0= while abm-step repeat abm-synths abm abm-app @ lf-instantiate!
  abl-closed ;
: abm-deeper ( -- e )
  false lf-mctx-depth{ lf-must >r ['] abm-run catch r> }lf-mctx-depth swap ?dup
  if nip throw then lf-must ;
: abm-framed ( d addr n -- e ) abm abm-open abm-deeper ;
: abm-of ( d addr n -- e ) abm-frames ['] abm-framed lf-with-record ;
: lf-mk-app-m-of ( d x1..xn n -- e ) abl-stored abm-of ;
\ The constant c-addr u's declaration under a call's stored cells.
: abl-decl-under ( c-addr u addr n -- d addr n ) 2>r abl-decl 2r> ;
: lf-mk-app-m ( c-addr u x1..xn n -- e ) abl-stored abl-decl-under abm-of ;
: abl-mp-by ( h p c-addr u -- e ) abl-decl -rot 2 lf-mk-app-m-of ;
: lf-mk-eq-mp ( h p -- e ) s" Eq.mp" abl-mp-by ;
: lf-mk-eq-mpr ( h p -- e ) s" Eq.mpr" abl-mp-by ;
\ mkAppOptM (402): the mask stored after the entries, then kept in the
\ frame, which it marks as mkAppOptM's.
: abo-framed ( d addr n -- e )
  2dup cells + @ abm tuck abm-mask ! true swap abm-opt ! abm-framed ;
: abo-stored ( x1..xn mask n -- addr n ) 1+ abl-stored 1- ;
: abo-of ( d addr n -- e ) abm-frames ['] abo-framed lf-with-record ;
: lf-mk-app-opt-m ( c-addr u x1..xn mask n -- e ) abo-stored abl-decl-under abo-of ;
\ mkDecide (570): mkAppOptM Decidable.decide #[p, none]: entry 0 some p
\ (mask bit 0), entry 1 none (its cell 0 ignored).
: lf-mk-decide ( p -- e ) s" Decidable.decide" rot 0 1 2 lf-mk-app-opt-m ;

\ ---- matchEq? (Meta/MatchUtil.lean:28, matchHelper?): Expr.eq? of t,
\ else of t put through whnf (the transparency in force; its failure
\ thrown). Rewriting's equation; omega and simp later (plan 9.4.8l-I).
: lf-match-eq? ( t -- α a b true | false ) dup abl-eq-app? 0= if lf-whnf! then lf-eq? ;

\ ---- matchNot? (62), matchNe? (71) and matchHEq? (31), each tried on t,
\ then on t put through whnf (matchHelper?, 22): Not p, or an arrow
\ p -> False (Expr.arrow?, its body False or False after whnf:
\ matchFalse); Ne α a b, or a negation of an equation (matchNot?, then
\ matchEq?); HEq α a β b. contradiction's tests (meta-tactic/
\ contradiction.fs). Each X-at word leaves t below false, for the retry.
: abl-false? ( t -- flag )
  dup s" False" lf-meta-const-named? if drop true exit then
  lf-whnf! s" False" lf-meta-const-named? ;
: abl-closed-body? ( pi -- flag ) lf-term-second@ lf-meta-loose lf-must 0= ;
: abl-arrow? ( t -- dom body true | false )   \ Expr.arrow?
  dup lf-term-pi? if dup abl-closed-body? else false then
  if dup lf-term-first@ swap lf-term-second@ true else drop false then ;
: abl-arrow-false? ( t -- p true | false )
  abl-arrow? 0= if false exit then abl-false? if true else drop false then ;
\ matchHelper?: xt ( t -- i*x true | t false ) on t, then on t after whnf.
: abl-helper ( t xt -- i*x true | false )
  >r r@ execute ?dup if r> drop exit then
  lf-whnf! r> execute ?dup if exit then drop false ;
: abl-not-at ( t -- p true | t false )
  dup 1 s" Not" lf-meta-app-of? if lf-term-second@ true exit then
  dup abl-arrow-false? if nip true else false then ;
: lf-match-not? ( t -- p true | false ) ['] abl-not-at abl-helper ;
\ An application's last argument and its function (abl-peel); the three
\ arguments of Ne α a b and the four of HEq α a β b, in order.
: abl-peel ( t -- a f ) dup lf-term-second@ swap lf-term-first@ ;
: abl-args3 ( t -- x y z ) abl-peel abl-peel lf-term-second@ swap rot ;
: abl-args4 ( t -- w x y z ) abl-peel abl-peel abl-peel lf-term-second@ swap 2swap swap ;
: abl-eq-of-not ( t -- α a b true | false )
  lf-match-not? if lf-match-eq? else false then ;
\ (matchHelper?'s retry on t after whnf finds nothing more here: whnf
\ unfolds Ne, and matchNot? retries after whnf itself.)
: lf-match-ne? ( t -- α a b true | false )
  dup 3 s" Ne" lf-meta-app-of? if abl-args3 true else abl-eq-of-not then ;
: abl-heq-at ( t -- α a β b true | t false )
  dup 4 s" HEq" lf-meta-app-of? if abl-args4 true else false then ;
: lf-match-heq? ( t -- α a β b true | false ) ['] abl-heq-at abl-helper ;
base !   \ the BASE this file was loaded with
