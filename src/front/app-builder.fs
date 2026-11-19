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
\   lf-mk-congr-arg ( f h -- h' )         mkCongrArg (212), with congrArg?
\                                         (199) fusing nested congrArg
\   lf-mk-app-m ( c-addr u x1..xn n -- e ) mkAppM (345), lf-mk-app-m-of
\                                         ( d x1..xn n -- e ) of a declaration
\   lf-mk-eq-mp ( h p -- e ), lf-mk-eq-mpr ( h p -- e )  mkEqMP, mkEqMPR
\                                         (444-447)
\   lf-eq? ( t -- α a b true | false )     Expr.eq?: Eq α a b's arguments
\   lf-meta-has-mvar? ( e -- flag outcome ) Expr.hasMVar: a term or level
\                                         metavariable reached (core/reach.fs)
\ Levels pass on the stack (never through a global); at most abl-most
\ levels or arguments a call. AppBuilder's private infer is inferType then
\ whnfD. mkAppM walks the constant's type in a new metavariable depth
\ (withNewMCtxDepth): an implicit binder a natural metavariable, an
\ instance binder a synthetic one filled at the end by instance search
\ (defeq.fs's lf-meta-synth hook; none found: rejected), an explicit one
\ the next argument, which isDefEq at default transparency at least must
\ fit (else rejected); whnfD where the type shows no pi (none: rejected,
\ too many arguments); the result instantiated must reach no assignable
\ metavariable (rejected) nor any other one (unsupported: the level
\ metavariables' assignability is not told apart). Binder kinds come
\ from telescope.fs's lf-binder-kind-at (the declaration's, until whnf).
\ Not ported yet (their slices): mkAppOptM (a2-iii), mkDecide,
\ mkExpectedTypeHint (S3), mkCongr, mkCongrFun, mkEqNDRec, mkOfEqTrue,
\ mkEqTrue (the simp core, which brings their first callers).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: abl-cells (one call's levels or arguments, read before any other
\ builder runs) and abm-frames (a frame per mkAppM open), in the checker
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
require ./term-eqv.fs
require ./term-find.fs
require ./instantiate.fs
require ./meta-must.fs
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
: lf-eq? ( t -- α a b true | false )
  dup 3 s" Eq" lf-meta-app-of? 0= if drop false exit then
  dup lf-term-second@ >r lf-term-first@ dup lf-term-first@ lf-term-second@ swap
  lf-term-second@ r> true ;
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
: abl-named ( t name -- t )
  over lf-term-input? if drop exit then
  ?dup if over swap lf-binder-default lf-pres-binder! lf-must then ;
: abl-lam-x ( dom body -- e ) lf-term-lam lf-made! s" x" lfa-intern abl-named ;

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

\ ---- mkCongrArg (a loop: congrArg? fuses a nested congrArg).
\ congrArg?: congrArg's α, f and h; congrFun's made into one.
: abl-arg ( t i -- a ) 6 lf-meta-nth-arg ;
: abl-from-arg ( h -- α f h1 ) dup 0 abl-arg over 4 abl-arg rot 5 abl-arg ;
: abl-from-fun ( h -- α' f' h1 )   \ α' := ∀ x : α, β x; f' := fun f : α' => f a
  dup 0 abl-arg over 1 abl-arg abl-bvar0 abl-beta1 lf-term-pi lf-made! s" x" lfa-intern
  abl-named over 5 abl-arg abl-bvar0 swap lf-mk-app over swap lf-term-lam lf-made!
  s" f" lfa-intern abl-named rot 4 abl-arg ;
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

\ ---- mkAppM: a frame per call open.
begin-structure /abm
  field: abm-app         \ the application so far
  field: abm-type        \ the rest of its type
  field: abm-d           \ the declaration whose binder kinds are read, or -1
  field: abm-k           \ binders passed
  field: abm-i           \ explicit arguments used
  field: abm-n           \ explicit arguments given
  abl-most cells +field abm-xs
  field: abm-insts#      \ instance metavariables made
  abl-most cells +field abm-insts
end-structure
/abm context-slab: abm-frames
: abm ( -- addr ) abm-frames slab-last ;
: abm-claim ( -- frame )
  1 abm-frames slab-claim lf-must abm-frames slab-at dup /abm erase ;
: abm-xs! ( addr n frame -- ) 2dup abm-n ! abm-xs swap cells move ;
: abm-open ( d addr n -- ) abm-claim dup >r abm-xs! r> abm-d ! ;
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
: abl-defeq-d ( t s -- flag )
  lf-defeq-mode lf-tr-all = if lf-defeq! exit then
  ['] lf-defeq! lf-tr-default lf-meta-at ;
: abm-explicit ( pi -- )
  dup lf-term-first@ abm-x lf-infer! abl-defeq-d 0= if abl-fail then
  abm-x abm-enter 1 abm abm-i +! ;
: abm-kind ( pi -- kind ) abm abm-d lf-walk-kind ;
: abm-binder ( pi -- )
  dup abm-kind dup lf-binder-default = if drop abm-explicit else abm-hole then ;
: abm-reduce ( -- )
  abm abm-type @ lf-whnf-d! dup lf-term-pi? 0= if abl-fail then
  abm abm-type ! -1 abm abm-d ! ;
: abm-step ( -- ) abm abm-type @ dup lf-term-pi? if abm-binder else drop abm-reduce then ;
\ mkAppMFinal: the instances, the result instantiated and closed.
: abm-synth ( mvar -- )
  dup lf-mvar-type drop lf-meta-synth lf-must 0= if abl-fail then lf-mvar-assign lf-must ;
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
: abm-of ( d addr n -- e ) abm-open ['] abm-deeper catch abm-frames slab-drop throw ;
: lf-mk-app-m-of ( d x1..xn n -- e ) abl-stored abm-of ;
: lf-mk-app-m ( c-addr u x1..xn n -- e ) abl-stored 2>r abl-decl 2r> abm-of ;
: lf-mk-eq-mp ( h p -- e ) s" Eq.mp" abl-decl -rot 2 lf-mk-app-m-of ;
: lf-mk-eq-mpr ( h p -- e ) s" Eq.mpr" abl-decl -rot 2 lf-mk-app-m-of ;
base !   \ the BASE this file was loaded with
