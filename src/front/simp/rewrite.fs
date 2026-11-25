\ Simp's rewriting with its theorems (plan row FE9, simp slice SL1a-1 of
\ docs/design/TACTIC_SIMP.md): Lean 4.35.0's rewrite? with the index
\ (src/lean/Lean/Meta/Tactic/Simp/Rewrite.lean:207-240),
\ tryTheoremWithExtraArgs? (178) and tryTheoremCore (115).
\ - lf-simp-rewrite? ( e tree rfl-only -- e' h true | false ): the
\   candidates of getMatchWithExtra (discr-tree.fs's lf-dt-get-match-extra
\   at mkIndexConfig, lf-with-simp-index) sorted by priority, highest
\   first, stably (lib/sort.fs, Lean's insertionSort); with rfl-only those
\   without the rfl flag passed over; the first that rewrites e answers.
\   A theorem is tried one metavariable depth deeper (lf-with-new-depth):
\   its value (a declaration's constant at fresh level metavariables,
\   SimpTheorem.getValue 475; a hypothesis itself), its type's
\   forallMetaTelescopeReducing, whnf of the body (reducible, simp's
\   transparency), its left side unified with e less its extra arguments
\   at mkMetaConfig (lf-with-simp-meta); then synthesizeArgs (58): a
\   metavariable left unassigned whose type is a proposition (the
\   discharger, SL2) or may be a class (instance synthesis, SL1a-2) is
\   unsupported; the proof none for an rfl theorem (implicitDefEqProofs),
\   else the value applied to the metavariables, refused (none) when one
\   is left; the result refused when it equals e (Lean's ==, term-eqv.fs)
\   or, for an rfl theorem, holds a metavariable left; a type with
\   binderNameHint unsupported (resolveBinderNameHint, 152);
\   addExtraArgs (Types.lean:617) with Meta.mkCongrFun on each extra
\   argument (app-builder.fs: Eq.refl alone, else unsupported).
\ - lf-simp-arg ( e n k -- a ): argument k (from 0) of e, an application
\   to n arguments (Expr.getArg!).
\ - lf-simp-rfl-match? ( e tree -- flag ): whether a theorem with the rfl
\   flag is among e's candidates (the dsimp guard of simp/main.fs).
\ Throws as meta-must.fs's words do. Untrusted: a rewrite's proof is
\ checked by the kernel. State: the context slabs sr-cands (the
\ candidates, pairs) and sr-xs (the telescope's metavariables), the
\ record srt (the theorem tried) and the sorter sr-sort, each valid
\ within one call.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/sort.fs
require ../../lib/context.fs
require ./types.fs
require ./theorems.fs

1 cells context-slab: sr-cands   \ (theorem, extra arguments) pairs
1 cells context-slab: sr-xs      \ the theorem's metavariables, in order
/sorter context-record: sr-sort
begin-structure /srt
  field: srt-e   field: srt-n   field: srt-thm   field: srt-app   field: srt-type
end-structure
/srt context-record: srt

\ ---- The candidates, highest priority first.
: sr-query ( e tree -- ) sr-cands slab-clear sr-cands lf-dt-get-match-extra ;
: sr-desc ( p1 p2 -- n ) swap sort-signed ;
: sr-prio ( a-addr -- p ) @ lf-simp-thm-prio ;
: sr-sorted ( -- )
  2 cells ['] sr-desc sr-sort sorter-init lf-must ['] sr-prio sr-sort sorter-key!
  sr-cands slab-base sr-cands slab-count 2/ sr-sort sort-records lf-must ;
: sr-cands-of ( e tree -- n )
  ['] sr-query lf-with-simp-index sr-sorted sr-cands slab-count 2/ ;
: sr-pair ( i -- thm extra ) 2* sr-cands slab-at 2@ swap ;

\ ---- tryTheoremCore's term: e less its extra arguments, and those.
: sr-strip ( e n -- e' ) 0 ?do lf-term-first@ loop ;
: lf-simp-arg ( e n j -- a ) - 1- sr-strip lf-term-second@ ;
: sr-congr-fun ( h a -- h' ) over lf-simp-none? if drop else lf-mk-congr-fun then ;
: sr-extras ( e' h -- e'' h' )
  srt srt-n @ 0 ?do srt srt-e @ srt srt-n @ i lf-simp-arg >r
    swap r@ lf-mk-app swap r> sr-congr-fun loop ;

\ ---- getValue and the telescope.
: sr-mvar ( app mvar kind -- app' ) drop dup sr-xs slab-push lf-must lf-mk-app ;
: sr-value ( t -- val d ) dup lf-simp-thm-proof swap lf-simp-thm-decl?
  if dup lf-meta-const-fresh lf-must swap else -1 then ;
: sr-keep ( app type -- ) lf-instantiate! lf-whnf-r! srt srt-type ! srt srt-app ! ;
: sr-open ( t -- )
  sr-xs slab-clear sr-value >r dup lf-infer! r> ['] sr-mvar
  lf-forall-meta-telescope-reducing sr-keep ;
: sr-sides ( -- lhs rhs ) srt srt-type @ lf-eq? 0= if lf-unported then rot drop ;
: sr-e0 ( -- e ) srt srt-e 2@ swap sr-strip ;   \ srt-e, srt-n a pair
: sr-unifies? ( -- flag ) sr-sides drop sr-e0 ['] lf-defeq! lf-with-simp-meta ;

\ ---- synthesizeArgs: an unassigned argument of a proposition or of a
\ type that may be a class.
: sr-x ( i -- x ) sr-xs slab-at @ ;
: sr-open? ( x -- flag ) lf-instantiate! lf-mvar? ;
: sr-needs? ( x -- flag )
  lf-infer! dup lf-meta-is-prop lf-must swap lf-meta-class-none? 0= or ;
: sr-check-x ( x -- ) dup sr-open? if sr-needs? if lf-unported then else drop then ;
: sr-synthesize ( -- ) sr-xs slab-count 0 ?do i sr-x sr-check-x loop ;
: sr-left? ( -- flag ) false sr-xs slab-count 0 ?do i sr-x sr-open? or loop ;
: sr-occurs ( e acc m -- e acc' ) >r over r> swap lf-mvar-occurs? lf-must or ;
: sr-in-x ( e acc x -- e acc' ) lf-instantiate! dup lf-mvar? if sr-occurs else drop then ;
: sr-in? ( e -- flag ) false sr-xs slab-count 0 ?do i sr-x sr-in-x loop nip ;

\ ---- tryTheoremCore's go: the rewrite, or none.
: sr-rfl? ( -- flag ) srt srt-thm @ lf-simp-thm-rfl? ;
: sr-proof ( -- h true | false )
  sr-rfl? if lf-simp-none true exit then
  sr-left? if false exit then srt srt-app @ lf-instantiate! true ;
: sr-hint-node? ( node -- flag ) s" binderNameHint" lf-meta-const-named? ;
: sr-hint? ( type -- flag ) ['] sr-hint-node? lf-term-holds-node? lf-must ;
: sr-rhs ( -- rhs ) sr-sides nip lf-instantiate! ;
: sr-same? ( rhs -- flag ) sr-e0 lf-instantiate! lf-meta-eqv lf-must ;
: sr-result ( h -- e' h true | false )
  sr-rhs dup sr-same? if 2drop false exit then
  sr-rfl? if dup sr-in? if 2drop false exit then then
  srt srt-type @ sr-hint? if lf-unported then swap sr-extras true ;
: sr-go ( t -- e' h true | false )
  sr-open sr-unifies? 0= if false exit then
  sr-synthesize sr-proof if sr-result else false then ;
: sr-try ( e t n -- e' h true | false )
  srt srt-n ! dup srt srt-thm ! swap srt srt-e ! ['] sr-go lf-with-new-depth ;

: sr-skip? ( rfl-only t -- flag ) lf-simp-thm-rfl? 0= and ;
: sr-candidate ( e rfl-only i -- e rfl-only e' h true | e rfl-only false )
  sr-pair >r 2dup sr-skip? if r> 2drop false exit then
  >r over r> r> sr-try ;
: lf-simp-rewrite? ( e tree rfl-only -- e' h true | false )
  >r over swap sr-cands-of r> swap 0 ?do i sr-candidate
    if 2swap 2drop true unloop exit then loop 2drop false ;
: sr-rfl-at? ( i -- flag ) sr-pair drop lf-simp-thm-rfl? ;
: lf-simp-rfl-match? ( e tree -- flag )
  sr-cands-of false swap 0 ?do i sr-rfl-at? or loop ;

base !   \ the BASE this file was loaded with
