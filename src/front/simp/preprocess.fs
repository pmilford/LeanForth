\ Simp's rules made from a term (plan row FE9, simp slice SL1b of
\ docs/design/TACTIC_SIMP.md): Lean 4.35.0's mkSimpTheoremFromExpr for a
\ term that is no constant (src/lean/Lean/Meta/Tactic/Simp/
\ SimpTheorems.lean:492-502) with its preprocess (319-390, isGlobal
\ false), as elabSimpArgs gives it a hypothesis (Elab/Tactic/Simp.lean:289).
\ - lf-simp-add-term ( h inv -- ): under mkIndexConfig at reducible
\   transparency (lf-with-simp-index), h's type whnf'd, then by its shape:
\   a pi: a new local x of its binder (forallTelescopeReducing, one binder
\   at a time), h x walked on, and every proof it gives is fun x => proof
\   (mkLambdaFVars); an Eq: h, with inv Eq.symm h; an Iff: propext h, with
\   inv its Eq.symm; Not p: eq_false h, of p = False (with inv Lean's error
\   503 "Invalid `←` modifier: Cannot be applied to simp theorems of the
\   form `¬ P`", its note naming p; p an Eq to Bool.true or Bool.false,
\   Lean's Bool.of_not_eq_true or _false, not supported yet); an And: its
\   projections h.1 and h.2 walked on, the left first; anything else p:
\   eq_true h, of p = True (with inv Lean's error 502 "Invalid `←`
\   modifier: Cannot be applied to a rule that rewrites to `True`", its
\   note naming p). The proofs, in Lean's order, then each added to the
\   set (simp/theorems.fs's lf-simp-add-hyp, post, origin .stx). A Ne is
\   no case of its own: whnf at reducible unfolds it (a reducible
\   definition) to Not, before Lean's ne? test, which so never holds here.
\   A pi whose binder's kind is unknown is unsupported (telescope.fs).
\ Lean call list: whnf -> lf-whnf-r!; forallTelescopeReducing ->
\ spp-open (lf-local-decl-new); mkAppN -> lf-mk-app; mkLambdaFVars ->
\ lf-mk-lambda-fvars; mkEqSymm -> lf-mk-eq-symm; mkPropExt -> lf-mk-app-m
\ of propext; mkEqFalse -> lf-mk-eq-false; mkProj -> lf-proj-of;
\ mkEqTrue -> lf-mk-eq-true; mkSimpTheoremCore -> lf-simp-add-hyp.
\ Throws as meta-must.fs's words do, the two errors as tactic errors.
\ Untrusted: a rule only proposes rewrites whose proofs the kernel checks.
\ State: the walk's slabs spp-work (the terms to walk, the next on top,
\ each with the count of binders over it), spp-xs (the locals open, which
\ a term with fewer binders cuts back; a local cut stays in the view, as
\ no term made later names it) and spp-out (the proofs), and the record
\ spp, each valid within one call; the locals are dropped at its end.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/context.fs
require ../../core/projections.fs
require ../telescope.fs
require ../tactic-msg.fs
require ./theorems.fs

502 lfa-lean
  s" Invalid `←` modifier: Cannot be applied to a rule that rewrites to `True`"
  lfa-code: lfa-e-simp-symm-true
503 lfa-lean
  s" Invalid `←` modifier: Cannot be applied to simp theorems of the form `¬ P`"
  lfa-code: lfa-e-simp-symm-not

2 cells context-slab: spp-work
1 cells context-slab: spp-xs
1 cells context-slab: spp-out
begin-structure /spp  field: spp-inv  field: spp-n  end-structure
/spp context-record: spp
: spp-n@ ( -- n ) spp spp-n @ ;
: spp-inv? ( -- flag ) spp spp-inv @ ;
: spp-push ( e n -- ) spp-work slab-2push lf-must ;

\ ---- The refusals of inv, their note naming p (SimpTheorems.lean:370, 387).
: spp-to. ( c-addr u -- outcome )
  lf-pp-emit s" `, which should not be applied in the reverse direction" lf-pp-emit
  outcome-ok ;
: spp-to-true. ( -- outcome ) s"  to `True" spp-to. ;
: spp-to-false. ( -- outcome ) s"  to `False" spp-to. ;
: spp-note. ( p xt -- outcome )
  s\" \n\nNote: This simp theorem will rewrite" lf-pp-emit lf-tac-spaced. ;
: spp-true. ( p -- outcome ) ['] spp-to-true. spp-note. ;
: spp-false. ( p -- outcome ) ['] spp-to-false. spp-note. ;
: spp-refuse ( p xt code -- ) >r lf-tac-inline r> lf-tac-stop ;

\ ---- The leaves: a proof of an Eq, closed over the binders open.
: spp-leaf ( p -- ) spp-xs slab-base spp-n@ lf-mk-lambda-fvars spp-out slab-push lf-must ;
: spp-eq ( e -- p ) spp-inv? if lf-mk-eq-symm then ;
: spp-iff ( e -- p ) s" propext" rot 1 lf-mk-app-m spp-eq ;
: spp-bool? ( p -- flag )   \ p.eq? with Bool.true or Bool.false on the right
  lf-eq? 0= if false exit then nip nip
  dup s" Bool.true" lf-meta-const-named? swap s" Bool.false" lf-meta-const-named? or ;
: spp-not ( e p -- p' )
  dup spp-bool? if lf-unported then
  spp-inv? if dup ['] spp-false. lfa-e-simp-symm-not spp-refuse then drop lf-mk-eq-false ;
: spp-true ( e t -- p )
  spp-inv? if dup ['] spp-true. lfa-e-simp-symm-true spp-refuse then drop lf-mk-eq-true ;

\ ---- The inner nodes: a pi's binder opened, an And's two projections.
: spp-binder ( pi -- name kind ) lf-binder-of 0= if lf-unported then ;
: spp-open ( e pi -- )
  dup lf-term-first@ swap spp-binder lf-local-decl-new lf-mctx-view!
  dup spp-xs slab-push lf-must lf-mk-app spp-n@ 1+ spp-push ;
: spp-proj ( e name i -- ) lf-proj-of lf-must spp-n@ spp-push ;
: spp-split ( e t -- )   \ h.2 below h.1, so h.1 is walked first
  lf-meta-head lf-const-name 2dup 1 spp-proj 0 spp-proj ;

\ ---- preprocess's go: one term of the worklist.
: spp-leaf-of ( e t -- p )   \ an Eq, an Iff, a Not or anything else
  dup lf-eq-app? if drop spp-eq exit then
  dup lf-iff-app? if drop spp-iff exit then
  dup lf-not-app? if lf-term-second@ spp-not exit then spp-true ;
: spp-shaped ( e t -- p true | false )
  dup lf-term-pi? if spp-open false exit then
  dup lf-and-app? if spp-split false exit then spp-leaf-of true ;
: spp-type ( e -- t ) lf-infer! lf-instantiate! lf-whnf-r! ;
: spp-go ( e n -- true outcome )
  dup spp spp-n ! spp-xs slab-cut dup spp-type spp-shaped if spp-leaf then
  true outcome-ok ;

: spp-walk ( h inv -- )
  spp spp-inv ! spp-work slab-clear spp-xs slab-clear spp-out slab-clear
  0 spp-push spp-work ['] spp-go slab-2all? lf-must drop ;
: spp-indexed ( h inv -- ) ['] spp-walk lf-with-simp-index ;
: spp-add ( i -- ) spp-out slab-at @ true lf-simp-add-hyp ;
: lf-simp-add-term ( h inv -- )
  ['] spp-indexed lf-with-new-locals spp-out slab-count 0 ?do i spp-add loop ;

base !   \ the BASE this file was loaded with
