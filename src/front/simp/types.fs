\ Simp's results and the proofs simpAppUsingCongr builds (plan row FE9,
\ simp slice SL1a-1 of docs/design/TACTIC_SIMP.md): Lean 4.35.0's
\ Simp.Result and its builders (src/lean/Lean/Meta/Tactic/Simp/
\ Types.lean). A result is two cells on the stack, ( e h ): the term
\ simplified and a proof that the source equals it, or lf-simp-none when
\ they are definitionally equal at reducible transparency (Lean's proof?
\ := none). Lean's third field, cache, is true throughout this slice
\ (only simprocs and dischargers make it false).
\ - lf-simp-none ( -- -1 ), lf-simp-none? ( h -- flag ).
\ - lf-simp-proof ( e h -- p ): Result.getProof (560): h, else mkEqRefl e.
\ - lf-simp-trans ( h1 e2 h2 -- e2 h ): r1.mkEqTrans r2
\   (mkEqTransOptProofResult, 345) for r1's proof h1: r2 as it is when h1
\   is none, with h1 when h2 is none, else with Meta.mkEqTrans h1 h2
\   (app-builder.fs's lf-mk-eq-trans).
\ - lf-simp-congr ( e fe fh ae ah -- e' h ): mkCongr' (714): e is an
\   application f a, (fe, fh) the result of f and (ae, ah) that of a; e'
\   is fe ae, its proof none when neither has one, else congrFun' α β f fe
\   fh ae (f's alone), congrArg α β a ae fe ah (a's alone) or congr α β f
\   fe a ae fh ah, each constant at the levels of α, a's type, and of β,
\   e's type (mkCongrPrefix, 697).
\ - lf-simp-congr-fun ( e fe fh a -- e' h ): mkCongrFun' (682): fe a with
\   no proof when fh is none; with one (Lean's congrFun α (fun x => βx) f
\   fe fh a) unsupported until slice SL1b.
\ Every word throws as the builders do (meta-must.fs). Untrusted: the
\ kernel checks every proof. State: the context record stc, the five
\ cells of the lf-simp-congr call running.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/context.fs
require ../app-builder.fs

-1 constant lf-simp-none
: lf-simp-none? ( h -- flag ) lf-simp-none = ;
: lf-simp-proof ( e h -- p ) dup lf-simp-none? if drop lf-mk-eq-refl else nip then ;
: lf-simp-trans ( h1 e2 h2 -- e2 h )
  rot dup lf-simp-none? if drop exit then
  over lf-simp-none? if nip exit then swap lf-mk-eq-trans ;

\ ---- mkCongr' (Types.lean:714), its five cells kept in stc.
begin-structure /stc
  field: stc-e   field: stc-fe   field: stc-fh   field: stc-ae   field: stc-ah
end-structure
/stc context-record: stc
: stc! ( e fe fh ae ah -- )
  stc stc-ah ! stc stc-ae ! stc stc-fh ! stc stc-fe ! stc stc-e ! ;
: st-e ( -- e ) stc stc-e @ ;
: st-fe ( -- fe ) stc stc-fe @ ;
: st-fh ( -- fh ) stc stc-fh @ ;
: st-ae ( -- ae ) stc stc-ae @ ;
: st-ah ( -- ah ) stc stc-ah @ ;
\ mkCongrPrefix (697): c.{u, v} α β, α the type of e's argument, β e's.
: st-alpha ( -- α ) st-e lf-term-second@ lf-infer! ;
: st-beta ( -- β ) st-e lf-infer! ;
: st-prefix ( c-addr u -- pre )
  st-alpha lf-level! st-beta lf-level! 2 lf-mk-const
  st-alpha lf-mk-app st-beta lf-mk-app ;
: st-fun ( -- h )
  s" congrFun'" st-prefix st-e lf-term-first@ st-fe st-fh st-ae 4 lf-mk-app-n ;
: st-arg ( -- h )
  s" congrArg" st-prefix st-e lf-term-second@ st-ae st-fe st-ah 4 lf-mk-app-n ;
: st-both ( -- h )
  s" congr" st-prefix st-e lf-term-first@ st-fe st-e lf-term-second@ st-ae st-fh st-ah
  6 lf-mk-app-n ;
: st-proof ( -- h )
  st-fh lf-simp-none? if st-ah lf-simp-none? if lf-simp-none else st-arg then exit then
  st-ah lf-simp-none? if st-fun else st-both then ;
: lf-simp-congr ( e fe fh ae ah -- e' h ) stc! st-fe st-ae lf-mk-app st-proof ;
: lf-simp-congr-fun ( e fe fh a -- e' h )
  swap lf-simp-none? 0= if lf-unported then lf-mk-app nip lf-simp-none ;

base !   \ the BASE this file was loaded with
