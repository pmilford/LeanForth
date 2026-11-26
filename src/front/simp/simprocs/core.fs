\ Lean 4.35.0's Core simprocs on if-then-else (simp group 4, pass 2;
\ src/lean/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean:15-80), ports
\ for simp/simprocs.fs, each its head ite or dite of five arguments
\ (let_expr):
\ - reduceIte (pre, :15): ite α c i tb eb, c simplified inside the walk
\   (simp c: simp/main.fs's lf-simp-nested, the run's cache and steps):
\   True gives tb by ite_eq_left_of_eq_true.{u} α c i tb eb pr, False eb
\   by ite_eq_right_of_eq_false, u ite's level (f.constLevels!), pr
\   r.getProof (Eq.refl of the result when it has no proof); visit;
\   else continue.
\ - reduceDIte (pre, :27): dite α c i tb eb the same, the new term
\   (tb (of_eq_true c pr)).headBeta, or eb's of of_eq_false, by
\   dite_eq_left_of_eq_true or dite_eq_right_of_eq_false.
\ - dreduceIte, dreduceDIte (pre dsimprocs, :47, :66): continue outside
\   dsimp (inDSimp), as simp always is here.
\ A step's theorem i is its place in spc-names: the port's x (reduceIte
\ 0, reduceDIte 2) plus the branch j (0 True: the then branch, argument
\ 3; 1 False: the else branch, argument 4), so i's low bit is j. A
\ simplification of c that throws throws (unsupported, as the walk).
\ Untrusted: the kernel checks every proof. State: none of its own.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../../lib/lib.fs
require ../../../lib/texts.fs
require ../../../core/terms.fs
require ../../../core/constant-term-boundary.fs
require ../types.fs
require ../main.fs
require ../simprocs.fs

texts-begin texts+ ite_eq_left_of_eq_true ite_eq_right_of_eq_false
texts+ dite_eq_left_of_eq_true dite_eq_right_of_eq_false of_eq_true of_eq_false
texts-end constant spc-names
: spc-name ( i -- c-addr u ) spc-names swap 0 ?do text-next loop count ;
: spc-arg ( e i -- a ) 5 lf-meta-nth-arg ;
: spc-branch ( e i -- a ) 1 and 3 + spc-arg ;
: spc-truth ( c -- j )
  dup s" True" lf-meta-const-named? if drop 0 exit then
  s" False" lf-meta-const-named? if 1 else -1 then ;
\ simp c, then its branch and r.getProof; neither True nor False: none.
: spc-cond ( e -- e pr j true | e false )
  dup 1 spc-arg lf-simp-nested over spc-truth
  dup 0< if drop 2drop false exit then
  >r lf-simp-proof r> true ;
\ thm i.{u} α c i tb eb pr.
: spc-thm ( e i -- e thm )
  spc-name 2>r dup lf-meta-head 0 lf-const-level@ 2r> rot lf-mk-const1 ;
: spc-applied ( e f -- e f' ) 5 0 do over i spc-arg lf-mk-app loop ;
: spc-proof ( pr e i -- h ) spc-thm spc-applied nip swap lf-mk-app ;
: spc-step ( e pr e' i -- e' h step ) >r -rot swap r> spc-proof lf-simp-visit ;
: spc-ite ( e pr i -- e' h step ) >r over r@ spc-branch r> spc-step ;
\ reduceDIte's term: (branch (of_eq c pr)).headBeta.
: spc-of-eq ( e pr i -- h )
  1 and 4 + spc-name lf-mk-const0 rot 1 spc-arg lf-mk-app swap lf-mk-app ;
: spc-dite-term ( e pr i -- e' )
  >r over r@ spc-branch -rot r> spc-of-eq lf-mk-app lf-meta-head-beta lf-must ;
: spc-dite ( e pr i -- e' h step ) >r 2dup r@ spc-dite-term r> spc-step ;
\ The condition simplified, then the branch's step by xt ( e pr i -- e' h step ).
: spc-decided ( e x xt -- e' h step )
  2>r spc-cond if 2r> >r + r> execute else 2r> 2drop lf-simp-pass then ;
: spc-reduce-ite ( e x -- e' h step ) ['] spc-ite spc-decided ;
: spc-reduce-dite ( e x -- e' h step ) ['] spc-dite spc-decided ;

' spc-reduce-ite 0 5 true false lf-simproc: ite reduceIte
' spc-reduce-dite 2 5 true false lf-simproc: dite reduceDIte
\ Outside dsimp continue: main.fs's answer of no simproc.
' lf-simp-no-procs 0 5 true true lf-simproc: ite dreduceIte
' lf-simp-no-procs 0 5 true true lf-simproc: dite dreduceDIte

base !   \ the BASE this file was loaded with
