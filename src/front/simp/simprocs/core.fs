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
\ A step's theorem k is its place in spc-names: the port's x (reduceIte
\ 0, reduceDIte 2) plus the branch j (0 True: the then branch; 1 False:
\ the else branch), so k's low bit is j. The proof h, theorem k applied
\ to α c i tb eb pr, is built first: the new term reads its branch (h's
\ argument 3 + j) and reduceDIte's c and pr (arguments 1 and 5) from it.
\ A simplification of c that throws throws (unsupported, as the walk).
\ Untrusted: the kernel checks every proof. State: none of its own.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../../lib/lib.fs
require ../../../lib/texts.fs
require ../../../core/terms.fs
require ../../../core/constant-term-boundary.fs
require ../../../author/declarations.fs
require ../types.fs
require ../main.fs
require ../simprocs.fs

texts-begin texts+ ite_eq_left_of_eq_true ite_eq_right_of_eq_false
texts+ dite_eq_left_of_eq_true dite_eq_right_of_eq_false of_eq_true of_eq_false
texts-end constant spc-names
: spc-name ( k -- c-addr u ) spc-names swap 0 ?do text-next loop count ;
: spc-arg ( e i -- a ) 5 lf-meta-nth-arg ;   \ of ite or dite
: spc-harg ( h i -- a ) 6 lf-meta-nth-arg ;  \ of the step's proof
: spc-branch ( h k -- a ) 1 and 3 + spc-harg ;
: spc-truth ( c -- j )
  dup s" True" lf-meta-const-named? if drop 0 exit then
  s" False" lf-meta-const-named? if 1 else -1 then ;
\ simp c, then r.getProof and c's branch; neither True nor False: none.
: spc-cond ( e -- pr e j true | e false )
  dup 1 spc-arg lf-simp-nested over spc-truth
  dup 0< if drop 2drop false exit then
  >r lf-simp-proof swap r> true ;
: spc-decided ( e x -- pr e k true | e false )
  >r spc-cond if r> + true else r> drop false then ;
\ Theorem k.{u} α c i tb eb pr: mkConst k f.constLevels!, then e's
\ arguments and pr.
: spc-const ( e k -- e c )
  spc-name lfa-intern over lf-meta-head lf-const-levels lf-mk-const-id ;
: spc-applied ( e f -- e f' ) 5 0 do over i spc-arg lf-mk-app loop ;
: spc-proof ( pr e k -- h k ) tuck spc-const spc-applied nip rot lf-mk-app swap ;
\ reduceDIte's term: (branch (of_eq c pr)).headBeta.
: spc-of-eq ( h k -- q )
  1 and 4 + spc-name lf-mk-const0 over 1 spc-harg lf-mk-app swap 5 spc-harg lf-mk-app ;
: spc-dite-term ( h k -- e' )
  2dup spc-branch -rot spc-of-eq lf-mk-app lf-meta-head-beta lf-must ;
\ The step: the proof, then the new term by xt ( h k -- e' ); visit.
: spc-step ( pr e k xt -- e' h step )
  >r spc-proof over swap r> execute swap lf-simp-visit ;
: spc-reduce-ite ( e x -- e' h step )
  spc-decided if ['] spc-branch spc-step else lf-simp-pass then ;
: spc-reduce-dite ( e x -- e' h step )
  spc-decided if ['] spc-dite-term spc-step else lf-simp-pass then ;

' spc-reduce-ite 0 5 true false lf-simproc: ite reduceIte
' spc-reduce-dite 2 5 true false lf-simproc: dite reduceDIte
\ Outside dsimp continue: main.fs's answer of no simproc.
' lf-simp-no-procs 0 5 true true lf-simproc: ite dreduceIte
' lf-simp-no-procs 0 5 true true lf-simproc: dite dreduceDIte

base !   \ the BASE this file was loaded with
