\ Local instances (plan FE3's first part; Forth review of small-tactics-1,
\ 2026-11-26, finding 1), after Lean 4.35.0's Meta/Basic.lean: a new
\ local whose type is a class is a local instance of that class
\ (withNewFVar, Basic.lean:1819, under withLocalDecl and withLetDecl;
\ withNewLocalInstances, :1441, for introNImp's locals, Intro.lean:25
\ and :59), found by isClass? (:1576).
\ - lf-class-whnf? ( type -- class true outcome | false outcome ):
\   isClass?: instances.fs's lf-class? (isClassQuick?), and where that
\   leaves the answer undefined (a definition, let or projection at the
\   head, a lambda head) isClassExpensive? (:1554): at reducible
\   transparency the type put through whnf, then isClassApp? (:1544), a
\   class constant at the head, else none. A pi past that whnf is read by
\   isClassQuick? again: a body it leaves undefined, which Lean puts
\   through whnf under the binders, is not supported yet (unsupported).
\ - lf-local-classed ( local -- local' outcome ) (telescope.fs's deferred
\   word, set here): the local with its class's name (lf-local-instance)
\   when lf-class-whnf? of its type finds a class, else the local as it
\   is. Every local the tactic library pushes (telescope.fs) and every
\   parameter of a declaration's header (elab-decl.fs) goes through it.
\ So instances.fs's getInstances, which reads the class marks of the
\ current view's locals, answers unsupported for a class a local instance
\ of the context has (FE1E §2.7: synthesis from local instances is plan
\ FE3), where it would otherwise take a global instance in place of
\ Lean's local one (review finding 1: p16, p17, q3, q4).
\ Example: the header (d : Decidable True) gives d the class Decidable;
\ (h : a ≠ b) none (Ne unfolds at reducible transparency to a = b →
\ False); (h : ∀ x, x ≠ b) is not supported yet.
\ Outcomes: ok; unsupported as above; whnf's and the instance table's
\ other outcomes passed on. Untrusted: only the kernel's check of the
\ finished term decides. State: none of its own. Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ./meta-config.fs
require ./meta-env.fs
require ./lctx-views.fs
require ./whnf.fs
require ./telescope.fs
require ./instances.fs

\ ---- isClass?: isClassQuick?, else isClassExpensive? at reducible
\ transparency (isClassApp? after whnf: no class constant at the head is
\ none, under binders not supported yet).
: li-none ( ... outcome -- ... outcome' )
  dup outcome-unsupported = if drop outcome-ok then ;
: li-app ( t -- class true outcome | false outcome )
  dup lf-term-pi? if lf-class? exit then lf-class? li-none ;
: li-expensive ( type -- class true outcome | false outcome )
  lf-meta-whnf ok-then? if li-app else false swap then ;
: lf-class-whnf? ( type -- class true outcome | false outcome )
  dup >r lf-class? dup outcome-unsupported <> if r> drop exit then
  2drop r> ['] li-expensive lf-with-reducible ;

\ ---- withNewFVar: the class's name in the context's names, the one
\ instances.fs's guard compares with the class asked for.
: li-named ( d -- name outcome ) lf-menv-name outcome-ok ;
: li-name ( class -- name outcome ) lf-menv-of-data ['] li-named ok-apply ;
: li-mark ( local class -- local' outcome ) li-name ['] lf-local-instance ok-apply2 ;
: li-classed ( local -- local' outcome )
  dup lf-local-fvar lf-fvar-type lf-class-whnf? ok-then? 0= if exit then
  if li-mark else outcome-ok then ;
' li-classed is lf-local-classed

base !   \ the BASE this file was loaded with
