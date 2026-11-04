\ Lean's definitional equality and weak head normal form as LeanForth
\ ports them (src/kernel/defeq.fs, src/kernel/whnf.fs; ADR 0014, plan
\ tasks 4.2.2b and 4.2.2c), on terms without definitions, outside a check
\ of the checked environment: quick_is_def_eq (Lean's ==, Sorts by
\ is_equivalent, binders), is_def_eq_binding (domains read with the free
\ variables of the binders before, the right side's domain for the bound
\ variable), whnf_core's beta (all leading lambdas at once; one at a time
\ when an argument has loose bound variables, which must be lifted),
\ is_def_eq_app (functions first, then counts, then arguments left to
\ right), is_def_eq_args (last argument first), the steps that only say
\ yes, every outcome (yes, no, unknown, exhausted, full, invalid) and a
\ fuel sweep; whnf on a constant outside a check (K1), Lean's name-matched
\ Nat operations (K7) and cheap_beta_reduce. With definitions, in a
\ check: tests/core/whnf.fs. Test-only; nothing here accepts a theorem.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/main.fs
include ../support/plain-terms.fs

\ Room for every case of this file in one session.
4096 lf-term-capacity! ok? must  1024 lf-level-capacity! ok? must
\ A frames record of the tests' own (its visitor is never run: every
\ visit of the port is opened with frame-open).
' lf-mconvert-no-visit frames: dq
: fuelled ( fuel -- ) dq frame-reset dq frame-budget must ;
: defeq ( t s -- flag outcome ) 100000 fuelled dq lf-defeq-on ;
: quick ( t s -- lbool outcome ) 100000 fuelled dq lf-quick-on ;
: app? ( t s -- flag outcome ) 100000 fuelled dq lf-defeq-app-on ;
: args? ( t s -- flag outcome ) 100000 fuelled dq lf-defeq-args-on ;
: core ( node -- node' outcome ) 100000 fuelled dq lf-whnf-core-on ;
: whnf ( node -- node' outcome ) 100000 fuelled dq lf-whnf-on ;
: same? ( t s -- flag ) 100000 lf-expr-equal ok? must ;
: max-of ( a b -- level ) lf-level-max must ;
\ The identity on Sort n, and a redex equal to node: (fun x : Sort n => x) node.
: id-on ( n -- node ) make-sort 0 make-var make-lam ;
: redex ( node n -- node' ) id-on swap make-app ;

\ ---------------------------------------------------------------------------
\ quick_is_def_eq. Equal terms by Lean's == (distinct nodes), two Sorts by
\ is_equivalent (yes, and no for different universes), two binders.
fresh-session
T{ 0 make-sort 0 make-sort quick -> lf-dq-yes outcome-ok }T
T{ 1 make-sort 2 make-sort quick -> lf-dq-no outcome-ok }T
T{ level-u level-v max-of make-sort level-v level-u max-of make-sort quick
   -> lf-dq-yes outcome-ok }T
T{ level-u make-sort level-v make-sort quick -> lf-dq-no outcome-ok }T
T{ 0 make-sort 0 make-var make-pi 0 make-sort 0 make-var make-pi quick -> lf-dq-yes outcome-ok }T
\ Undecided: an application against a Sort, two bound variables.
T{ 0 make-sort 1 redex 0 make-sort quick -> lf-dq-undef outcome-ok }T
T{ 0 make-var 1 make-var quick -> lf-dq-undef outcome-ok }T

\ is_def_eq_core: step 3 (whnf_core, then quick again) decides a redex;
\ step 10 (is_def_eq_app) an application with a redex argument; Lean's no
\ through quick on Sorts, also inside binders; unknown where only steps
\ LeanForth does not port yet could decide (different variables).
T{ 0 make-sort 1 redex 0 make-sort defeq -> true outcome-ok }T
T{ 0 make-sort 0 make-sort 1 redex defeq -> true outcome-ok }T
T{ 0 make-var 0 make-sort make-app 0 make-var 0 make-sort 1 redex make-app defeq
   -> true outcome-ok }T
T{ 1 make-sort 1 redex 2 make-sort defeq -> false outcome-ok }T
T{ 0 make-sort 0 make-var make-lam 1 make-sort 0 make-var make-lam defeq -> false outcome-ok }T
T{ 0 make-var 1 make-var defeq -> 0 outcome-unknown }T
T{ 0 make-var 0 make-sort make-app 0 make-var defeq -> 0 outcome-unknown }T

\ is_def_eq_binding (ADR 0003 Amendment 1): domains equal only by beta,
\ and a dependent telescope whose second domain names the first binder
\ (read with its free variable, instantiate_rev): (x : Sort 1) -> (y : x)
\ -> y against the same with y : (fun z : Sort 1 => z) x.
: telescope ( domain -- node ) 1 make-sort swap 0 make-var make-pi make-pi ;
T{ 0 make-sort 1 redex 0 make-var make-pi 0 make-sort 0 make-var make-pi defeq
   -> true outcome-ok }T
T{ 0 make-var telescope 0 make-var 1 redex telescope defeq -> true outcome-ok }T
T{ 0 make-var 1 redex telescope 0 make-var telescope defeq -> true outcome-ok }T
\ The free variables of a telescope are popped whatever the outcome.
T{ lf-dq-depth @ -> 0 }T
T{ 0 make-var telescope 1 make-sort telescope defeq lf-dq-depth @ -> 0 outcome-unknown 0 }T

\ is_def_eq_app: the functions, the counts, then the arguments left to
\ right; is_def_eq_args: the last arguments first, the spines end together.
: pair-app ( a b -- node ) 2 make-var rot make-app swap make-app ;
T{ 0 make-sort 1 make-sort pair-app 0 make-sort 1 make-sort pair-app app? -> true outcome-ok }T
T{ 0 make-sort 1 make-sort pair-app 0 make-sort 2 make-sort pair-app app? -> false outcome-ok }T
T{ 0 make-sort 1 make-sort pair-app 2 make-var 0 make-sort make-app app? -> false outcome-ok }T
T{ 0 make-sort 0 make-sort app? -> false outcome-ok }T
T{ 0 make-sort 1 make-sort pair-app 0 make-sort 1 make-sort pair-app args? -> true outcome-ok }T
T{ 0 make-sort 1 make-sort pair-app 2 make-sort 1 make-sort pair-app args? -> false outcome-ok }T
\ The spines end together: f a b against g b (g = f a) holds by args
\ only if both run out of applications at once.
T{ 0 make-sort 1 make-sort pair-app 2 make-var 0 make-sort make-app args? -> false outcome-ok }T
T{ 2 make-var 2 make-var args? -> true outcome-ok }T

\ ---------------------------------------------------------------------------
\ whnf_core: all leading lambdas at once, the other arguments applied
\ again; an argument with a loose bound variable is lifted under the
\ lambda it crosses: (fun x : Sort 1 => fun y : Sort 1 => x) #3 is
\ fun y : Sort 1 => #4, never #3 (that would capture y).
: k-comb ( -- node ) 1 make-sort 1 make-sort 1 make-var make-lam make-lam ;
T{ k-comb 0 make-sort make-app 1 make-sort make-app core swap 0 make-sort same? -> outcome-ok true }T
T{ k-comb 0 make-sort make-app core swap 1 make-sort 0 make-sort make-lam same? -> outcome-ok true }T
T{ k-comb 3 make-var make-app core swap 1 make-sort 4 make-var make-lam same? -> outcome-ok true }T
T{ k-comb 3 make-var make-app 1 make-sort 4 make-var make-lam defeq -> true outcome-ok }T
T{ k-comb 3 make-var make-app 1 make-sort 3 make-var make-lam defeq -> 0 outcome-unknown }T
\ Normal forms are kept as they are (the same node).
T{ 0 make-var 0 make-sort make-app dup core drop = -> true }T

\ cheap_beta_reduce: a body without loose bound variables; a body that is
\ a bound variable (the argument it names); anything else unchanged.
: cheap ( node -- node' outcome ) 100000 fuelled dq lf-cheap-beta ;
T{ 1 make-sort 2 make-sort make-lam 0 make-sort make-app cheap swap 2 make-sort same?
   -> outcome-ok true }T
T{ k-comb 0 make-sort make-app 2 make-sort make-app cheap swap 0 make-sort same?
   -> outcome-ok true }T
: self-app ( -- node ) 1 make-sort 0 make-var 0 make-var make-app make-lam 0 make-sort make-app ;
T{ self-app dup cheap drop = -> true }T

\ ---------------------------------------------------------------------------
\ whnf outside a check: a constant at the head may have a value (K1):
\ unknown, diagnostic 64; whnf_core keeps it (no constant is a recursor).
create no-levels 1 cells allot
: name-of ( c-addr u -- name ) 0 -rot lf-name-str must ;
: const ( name -- node )
  lf-name-generation @ no-levels 0 lf-cref-new must lf-cterm-new must drop ;
T{ lf-diag-clear s" c" name-of const whnf lf-diag-code@ -> -1 outcome-unknown lf-diag-needs-unfolding }T
T{ s" c" name-of const 0 make-sort make-app dup core drop = -> true }T

\ K7 (ADR 0014 Q8): Nat.succ with one argument, a binary Nat operation
\ with two, by name and without universe arguments; not with another
\ count, another name, or Nat.succ as one component.
: nat-name ( c-addr u -- name ) 0 s" Nat" lf-name-str must -rot lf-name-str must ;
: nat ( c-addr u -- node ) nat-name const ;
T{ s" succ" nat 0 make-sort make-app lf-whnf-k7? -> true }T
T{ s" succ" nat 0 make-sort make-app 0 make-sort make-app lf-whnf-k7? -> false }T
T{ s" add" nat 0 make-sort make-app 0 make-sort make-app lf-whnf-k7? -> true }T
T{ s" shiftRight" nat 0 make-sort make-app 0 make-sort make-app lf-whnf-k7? -> true }T
T{ s" add" nat 0 make-sort make-app lf-whnf-k7? -> false }T
T{ s" succ" name-of const 0 make-sort make-app lf-whnf-k7? -> false }T
T{ s" Nat.succ" name-of const 0 make-sort make-app lf-whnf-k7? -> false }T
create one-level 2 cells allot
: leveled ( name -- node )
  0 one-level ! 0 lf-level-identity must one-level cell+ !
  lf-name-generation @ one-level 1 lf-cref-new must lf-cterm-new must drop ;
T{ s" succ" nat-name leveled 0 make-sort make-app lf-whnf-k7? -> false }T

\ ---------------------------------------------------------------------------
\ Every failure outcome, and a fuel sweep: with less fuel a comparison is
\ exhausted until it gives its answer, never another one.
T{ 0 make-sort 1 redex 0 make-sort 0 fuelled dq lf-defeq-on -> 0 outcome-exhausted }T
T{ 0 make-sort 1 redex 0 make-sort 3 fuelled dq lf-defeq-on -> 0 outcome-exhausted }T
T{ -1 0 make-sort defeq nip -> outcome-invalid }T
variable sweep-t variable sweep-s variable sweep-answer
: sweep-pair ( -- ) 0 make-var telescope sweep-t ! 0 make-var 1 redex telescope sweep-s ! ;
: sweep-once ( fuel -- outcome ) fuelled sweep-t @ sweep-s @ dq lf-defeq-on nip ;
: sweep ( -- first-ok )
  sweep-pair 0 begin dup sweep-once dup outcome-exhausted = while drop 1+ repeat
  ok? must ;
T{ sweep 0> -> true }T
\ Above the first fuel that answers, every fuel gives the same answer.
: answers? ( from -- flag )
  true swap dup 40 + swap ?do i sweep-once ok? and loop ;
T{ sweep answers? -> true }T
\ Full: the frames' stack the heap cannot grow.
dq frame-free  1 heap-refusals !
T{ 0 make-sort 1 redex 0 make-sort 100 fuelled dq lf-defeq-on -> 0 outcome-full }T
0 heap-refusals !
dq frame-free
bye
