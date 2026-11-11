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
\ yes, eta against a free variable (plan task 4.2.4; proof irrelevance
\ needs a typer: tests/core/definite-rejection.fs and the table rows),
\ every outcome (yes, no, unknown, exhausted, full, invalid) and a
\ fuel sweep; whnf on a constant outside a check (K1), Lean's name-matched
\ Nat operations (K7) and cheap_beta_reduce. With definitions, in a
\ check: tests/core/whnf.fs. Test-only; nothing here accepts a theorem.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/main.fs
include ../support/plain-terms.fs
require ../support/store-faults.fs

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
T{ 0 make-var telescope 1 make-sort telescope defeq lf-dq-depth @ -> 0 outcome-ok 0 }T

\ Two different free variables (the bodies of fun x y => x and fun x y =>
\ y), whose type is a Sort (so no proof, step 4, and no unit-like type,
\ step 14), nothing unfolds: Lean's no (plan task 4.2.2d). Loose bound
\ variables (above) have no type a bare call can see: no is unknown.
: two-lams ( body -- node ) 1 make-sort swap make-lam 1 make-sort swap make-lam ;
T{ 1 make-var two-lams 0 make-var two-lams defeq -> 0 outcome-ok }T
T{ 1 make-var two-lams 1 make-var two-lams defeq -> true outcome-ok }T

\ Eta (step 11, plan task 4.2.4) where the other side is a free variable,
\ whose type a bare call knows: fun (f : Sort 1 -> Sort 1) => fun x =>
\ f x against fun f => f is Lean's yes, in both orders (the lambda on
\ either side). The wrong function, fun f g => fun x => f x against fun f
\ g => g, is a no that the skipped step 4 (no typer: is the lambda a
\ proof?) makes unknown. With less fuel the yes is exhausted, never
\ another answer.
: arrow1 ( -- node ) 1 make-sort 1 make-sort make-pi ;
: eta-of ( var -- node ) 1 make-sort swap 0 make-var make-app make-lam ;
: over-f ( body -- node ) arrow1 swap make-lam ;
: eta-pair ( -- t s ) 1 make-var eta-of over-f 0 make-var over-f ;
T{ eta-pair defeq -> true outcome-ok }T
T{ eta-pair swap defeq -> true outcome-ok }T
T{ 2 make-var eta-of over-f over-f 0 make-var over-f over-f defeq -> 0 outcome-unknown }T
variable eta-t variable eta-s
: eta-fuel-ok? ( fuel -- flag )
  fuelled eta-t @ eta-s @ dq lf-defeq-on
  dup outcome-exhausted = if 2drop true else ok? and then ;
: eta-sweep ( -- flag ) eta-pair eta-s ! eta-t ! true 60 0 do i eta-fuel-ok? and loop ;
T{ eta-sweep 60 eta-fuel-ok? 0 eta-fuel-ok? -> true true true }T
T{ 60 fuelled eta-t @ eta-s @ dq lf-defeq-on -> true outcome-ok }T
T{ 0 fuelled eta-t @ eta-s @ dq lf-defeq-on -> 0 outcome-exhausted }T

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
T{ 0 make-sort 1 make-sort pair-app 2 make-var 1 make-sort make-app args? -> false outcome-ok }T
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

\ cheap_proj (whnf.fs; plan task 5.2.2): reduce_proj's visit of a
\ projection's term is whnf_core in a cheap whnf_core visit's mode, else
\ whnf -- told apart by a constant: whnf_core keeps it, whnf is unknown
\ (K1). A visit that changes the mode pushes the step that puts it back
\ (one cell), one that keeps it pushes nothing; after a cheap visit the
\ mode is put back.
: proj-term ( node flag -- node' outcome )
  lf-whnf-cheap ! 100000 fuelled dq ['] lf-whnf-proj-call frame-through drop lf-whnf-reset ;
T{ s" c" name-of const dup true proj-term -rot = -> outcome-ok true }T
T{ s" c" name-of const false proj-term nip -> outcome-unknown }T
T{ dq frame-reset dq true lf-whnf-mode frame-used @ lf-whnf-cheap? -> 1 true }T
T{ 0 outcome-ok dq dq frame-restore execute nip nip nip lf-whnf-cheap? -> 0 false }T
T{ dq frame-reset dq false lf-whnf-mode frame-used @ lf-whnf-cheap? -> 0 false }T
: cheap-core ( node -- node' outcome )
  100000 fuelled dq ['] lf-whnf-cheap-call frame-through drop ;
T{ s" c" name-of const cheap-core nip lf-whnf-cheap? -> outcome-ok false }T
\ Lean's is_proj, is_app and get_app_fn (defeq.fs): a projection, a node
\ of its own over a projection leaf and its term, is no application; the
\ function of (p.0 a) is p.0, with one argument.
: proj-of ( node -- node' )
  s" P" name-of 0 lf-hterm-proj must drop swap lf-tag-projection lf-term-binary must ;
T{ 0 make-var proj-of dup lf-dq-proj? swap lf-dq-app? -> true false }T
T{ 0 make-var proj-of dup 1 make-var make-app lf-dq-fn -rot = -> 1 true }T
T{ 0 make-var proj-of 1 make-var make-app dup lf-dq-proj? swap lf-dq-app? -> false true }T

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

\ Step 6: the same constant with equivalent universe arguments; with
\ universe arguments that differ (Sort 1 and Sort 2 levels) not shown
\ equal: unknown (only lazy delta, plan task 4.2.2d, could unfold them).
: c-at ( level -- node )
  dup one-level ! lf-level-identity must one-level cell+ !
  s" c" name-of lf-name-generation @ one-level 1 lf-cref-new must lf-cterm-new must drop ;
T{ 1 c-at 1 c-at defeq -> true outcome-ok }T
T{ 1 c-at 2 c-at defeq -> 0 outcome-unknown }T
T{ level-u level-v max-of c-at level-v level-u max-of c-at defeq -> true outcome-ok }T

\ cheap_beta_reduce in inference (type_checker.cpp 140): fun (A : Sort 1)
\ (h : (fun T : Sort 1 => T) A) => h has the type (A : Sort 1) -> (h :
\ (fun T : Sort 1 => T) A) -> A, the body's type reduced, not left a redex.
: wrapped-id ( -- node )
  1 make-sort  1 make-sort 0 make-var make-lam 0 make-var make-app  0 make-var make-lam
  make-lam ;
: wrapped-type ( -- node )
  1 make-sort  1 make-sort 0 make-var make-lam 0 make-var make-app  1 make-var make-pi
  make-pi ;
T{ empty-token wrapped-id handle 100000 lf-mixed-infer nip swap wrapped-type same?
   -> outcome-ok true }T

\ No depth limit (plan task 6.2.0): two telescopes of 5,000 binders with
\ equal domains, whose bodies differ (Sort 1, Sort 2): Lean's no, the
\ binders walked as steps of the frames' loop, the host's stacks flat.
65536 lf-term-capacity! ok? must
: pis ( body n -- node ) 0 ?do 0 make-sort swap make-pi loop ;
T{ fresh-session 1 make-sort 5000 pis 2 make-sort 5000 pis 1000000 fuelled dq lf-defeq-on
   -> false outcome-ok }T

\ ---------------------------------------------------------------------------
\ String literals (plan task 5.2.3, strings; core/string-literals.fs and
\ kernel/string-literals.fs): leaves of valid UTF-8 only; == by their
\ bytes; quick_is_def_eq's no for two literals apart, also against a
\ natural-number literal; whnf keeps a literal; string_lit_to_constructor
\ over the code points, last built first, one unit of fuel a character;
\ when step 13 applies.
fresh-session
: str ( c-addr u -- node ) lf-str-new ok? must drop ;
T{ s\" a\xc3" lf-str-new -> 0 0 outcome-invalid }T
T{ s\" \xed\xa0\x80" lf-str-new -> 0 0 outcome-invalid }T
T{ s\" \xc0\xaf" lf-str-new -> 0 0 outcome-invalid }T
: twins ( -- t s ) s" ab" str s" ab" str ;
T{ twins = -> false }T
T{ twins quick -> lf-dq-yes outcome-ok }T
T{ s" ab" str s" ac" str quick -> lf-dq-no outcome-ok }T
T{ s" " str s" " str quick -> lf-dq-yes outcome-ok }T
T{ s" " str 0 lf-hterm-cell must drop quick -> lf-dq-no outcome-ok }T
T{ 0 lf-hterm-cell must drop s" " str quick -> lf-dq-no outcome-ok }T
T{ s" ab" str dup whnf drop = -> true }T
T{ s" ab" str dup core drop = -> true }T
\ The audit's field check: inside the bytes in use, both nonnegative.
T{ 0 lf-str-bytes slab-count lf-str-fields? -> true }T
T{ 1 lf-str-bytes slab-count lf-str-fields? -> false }T
T{ -1 1 lf-str-fields? 0 -1 lf-str-fields? -> false false }T
\ The constructor form: String.ofList, then List.cons.{0} Char (Char.ofNat
\ c) .. ending in List.nil.{0} Char.
: expanded ( leaf fuel -- node outcome ) fuelled dq lf-str-expand ;
: str-list ( node -- list ) lf-term-second@ ;
: code-of ( list -- u ) lf-term-first@ lf-term-second@ lf-term-second@ lf-lit-cell ;
: tail-of ( list -- list' ) lf-term-second@ ;
: length-of ( list -- n )
  0 swap begin dup lf-mhead-spine nip 3 = while tail-of swap 1+ swap repeat
  lf-mhead-spine nip 1 = and ;
: form-of ( c-addr u -- list flag )
  str 100 expanded ok? must dup str-list swap lf-sx-string-app? ;
: codes-of ( list -- u1 u2 u3 ) dup code-of swap tail-of dup code-of swap tail-of code-of ;
T{ s\" a\xc3\xa9\xf0\x9f\x98\x80" form-of swap dup length-of swap codes-of
   -> true 3 $61 $e9 $1f600 }T
T{ s" " form-of swap length-of -> true 0 }T
T{ s" abc" str 2 expanded -> -1 outcome-exhausted }T
T{ s" abc" str 3 expanded nip dq frame-fuel @ -> outcome-ok 0 }T
\ Bytes that are no UTF-8 character (a corrupted leaf): invalid.
: cut ( leaf -- leaf ) 1 over term-second! ;
T{ s\" \xc3\xa9" str cut 100 expanded -> -1 outcome-invalid }T
\ Step 13 applies to a literal t and String.ofList x as s alone: not to a
\ String.ofList with a universe argument, with two arguments, or of
\ another name, nor to t and s swapped (the step tries both orders). Its
\ comparisons need a check in which String.ofList does not unfold (lazy
\ delta comes first): the table's primitive.string-opaque-* rows.
: of-list-name ( -- name )
  s" ofList" 0 s" String" lf-name-str must -rot lf-name-str must ;
: of-list ( -- node ) of-list-name const ;
T{ of-list 0 make-sort make-app lf-sx-string-app? -> true }T
T{ of-list-name leveled 0 make-sort make-app lf-sx-string-app? -> false }T
T{ s" ofList" name-of const 0 make-sort make-app lf-sx-string-app? -> false }T
T{ of-list lf-sx-string-app? -> false }T
T{ of-list 0 make-sort make-app 0 make-sort make-app lf-sx-string-app? -> false }T
: x-of-list ( -- node ) of-list 0 make-sort make-app ;
: x-other ( -- node ) s" c" name-of const 0 make-sort make-app ;
T{ s" ab" str x-of-list lf-sx-applies? -> true }T
T{ x-of-list s" ab" str lf-sx-applies? -> false }T
T{ s" ab" str x-other lf-sx-applies? -> false }T
T{ 0 lf-hterm-cell must drop x-of-list lf-sx-applies? -> false }T

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
