\ Unit tests of tactic batch 2a (plan row TB2) over decide's slice of Init
\ in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: the shapes of tactic-syntax.fs (read as
\ records), telescope.fs's mkLetDecl and mkLetFVars, meta-tactic/
\ assert.fs's lf-goal-have, lf-goal-let, lf-goal-have-with and lf-goal-try-clear,
\ tactic-core.fs's elabType hook, and each tactic word of tactics/have.fs
\ and replace.fs through LeanForth text (tests/support/tactic-text.fs):
\ 1. outcomes: each word accepted, each refusal with its code (96, 130,
\    2, 84, 86), each case not ported (99, 93; unsupported thrown by the
\    library words);
\ 2. malformed input: a missing name, a name that is a word, the name on
\    the next line, too few values, an assigned goal (invalid), a let past
\    the first variable and a let over a natural metavariable
\    (unsupported);
\ 3. stack effects: each T{ }T checks the depth; the shapes' fields;
\ 5. resources (tests/support/meta-sweeps.fs): lf-goal-have, lf-goal-let,
\    lf-goal-have-with, lf-goal-try-clear and lf-let-decl-new with every
\    heap allocation refused in turn and with room for every count of
\    terms (and local context entries) in turn, by-have-goal: through
\    its text with every heap allocation refused: the answer or full,
\    never another answer (tryClear passes full on);
\ 6. state: the goal assigned, the new local's kind (let, have) and
\    binder, the cleared or kept hypothesis, the hook put back, the body
\    of an assigned goal never made; two lets bound at once, with no
\    variable e itself; the terms are checked node for node with pinned
\    Lean by check.py.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
include ../../../support/heap-watch.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/decide-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/decide-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" batch-b test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: local+ ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: tagged ( type -- goal ) goal dup s" t" lfa-intern lf-mvar-tag! made ;
: code1 ( x xt -- code ) catch dup if nip then ;
: le ( x y -- t ) s" LE.le" 2swap 2 lf-mk-app-m ;
: view# ( goal -- n ) lf-goal-view lf-view-count ;
: open? ( mvar -- flag ) lf-goal-assigned? 0= ;
: newest ( goal -- fvar ) lf-goal-view dup lf-view-count 1- lf-view-fvar ;
: nm ( c-addr u -- id ) lfa-intern ;

\ ---- 3. The shapes: their fields, as made.
T{ 2 1 tac-shape-term-names dup shape-want @ swap shape-names @ -> 2 1 }T
T{ tac-shape-decl dup shape-want @ swap shape-names @ -> 2 1 }T
T{ 1 tac-shape-term-this dup shape-want @ swap shape-names @ -> 1 0 }T
T{ 3 tac-shape-terms dup shape-want @ swap shape-names @ -> 3 0 }T
T{ tac-shape-plain shape-want @ tac-shape-term shape-want @ tac-shape-name shape-names @
   -> 0 1 1 }T
T{ tac-shape-rules shape-want @ tac-shape-rules shape-names @ -> 0 0 }T

\ ---- 1. Records: by-have:'s step holds T, e and the name; by-have's e and
\ this; by-intro: still one name, the next token the next step's.
: vars ( -- c-addr u ) s" Nat explicit: a Nat explicit: b " ;
create stmt 512 allot  variable stmt#
: stmt+ ( c-addr u -- ) tuck stmt stmt# @ + swap move stmt# +! ;
: st ( c-addr u -- c-addr' u' ) 0 stmt# ! vars stmt+ stmt+ stmt stmt# @ ;
: hab ( -- c-addr u ) s" a b ≤ explicit: h a b ≤" st ;
: step@ ( i -- addr ) lf-tactic-step ;
: arg@ ( i k -- x ) swap step@ tac-first @ + lf-tactic-arg drop ;
T{ hab s" a b ≤ ' h by-have: k ' k by-exact" tactic-ran -> 0 }T
T{ 1 step@ tac-kind @ 1 step@ tac-count @ 1 2 arg@ s" k" nm = -> tac-k-have 3 true }T
T{ 1 step@ tac-shape @ tac-shape-decl = -> true }T
T{ 1 1 arg@ syn-kind@ 2 step@ tac-kind @ -> syn-k-var tac-k-exact }T
T{ hab s" ' h by-have ' this by-exact" tactic-ran -> 0 }T
T{ 1 step@ tac-count @ 1 1 arg@ s" this" nm = -> 2 true }T
T{ hab s" ' h by-revert by-intro: k ' k by-exact" tactic-ran -> 0 }T
T{ 2 step@ tac-count @ 2 step@ tac-shape @ tac-shape-name = 3 step@ tac-kind @
   -> 1 true tac-k-exact }T
lf-tac-forget
\ 2. Malformed: the name a word (84: end, by-exact), missing on its line
\ (2); too few values (86); _ is read (inaccessible), not supported (99).
T{ hab s" a b ≤ ' h by-have:" tactic-ran -> 84 }T
T{ hab s" a b ≤ ' h by-have: by-exact" tactic-ran -> 84 }T
T{ hab s\" a b \xe2\x89\xa4 ' h by-have:\n k ' k by-exact" tactic-ran -> 2 }T
T{ hab s" ' h by-have: k" tactic-ran -> 86 }T
T{ hab s" by-have" tactic-ran -> 86 }T
T{ hab s" a b ≤ ' h by-have: _ ' h by-exact" tactic-ran -> 99 }T
T{ 1 2 arg@ -> 0 }T
lf-tac-forget

\ ---- telescope.fs: mkLetDecl, a let and a have.
fresh
nat s" a" local+ constant fa
nat s" b" local+ constant fb
fa fb le constant ab-le
fb fa le constant ba-le
ab-le s" h" local+ constant fh
T{ nat fa s" x" nm false lf-let-decl-new lf-view-count swap dup lf-fvar-let? swap
   lf-fvar-nondep? -> 4 true false }T
T{ ab-le fh s" k" nm true lf-let-decl-new drop dup lf-fvar-let? over lf-fvar-nondep?
   rot lf-fvar-value fh = -> false true true }T
\ Its local explicit, named as given.
: newest-local ( view -- local ) dup lf-view-count 1- lf-view-local ;
T{ ab-le fh s" k" nm true lf-let-decl-new nip newest-local dup lf-local-binder
   swap lf-local-name s" k" nm = -> lf-binder-default true }T

\ ---- assert.fs: lf-goal-have and lf-goal-let; the goal assigned
\ let k : T := v; ?_ (the binder over ?n k, delayed-assigned ?_).
ab-le tagged constant g1
g1 s" k" nm ab-le fh lf-goal-have constant g1'
T{ g1' lf-goal-type ab-le = g1' lf-goal-tag g1 lf-goal-tag = g1' view# g1 view# 1+ =
   g1' lf-goal-kind mv-opaque = -> true true true true }T
T{ g1' newest dup lf-fvar-nondep? swap lf-fvar-type ab-le = g1 open? -> true true false }T
T{ g1' fh lf-mvar-assign g1 lf-instantiate! dup lf-let? swap dup lf-let-nondep swap
   lf-let-value fh = -> outcome-ok true true true }T
T{ g1 lf-instantiate! dup lf-let-type ab-le lf-meta-eqv made swap lf-let-body fh =
   -> true true }T
ab-le tagged constant g2
g2 s" x" nm nat fa lf-goal-let constant g2'
T{ g2' newest dup lf-fvar-let? swap lf-fvar-value fa = -> true true }T
T{ g2' fh lf-mvar-assign g2 lf-instantiate! dup lf-let-nondep swap lf-let-value fa =
   -> outcome-ok false true }T
\ 2. An assigned goal is refused (invalid), before the body is made.
: let-again ( goal -- ) s" k" nm ab-le fh lf-goal-have drop ;
T{ g1 ' let-again code1 -> thrown-invalid }T
variable body-made
: body-noted ( goal -- e ) drop true body-made ! fh ;
: with-again ( goal -- ) s" k" nm ab-le fh ['] body-noted lf-goal-have-with drop ;
T{ false body-made ! g1 ' with-again code1 body-made @ -> thrown-invalid false }T
\ lf-goal-have-with: a closed body (suffices' e), still bound by the let.
: body-fh ( goal -- e ) drop fh ;
ba-le tagged constant g3
T{ g3 s" k" nm ab-le fh ' body-fh lf-goal-have-with fh = -> true }T
T{ g3 lf-instantiate! dup lf-let? swap lf-let-body fh = -> true true }T
T{ ab-le tagged lf-goal-target swap ab-le = swap s" t" nm = -> true true }T
\ A target that is an assigned metavariable: instantiated (getMainTarget).
ab-le lf-infer! mv-natural lf-mvar-new made constant m1
T{ m1 ab-le lf-mvar-assign m1 tagged lf-goal-target drop ab-le = -> outcome-ok true }T

\ ---- lf-goal-try-clear: h cleared; a, which h's type names, kept.
ab-le tagged constant g4
T{ g4 fh lf-goal-try-clear dup g4 = swap view# -> false 2 }T
ab-le tagged constant g5
T{ g5 fa lf-goal-try-clear g5 = g5 open? -> true true }T

\ ---- 5. Resources: each goal operation on a new goal of ab-le, with
\ every heap allocation refused in turn (the frame slabs given back
\ first) and with room for every count of terms in turn: the answer (the
\ new goal's context's size, the body) or full, never another answer.
\ tryClear keeps the goal only when clear refuses invalid: full is
\ passed on, never read as "cannot clear".
: frames-anew ( -- ) mat-frames sweep-slab-anew tl-frames sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
s" k" nm constant nk  s" x" nm constant nx
: new-goal ( type -- goal ) 0 lf-mctx-view lf-goal-new lf-must ;
: s-have ( type -- n ) new-goal nk ab-le fh lf-goal-have view# ;
: s-let ( type -- n ) new-goal nx nat fa lf-goal-let view# ;
: s-with ( type -- e ) new-goal nk ab-le fh ['] body-fh lf-goal-have-with ;
: s-clear ( type -- n ) new-goal fh lf-goal-try-clear view# ;
: s-let-decl ( type -- n ) drop ab-le fh nk true lf-let-decl-new nip lf-view-count ;
: caught ( type xt -- x outcome ) 1 1 lf-meta-catch ;
: p-have ( type -- n outcome ) ['] s-have caught ;
: p-let ( type -- n outcome ) ['] s-let caught ;
: p-with ( type -- e outcome ) ['] s-with caught ;
: p-clear ( type -- n outcome ) ['] s-clear caught ;
: p-let-decl ( type -- n outcome ) ['] s-let-decl caught ;
: both-swept ( type xt -- heap? room? )
  2dup heap-sweep swept? >r room-sweep swept? r> swap ;
T{ ab-le ' p-have both-swept ab-le ' p-let both-swept -> true true true true }T
T{ ab-le ' p-with both-swept ab-le ' p-clear both-swept -> true true true true }T
\ mkLetDecl makes no heap block: its terms, and its local context entry.
T{ ab-le ' p-let-decl room-sweep swept? -> true }T
' lf-lctx sweep-store-xt !
T{ ab-le ' p-let-decl room-sweep swept? ab-le ' p-have room-sweep swept? -> true true }T
' lf-terms sweep-store-xt !

\ ---- mkLetFVars: none gives e; a let past the first variable, or over a
\ natural metavariable, is not supported (unsupported thrown).
create xs 2 cells allot
T{ fh xs 0 lf-mk-let-fvars fh = -> true }T
\ With none, e itself, not instantiated (Lean's mkLambdaFVars,
\ mkForallFVars and mkLetFVars of #[]): m1 is assigned ab-le.
: none-bound? ( xt -- flag ) >r m1 xs 0 r> execute m1 = ;
T{ ' lf-mk-lambda-fvars none-bound? ' lf-mk-forall-fvars none-bound?
   ' lf-mk-let-fvars none-bound? -> true true true }T
: two-lets ( -- e ) ab-le goal xs 2 lf-mk-let-fvars ;
fresh
nat s" a" local+ drop
nat s" c" local+ xs !
nat fa s" y" nm false lf-let-decl-new lf-mctx-view! xs cell+ !
T{ ' two-lets catch -> thrown-unsupported }T
: natural-let ( -- e ) ab-le mv-natural lf-mvar-new made xs cell+ 1 lf-mk-let-fvars ;
T{ ' natural-let catch -> thrown-unsupported }T
: lambda-let ( -- e ) fa xs cell+ 1 lf-mk-lambda-fvars ;
T{ ' lambda-let catch -> thrown-unsupported }T
\ Two lets, the second's value naming the first: let x : Nat := a;
\ let y : Nat := #0; #0, each value abstracted over the variables before it.
fresh
nat s" a" local+ constant fa3
nat fa3 s" x" nm false lf-let-decl-new lf-mctx-view! constant fx
nat fx s" y" nm false lf-let-decl-new lf-mctx-view! constant fy
create xy fx , fy ,
0 lf-term-bvar drop constant bv0
: two-bound ( -- e ) fy xy 2 lf-mk-let-fvars ;
: bv0? ( t -- flag ) bv0 lf-meta-eqv made ;
T{ two-bound dup lf-let-value fa3 = swap lf-let-body dup lf-let-value bv0?
   swap lf-let-body bv0? -> true true true }T

\ ---- elabType's hook: without the elaborator, 71; put back after.
action-of lf-tac-elab-as-type constant real-type
' tcr-untyped is lf-tac-elab-as-type
T{ hab s" a b ≤ ' h by-have: k ' k by-exact" tactic-ran -> 71 }T
real-type is lf-tac-elab-as-type
lf-tac-forget

\ ---- The tactics through LeanForth text.
: hab2 ( -- c-addr u ) s" a b ≤ explicit: h b a ≤ explicit: h2 a b ≤" st ;
T{ hab s" b a ≥ ' h by-have: k ' k by-exact" tactic-ran -> 0 }T
T{ hab s" b a ≤ ' h by-have: k" tactic-ran -> 96 }T
T{ hab s" a ' h by-have: k" tactic-ran -> 130 }T
T{ hab s" ' Nat.le_trans by-have ' h by-exact" tactic-ran -> 93 }T
\ A cleared hypothesis named again (Lean's unknown identifier): 76, as
\ elab-term.fs refuses a name the goal's context lacks.
T{ hab s" ' h by-clear a b ≤ ' h by-have: k" tactic-ran -> 76 }T
T{ hab s" ' h by-clear ' h by-have" tactic-ran -> 76 }T
T{ s" a b ≤ explicit: h b a ≤" st s" ' h by-have ' this by-exact" tactic-ran -> 96 }T
T{ hab s" Nat a by-let: x ' h by-exact" tactic-ran -> 0 }T
T{ s" a a ≤" st s" Nat a by-let: x ' Nat.le_refl x $ by-exact" tactic-ran -> 0 }T
T{ hab s" Nat ' h by-let: x" tactic-ran -> 96 }T
T{ hab2 s" b a ≤ ' h by-suffices: k ' h2 by-exact" tactic-ran -> 0 }T
T{ hab s" b a ≥ ' h by-suffices: h ' h by-exact" tactic-ran -> 0 }T
T{ hab2 s" a b ≤ ' h2 by-suffices: k" tactic-ran -> 96 }T
T{ hab s" b a ≤ by-suffices: k" tactic-ran -> 86 }T
T{ hab s" a b ≤ by-have-goal: k ' h by-exact ' k by-exact" tactic-ran -> 0 }T
T{ hab s" b a ≤ by-have-goal: k ' h by-exact" tactic-ran -> 96 }T
T{ hab s" b a ≤ by-have-goal: k ' h by-exact ' h by-exact" tactic-ran -> 96 }T
T{ hab s" a by-have-goal: k" tactic-ran -> 130 }T
T{ hab s" a b ≤ by-have-goal: _" tactic-ran -> 99 }T
T{ s" a b ≤ explicit: h b a ≤ explicit: h2 b a ≥" st s" b a ≥ ' h by-replace: h ' h by-exact"
   tactic-ran -> 0 }T
T{ hab s" a b ≤ ' h by-replace: k ' k by-exact" tactic-ran -> 0 }T
T{ hab s" Nat ' a by-replace: a ' h by-exact" tactic-ran -> 0 }T
T{ hab s" b a ≤ ' h by-replace: h" tactic-ran -> 96 }T
\ The replaced h is gone: only the new one, b ≥ a, is left to name.
T{ hab2 s" b a ≥ ' h by-replace: h ' h by-exact" tactic-ran -> 0 }T
T{ hab2 s" b a ≤ ' h2 by-replace: h ' h by-exact" tactic-ran -> 96 }T
lf-tac-forget
\ 5. by-have-goal: through the text (its new goals, run-push), every heap
\ allocation of the run refused in turn: accepted, or full (error 60, 88
\ or another out of room), never another error.
: p-have-goal ( type -- code outcome )
  drop hab s" a b ≤ by-have-goal: k ' h by-exact ' k by-exact" text-full ;
T{ 0 ' p-have-goal heap-sweep swept? -> true }T
lf-tac-forget
.( batch-b test.fs: all tests passed) cr
