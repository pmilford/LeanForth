\ Unit tests of case patterns, slice E2b (plan row TB2, piece E; design
\ docs/design/TACTIC_PATTERNS.md) over decide's slice of Init in an
\ authoring run: by-contra[ ], by-contra: and by-contra read as rintro
\ patterns (pattern-syntax.fs), tactic-run.fs's lf-tac-ported,
\ meta-must.fs's lf-meta-try, and contradiction's rule 6
\ (meta-tactic/contradiction.fs, Lean's elimEmptyInductive) called on
\ goals built here.
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
: made ( x outcome -- x ) ok? 0= abort" batch-h2 test: not made" ;
lf-meta-throw-base outcome-rejected - constant thrown-rejected
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
: authored ( code -- n ) dup lf-author-throw = if drop lf-author-code lf-tac-forget then ;
: code1 ( x xt -- code ) catch dup if nip then authored ;
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: binder ( type c-addr u -- fvar )
  lfa-intern swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: open? ( goal -- flag ) lf-goal-assigned? 0= ;
create xs 1 cells allot
: lam1 ( e x -- e' ) xs ! xs 1 lf-mk-lambda-fvars ;

\ ---- 1. The reader: by-contra[ pat ] is rintro's sequence of one
\ pattern; by-contra: NAME and by-contra the same with NAME or this.
: st ( -- c-addr u ) s" Nat explicit: a Nat explicit: b b a = ¬ explicit: k a b = b a = ∧ ¬" ;
: parg ( k -- x span ) 1 lf-tactic-step tac-first @ + dup lf-tactic-arg drop swap lf-tactic-arg-span ;
: name? ( x c-addr u -- flag ) lfa-intern lf-name-same? ;
T{ st s" by-contra[ << hab hba >> ] by-contradiction" tactic-ran 1 lf-tactic-step tac-count @
   -> 0 4 }T
T{ 0 parg swap s" hab" name? 1 parg swap s" hba" name? 2 parg 3 parg -> 1 true 1 true pat-tuple 3 pat-seq 4 }T
: sn ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h a b =" ;
T{ sn s" by-contra: k by-contradiction" tactic-ran 0 parg swap s" k" name? 1 parg -> 0 1 true pat-seq 2 }T
T{ sn s" by-contra by-contradiction" tactic-ran 0 parg swap s" this" name? 1 parg -> 0 1 true pat-seq 2 }T
T{ sn s" by-contra: _ by-contradiction" tactic-ran 0 parg -> 0 0 1 }T
T{ s" Nat explicit: a Nat explicit: b a a = ¬ explicit: h a b = ¬" s" by-contra: rfl by-contradiction"
   tactic-ran 0 parg -> 0 pat-rfl 1 }T
\ Refusals: one pattern (474: two, none), a bar first or last (472), a
\ closer of another bracket or none (473), a word (458), @ (72).
T{ sn s" by-contra[ k j ]" tactic-ran sn s" by-contra[ ]" tactic-ran -> 474 474 }T
T{ sn s" by-contra[ | k ]" tactic-ran sn s" by-contra[ k | ]" tactic-ran -> 472 472 }T
T{ sn s" by-contra[ << k ]" tactic-ran sn s" by-contra[ k >> ]" tactic-ran -> 473 473 }T
T{ sn s" by-contra[ k by-rfl ]" tactic-ran sn s" by-contra[ @k ]" tactic-ran -> 458 72 }T
\ The patterns rintro takes: alternatives on a disjunction, - (cleared).
T{ s" Nat explicit: a Nat explicit: b a b = ¬ explicit: h b a = ¬ explicit: k a b = b a = ∨ ¬"
   s" by-contra[ h1 | h2 ] by-contradiction by-contradiction" tactic-ran -> 0 }T
T{ s" False explicit: h True ¬" s" by-contra[ - ] ' h by-exact" tactic-ran -> 0 }T
T{ s" Nat explicit: a Nat explicit: b False explicit: h True ¬" s" by-contra[ - ] by-assumption"
   tactic-ran -> 0 }T
lf-tac-forget

\ ---- 2. lf-tac-ported: a Meta refusal thrown unsupported is 99; a Lean
\ error (rejected) and any other THROW pass on; nothing thrown, nothing
\ changed.
: unsup ( -- ) outcome-unsupported lf-must ;
: rejd ( -- ) outcome-rejected lf-must ;
: unported ( -- ) lf-tac-unported ;
: ported ( xt -- code ) ['] lf-tac-ported code1 ;
T{ ' unsup ported ' rejd ported ' unported ported -> 99 thrown-rejected 99 }T
T{ 5 ' 1+ lf-tac-ported -> 6 }T
T{ 7 ' abort ' lf-tac-ported catch nip nip -> -1 }T
lf-tac-forget

\ ---- 3. lf-meta-try: true after xt, false after a Lean error with its
\ out cells dropped, any other failure thrown.
: two-rejd ( x -- y z ) drop rejd 0 0 ;
: two-unsup ( x -- y z ) drop unsup 0 0 ;
T{ 3 ' dup 1 2 lf-meta-try -> 3 3 true }T
T{ 3 ' two-rejd 1 2 lf-meta-try -> false }T
T{ 3 ' two-unsup 1 2 ' lf-meta-try catch nip nip nip nip -> thrown-unsupported }T

\ ---- 4. Rule 6 (elimEmptyInductive): h : (fun _ : Nat => False) a has
\ a free variable (rule 5 passes it over) and whnfD False, no constructor:
\ exfalso, cases on h, the goal closed by False.casesOn. True (one
\ constructor), False ∧ True (one constructor: it only looks empty) and
\ a ≤ b (an index, slice E4: 99) are no such hypothesis.
fresh
nat s" a" binder constant fa
nat s" b" binder constant fb
: beta ( p -- t ) fa lam1 fa lf-mk-app ;
: false-of ( -- t ) s" False" lf-mk-const0 beta ;
: true-of ( -- t ) s" True" lf-mk-const0 beta ;
: and-of ( p q -- t ) s" And" lf-mk-const0 rot lf-mk-app swap lf-mk-app ;
: le-of ( x y -- t ) s" LE.le" 2swap 2 lf-mk-app-m ;
lf-mctx-view constant view-ab
: goal-with ( type c-addr u -- goal ) view-ab lf-mctx-view! binder drop fa fb lf-mk-eq goal ;
: contra ( goal -- code ) ['] lf-goal-contradiction code1 ;
false-of s" h" goal-with constant g-false
T{ g-false contra g-false open? -> 0 false }T
T{ g-false lf-instantiate! lf-meta-head s" False.elim" lf-meta-const-named? -> true }T
T{ g-false lf-instantiate! lf-has-open-mvar? -> false }T
T{ true-of s" h" goal-with dup contra swap open? -> 449 true }T
T{ false-of true-of and-of s" h" goal-with dup contra swap open? -> 449 true }T
T{ fa fb le-of s" h" goal-with dup contra swap open? -> 99 true }T
\ A hypothesis that is no candidate before one that is.
view-ab lf-mctx-view! true-of s" k" binder drop false-of s" h" binder drop
fa fb lf-mk-eq goal constant g-later
T{ g-later contra g-later open? -> 0 false }T
lf-tac-forget

\ ---- 5. Resources: rule 6 called directly and by-contra[ ] through
\ text, every heap allocation refused in turn: the answer or full.
: frames-anew ( -- ) mcd-frames sweep-slab-anew mcs-frames sweep-slab-anew
  mid-frames sweep-slab-anew mri-frames sweep-slab-anew mrv-frames sweep-slab-anew
  mti-frames sweep-slab-anew rcs-frames sweep-slab-anew pat-frames sweep-slab-anew
  lfa-brackets sweep-slab-anew ;
: context-anew ( -- ) frames-anew sweep-view-anew ;
view-ab lf-mctx-view! false-of s" h" binder drop sweep-keep-view
' context-anew sweep-slabs-xt !
: d-rule6 ( x -- open? outcome )
  drop fa fb lf-mk-eq goal dup ['] lf-goal-contradiction 1 0 lf-meta-catch swap open? swap ;
T{ 0 ' d-rule6 heap-sweep swept? -> true }T
' frames-anew sweep-slabs-xt !
: p-contra ( x -- code outcome )
  drop st s" by-contra[ << hab hba >> ] by-contradiction" text-full ;
T{ 0 ' p-contra heap-sweep swept? -> true }T
lf-tac-forget
.( batch-h2 test.fs: all tests passed) cr
