\ Unit tests of tactic batch 3a (plan row TB2) over decide's slice of Init
\ in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: the reader's at: (tactic-syntax.fs, read as
\ records), tactic-core.fs's location words and lf-with-location,
\ app-builder.fs's lf-const-meta-applied, the goal operations
\ meta-tactic/assert.fs's lf-goal-replace-local-decl and
\ lf-goal-change-local-decl, symm.fs's lf-symm-expr and lf-goal-symm-at,
\ goal.fs's rfl changes, and each tactic word with at: through LeanForth
\ text (tests/support/tactic-text.fs):
\ 1. outcomes: each word at a hypothesis accepted, each refusal with its
\    code (455, 215, 456, 448, 457, 443, 451), each case not ported (99,
\    93);
\ 2. malformed input: at: with no name, _, a word, * among names, after
\    a tactic that takes none, twice, inside a bracket, after a value,
\    after a block's end (453, 454, 82, 86);
\ 3. stack effects and records: each T{ }T checks the depth; the step's
\    tac-loc flags, tac-loc# and each name's ID and place, its text's end;
\    every field of each goal and hypothesis made;
\ 5. resources (tests/support/meta-sweeps.fs): the goal operations with
\    every heap allocation refused in turn and with room for every count
\    of terms in turn, and the words through their text with every heap
\    allocation refused: the answer or full, never another answer;
\ 6. state: an assigned goal refused before anything is made (no
\    metavariable, no term), the frames and the current view put back.
\ The terms are checked node for node with pinned Lean by check.py.
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
: made ( x outcome -- x ) ok? 0= abort" batch-d test: not made" ;
lf-meta-throw-base outcome-invalid - constant thrown-invalid
lf-meta-throw-base outcome-unsupported - constant thrown-unsupported
: nat ( -- t ) s" Nat" lf-mk-const0 ;
: nm ( c-addr u -- id ) lfa-intern ;
: fresh ( -- ) lf-view-empty lf-mctx-view! ;
: local+ ( type c-addr u -- fvar )
  nm swap lf-lctx-local made tuck swap 0 lf-local-new made
  lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: goal ( type -- goal ) 0 lf-mctx-view lf-goal-new made ;
: tagged ( type -- goal ) goal dup s" t" nm lf-mvar-tag! made ;
: le ( x y -- t ) s" LE.le" 2swap 2 lf-mk-app-m ;
: eqv? ( t s -- flag ) lf-meta-eqv made ;
: open? ( mvar -- flag ) lf-goal-assigned? 0= ;
: arg-k ( app j -- x ) 0 ?do lf-term-first@ loop lf-term-second@ ;
: code1 ( x xt -- code ) catch if drop lf-author-code else drop 0 then ;
: detail-has? ( c-addr u -- flag )
  0 lfa-detail slab-at lfa-detail slab-count 2swap search nip nip ;
: made-so-far ( -- mvars terms ) lf-mvar-count lf-term-count @ ;
\ Local k of goal's context, its name and type.
: local@ ( goal k -- local ) swap lf-goal-view swap lf-view-local ;
: name@ ( goal k -- name ) local@ lf-local-name ;
: type@ ( goal k -- type ) local@ lf-local-fvar lf-fvar-type ;
: count@ ( goal -- n ) lf-goal-view lf-view-count ;

\ ---- 3. Records: at: on the step before it.
: vars ( -- c-addr u ) s" Nat explicit: a Nat explicit: b Nat explicit: c " ;
create stmt 512 allot  variable stmt#
: stmt+ ( c-addr u -- ) tuck stmt stmt# @ + swap move stmt# +! ;
: st ( c-addr u -- c-addr' u' ) 0 stmt# ! vars stmt+ stmt+ stmt stmt# @ ;
: step@ ( i -- addr ) lf-tactic-step ;
: hac ( -- c-addr u ) s" a b = explicit: h a c ≤ explicit: h2 b c ≤" st ;
\ (h2 and h rewritten; at the goal the rule h, elaborated again, is the
\ new h : b = b, as in Lean, so b ≤ c stays: unsolved, 89)
T{ hac s\" by-rw[ ' h ] at: h2 h |-\n" tactic-ran -> 89 }T
T{ 1 step@ tac-loc @ 1 step@ tac-loc# @ 1 step@ tac-count @
   -> tac-loc-given tac-loc-goal or 2 1 }T
T{ 1 0 lf-tac-loc-hyp s" h2" nm = 1 1 lf-tac-loc-hyp s" h" nm = 1 lf-tac-loc# -> true true 2 }T
T{ 1 lf-tac-located? 1 lf-tac-loc-goal? 1 lf-tac-loc-all? -> true true false }T
\ Each name's argument: its ID, its place on the line, left to right (no
\ symm); the step's text ends past the last token.
: loc-arg ( i k -- addr ) over lf-tac-args# + swap step@ tac-first @ + tac-args store-slot ;
T{ 1 0 loc-arg dup targ-x @ s" h2" nm = swap targ-symm @ -> true 0 }T
T{ 1 0 loc-arg targ-at @ 1 1 loc-arg targ-at @ < 1 step@ tac-to @ 1 1 loc-arg targ-at @ >
   -> true true }T
lf-tac-forget
\ No at:: the goal alone (targets #[] true); * the wildcard alone.
T{ s" a b = explicit: h b c ≤ explicit: h2 a c ≤" st s" by-rw[ ' h ] ' h2 by-exact" tactic-ran
   1 lf-tac-located? 1 lf-tac-loc-goal?
   1 lf-tac-loc-all? 1 lf-tac-loc# -> 0 false true false 0 }T
T{ hac s\" by-rw[ ' h ] at: *\n" tactic-ran 1 step@ tac-loc @ 1 lf-tac-loc# 1 lf-tac-loc-goal?
   -> 99 tac-loc-given tac-loc-all or 0 false }T
lf-tac-forget
\ The shapes: located ones and not.
T{ tac-shape-plain-at shape-at @ tac-shape-term-at shape-at @ tac-shape-rules shape-at @
   tac-shape-plain shape-at @ tac-shape-term shape-at @ tac-shape-list shape-at @
   -> true true true 0 0 0 }T
T{ tac-k-change lf-tactic-shape@ tac-k-symm lf-tactic-shape@ tac-k-delta lf-tactic-shape@
   -> tac-shape-term-at tac-shape-plain-at tac-shape-term-at }T

\ ---- 2. Malformed at:.
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
T{ hac s\" by-rw[ ' h ] at:\n" tactic-ran -> 454 }T
T{ hac s\" by-rw[ ' h ] at: _\n" tactic-ran -> 454 }T
T{ hac s\" by-rw[ ' h ] at: by-rfl\n" tactic-ran -> 454 }T
T{ hac s\" by-rw[ ' h ] at: * h2\n" tactic-ran token s" h2" compare -> 454 0 }T
T{ hac s\" by-rw[ ' h ] at: h2 *\n" tactic-ran -> 454 }T
T{ hac s\" ' h2 by-exact at: h2\n" tactic-ran token s" at:" compare -> 453 0 }T
\ (the names run to the end of the line: by-rw[ there is a LeanForth word)
T{ hac s\" by-rw[ ' h ] at: h2 by-rw[ ' h ] at: h2\n" tactic-ran -> 454 }T
T{ hac s\" by-rw[ ' h at: h2 ]\n" tactic-ran -> 82 }T
T{ hac s\" by-rw[ ' h ] ' h at: h2\n" tactic-ran -> 86 }T
T{ hac s\" at: h2\n" tactic-ran -> 453 }T
T{ hac s\" by-case: _ => by-rw[ ' h ] by-end at: h2\n" tactic-ran -> 453 }T
lf-tac-forget
\ A hypothesis named at: is refused where it is named (78, a reserved
\ word), not later at ' at: (review tb2-batch3a finding 5).
T{ s" a b = explicit: at: a b =" st s" ' at: by-exact" tactic-ran token s" at:" compare
   -> 78 0 }T
\ A second at: on the next line: the step has one already (453).
T{ hac s\" by-rw[ ' h ] at: h2\n at: h" tactic-ran -> 453 }T
lf-tac-forget

\ ---- 1. The tactics through the text.
T{ hac s\" by-rw[ ' h ] at: h2\n ' h2 by-exact" tactic-ran -> 0 }T
T{ hac s\" by-rewrite[ ' h ] at: h2\n ' h2 by-exact" tactic-ran -> 0 }T
\ (a later step names the new hypothesis; the old one would not fit)
T{ hac s\" by-rw[ ' h ] at: h2\n ' h2 by-revert by-intro: k ' k by-exact" tactic-ran -> 0 }T
T{ hac s\" by-rw[ ' h ] at: foo\n" tactic-ran -> 455 }T
T{ s"   foo" detail-has? s" Unknown identifier `foo`" detail-has? -> false false }T
lf-tac-forget
T{ hac s\" by-rw[ ' h ] at: Nat.le_refl\n" tactic-ran -> 99 }T
\ (the rule's own hypothesis first: h becomes b = b, and the rule,
\ elaborated again at h2, is that new h, whose b a ≤ c lacks: 215)
T{ hac s\" by-rw[ ' h ] at: h h2\n" tactic-ran -> 215 }T
T{ s" a b = explicit: h c c ≤ explicit: h2 c c ≤" st s\" by-rw[ ' h ] at: h2\n" tactic-ran -> 215 }T
lf-tac-forget
\ rwa: at one hypothesis, at none (the hypothesis as it is), the legacy
\ form, 456; rfl on a ≤ c and ¬ fails as Lean's, assumption closes.
T{ hac s\" by-rwa[ ' h ] at: h2\n" tactic-ran -> 0 }T
T{ s" a b ≤ explicit: h a b ≤" st s\" by-rwa[ ] at: h\n" tactic-ran -> 0 }T
T{ s" a b = explicit: h a c ≤ explicit: h2 a c ≤" st s\" by-rwa[ ' h ] at: h2 |-\n" tactic-ran -> 0 }T
\ (the legacy form's assumption finds no a ≤ c once h2 is b ≤ c: 381)
T{ s" a b = explicit: h a c ≤ explicit: h2 a c ≤" st s\" by-rwa[ ' h ] at: h2 h\n" tactic-ran
   -> 381 }T
T{ s" a b ≤ ¬ explicit: k False" st s\" by-rwa[ ] at: k\n" tactic-ran -> 456 }T
T{ s" a b = explicit: h b c ≤ ¬ explicit: h2 a c ≤ ¬" st s" by-rwa[ ' h ]" tactic-ran -> 0 }T
lf-tac-forget
\ change, symm, delta at a hypothesis.
T{ s" a 0 + b = explicit: h a b =" st s\" a b = by-change at: h\n ' h by-exact" tactic-ran -> 0 }T
T{ s" a b = explicit: h a b =" st s\" b a = by-change at: h\n" tactic-ran -> 443 }T
T{ s" a b = explicit: h b a =" st s\" by-symm at: h\n ' h by-exact" tactic-ran -> 0 }T
T{ s" a b ≤ ¬ explicit: h a b ≤ ¬" st s\" by-symm at: h\n" tactic-ran -> 451 }T
T{ s" a b ≤ explicit: h a b ≤" st s\" ' Nat.le by-delta at: h\n" tactic-ran -> 448 }T
T{ s" ] at h" detail-has? -> true }T
lf-tac-forget
\ At the goal (no at:, or |- alone): symm and change act on the target.
T{ s" a b = explicit: h b a =" st s\" by-symm\n ' h by-exact" tactic-ran -> 0 }T
T{ s" a b = explicit: h a b =" st s\" b a = by-change at: |-\n" tactic-ran -> 443 }T
lf-tac-forget
T{ s" a b ≠ explicit: h a b ≠" st s\" ' Ne by-delta at: h\n" tactic-ran -> 99 }T
T{ s" a b = explicit: h a b =" st s\" by-symm at: *\n" tactic-ran -> 99 }T
lf-tac-forget
\ rfl: Iff.rfl closes; ¬ is no relation (457); a ≤ a has no refl lemma
\ known (93); an assumption inside rw's try is untouched.
T{ s" a b ≤ a b ≤ ↔" st s" by-rfl" tactic-ran -> 0 }T
T{ s" a b ≤ ¬ explicit: h a b ≤ ¬" st s" by-rfl" tactic-ran -> 457 }T
T{ s" a a ≤" st s" by-rfl" tactic-ran -> 93 }T
lf-tac-forget

\ ---- lf-const-meta-applied: Iff.rfl at a new metavariable, its body.
fresh
nat s" a" local+ constant fa
nat s" b" local+ constant fb
nat s" c" local+ constant fc
fa fb lf-mk-eq constant ab-eq
fb fa lf-mk-eq constant ba-eq
fa fc le constant ac-le
fb fc le constant bc-le
: decl ( c-addr u -- d ) nm lf-menv-find made ;
T{ lf-mvar-count s" Iff.rfl" decl lf-const-meta-applied drop lf-term-second@ lf-mvar?
   swap lf-mvar-count swap - -> true 1 }T
T{ s" Iff.rfl" decl lf-const-meta-applied 2 s" Iff" lf-meta-app-of? swap
   lf-meta-head s" Iff.rfl" lf-meta-const-named? -> true true }T

\ ---- lf-goal-replace-local-decl: h2 : a ≤ c replaced by Eq.mp proof h2
\ of type b ≤ c, proof MVarId.rewrite's of h : a = b.
ab-eq s" h" local+ constant fh
ac-le s" h2" local+ constant fh2
lf-mctx-view constant view-d
: rewritten ( goal -- goal new proof ) dup fh2 lf-fvar-type fh false lf-goal-rewrite drop ;
: replaced ( goal -- goal' fvar' ) rewritten >r >r fh2 r> r> lf-goal-replace-local-decl ;
bc-le tagged constant gr
gr rewritten constant pr constant new-t drop
gr fh2 new-t pr lf-goal-replace-local-decl constant fr' constant gr'
T{ gr open? gr' open? gr' lf-goal-type bc-le eqv? gr' lf-goal-tag s" t" nm =
   gr' lf-goal-kind mv-opaque = -> false true true true true }T
T{ gr' count@ view-d lf-view-count = gr' 4 name@ s" h2" nm = gr' 4 type@ bc-le eqv?
   gr' 4 local@ lf-local-fvar fr' = -> true true true true }T
T{ gr' lf-goal-view fh2 lf-view-has? gr' lf-goal-view fh lf-view-has? -> false true }T
\ The value: ?g (Eq.mp.{0} (a ≤ c) (b ≤ c) proof h2), ?g the asserted goal
\ of (h2 : b ≤ c) -> b ≤ c (assert's), whose value is fun h2 => ...
: val@ ( mvar -- e ) lf-mvar-value drop ;
gr val@ constant vr
T{ vr lf-term-first@ lf-mvar? vr lf-term-second@ dup 4 s" Eq.mp" lf-meta-app-of?
   swap 0 arg-k fh2 = -> true true true }T
T{ vr lf-term-second@ dup 3 arg-k ac-le eqv? over 2 arg-k bc-le eqv? rot 1 arg-k pr =
   -> true true true }T
T{ vr lf-term-first@ dup lf-goal-type dup lf-term-pi? swap lf-term-first@ bc-le eqv? rot val@
   lf-term-lam? -> true true true }T
\ An assigned goal: invalid (checkNotAssigned, after mkEqMP's term and
\ its metavariables, as Lean's order is), its value untouched.
: replace-again ( -- ) gr fh2 new-t pr lf-goal-replace-local-decl 2drop ;
T{ ' replace-again catch gr val@ vr = mat-frames slab-count -> thrown-invalid true 0 }T

\ ---- lf-view-local-of, lf-fvar-user-name: a free variable's local in a
\ view, its user name in the view in force; a view without it is invalid
\ thrown (a valid view, a dead variable).
T{ view-d fh2 lf-view-local-of lf-local-fvar fh2 lf-fvar-user-name s" h2" nm = -> fh2 true }T
T{ fb lf-fvar-user-name s" b" nm = gr' lf-goal-view fr' lf-view-local-of lf-local-fvar -> true fr' }T
T{ lf-view-empty fh2 ' lf-view-local-of catch nip nip -> thrown-invalid }T
T{ gr' lf-goal-view fh2 ' lf-view-local-of catch nip nip -> thrown-invalid }T

\ ---- lf-goal-change-local-decl: h2 : a ≤ c to Nat.le a c, defeq.
s" Nat.le" fa fc 2 lf-mk-app-m constant nle-ac
bc-le tagged constant gc
gc fh2 nle-ac lf-goal-change-local-decl constant gc'
T{ gc open? gc' open? gc' lf-goal-type bc-le eqv? gc' lf-goal-tag s" t" nm =
   gc' lf-goal-kind mv-opaque = -> false true true true true }T
T{ gc' count@ view-d lf-view-count = gc' 4 name@ s" h2" nm = gc' 4 type@ nle-ac eqv?
   gc' lf-goal-view fh2 lf-view-has? -> true true true false }T
\ The value: ?g1 h2 (revert), ?g1 := @id.{0} ((h2 : a ≤ c) -> b ≤ c) ?g2
\ (replaceTargetDefEq), ?g2 := fun h2 : Nat.le a c => .. (introNP).
gc val@ constant vc
vc lf-term-first@ val@ constant vc1
vc1 lf-term-second@ val@ constant vc2
T{ vc lf-term-second@ fh2 = vc lf-term-first@ lf-mvar? vc1 2 s" id" lf-meta-app-of?
   -> true true true }T
T{ vc1 1 arg-k dup lf-term-pi? swap lf-term-first@ ac-le eqv? -> true true }T
T{ vc2 lf-term-lam? vc2 lf-term-first@ nle-ac eqv? vc2 lf-binder-name s" h2" nm = -> true true true }T
\ Not defeq (b ≤ a): unsupported; an assigned goal: invalid, nothing made.
fb fa le constant ba-le
: change-code ( type -- code ) bc-le tagged fh2 rot ['] lf-goal-change-local-decl catch
  dup if nip nip nip else nip then ;
T{ ba-le change-code mat-frames slab-count -> thrown-unsupported 0 }T
: change-again ( -- ) gc fh2 nle-ac lf-goal-change-local-decl drop ;
T{ made-so-far ' change-again catch -rot made-so-far d= -> thrown-invalid true }T
\ A local that depends on it (k : h2 = h2): unsupported (revert takes two).
fh2 fh2 lf-mk-eq s" k" local+ constant fk
T{ nle-ac change-code -> thrown-unsupported }T
view-d lf-mctx-view!

\ ---- lf-symm-expr, lf-goal-symm-at: h : a = b to b = a.
T{ fh lf-symm-expr dup 2 s" id" lf-meta-app-of? over 1 arg-k ba-eq eqv? rot lf-term-second@
   4 s" Eq.symm" lf-meta-app-of? -> true true true }T
T{ fh lf-symm-expr lf-infer made ba-eq eqv? -> true }T
bc-le tagged constant gs
gs fh lf-goal-symm-at constant gs'
T{ gs open? gs' open? gs' 3 name@ s" h" nm = gs' 3 type@ ba-eq eqv?
   gs' lf-goal-view fh lf-view-has? gs' lf-goal-type bc-le eqv? -> false true true true false true }T
T{ fh2 ' lf-symm-expr code1 -> 99 }T
\ applyRfl on HEq a b, four arguments: its HEq.refl path not ported, 93
\ (thrown unsupported), the goal left open.
s" HEq" fa fb 2 lf-mk-app-m tagged constant gheq
T{ gheq ' lf-goal-refl catch nip gheq open? -> thrown-unsupported true }T
lf-tac-forget

\ ---- 5. Resources: each goal operation on a new goal with every heap
\ allocation refused in turn and with room for every count of terms in
\ turn: the answer or full, never another answer.
: frames-anew ( -- ) mat-frames sweep-slab-anew mrw-frames sweep-slab-anew
  tl-frames sweep-slab-anew mrv-frames sweep-slab-anew mti-frames sweep-slab-anew
  tlc-frames sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
: caught ( x xt -- y outcome ) 1 1 lf-meta-catch ;
: new-goal ( type -- goal ) 0 lf-mctx-view lf-goal-new lf-must ;
: s-replace ( type -- type' ) new-goal replaced nip lf-fvar-type ;
: s-change ( type -- type' ) new-goal fh2 nle-ac lf-goal-change-local-decl lf-goal-type ;
: s-symm-at ( type -- type' ) new-goal fh lf-goal-symm-at lf-goal-type ;
: p-replace ( type -- type' outcome ) ['] s-replace caught ;
: p-change ( type -- type' outcome ) ['] s-change caught ;
: p-symm-at ( type -- type' outcome ) ['] s-symm-at caught ;
: both-swept ( type xt -- heap? room? )
  2dup heap-sweep swept? >r room-sweep swept? r> swap ;
T{ bc-le ' p-replace both-swept bc-le ' p-change both-swept -> true true true true }T
T{ bc-le ' p-symm-at both-swept -> true true }T
\ Through the text: accepted, or full, never another error (a refusal
\ inside rfl's alternatives is never the next one, nor rwa's assumption).
: full-code? ( code -- flag ) dup if lf-author-outcome outcome-full = then ;
: text-full ( c-addr u c-addr' u' -- code outcome )
  tactic-ran dup full-code? if drop -1 outcome-full else outcome-ok then ;
: p-rw-text ( x -- code outcome ) drop hac s\" by-rw[ ' h ] at: h2\n ' h2 by-exact" text-full ;
: p-rwa-text ( x -- code outcome ) drop hac s\" by-rwa[ ' h ] at: h2\n" text-full ;
: p-change-text ( x -- code outcome )
  drop s" a 0 + b = explicit: h a b =" st s\" a b = by-change at: h\n ' h by-exact" text-full ;
T{ 0 ' p-rw-text heap-sweep swept? 0 ' p-rwa-text heap-sweep swept? -> true true }T
T{ 0 ' p-change-text heap-sweep swept? tlc-frames slab-count -> true 0 }T
lf-tac-forget
.( batch-d test.fs: all tests passed) cr
