\ Iota and projection reduction (src/kernel/iota.fs; plan tasks 5.2.1b,
\ 5.2.1c, 5.2.2; ADR 0015 rules R1-R3), on cases of the inductive table
\ (tests/core/check-block-cases/, each the export pinned Lean printed;
\ tests/core/check-block.fs checks their verdicts). Coverage classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 3. Interfaces: the recursor record's numbers (get_rec_rule_for, the
\    major premise's place, k, the major inductive type) on Bool.rec,
\    Eq.rec and List.rec as Lean exported them; the spine words; in a
\    check, the lookups (is_constructor_app, get_first_cnstr, the
\    recursor of an application, mk_nullary_cnstr, the structure test),
\    each answer and its outcome, the stack as before.
\ 2. Malformed records: a recursor whose type is no Pi telescope names no
\    major inductive type (unknown for K, -1 for structure eta).
\ 1, 7. whnf.fs's hook through lf-whnf-on: the reduct of a case's type is
\    the minor premise Lean's rule picks, or a new node; K outside an
\    inference job in environment mode is undecided, and the major
\    premise, a constructor, still reduces.
\ 5. Resources: in a check, every fuel below the least that suffices
\    exhausts the whnf, the least gives the reduct, and every allocation
\    refused in turn makes it full; whole checks through K (R2) and
\    structure eta (R3) swept the same way (every n-th budget and
\    allocation), and a crowded term store, full.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

\ ---------------------------------------------------------------------------
\ Helpers. A case's target type is an application of a recursor; its head
\ names the recursor's input declaration, its major premise a
\ constructor application.
: decl-named ( name -- decl|0 )
  lf-input-count 0 ?do
    dup i lf-input-decl lf-idecl-name @ lf-name-same? if drop i lf-input-decl unloop exit then
  loop drop 0 ;
: head-decl ( node -- decl ) lf-iota-head-name decl-named ;
: rec ( -- decl ) cs-type head-decl ;
: major ( -- node ) cs-type rec lf-iota-major ;
: rule-for ( node -- rule|0 ) rec swap lf-iota-head-name lf-iota-rule ;
\ Nodes made in a check (scratch, rolled back after it): a Sort, and a
\ constant of no universe arguments.
: sort-node ( -- node ) 0 lf-term-sort cs-must ;
: const-of ( name -- node )
  lf-name-generation @ 0 0 lf-cref-new cs-must lf-cterm-new cs-must drop ;
\ The declaration being checked, which no slot holds yet.
: target-name ( -- name ) cs cs-target @ lf-input-decl lf-idecl-name @ ;
: absent-node ( -- node ) target-name const-of ;

\ ---------------------------------------------------------------------------
\ 3. The recursor's record and the spine.
\ Bool.rec (fun _ => Prop) False True Bool.true: no parameters, a motive,
\ two minor premises, no index, the major premise fourth; not K; the rule
\ for Bool.true takes no field, the recursor's own name has none.
s" iota.bool-true" cs-load
T{ rec lf-iota-prefix rec lf-iota-major-idx rec lf-iota-k? -> 3 3 false }T
T{ cs-type lf-iota-n -> 4 }T
T{ major cs-type 4 3 lf-iota-arg = -> true }T
T{ major rule-for dup 0<> swap lf-irule-nfields -> true 0 }T
T{ cs-type rule-for -> 0 }T
T{ rec lf-iota-induct major head-decl lf-idecl-data lf-ict-induct lf-more-field
   lf-name-same? -> true }T
\ lf-iota-field-of ( c k -- field|-1 ): argument k when there is one.
T{ cs-type 3 lf-iota-field-of major = cs-type 4 lf-iota-field-of -> true -1 }T
T{ cs-type 0 lf-iota-peel cs-type = cs-type 4 lf-iota-peel lf-iota-head-name
   rec lf-idecl-name @ lf-name-same? -> true true }T
cs-unload

\ Eq.rec on Eq.refl: two parameters, a motive, one minor premise, one
\ index: the major premise sixth; K.
s" iota.eq-refl" cs-load
T{ rec lf-iota-prefix rec lf-iota-major-idx rec lf-iota-k? -> 4 5 true }T
T{ major rule-for lf-irule-nfields -> 0 }T
cs-unload

\ List.rec on List.cons: a parameter, a motive, two minor premises; the
\ rule for cons takes its two fields.
s" iota.list-hypothesis" cs-load
T{ rec lf-iota-prefix rec lf-iota-major-idx rec lf-iota-k? -> 4 4 false }T
T{ major rule-for lf-irule-nfields -> 2 }T
cs-unload

\ ---------------------------------------------------------------------------
\ 3, 2. In a check of iota.bool-true: Bool, Bool.true, Bool.rec; the
\ declaration checked, no slot's yet (Lean's environment has no such
\ constant).
: true-node ( -- node ) major ;
: bool-node ( -- node ) major head-decl lf-idecl-type @ ;
: bool-name ( -- name ) rec lf-iota-induct ;
: first-ctor ( -- name ) bool-name lf-iota-first-ctor drop ;
: kind-of ( name -- kind ) decl-named lf-idecl-kind @ ;
\ The lookups give the published slot's declaration: the same name.
: named-as? ( decl1 decl2 -- flag ) lf-idecl-name @ swap lf-idecl-name @ lf-name-same? ;
\ The recursor of an application, -1 for none.
: recursors ( -- )
  T{ cs-type lf-iota-recursor swap rec named-as? -> outcome-ok true }T
  T{ sort-node lf-iota-recursor -> -1 outcome-ok }T
  T{ true-node lf-iota-recursor -> -1 outcome-ok }T
  T{ absent-node lf-iota-recursor -> -1 outcome-ok }T ;
\ is_constructor_app: the constructor's declaration, else 0.
: constructors ( -- )
  T{ true-node lf-iota-ctor swap true-node head-decl named-as? -> outcome-ok true }T
  T{ cs-type lf-iota-ctor -> 0 outcome-ok }T
  T{ sort-node lf-iota-ctor -> 0 outcome-ok }T
  T{ absent-node lf-iota-ctor -> 0 outcome-ok }T
  T{ true-node lf-iota-ctor? cs-type lf-iota-ctor? -> true outcome-ok false outcome-ok }T ;
\ get_first_cnstr: Bool.false (a constructor, not Bool.true); none for a
\ recursor; unknown for a name Lean's environment does not hold.
: first-constructors ( -- )
  T{ bool-name lf-iota-first-ctor nip -> outcome-ok }T
  T{ first-ctor kind-of first-ctor true-node lf-iota-head-name lf-name-same?
     -> lf-kind-constructor false }T
  T{ rec lf-idecl-name @ lf-iota-first-ctor -> 0 outcome-ok }T
  T{ target-name lf-iota-first-ctor -> 0 outcome-unknown }T ;
\ K's pieces: the major inductive type of a type (Bool for Bool, none for
\ a Sort or another head); mk_nullary_cnstr, unknown when the type has
\ fewer arguments than parameters asked for.
: k-pieces ( -- )
  T{ bool-node rec lf-iota-k-induct swap bool-name lf-name-same? -> outcome-ok true }T
  T{ sort-node rec lf-iota-k-induct -> 0 outcome-ok }T
  T{ cs-type rec lf-iota-k-induct -> 0 outcome-ok }T
  T{ first-ctor bool-node 1 lf-iota-k-make -> -1 outcome-unknown }T
  T{ first-ctor bool-node 0 lf-iota-k-make swap lf-iota-head-name first-ctor lf-name-same?
     -> outcome-ok true }T
  T{ sort-node rec lf-iota-k-null -> -1 outcome-ok }T
  T{ bool-node rec lf-iota-k-null swap lf-iota-head-name first-ctor lf-name-same?
     -> outcome-ok true }T ;
\ Structure eta's pieces: Bool is no structure; a Sort is no application
\ of one; the universe arguments as many as the recursor's parameters.
: eta-pieces ( -- )
  T{ rec lf-iota-structure -> 0 outcome-ok }T
  T{ rec sort-node lf-iota-of-struct? rec bool-node lf-iota-of-struct? -> false false }T
  T{ cs-type rec lf-iota-levels? -> true }T
  T{ cs-type rec major true-node rule-for lf-iota-applies? -> true }T ;
\ A recursor whose type is a Sort, not its Pi telescope (forged in the
\ input, put back at once): no major inductive type, so K is unknown and
\ eta cannot name the structure (-1).
variable saved-type
: forge ( -- ) rec lf-idecl-type @ saved-type ! sort-node rec lf-idecl-type ! ;
: unforge ( decl -- ) saved-type @ swap lf-idecl-type ! ;
: forged ( -- )
  T{ rec forge lf-iota-induct rec unforge -> 0 }T
  T{ rec forge bool-node over lf-iota-k-induct rot unforge -> 0 outcome-unknown }T
  T{ rec forge bool-node over lf-iota-k-null rot unforge -> -1 outcome-unknown }T
  T{ rec forge dup lf-iota-structure rot unforge -> -1 outcome-ok }T ;
: in-bool-true ( xt -- ) s" iota.bool-true" rot outcome-ok cs-probe-gives ;
' recursors in-bool-true
' constructors in-bool-true
' first-constructors in-bool-true
' k-pieces in-bool-true
' eta-pieces in-bool-true
' forged in-bool-true

\ ---------------------------------------------------------------------------
\ 1, 7, 5. In the target's check, Lean's whnf of its type: the reduct, its
\ outcome, every fuel below the least exhausted and the least giving the
\ same node, each allocation refused full. Notes: 0 the reduct, 1 its
\ outcome, 2 whether the sweep agreed, 3 whether every refusal was full,
\ 4 the type's minor premise at index i (what the rule gives), 5 whether
\ the reduct is another node than the type.
variable minor-at
: swept ( -- )
  cs-type ['] cs-whnf cs-pass-sweep cs-note
  cs-type ['] cs-whnf cs-pass-refusals cs-note
  cs-type dup lf-iota-n minor-at @ lf-iota-arg cs-note 0 cs-noted cs-type <> cs-note ;
: reduced ( c-addr u i -- outcome errors ) minor-at ! ['] swept cs-probed ;
: as-minor? ( -- flag ) 0 cs-noted 4 cs-noted = ;
: sweeps? ( -- flag1 flag2 ) 2 cs-noted 3 cs-noted ;
: changed? ( -- flag ) 5 cs-noted ;

\ Bool.rec motive False True Bool.true is True, the second minor premise
\ (argument 2); the wrong row's check is rejected, its reduct the same.
T{ s" iota.bool-true" 2 reduced 1 cs-noted -> outcome-ok 0 outcome-ok }T
T{ as-minor? sweeps? -> true true true }T
T{ s" iota.bool-true-wrong" 2 reduced 1 cs-noted -> outcome-rejected 0 outcome-ok }T
T{ as-minor? sweeps? -> true true true }T
\ Nat.rec motive True (fun _ _ => False) Nat.zero is True (argument 1).
T{ s" iota.nat-zero" 1 reduced 1 cs-noted -> outcome-ok 0 outcome-ok }T
T{ as-minor? sweeps? -> true true true }T
\ Reducts that are applications of the rule's right side: another node
\ than the type, with the sweeps.
T{ s" iota.nat-succ" 0 reduced 1 cs-noted changed? -> outcome-ok 0 outcome-ok true }T
T{ sweeps? -> true true }T
T{ s" iota.eq-refl" 0 reduced 1 cs-noted changed? -> outcome-ok 0 outcome-ok true }T
T{ sweeps? -> true true }T
T{ s" iota.list-hypothesis" 0 reduced 1 cs-noted changed? -> outcome-ok 0 outcome-ok true }T
T{ sweeps? -> true true }T
T{ s" iota.list-field" 0 reduced 1 cs-noted changed? -> outcome-ok 0 outcome-ok true }T
T{ sweeps? -> true true }T
T{ s" iota.argument-after-major" 0 reduced 1 cs-noted changed? -> outcome-ok 0 outcome-ok true }T
T{ sweeps? -> true true }T

\ K (Eq.rec on Eq.refl) in an inference job off environment mode: K is
\ undecided, the major premise is a constructor, and the reduct is the
\ one environment mode gives.
: off-env ( node fuel -- node' outcome ) 0 swap lf-minfer-start lf-minfer-frames lf-whnf-on ;
: both-modes ( -- )
  cs-type ['] cs-whnf cs-pass! cs-plenty cs-pass cs-note cs-note
  cs-type ['] off-env cs-pass! cs-plenty cs-pass cs-note cs-note ;
T{ s" iota.eq-refl" ' both-modes cs-probed -> outcome-ok 0 }T
T{ 0 cs-noted 2 cs-noted 1 cs-noted 3 cs-noted = -> outcome-ok outcome-ok true }T

\ ---------------------------------------------------------------------------
\ 5. Whole checks whose iota runs under binders the check opened: K (R2)
\ on Eq (accepted and rejected), structure eta (R3) on Prod. Every
\ fuel-th budget, then each alloc-th allocation refused, then a crowded
\ term store: the plenty outcome or exhausted, full, full.
: whole ( c-addr u fuel alloc -- fuel-ok? alloc-ok? outcome )
  2swap cs-load swap cs-fuel-sweep swap cs-refusal-sweep cs-crowded cs-unload ;
T{ s" k.eq-variable-proof" 97 23 whole -> true true outcome-full }T
T{ s" k.eq-different-ends" 101 29 whole -> true true outcome-full }T
T{ s" iota.prod-eta" 89 19 whole -> true true outcome-full }T

bye
