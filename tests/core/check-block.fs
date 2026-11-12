\ The check of inductive blocks (plan tasks 5.2.1a and 5.2.1b; ADR 0015;
\ src/kernel/check-block.fs, inductive-block.fs, inductive-recursor.fs,
\ level-geq.fs) end to end: staged and fed exports, checked by
\ check-declaration, published by the checked environment.
\ 1. Cases of the inductive table (tests/core/check-block-cases/, each the
\    export tests/reference/inductive-expected.lean prints for its row;
\    tests/core/inductive-table.py checks they are still Lean's): every
\    outcome, each rejection with its rule's diagnostic and step, Lean's
\    replay of the Bool and N blocks mutated (B3) and their ignored fields
\    (B4); recursive blocks with their induction hypotheses, positivity.
\ 2. tests/reference/inductive/blocks.ndjson: a block's members published
\    together (every slot final, one outcome, handles, no axioms).
\ 3. That export tampered after the feed, one field at a time (ADR 0015
\    §13, test plan 3): recursors, rules and constructors rejected with
\    the field named; the type's ignored fields accepted with a warning; a
\    malformed block invalid; unsafe members and unsupported forms
\    unsupported; a loose variable invalid.
\ 4. Fuel: every budget gives ok or exhausted, ok from the least on.
\ 5. Room: a term store with no room left gives full, never ok; and each
\    allocation of a block's check refused in turn gives full (review
\    rvN1 L2).
\ 6. After a block (review rvI21 B2, M1): Lean's generated recursor
\    T.rec held when the file leaves it out; the type visible only within
\    its own check; the publisher's re-check of members and of T.rec.
\ 7. Axioms, opaque declarations and quotients: Lean's verdicts; the four
\    quotient names add_quot holds (review rvAX). 8. The statement matcher
\    and the allowlist. 9. The fuel axioms and quotient records use, as
\    cli/check-run.fs reports it: exact.
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
require ../support/alloc-fail.fs
require ../../src/import/feed.fs
require ../../src/kernel/check-declaration.fs
require ../../src/cli/check-run.fs

create stg /stage allot
create fdd /feed allot
variable the-env
1000000 constant fuel
64 constant most
\ Per checked declaration: its diagnostic's code and second number, its
\ step (check-block's for a block, else check-declaration's) and, for a
\ block, its warnings.
create codes most cells allot
create n2s most cells allot
create steps most cells allot
create block-warns most cells allot
create visibles most cells allot
: at ( d table -- addr ) swap cells + ;
: must ( flag -- ) 0= abort" check-block: refused" ;
: step-now ( d -- step )
  lf-input-decl lf-ind-member? if lf-block-step@ else lf-check-step@ then ;
: record-diag ( d -- ) >r lf-diag@ r@ codes at ! drop r> n2s at ! drop ;
: record ( -- )
  lf-check-declaration lf-env-limit dup most < 0= if drop exit then
  dup record-diag dup step-now over steps at ! lf-block-warnings over block-warns at !
  lf-blk-visible? swap visibles at ! ;
: staged ( c-addr u -- outcome )
  16 stg stage-init ok? must stg stage-load-unchecked dup ok? if drop stg fdd lf-feed then ;
: unstage ( -- ) lf-name-viewed? if lf-name-detach then stg stage-free ;
: fresh ( budget -- )
  lf-check-budget 4096 lf-env-new ok? must dup the-env ! lf-env-use ok? must ;
\ Every declaration checked by xt (record, or a variant of it).
: checked-by ( budget xt -- )
  swap fresh ['] lf-check-no-maker lf-env-run drop lf-env-view ok? must ;
: checked ( budget -- ) ['] record checked-by ;
: finish ( -- ) the-env @ lf-env-free ok? must unstage ;
\ A block's member stands for its first member, which its check ran for.
: owner ( d -- d' ) dup lf-input-decl lf-idecl-header ?dup if nip lf-hdr-first lf-more-field then ;
\ Declaration d's outcome, and its check's code and step.
: result ( d -- outcome code step )
  dup lf-env-outcome swap owner dup codes at @ swap steps at @ ;
: n2-of ( d -- n2 ) owner n2s at @ ;
: warned ( d -- bits ) owner block-warns at @ ;
: final-decl ( -- d ) lf-input-count 1- ;
\ A case file's last declaration: its outcome, code and step.
: case+ ( c-addr u -- ) pad count + swap dup pad c@ + pad c! move ;
: case-path ( c-addr u -- c-addr' u' )
  0 pad c! s" tests/core/check-block-cases/" case+ case+ s" .ndjson" case+ pad count ;
: verdict ( c-addr u -- outcome code step )
  case-path staged dup ok? 0= if unstage 0 0 exit then drop
  fuel checked final-decl result finish ;
\ The same with the second number of the diagnostic, or the warnings.
: verdict-field ( c-addr u -- outcome code step n2 )
  case-path staged ok? must fuel checked final-decl result final-decl n2-of finish ;
: verdict-warned ( c-addr u -- outcome code step bits )
  case-path staged ok? must fuel checked final-decl result final-decl warned finish ;
\ Declaration d's outcome and code.
: used ( c-addr u -- outcome code ) verdict drop ;
\ The same for the declaration before a case file's last.
: before-last ( c-addr u -- outcome code )
  case-path staged ok? must fuel checked final-decl 1- result drop finish ;
: decl-verdict ( c-addr u d -- outcome code )
  >r case-path staged ok? must fuel checked r> result drop finish ;
15 constant all-steps

\ ---------------------------------------------------------------------------
\ 1. Accepted: every step finish.
T{ s" ind.bool" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.and" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.or" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.exists" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.exists-prop-witness" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.true" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.empty-prop" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.eq" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.unit" verdict -> outcome-ok 0 all-steps }T
T{ s" universe.field-fits" verdict -> outcome-ok 0 all-steps }T
T{ s" universe.predicate-any-field" verdict -> outcome-ok 0 all-steps }T
T{ s" params.constructor-binder-beta" verdict -> outcome-ok 0 all-steps }T
\ An index (task 5.2.1c's row, decided here too): its field a : α in Type
\ fits Type 1 by is_geq's offsets, not by equality.
T{ s" params.index-one-universe-up" verdict -> outcome-ok 0 all-steps }T
\ Two universe parameters: U1's is_geq orders u and v by their names in
\ the feed's name view (the review rvKC's finding H1, fixed).
T{ s" ind.universe-max" verdict -> outcome-ok 0 all-steps }T
\ Recursive blocks (task 5.2.1b): the recursor with its induction
\ hypotheses and recursive calls equal to Lean's (B3): N and List, a
\ binary tree (two hypotheses), functions into the type (reflexive: one
\ and two arguments, under a parameter), recursive propositions (Prop
\ only; any universe with one constructor), a list in Sort (max 1 u), a
\ field whose type whnf beta-reduces to a function into the type, and one
\ it reduces to Nat (no hypothesis).
T{ s" ind.nat" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.list" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.binary-tree" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.reflexive" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.reflexive-two-arguments" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.reflexive-parameter" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.recursive-predicate" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.recursive-predicate-one-constructor" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.list-sort-max" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.recursive-through-beta" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.erased-by-beta" verdict -> outcome-ok 0 all-steps }T
\ Review rvN1 (M1): a W type; indexed recursive blocks, whose hypotheses'
\ indices are read under the hypothesis's own binders and whose minor
\ premises' result indices are shifted past the hypotheses (an Acc, a
\ vector, reflexive fields into other indices, a predicate); a reflexive
\ field with annotated binders (the hypothesis's binders consume them);
\ a Pi body that is a redex (the hypothesis needs whnf there); a redex
\ under a parameter.
T{ s" ind.w-type" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.acc" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.vec" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.reflexive-indexed" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.indexed-mixed" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.reflexive-indexed-dependent" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.indexed-predicate-one-constructor" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.reflexive-annotated-binders" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.reflexive-body-redex" verdict -> outcome-ok 0 all-steps }T
T{ s" ind.redex-with-parameter" verdict -> outcome-ok 0 all-steps }T
\ Mutual blocks (task 5.2.5a): each type's recursor with one motive per
\ type and the minor premises of every constructor, equal to Lean's: two
\ propositions (Prop only), tree and forest, even and odd with an index,
\ indexed data, three types with a parameter and a universe, a function
\ field into the other type.
T{ s" mutual.single-ctor-props" verdict -> outcome-ok 0 all-steps }T
T{ s" mutual.tree-forest" verdict -> outcome-ok 0 all-steps }T
T{ s" mutual.even-odd-constructors" verdict -> outcome-ok 0 all-steps }T
T{ s" mutual.indexed-data" verdict -> outcome-ok 0 all-steps }T
T{ s" mutual.three-types" verdict -> outcome-ok 0 all-steps }T
T{ s" mutual.reflexive" verdict -> outcome-ok 0 all-steps }T
\ One constructor in the whole block: E1 (Prop only), where one type would
\ have E3's large eliminator.
T{ s" mutual.one-constructor" verdict -> outcome-ok 0 all-steps }T
\ Rejected as Lean's check_inductive_types rejects them, at step 8 of the
\ second type: parameters that differ, too few of them, another universe;
\ and a negative occurrence of the other type (step 9, P1).
T{ s" mutual.parameter-mismatch" verdict -> outcome-rejected lf-diag-mutual-params 8 }T
T{ s" mutual.parameter-count" verdict-field -> outcome-rejected lf-diag-param-count 8 0 }T
T{ s" mutual.universe-mismatch" verdict -> outcome-rejected lf-diag-universe-mismatch 8 }T
T{ s" mutual.non-positive" verdict-field -> outcome-rejected lf-diag-non-positive 9 0 }T

\ Rejected, each with its rule's diagnostic, at its step.
T{ s" uniform.result-other-argument" verdict -> outcome-rejected lf-diag-nonuniform 3 }T
T{ s" params.too-few-binders" verdict -> outcome-rejected lf-diag-param-binders 4 }T
T{ s" names.duplicate-universe" verdict -> outcome-rejected lf-diag-duplicate-param 5 }T
T{ s" names.already-declared-earlier" verdict
   -> outcome-rejected lf-diag-already-declared 6 }T
T{ s" universe.type-not-a-sort-param" verdict -> outcome-rejected lf-diag-block-not-sort 8 }T
T{ s" universe.field-too-big" verdict -> outcome-rejected lf-diag-universe-too-big 9 }T
T{ s" result.other-type-sort" verdict -> outcome-rejected lf-diag-return-type 9 }T
T{ s" params.constructor-mismatch-sort" verdict -> outcome-rejected lf-diag-ctor-param 9 }T
T{ s" names.duplicate-constructor" verdict -> outcome-rejected lf-diag-duplicate-ctor 9 }T
\ T1 on the constructors (Lean's get_params; review rvI21 L1), T0 with the
\ reserved constant declared, N2 on a constructor and on T.rec (step 11)
\ against a constructor of that name.
T{ s" params.constructor-too-few-binders" verdict
   -> outcome-rejected lf-diag-param-binders 4 }T
T{ s" names.reserved-nested-prefix-declared" verdict
   -> outcome-rejected lf-diag-reserved-prefix 2 }T
T{ s" names.constructor-already-declared" verdict
   -> outcome-rejected lf-diag-already-declared 9 }T
T{ s" names.constructor-named-rec" verdict
   -> outcome-rejected lf-diag-already-declared 11 }T
\ Fields typed optParam and outParam: the recursor has them removed
\ (consume_type_annotations), as Lean's does.
T{ s" ind.annotated-fields" verdict -> outcome-ok 0 all-steps }T
\ Rows that use Nat, decided since Nat is (task 5.2.1b): T : Nat is no
\ Sort (Nat is an inductive type, which Lean's whnf leaves), a
\ constructor returning Nat, a parameter of the wrong type, Nat declared
\ again; and an index mentioning the type (C3, is_valid_ind_app).
T{ s" universe.type-not-a-sort" verdict -> outcome-rejected lf-diag-block-not-sort 8 }T
T{ s" result.other-type" verdict -> outcome-rejected lf-diag-return-type 9 }T
T{ s" params.constructor-mismatch" verdict -> outcome-rejected lf-diag-ctor-param 9 }T
T{ s" names.already-declared" verdict -> outcome-rejected lf-diag-already-declared 6 }T
T{ s" result.index-mentions-type" verdict -> outcome-rejected lf-diag-return-type 9 }T
\ Positivity (P1, P2) at step 9, after U1, with the field's binder: a
\ negative occurrence, doubly negative, after beta, in a later binder of
\ the field's type, in a later field; an occurrence that is no valid
\ application, directly and after a Pi; the universe checked first; C1
\ before them all.
T{ s" pos.negative" verdict-field -> outcome-rejected lf-diag-non-positive 9 0 }T
T{ s" pos.double-negative" verdict-field -> outcome-rejected lf-diag-non-positive 9 0 }T
T{ s" pos.negative-through-beta" verdict-field -> outcome-rejected lf-diag-non-positive 9 0 }T
T{ s" pos.negative-second-binder" verdict-field -> outcome-rejected lf-diag-non-positive 9 0 }T
T{ s" pos.negative-later-field" verdict-field -> outcome-rejected lf-diag-non-positive 9 1 }T
T{ s" pos.non-valid-occurrence" verdict-field -> outcome-rejected lf-diag-non-valid 9 1 }T
T{ s" pos.non-valid-after-pi" verdict-field -> outcome-rejected lf-diag-non-valid 9 1 }T
\ A Pi's domain tested for an occurrence before any reduction, though a
\ redex there drops it (review rvN1 M1); the type as an index of another
\ inductive type, no nesting.
T{ s" pos.negative-redex-domain" verdict-field -> outcome-rejected lf-diag-non-positive 9 0 }T
T{ s" pos.negative-redex-domain-later" verdict-field
   -> outcome-rejected lf-diag-non-positive 9 0 }T
T{ s" pos.non-valid-index-of-other" verdict-field -> outcome-rejected lf-diag-non-valid 9 0 }T
T{ s" pos.universe-checked-first" verdict -> outcome-rejected lf-diag-universe-too-big 9 }T
\ K and structure eta on a variable of the block's own telescope (the
\ follow-up of task 5.2.1b, iota.fs; the arena's bugs/proj-of-stuck-prop
\ and bugs/rec-missing-ih): each binder steps 8 and 9 walk into is opened
\ on the job's scope, as Lean's mk_local_decl_for opens it. A recursive
\ field reached so stays unknown in the recursor builder (step 12), whose
\ binders no scope holds (GAPS in tests/core/inductive-table.py).
T{ s" k.block-index-variable" verdict -> outcome-ok 0 all-steps }T
T{ s" k.mutual-index-variable" verdict -> outcome-ok 0 all-steps }T
T{ s" eta.block-index-variable" verdict -> outcome-ok 0 all-steps }T
T{ s" k.block-index-stuck" verdict -> outcome-rejected lf-diag-block-not-sort 8 }T
T{ s" k.mutual-index-stuck" verdict -> outcome-rejected lf-diag-block-not-sort 8 }T
T{ s" eta.block-index-prop-stuck" verdict -> outcome-rejected lf-diag-block-not-sort 8 }T
\ The same with a parameter before the index (review rvIO G3).
T{ s" k.param-index-variable" verdict -> outcome-ok 0 all-steps }T
T{ s" eta.param-index-variable" verdict -> outcome-ok 0 all-steps }T
T{ s" k.param-index-stuck" verdict -> outcome-rejected lf-diag-block-not-sort 8 }T
T{ s" eta.param-index-prop-stuck" verdict -> outcome-rejected lf-diag-block-not-sort 8 }T
T{ s" k.field-stuck" verdict-field -> outcome-rejected lf-diag-non-valid 9 1 }T
T{ s" k.field-under-binder-stuck" verdict-field -> outcome-rejected lf-diag-non-valid 9 2 }T
T{ s" k.field-variable" verdict -> outcome-unknown lf-diag-iota-pending 12 }T
T{ s" k.field-after-binder-variable" verdict -> outcome-unknown lf-diag-iota-pending 12 }T
T{ s" uniform.other-argument" verdict -> outcome-rejected lf-diag-nonuniform 3 }T
T{ s" uniform.definitionally-equal-argument" verdict -> outcome-rejected lf-diag-nonuniform 3 }T
\ A let in a constructor type: its value is walked like any child (Lean's
\ check_uniform_ind_occs); pinned Lean agrees on both (review rvS5B T1).
T{ s" uniform.let-other-argument" verdict -> outcome-rejected lf-diag-nonuniform 3 }T
T{ s" uniform.let-uniform" verdict -> outcome-ok 0 all-steps }T
\ Thirty shared closed terms met at many depths in turn: C1 visits each
\ (term, depth) pair once, as Lean's for_each with an offset does, within
\ this file's million units (review rvKN 1: marks keeping one depth per
\ term ran out of fuel; pinned Lean accepts).
T{ s" uniform.shared-depths" verdict -> outcome-ok 0 all-steps }T

\ Lean's replay of the Bool block (B3, B4).
T{ s" replay-bool.original" verdict -> outcome-ok 0 all-steps }T
T{ s" replay-bool.rule-right-sides-swapped" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 9 }T
T{ s" replay-bool.recursor-k-set" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 10 }T
T{ s" replay-bool.recursor-motives-changed" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 7 }T
T{ s" replay-bool.recursor-universe-dropped" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 2 }T
T{ s" replay-bool.constructor-type-changed" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 3 }T
T{ s" replay-bool.recursor-renamed" verdict -> outcome-rejected lf-diag-no-such-recursor 13 }T
T{ s" replay-bool.constructor-index-changed" verdict-field
   -> outcome-rejected lf-diag-invalid-constructor 13 3 }T
T{ s" replay-bool.constructor-fields-changed" verdict-field
   -> outcome-rejected lf-diag-invalid-constructor 13 5 }T
T{ s" replay-bool.parameters-changed" verdict -> outcome-rejected lf-diag-nonuniform 3 }T
T{ s" replay-bool.isRec-changed" verdict-warned -> outcome-ok 0 all-steps lf-warn-rec }T
T{ s" replay-bool.indices-changed" verdict-warned -> outcome-ok 0 all-steps lf-warn-indices }T
T{ s" replay-bool.recursor-left-out" verdict-warned
   -> outcome-ok 0 all-steps lf-warn-no-recursor }T
\ The review rvI21's probes: the recursor's universe renamed or doubled,
\ its all doubled, its minor premises swapped (with its rules too), a
\ constructor given a universe; k set for And and for U (in Type), Or's
\ recursor made to eliminate into every universe.
T{ s" replay-bool.recursor-universe-renamed" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 2 }T
T{ s" replay-bool.recursor-universe-doubled" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 2 }T
T{ s" replay-bool.recursor-all-doubled" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 4 }T
T{ s" replay-bool.minor-premises-swapped" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 3 }T
T{ s" replay-bool.minor-premises-and-rules-swapped" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 3 }T
T{ s" replay-bool.constructor-universe-added" verdict-field
   -> outcome-rejected lf-diag-invalid-constructor 13 1 }T
T{ s" replay-and.recursor-k-set" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 10 }T
T{ s" replay-unit.recursor-k-set" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 10 }T
T{ s" replay-or.recursor-large-elimination" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 2 }T
\ Lean's replay of the recursive N block (task 5.2.1b): the recursive
\ rule's right side swapped with the other, k set, the motives changed, a
\ constructor's field count, a constructor's type (the recursor then
\ differs), the parameters (C1); the ignored fields (B4).
T{ s" replay.original" verdict -> outcome-ok 0 all-steps }T
T{ s" replay.rule-right-sides-swapped" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 9 }T
T{ s" replay.recursor-k-set" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 10 }T
T{ s" replay.recursor-motives-changed" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 7 }T
T{ s" replay.constructor-fields-changed" verdict-field
   -> outcome-rejected lf-diag-invalid-constructor 13 5 }T
T{ s" replay.constructor-type-changed" verdict-field
   -> outcome-rejected lf-diag-invalid-recursor 13 3 }T
T{ s" replay.parameters-changed" verdict -> outcome-rejected lf-diag-nonuniform 3 }T
T{ s" replay.isRec-changed" verdict-warned -> outcome-ok 0 all-steps lf-warn-rec }T
T{ s" replay.indices-changed" verdict-warned -> outcome-ok 0 all-steps lf-warn-indices }T
T{ s" replay.recursor-left-out" verdict-warned
   -> outcome-ok 0 all-steps lf-warn-no-recursor }T

\ Lean's whnf with delta (whnf.fs) in positivity and in the telescope:
\ id (Bad -> Nat) unfolds to a negative occurrence (rejected, as Lean);
\ a telescope ending in a definition equal to Type is a Sort (accepted,
\ the recursor equal to Lean's; review rvN1 M1).
T{ s" pos.through-definition" verdict-field -> outcome-rejected lf-diag-non-positive 9 0 }T
T{ s" universe.type-a-sort-by-definition" verdict -> outcome-ok 0 all-steps }T
\ Through iota (iota.fs) too: Bool.rec reduces a field's type to the type
\ itself (recursive, with its hypothesis in the recursor) or to Nat; and
\ Function.const unfolds to Nat. All accepted, as Lean.
T{ s" pos.through-recursor" verdict -> outcome-ok 0 all-steps }T
T{ s" pos.erased-by-recursor" verdict -> outcome-ok 0 all-steps }T
T{ s" pos.erased-by-definition" verdict -> outcome-ok 0 all-steps }T
\ Shared terms (the Navier-Stokes structures): a field type of 41 terms
\ and 2^40 paths, in the field's whnf (lets) or in the constructor type
\ itself, checked on this file's fuel (a million units), as Lean visits
\ each shared term once: the products of Nat accepted (the recursor equal
\ to Lean's by ==), the product of Bad -> Nat a non-valid occurrence and
\ the functions of Bad a non-positive one, as Lean says. Before each walk
\ met a shared node once, all four ran out of fuel.
T{ s" pos.shared-whnf" verdict -> outcome-ok 0 all-steps }T
T{ s" pos.shared-field" verdict -> outcome-ok 0 all-steps }T
T{ s" pos.shared-whnf-non-valid" verdict-field -> outcome-rejected lf-diag-non-valid 9 0 }T
T{ s" pos.shared-field-negative" verdict-field
   -> outcome-rejected lf-diag-non-positive 9 0 }T
\ Iota in a declaration's check (Lean's reduce_recursor, behind whnf.fs's
\ hook): a constructor's rule with its fields, its induction hypothesis
\ and an argument after the major premise, Nat.zero, Eq.refl (k set);
\ Nat.succ is a literal first (Lean's reduce_nat, K7: task 5.2.3).
T{ s" iota.bool-true" used -> outcome-ok 0 }T
T{ s" iota.list-hypothesis" used -> outcome-ok 0 }T
T{ s" iota.list-field" used -> outcome-ok 0 }T
T{ s" iota.argument-after-major" used -> outcome-ok 0 }T
T{ s" iota.nat-zero" used -> outcome-ok 0 }T
T{ s" iota.eq-refl" used -> outcome-ok 0 }T
\ Lean's is_def_eq says no after iota (or with iota stuck): rejected since
\ plan task 4.2.2d (declTypeMismatch).
T{ s" iota.bool-true-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" iota.list-hypothesis-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" iota.bool-stuck" used -> outcome-rejected lf-diag-value-apart }T
T{ s" iota.nat-succ" used -> outcome-ok 0 }T
\ K-like reduction (R2, Lean's to_cnstr_when_K; task 5.2.1c): Eq.rec and
\ True.rec on a variable proof reduce when its type is is_def_eq the
\ nullary constructor's -- equal, equal after unfolding id, or the
\ inductive type only after whnf; with different ends they stay stuck and
\ the declaration is rejected, as by Lean.
T{ s" k.eq-variable-proof" used -> outcome-ok 0 }T
T{ s" k.eq-ends-defeq" used -> outcome-ok 0 }T
T{ s" k.type-through-definition" used -> outcome-ok 0 }T
T{ s" k.true-variable-proof" used -> outcome-ok 0 }T
T{ s" k.eq-different-ends" used -> outcome-rejected lf-diag-value-apart }T
T{ s" k.eq-different-ends-wrong" used -> outcome-rejected lf-diag-value-apart }T
\ Literals (task 5.2.3): Nat.rec on a literal major (L2), as its
\ constructor; 2^64 by Nat.pow, two limbs, right and wrong; Nat.pow by
\ 2^32, Lean's refusal (rejected; the declaration's mismatch records it),
\ and by 2^32 - 1 of 1.
T{ s" iota.nat-literal-major" used -> outcome-ok 0 }T
T{ s" iota.nat-literal-major-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" lit.pow-direct" used -> outcome-ok 0 }T
T{ s" lit.pow-direct-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" lit.pow-count-too-big" used drop -> outcome-rejected }T
T{ s" lit.pow-count-limit" used -> outcome-ok 0 }T
\ String literals (task 5.2.3, strings): with String.ofList an axiom, a
\ literal against String.ofList of its characters is decided by
\ try_string_lit_expansion (step 13), either way round; a wrong character
\ rejected.
T{ s" primitive.string-opaque-expansion" used -> outcome-ok 0 }T
T{ s" primitive.string-opaque-expansion-reversed" used -> outcome-ok 0 }T
T{ s" primitive.string-opaque-expansion-wrong" used -> outcome-rejected lf-diag-value-apart }T
\ A recursor on a literal of a String with two constructors (no structure
\ eta): iota through the literal's constructor form (L2), right and wrong.
T{ s" primitive.string-major-two-constructors" used -> outcome-ok 0 }T
T{ s" primitive.string-major-two-constructors-wrong" used
   -> outcome-rejected lf-diag-value-apart }T
\ Review rvCONV B1: whnf's reduce_nat computes under a variable, as Lean's
\ (no free-variable test: type_checker.cpp 672-703, 732): 0 ^ 2^32 and
\ 2 <<< 2^32 refused, 0 ^ 4 computed. With a Nat.add that gives Nat.zero,
\ Nat.add ((fun _ => 2) x) 3 is 5: IE.A, whose type then needs the empty
\ IE.F, is rejected, and IE.bad, the proof of IE.F after it, too; the
\ twin IE.A, for IE.T, accepted.
T{ s" lit.free-variable-pow-refused" used drop -> outcome-rejected }T
T{ s" lit.free-variable-pow" used -> outcome-ok 0 }T
T{ s" lit.free-variable-shift-refused" used drop -> outcome-rejected }T
T{ s" k7.free-variable-computes" before-last -> outcome-rejected lf-diag-value-apart }T
T{ s" k7.free-variable-computes" used drop -> outcome-rejected }T
T{ s" k7.free-variable-computes-twin" used -> outcome-ok 0 }T
\ Review rvCONV M1: a power of a three-limb base, 12,800 bits, computed
\ (the scratch estimate once left it full), against two halves' product.
T{ s" lit.pow-multi-limb-base" used -> outcome-ok 0 }T
T{ s" lit.pow-multi-limb-base-wrong" used -> outcome-rejected lf-diag-value-apart }T
\ Review rvCONV B2: structure eta (R4) and unit-like types (R5) read the
\ numIndices and isRec the block check computed (lf-env-shape), never the
\ file's, which Lean's replay ignores (B4: a warning only). An indexed
\ type said unindexed is no unit-like type, a recursive one said not
\ recursive no structure: rejected, as with the true file; a unit type
\ said indexed, and a structure said recursive, still are: accepted.
T{ s" lie.indexed-then-unit-like" used -> outcome-rejected lf-diag-value-apart }T
T{ s" lie.indexed-said-unindexed-then-unit-like" used
   -> outcome-rejected lf-diag-value-apart }T
T{ s" lie.unit-said-indexed-then-unit-like" used -> outcome-ok 0 }T
T{ s" lie.recursive-then-eta" used -> outcome-rejected lf-diag-value-apart }T
T{ s" lie.recursive-said-not-then-eta" used -> outcome-rejected lf-diag-value-apart }T
T{ s" lie.structure-said-recursive-then-eta" used -> outcome-ok 0 }T
\ The same for projections (J1: a structure said indexed takes no index
\ argument) and for iota's structure eta (R3: a structure said recursive
\ still expands, a recursive type said not recursive does not).
T{ s" lie.structure-said-indexed-then-eta" used -> outcome-ok 0 }T
T{ s" lie.structure-said-recursive-then-iota" used -> outcome-ok 0 }T
T{ s" lie.recursive-said-not-then-iota" used -> outcome-rejected lf-diag-value-apart }T
\ Review rvCACHE: a definition whose value, (fun _ : PUnit.{1} =>
\ PUnit.{2}) PUnit.unit.{1}, is a Type 1: declared a Type, rejected (a
\ cache key without universe arguments would reuse PUnit.{1}'s type for
\ PUnit.{2}), declared a Type 1, accepted. And fun p : Bool x Nat => (fun
\ (_ : Bool) (b : t) => b) p.1 p.2: rejected for t Bool, accepted for t
\ Nat (a key without the projection's index would give p.2 p.1's type).
T{ s" cache.universe-arguments-differ" used -> outcome-rejected lf-diag-value-apart }T
T{ s" cache.universe-arguments-differ-twin" used -> outcome-ok 0 }T
T{ s" cache.projection-index-differs" used drop -> outcome-rejected }T
T{ s" cache.projection-index-differs-twin" used -> outcome-ok 0 }T
\ Review rvN1 round 2 (L1): a reduct that keeps the recursor's universe
\ arguments in its recursive call; iota on Lean's generated recursor
\ after B3 refused the block's swapped rules (not ported yet: unknown,
\ never the file's rules).
T{ s" iota.levels-in-reduct" used -> outcome-ok 0 }T
T{ s" iota.levels-in-reduct-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" after.b3-swapped-then-iota-lean-rule" used -> outcome-unknown lf-diag-iota-pending }T
T{ s" after.b3-swapped-then-iota-forged-rule" used -> outcome-unknown lf-diag-iota-pending }T
\ Projections (task 5.2.2): typed by infer_proj, a data field of a pair
\ and a proof's field of a conjunction; invalidProj rejected: a data
\ field out of a proof, the wrong structure, an index past the fields.
T{ s" proj.data" used -> outcome-ok 0 }T
T{ s" proj.proof-of-proof" used -> outcome-ok 0 }T
T{ s" proj.data-from-proof" used -> outcome-rejected lf-diag-invalid-proj }T
T{ s" proj.wrong-structure" used -> outcome-rejected lf-diag-invalid-proj }T
T{ s" proj.index-out-of-range" used -> outcome-rejected lf-diag-invalid-proj }T
\ A projection of a constructor application reduces to its field
\ (reduce_proj): (Bool, Nat).1 is Bool; the wrong twin rejected, as by
\ Lean.
T{ s" proj.reduces" used -> outcome-ok 0 }T
T{ s" proj.reduces-wrong" used -> outcome-rejected lf-diag-value-apart }T
\ Structure eta in iota (R3): the major premises of PUnit and Prod
\ expanded, accepted; And's, a proposition's, left stuck as by Lean, so
\ rejected; a reduct p.1 compared with Prod.fst p, two projections.
T{ s" iota.punit-eta" used -> outcome-ok 0 }T
T{ s" iota.prod-eta" used -> outcome-ok 0 }T
T{ s" iota.and-prop-stuck-bool" used -> outcome-rejected lf-diag-value-apart }T
T{ s" iota.structure-eta" used -> outcome-ok 0 }T
\ p.1 = p.2: two projections of p that differ in the field, never equal
\ by Lean's ==; no step of defeq.fs's comparison finds them equal (step
\ 8 needs one field, is_def_eq_app takes no projection), rejected as by
\ Lean.
T{ s" proj.index-differs" used -> outcome-rejected lf-diag-value-apart }T
\ The comparison's projection steps (task 5.2.2, defeq.fs), each accepted
\ and its wrong twin rejected, as by Lean: is_def_eq_app takes no
\ projection, so p.1 against a pair goes on to structure eta (the shape
\ of Init's UInt8.toNat_toUInt32); step 8 equates (g (id a)).1 and
\ (g a).1, and the fields of two pairs; step 9 reduces (id (a, b)).2,
\ which whnf_core with cheap_proj leaves; try_unfold_proj_app puts a
\ projection's application in whnf_core first, or unfolds id p.1 when
\ that changes nothing.
T{ s" proj.app-eta" used -> outcome-ok 0 }T
T{ s" proj.app-eta-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" proj.lazy-terms" used -> outcome-ok 0 }T
T{ s" proj.lazy-terms-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" proj.lazy-fields" used -> outcome-ok 0 }T
T{ s" proj.lazy-fields-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" proj.whnf-term" used -> outcome-ok 0 }T
T{ s" proj.whnf-term-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" proj.unfold-proj-app" used -> outcome-ok 0 }T
T{ s" proj.unfold-proj-app-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" proj.unfold-proj-app-stuck" used -> outcome-ok 0 }T
T{ s" proj.unfold-proj-app-stuck-wrong" used -> outcome-rejected lf-diag-value-apart }T
\ Structure eta and unit-like types in is_def_eq (R4, R5; task 5.2.2,
\ defeq.fs steps 12 and 14): p and (p.1, p.2) equal either way round,
\ two values of PUnit equal, as by Lean; a pair whose second field is not
\ p.2, Bool (no structure) and a pair of units (Lean's own limitation
\ BL-7) rejected, as by Lean.
T{ s" unit.bool-not-unit-like" used -> outcome-rejected lf-diag-value-apart }T
T{ s" unit.bool-variables" used -> outcome-rejected lf-diag-value-apart }T
T{ s" unit.pair-of-units" used -> outcome-rejected lf-diag-value-apart }T
T{ s" eta.structure" used -> outcome-ok 0 }T
T{ s" eta.structure-left" used -> outcome-ok 0 }T
T{ s" eta.structure-wrong-field" used -> outcome-rejected lf-diag-value-apart }T
\ Init's WellFounded.extrinsicFix₂ needs R ⟨a, b⟩ x equal to
\ R ⟨a, b⟩ ⟨x.1, x.2⟩ (structure eta on PSigma): its shape, accepted.
T{ s" eta.psigma-extrinsic-fix" used -> outcome-ok 0 }T
T{ s" unit.punit" used -> outcome-ok 0 }T
\ C2's comparison of id Type with Type needs Lean's lazy delta reduction
\ (accepted since plan task 4.2.2d). Unknown, unsupported and invalid:
T{ s" params.constructor-binder-defeq" verdict nip -> outcome-ok 15 }T
\ Forged arithmetic (review rvN1 B1, B2). Lean's whnf computes the Nat
\ operations by name (task 5.2.3, reduce-nat.fs) and refuses Nat.pow or
\ Nat.shiftLeft by 2^32 or more (get_count_arg), on a field whose type
\ mentions no type of the block too (positivity puts every field in
\ whnf): rejected at step 9 (92), Lean's natCountTooBig; below the limit
\ accepted. A block named Nat.add: Lean's whnf computes Nat.add 0 0 to 0,
\ so its field is no recursive one: accepted, and the recursor with a
\ hypothesis rejected (B3), as by Lean.
T{ s" forged.pow-field" verdict -> outcome-rejected lf-diag-nat-count 9 }T
T{ s" forged.pow-field-recursive" verdict -> outcome-rejected lf-diag-nat-count 9 }T
T{ s" forged.pow-field-small" used -> outcome-ok 0 }T
T{ s" forged.pow-through-definition" verdict -> outcome-rejected lf-diag-nat-count 9 }T
T{ s" forged.pow-through-definition-nonrecursive" verdict
   -> outcome-rejected lf-diag-nat-count 9 }T
T{ s" forged.pow-erased-by-beta" verdict -> outcome-rejected lf-diag-nat-count 9 }T
T{ s" forged.shiftleft-field" verdict -> outcome-rejected lf-diag-nat-count 9 }T
T{ s" forged.type-named-nat-pow" used -> outcome-ok 0 }T
T{ s" forged.type-named-nat-add" used -> outcome-ok 0 }T
T{ s" forged.type-named-nat-add-recursor-with-hypothesis" verdict
   -> outcome-rejected lf-diag-invalid-recursor 13 }T
\ Nested blocks (task 5.2.5b): List Tree, and List (Bad -> Nat), which Lean
\ rejects only after making the block mutual: the auxiliary constructor
\ _nested.List_1.cons's field 0 (the diagnostic names the first member).
T{ s" nested.tree" verdict -> outcome-ok 0 all-steps }T
T{ s" nested.non-positive" verdict-field -> outcome-rejected lf-diag-non-positive 9 0 }T
\ Lean's auxiliary blocks for Array (Array_1, List_2), List (List _), Option,
\ Prod with two parameters, a block parameter, a universe parameter,
\ under a binder (Ds lowered past it), inside a mutual block, Thunk
\ (reflexive only as the auxiliary block: no B4 warning), and a parameter
\ the auxiliary block drops: accepted, every recursor equal to Lean's.
T{ s" nested.array-tree" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.list-list" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.option" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.prod" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.parameter" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.universe" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.under-binder" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.mutual" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.thunk" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.tree" verdict-warned -> outcome-ok 0 all-steps 0 }T
T{ s" nested.phantom-parameter" verdict -> outcome-ok 0 all-steps }T
\ Names: _nested.List_1 declared before, so the auxiliary type is
\ _nested.List_2 (mk_unique_name); _nested.List_1.rec declared before
\ (step 6, N2); a constructor named Tree.rec_1, the restored auxiliary
\ recursor's name (step 12, check_name).
T{ s" nested.aux-name-taken" verdict -> outcome-ok 0 all-steps }T
T{ s" nested.aux-rec-name-taken" verdict -> outcome-rejected lf-diag-already-declared 6 }T
T{ s" nested.constructor-named-rec-1" verdict
   -> outcome-rejected lf-diag-already-declared 12 }T
\ Review rvUNNI, each with the official checker's verdict (lean4export's
\ parser, then Lean's replay): a definition named T.rec_1 after a nested
\ block (N2); one named T.rec_18446744073709551617, never read modulo
\ 2^64 as rec_1 (L1); a constructor with a projection of a structure
\ named under _nested (T0, M3), and its twin with Prod.
T{ s" nested.def-named-rec-1" used -> outcome-rejected lf-diag-already-declared }T
T{ s" nested.def-named-rec-huge" used -> outcome-ok 0 }T
T{ s" names.reserved-nested-prefix-proj" verdict -> outcome-rejected lf-diag-reserved-prefix 2 }T
T{ s" names.reserved-nested-prefix-proj-twin" verdict -> outcome-ok 0 all-steps }T
\ A skipped definition named like the recursor Lean's kernel generates
\ for a later block that leaves it out (M1): the block is accepted, for
\ T.rec and for a nested block's T.rec_1; when the block holds that
\ recursor, its name is given twice (step 6). An unsafe block whose two
\ constructors have one name, as the exporter writes it (B1): rejected.
T{ s" unsafe.rec-name-before-block" verdict -> outcome-ok 0 all-steps }T
T{ s" partial.rec-name-before-block" verdict -> outcome-ok 0 all-steps }T
T{ s" unsafe.aux-rec-name-before-nested-block" verdict -> outcome-ok 0 all-steps }T
T{ s" unsafe.rec-name-before-block-holding-it" verdict
   -> outcome-rejected lf-diag-already-declared 6 }T
T{ s" unsafe.block-constructor-twice" verdict -> outcome-rejected lf-diag-already-declared 1 }T
\ A local variable in Ds (N2, step 4); Array (Bad -> Nat) (P1 in the
\ auxiliary List_2.cons); an ill-typed Ds only the typing of the nested
\ occurrences sees (step 12).
T{ s" nested.local-variable" verdict -> outcome-rejected lf-diag-nested-local 4 }T
T{ s" nested.array-non-positive" verdict -> outcome-rejected lf-diag-non-positive 9 }T
T{ s" nested.ill-typed-parameter" verdict -> outcome-rejected lf-diag-function-expected 12 }T
\ Lean's replay of Tree with Tree.rec_1 (the auxiliary recursor) mutated:
\ the field B3 names (3 type, 7 motives, 8 minors, 9 rules), no such
\ recursor, or accepted (left out; numNested only warned, B4).
: invalid-rec ( n2 -- outcome code step n2 ) >r outcome-rejected lf-diag-invalid-recursor 13 r> ;
T{ s" replay-nested.original" verdict-field -> outcome-ok 0 all-steps 0 }T
T{ s" replay-nested.aux-rules-swapped" verdict-field -> 9 invalid-rec }T
T{ s" replay-nested.aux-type-changed" verdict-field -> 3 invalid-rec }T
T{ s" replay-nested.aux-motives-changed" verdict-field -> 7 invalid-rec }T
T{ s" replay-nested.aux-minors-changed" verdict-field -> 8 invalid-rec }T
T{ s" replay-nested.aux-nfields-changed" verdict-field -> 9 invalid-rec }T
T{ s" replay-nested.aux-rule-constructor-changed" verdict-field -> 9 invalid-rec }T
T{ s" replay-nested.main-motives-changed" verdict-field -> 7 invalid-rec }T
T{ s" replay-nested.aux-renamed" verdict-field
   -> outcome-rejected lf-diag-no-such-recursor 13 0 }T
T{ s" replay-nested.aux-left-out" verdict-field -> outcome-ok 0 all-steps 0 }T
T{ s" replay-nested.numNested-changed" verdict-warned
   -> outcome-ok 0 all-steps lf-warn-nested }T
\ An empty block: the importer stages it as one declaration (ADR 0016
\ amendment 1), which the check rejects at step 4 as Lean's kernel does
\ (emptyBlock).
T{ s" names.empty-block" verdict -> outcome-rejected lf-diag-empty-block 4 }T
\ Two variables of a unit-like structure: Lean's is_def_eq_unit_like
\ equates them, so D3/D5 must not call P x and P y apart (P4): accepted.
T{ s" unit.punit-variables" used -> outcome-ok 0 }T

\ ---------------------------------------------------------------------------
\ 2. blocks.ndjson: N, Both, Same, Either, Nat, the mutual Even/Odd, List,
\ the nested Tree (with Tree.rec_1; task 5.2.5b) and Point accepted, every
\ member's slot final and accepted, with a handle and no axioms; and
\ Point.x, a projection, accepted (task 5.2.2).
: blocks ( -- c-addr u ) s" tests/reference/inductive/blocks.ndjson" ;
: member-ok? ( d -- flag )
  dup lf-env-outcome ok? over lf-env-handle ok? nip nip and
  swap lf-env-axioms ok? swap 0= and and ;
: all-ok? ( from to -- flag ) true -rot swap ?do i member-ok? and loop ;
T{ blocks staged fuel checked -> outcome-ok }T
T{ 0 18 all-ok? 18 25 all-ok? 25 29 all-ok? -> true true true }T
T{ 29 33 all-ok? 33 36 all-ok? 36 37 all-ok? -> true true true }T
finish

\ ---------------------------------------------------------------------------
\ 3. Tampered after the feed (the input is sealed, but its inductive data
\ is plain cells a test can change). Both: 4 Both, 5 Both.intro, 6
\ Both.rec; Same: 7-9 (k set); Either: 10 Either, 11 inl, 12 inr, 13
\ Either.rec; Point.x (36) holds a projection.
: data ( d -- addr ) lf-input-decl lf-idecl-data ;
: cell! ( x d k -- ) cells swap data + ! ;
: rule ( d j -- addr ) swap data lf-irc-rules@ drop swap lf-irc-rule ;
: rhs ( d j -- addr ) rule 2 cells + ;
\ Run xt, then give block d's outcome, code and second number.
: block-verdict ( xt d -- outcome code n2 )
  >r blocks staged ok? must execute fuel checked
  r@ lf-env-outcome r@ codes at @ r> n2s at @ finish ;
: block-warned ( xt d -- outcome bits )
  >r blocks staged ok? must execute fuel checked
  r@ lf-env-outcome r> block-warns at @ finish ;
\ The recursor (B3), the field differing named.
: k-cleared ( -- ) 0 9 lf-irc-k cell! ;
T{ ' k-cleared 7 block-verdict -> outcome-rejected lf-diag-invalid-recursor 10 }T
: minors+ ( -- ) 2 6 lf-irc-minors cell! ;
T{ ' minors+ 4 block-verdict -> outcome-rejected lf-diag-invalid-recursor 8 }T
: indices- ( -- ) 0 9 lf-irc-indices cell! ;
T{ ' indices- 7 block-verdict -> outcome-rejected lf-diag-invalid-recursor 6 }T
: params- ( -- ) 1 6 lf-irc-params cell! ;
T{ ' params- 4 block-verdict -> outcome-rejected lf-diag-invalid-recursor 5 }T
: nfields+ ( -- ) 1 13 0 rule cell+ +! ;
T{ ' nfields+ 10 block-verdict -> outcome-rejected lf-diag-invalid-recursor 9 }T
: ctor-renamed ( -- ) 13 1 rule @ 13 0 rule ! ;
T{ ' ctor-renamed 10 block-verdict -> outcome-rejected lf-diag-invalid-recursor 9 }T
: rules-swapped ( -- ) 13 0 rhs 13 1 rhs over @ over @ >r swap ! r> swap ! ;
T{ ' rules-swapped 10 block-verdict -> outcome-rejected lf-diag-invalid-recursor 9 }T
: rec-type ( -- ) 9 lf-input-decl lf-idecl-type @ 6 lf-input-decl lf-idecl-type ! ;
T{ ' rec-type 4 block-verdict -> outcome-rejected lf-diag-invalid-recursor 3 }T
\ The recursive N (0 N, 1 zero, 2 succ, 3 N.rec): its rules swapped (the
\ recursive call given to zero), its type replaced by Both.rec's.
: n-rules-swapped ( -- ) 3 0 rhs 3 1 rhs over @ over @ >r swap ! r> swap ! ;
T{ ' n-rules-swapped 0 block-verdict -> outcome-rejected lf-diag-invalid-recursor 9 }T
: n-rec-type ( -- ) 6 lf-input-decl lf-idecl-type @ 3 lf-input-decl lf-idecl-type ! ;
T{ ' n-rec-type 0 block-verdict -> outcome-rejected lf-diag-invalid-recursor 3 }T
\ The constructors.
: cidx+ ( -- ) 1 5 lf-ict-cidx cell! ;
T{ ' cidx+ 4 block-verdict -> outcome-rejected lf-diag-invalid-constructor 3 }T
: ctor-params ( -- ) 1 5 lf-ict-params cell! ;
T{ ' ctor-params 4 block-verdict -> outcome-rejected lf-diag-invalid-constructor 4 }T
: ctor-fields ( -- ) 2 12 lf-ict-fields cell! ;
T{ ' ctor-fields 10 block-verdict -> outcome-rejected lf-diag-invalid-constructor 5 }T
\ The type's fields Lean's replay ignores (B4): accepted, with a warning.
: nested ( -- ) 1 4 lf-ity-nested cell! ;
T{ ' nested 4 block-warned -> outcome-ok lf-warn-nested }T
: reflexive ( -- ) lf-ity-reflexive-bit 10 lf-ity-flags cell! ;
T{ ' reflexive 10 block-warned -> outcome-ok lf-warn-reflexive }T
\ N is recursive (Lean's is_rec): its isRec bit cleared is a warning.
: n-not-rec ( -- ) 0 0 lf-ity-flags cell! ;
T{ ' n-not-rec 0 block-warned -> outcome-ok lf-warn-rec }T
\ The shape (B0): a constructor naming another type is invalid.
: induct ( -- ) 7 lf-input-name 5 lf-ict-induct cell! ;
T{ ' induct 4 block-verdict drop -> outcome-invalid lf-diag-block-shape }T
\ The audit: an unsafe member, a literal in a constructor type (U2; a
\ projection planted in a rule was the case until task 5.2.2 supported
\ projections), a loose variable (V1).
: unsafe ( -- ) lf-safety-unsafe 5 lf-input-decl lf-idecl-safety ! ;
T{ ' unsafe 4 block-verdict drop -> outcome-unsupported lf-diag-unsupported-kind }T
\ Every member unsafe, as Lean writes an unsafe block (plan task 5.2.7):
\ skipped as Lean's replay skips it, rejected, each member marked.
: all-unsafe ( -- ) 7 4 do lf-safety-unsafe i lf-input-decl lf-idecl-safety ! loop ;
T{ ' all-unsafe 4 block-verdict -> outcome-rejected lf-diag-skipped lf-safety-unsafe }T
: members-skipped ( -- flag flag flag flag )
  blocks staged ok? must all-unsafe fuel checked
  4 lf-env-skipped? 5 lf-env-skipped? 6 lf-env-skipped? 7 lf-env-skipped? finish ;
T{ members-skipped -> true true true false }T
\ Two constructors of one name in an unsafe block (review rvUNNI B1):
\ Either's inr named inl, in its ctors list too. lean4export's parser
\ refuses the file, so the block is rejected as already declared (the
\ name, inl's declaration), never skipped, also with only some members
\ unsafe; safe, C4 rejects it at step 9.
: either-unsafe ( -- ) 14 10 do lf-safety-unsafe i lf-input-decl lf-idecl-safety ! loop ;
: inr-named-inl ( -- )
  11 lf-input-name dup 12 lf-input-decl lf-idecl-name !
  10 data lf-ity-ctors@ drop cell+ ! ;
: either-twice ( -- ) either-unsafe inr-named-inl ;
T{ ' either-twice 10 block-verdict -> outcome-rejected lf-diag-already-declared 11 }T
: either-twice-skipped? ( -- flag )
  blocks staged ok? must either-twice fuel checked 12 lf-env-skipped? finish ;
T{ either-twice-skipped? -> false }T
: inr-unsafe-twice ( -- ) lf-safety-unsafe 12 lf-input-decl lf-idecl-safety ! inr-named-inl ;
T{ ' inr-unsafe-twice 10 block-verdict -> outcome-rejected lf-diag-already-declared 11 }T
T{ ' inr-named-inl 10 block-verdict drop -> outcome-rejected lf-diag-duplicate-ctor }T
T{ s" mutual.even-odd" used -> outcome-ok 0 }T
: a-variable ( -- node ) 0 begin dup lf-term-tag@ lf-tag-bvar <> while 1+ repeat ;
: loose ( -- ) a-variable 6 0 rhs ! ;
T{ ' loose 4 block-verdict drop -> outcome-invalid lf-diag-out-of-scope }T

\ ---------------------------------------------------------------------------
\ 4. Fuel: every budget 2^k - 1 gives ok or exhausted; the least budget
\ that gives ok is found by bisection, and one unit less is exhausted: for
\ Bool, and for List (positivity, induction hypotheses).
2variable fuel-case
: bool-at ( budget -- outcome )
  fuel-case 2@ case-path staged ok? must checked 0 lf-env-outcome finish ;
: ok-or-exhausted? ( outcome -- flag ) dup ok? swap outcome-exhausted = or ;
: doubling? ( -- flag ) true 21 0 do 1 i lshift 1- bool-at ok-or-exhausted? and loop ;
: halfway ( lo hi -- lo hi mid ) 2dup + 2/ ;
: least-ok ( -- budget )
  0 1 20 lshift begin 2dup - -1 < while
    halfway dup bool-at ok? if nip else rot drop swap then
  repeat nip ;
s" ind.bool" fuel-case 2!
T{ doubling? -> true }T
T{ least-ok dup 1- bool-at swap bool-at -> outcome-exhausted outcome-ok }T
s" ind.list" fuel-case 2!
T{ doubling? -> true }T
T{ least-ok dup 1- bool-at swap bool-at -> outcome-exhausted outcome-ok }T
\ A field put in whnf by beta (the recursor builder's own whnf): running out
\ of fuel there ends the block exhausted, not full or ok.
s" ind.recursive-through-beta" fuel-case 2!
T{ doubling? -> true }T
T{ least-ok dup 1- bool-at swap bool-at -> outcome-exhausted outcome-ok }T

\ 5. Room: with the term store's capacity cut to the records in use, the
\ check runs out of room: full, never ok.
: crowded ( -- ) lf-term-count @ lf-term-capacity! drop ;
T{ s" ind.bool" case-path staged ok? must crowded fuel checked 0 lf-env-outcome finish
   -> outcome-full }T
T{ s" ind.list" case-path staged ok? must crowded fuel checked 0 lf-env-outcome finish
   -> outcome-full }T
\ Refusals (tests/support/alloc-fail.fs; review rvN1 L2): each allocation
\ the block's check makes, the k-th after the run starts, refused in turn
\ as if its store were full while the others go ahead: the block ends
\ full, never another outcome. Its positivity and its recursor put a
\ field's type in whnf by beta, which allocates, so a failure there that
\ were dropped would show (ind.recursive-through-beta).
create starts most cells allot
create ends most cells allot
\ Record, with the allocations seen when each check starts and ends.
: allocs-counted ( -- )
  af-seen@ record lf-env-limit dup most <
  if tuck starts at ! af-seen@ swap ends at ! else 2drop then ;
: refused-run ( c-addr u k -- )
  >r case-path staged ok? must fuel fresh r> af-arm
  ['] allocs-counted ['] lf-check-no-maker lf-env-run drop lf-env-view ok? must ;
2variable refused-case
: block-slot ( -- d ) final-decl owner ;
\ The allocations of the block's check, from the run without a refusal.
: window ( -- end start )
  refused-case 2@ 0 refused-run af-off block-slot dup ends at @ swap starts at @ finish ;
\ The block's outcome with allocation k refused, and whether k was reached.
: refused ( k -- outcome hit )
  refused-case 2@ rot refused-run block-slot lf-env-outcome af-hit 0<> af-off finish ;
: all-full? ( -- flag )
  true window ?do i 1+ refused swap outcome-full = and and loop ;
s" ind.recursive-through-beta" refused-case 2!
T{ window - 0> all-full? -> true true }T

\ ---------------------------------------------------------------------------
\ 6. After a block. Lean's replay generates IE.B.rec whether or not the
\ file holds it, so a later definition of that name is Lean's
\ alreadyDeclared: rejected here, the name held by the accepted type.
T{ s" after.recursor-left-out-then-def-rec" verdict drop
   -> outcome-rejected lf-diag-already-declared }T
T{ s" after.recursor-then-def-rec" verdict drop
   -> outcome-rejected lf-diag-already-declared }T
T{ s" after.recursor-left-out-then-use-and-def-rec" verdict drop
   -> outcome-rejected lf-diag-already-declared }T
\ A use of it before that definition (declaration 3) is accepted, as
\ Lean accepts it: Lean's kernel holds the recursor it generated, and
\ LeanForth builds the same again from the recipe on IE.B's slot (ADR
\ 0015 decision 12); so is a use in a file that declares IE.B.rec nowhere
\ (ADR 0016 amendment 1), and one without its universe argument is
\ rejected (L1), as Lean's universeArity.
T{ s" after.recursor-left-out-then-use-and-def-rec" 3 decl-verdict -> outcome-ok 0 }T
T{ s" after.recursor-left-out-then-use-rec" verdict drop -> outcome-ok 0 }T
T{ s" after.recursor-left-out-then-use-rec-no-level" verdict drop
   -> outcome-rejected lf-diag-level-count }T
\ A rejected block's type is no constant for a later declaration (Lean's
\ unknownConstant). The type is visible to inference only within the
\ block's own check: the flag is clear after it, and a flag left set
\ (as a fault would leave it) still exposes nothing to a later check.
: rejected-then-use ( -- c-addr u ) s" after.rejected-block-then-use" ;
T{ rejected-then-use verdict drop -> outcome-rejected lf-diag-unknown-constant }T
: visible-after ( -- flag )
  rejected-then-use case-path staged ok? must fuel checked 0 visibles at @ finish ;
T{ visible-after -> false }T
: leaky ( -- ) record true lf-ind-state lf-ind-visible ! ;
: leaked ( -- outcome )
  rejected-then-use case-path staged ok? must fuel ['] leaky checked-by
  final-decl lf-env-outcome finish ;
T{ leaked -> outcome-rejected }T
\ The publisher's re-check, for checks that claim ok wrongly: a block
\ claimed ok with a member made unsafe (its members, part 5), and a
\ definition of IE.B.rec claimed ok after IE.B was accepted without its
\ recursor (its name, part 4): both refused, invalid.
: claim ( d -- outcome )
  lf-env-begin drop outcome-ok lf-env-finish lf-env-hand-over drop ;
: claimed-unsafe ( -- outcome outcome )
  s" ind.bool" case-path staged ok? must
  lf-safety-unsafe 2 lf-input-decl lf-idecl-safety !
  fuel fresh 0 lf-env-begin drop 4 lf-env-span! outcome-ok lf-env-finish
  lf-env-hand-over drop lf-env-view ok? must 0 lf-env-outcome finish ;
T{ claimed-unsafe -> outcome-invalid outcome-invalid }T
\ A check that claims its block skipped (plan task 5.2.7): marked when
\ every member is unsafe; refused when they are safe (part 7), invalid
\ and not marked.
: claim-skip ( safety -- outcome flag )
  s" ind.bool" case-path staged ok? must 4 0 do dup i lf-input-decl lf-idecl-safety ! loop
  drop fuel fresh 0 lf-env-begin drop 4 lf-env-span! true lf-env-skipped!
  outcome-rejected lf-env-finish lf-env-hand-over 2drop
  lf-env-view ok? must 0 lf-env-outcome 3 lf-env-skipped? finish ;
T{ lf-safety-unsafe claim-skip -> outcome-rejected true }T
T{ lf-safety-safe claim-skip -> outcome-invalid false }T
: claimed-rec ( -- outcome outcome )
  s" after.recursor-left-out-then-def-rec" case-path staged ok? must
  fuel fresh ['] record 0 lf-env-step 2drop
  3 claim lf-env-view ok? must 3 lf-env-outcome finish ;
T{ claimed-rec -> outcome-invalid outcome-invalid }T
\ A scheduler waits for the type that holds IE.B.rec (lf-env-ready?).
: ready-around ( -- flag flag )
  s" after.recursor-left-out-then-def-rec" case-path staged ok? must fuel fresh
  3 lf-input-name 3 lf-env-ready? ['] record 0 lf-env-step 2drop
  3 lf-input-name 3 lf-env-ready? lf-env-view ok? must finish ;
T{ ready-around -> false true }T
\ Which types hold a name (lf-env-reserving's class): T.rec by T accepted
\ or not; T.rec_k, the auxiliary recursors of a nested block, by an
\ accepted T only when it is its block's first type and k (from 1, no
\ leading zero) at most the block's auxiliary types (task 5.2.5b: the
\ nested Tree has one), by a T not accepted always; no other name.
\ The type is the file's declaration d (held-at) or its first (held-as).
: held-at ( part-addr part-u c-addr u d -- class )
  >r case-path staged ok? must fuel checked
  r> lf-input-name -rot lf-name-str must lf-env lf-env-length lf-env-reserving nip finish ;
: held-as ( part-addr part-u c-addr u -- class ) 0 held-at ;
T{ s" rec" s" ind.bool" held-as -> outcome-ok }T
T{ s" rec" s" ind.nat" held-as -> outcome-ok }T
T{ s" rec" s" mutual.single-ctor-props" held-as -> outcome-ok }T
T{ s" rec" s" nested.tree" 4 held-at -> outcome-ok }T
T{ s" rec_1" s" nested.tree" 4 held-at -> outcome-ok }T
T{ s" rec_2" s" nested.tree" 4 held-at -> outcome-rejected }T
T{ s" rec_0" s" nested.tree" 4 held-at -> outcome-rejected }T
T{ s" rec_01" s" nested.tree" 4 held-at -> outcome-rejected }T
T{ s" rec_1" s" ind.nat" held-as -> outcome-rejected }T
T{ s" rec_1" s" ind.bool" held-as -> outcome-rejected }T
T{ s" recOn" s" ind.bool" held-as -> outcome-rejected }T
T{ s" rec_x" s" ind.nat" held-as -> outcome-rejected }T
\ Not digits, so no auxiliary recursor of nested.tree: the name is held
\ by no type (letters, a digit then a letter, nothing).
T{ s" rec_x" s" nested.tree" 4 held-at -> outcome-rejected }T
T{ s" rec_1x" s" nested.tree" 4 held-at -> outcome-rejected }T
T{ s" rec_" s" nested.tree" 4 held-at -> outcome-rejected }T
\ A block rejected only by B3 (review rvI21 R2-1; ADR 0015 decision 11):
\ Lean's replay compares after its kernel added the block, so the type's,
\ the constructors' and T.rec's names are taken (a later definition of one
\ is alreadyDeclared) and later uses of them are accepted, as Lean's later
\ declarations meet the kernel's constants; the file's recursor, renamed,
\ is neither taken nor usable. A block the kernel rejects (U1) takes no
\ name.
T{ s" after.b3-renamed-then-def-rec" verdict drop
   -> outcome-rejected lf-diag-already-declared }T
T{ s" after.b3-ctor-then-def-rec" verdict drop
   -> outcome-rejected lf-diag-already-declared }T
T{ s" after.b3-ctor-then-def-type" verdict drop
   -> outcome-rejected lf-diag-already-declared }T
T{ s" after.b3-ctor-then-def-constructor" verdict drop
   -> outcome-rejected lf-diag-already-declared }T
T{ s" after.b3-renamed-then-def-renamed" verdict drop -> outcome-ok 0 }T
T{ s" after.rejected-block-then-def-rec" verdict drop -> outcome-ok 0 }T
T{ s" after.b3-ctor-then-use" verdict drop -> outcome-ok 0 }T
T{ s" after.b3-ctor-then-use-constructor" verdict drop -> outcome-ok 0 }T
T{ s" after.b3-ctor-then-use-rec" verdict drop -> outcome-ok 0 }T
T{ s" after.b3-renamed-then-use-rec" verdict drop -> outcome-ok 0 }T
T{ s" after.b3-renamed-then-use-renamed" verdict drop
   -> outcome-rejected lf-diag-unknown-constant }T
\ Its constructors take the type's universe parameters (Lean's kernel
\ declares them so), not their file records' (B3 field 1).
: ctor-arity ( -- n )
  s" replay-bool.constructor-universe-added" case-path staged ok? must fuel checked
  2 lf-env-params drop nip finish ;
T{ ctor-arity -> 0 }T
\ The generated recursor on several shapes (review rvI21 R4-2): each block
\ with its recursors left out, then def T.useRec.{us} : <Lean's type of
\ T.rec> := @T.rec.{us}, accepted as Lean accepts it: And (fields, large
\ elimination), Or and Exists (Prop only), True (K), an empty Prop, a
\ Unit, Pr (two universes and fields), a predicate with a Type field
\ (Prop only), Eq (indices, K) and a family with an index; and a use at
\ level 1 in a definition and during another block's check, where the
\ motive's universe is no level of the file (R4-1). A type that is a
\ Sort only after whnf leaves no recipe: unknown (task 4.2.2).
T{ s" after.and-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.or-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.exists-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.true-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.empty-prop-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.unit-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.universe-max-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.predicate-any-field-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.eq-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.index-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.many-universes-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.recursor-left-out-then-lookup-in-def" used -> outcome-ok 0 }T
T{ s" after.recursor-left-out-then-lookup-during-block" used -> outcome-unknown lf-diag-iota-pending }T
\ The generated recursor at universes other than its own names (review
\ rvI21 R5-1): renamed, concrete, swapped and applied (eta) uses of Eq's,
\ Exists' and Pr's, whose domains mention the block's universes.
T{ s" after.eq-at-renamed" used -> outcome-ok 0 }T
T{ s" after.eq-at-concrete" used -> outcome-ok 0 }T
T{ s" after.eq-at-applied" used -> outcome-ok 0 }T
T{ s" after.exists-at-renamed" used -> outcome-ok 0 }T
T{ s" after.exists-at-concrete" used -> outcome-ok 0 }T
T{ s" after.exists-at-applied" used -> outcome-ok 0 }T
T{ s" after.universe-max-at-renamed" used -> outcome-ok 0 }T
T{ s" after.universe-max-at-concrete" used -> outcome-ok 0 }T
T{ s" after.universe-max-at-swapped" used -> outcome-ok 0 }T
T{ s" after.universe-max-at-applied" used -> outcome-ok 0 }T
T{ s" after.redex-type-left-out-then-use-rec" used
   -> outcome-unknown lf-diag-generated-recursor }T
\ Recursive blocks (task 5.2.1b): the generated recursor with its
\ induction hypotheses, found again on the constructors' instances, at
\ its own universes and at renamed, concrete and applied ones.
T{ s" after.nat-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.list-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.reflexive-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.binary-tree-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.list-at-renamed" used -> outcome-ok 0 }T
T{ s" after.list-at-concrete" used -> outcome-ok 0 }T
T{ s" after.list-at-applied" used -> outcome-ok 0 }T
T{ s" after.list-sort-max-at-concrete" used -> outcome-ok 0 }T
T{ s" after.reflexive-parameter-at-renamed" used -> outcome-ok 0 }T
\ The list's recursor built again while a block with a parameter checks
\ its constructor: that block's parameter domains survive the rebuild.
\ Since task 5.2.3 positivity puts every field in whnf, as Lean does, and
\ this field's whnf needs iota on a recursor no slot holds: unknown (81)
\ until that follow-up of task 5.2.1b, as is the row before.
T{ s" after.list-left-out-then-lookup-during-param-block" used -> outcome-unknown lf-diag-iota-pending }T
\ A rebuild gives back what the interrupted block's check had in its three
\ slabs (domains, type records, constructors' records): their bytes after
\ save, clobber and restore are the bytes before. (The row above stops
\ before the check goes on with its constructors, so it cannot see this.)
: bytes-sum ( addr u -- n ) 0 -rot bounds ?do i c@ + loop ;
: slab-sum ( xt -- n ) execute dup slab-base swap slab-bytes bytes-sum ;
: slab-clobbered ( xt -- ) execute dup slab-base swap slab-bytes 255 fill ;
\ True when the clobbering changed the slab and the restore undid it.
: slab-back? ( xt -- flag )
  dup slab-sum >r lf-genrec-save ok? must dup slab-clobbered
  dup slab-sum r@ <> lf-genrec-restore swap slab-sum r> = and ;
: given-back ( xt -- flag )
  s" ind.nat" case-path staged ok? must fuel checked slab-back? finish ;
T{ ' lf-ind-domains given-back -> true }T
T{ ' lf-ind-type-cells given-back -> true }T
T{ ' lf-ind-ctor-cells given-back -> true }T
\ Mutual blocks (task 5.2.5a): the generated recursor of the first type and
\ of a later one, with indices, and at concrete and renamed universes.
T{ s" after.mutual-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.even-odd-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.even-odd-left-out-then-use-second-rec" used -> outcome-ok 0 }T
T{ s" after.indexed-data-left-out-then-use-second-rec" used -> outcome-ok 0 }T
T{ s" after.three-types-at-concrete" used -> outcome-ok 0 }T
T{ s" after.three-types-at-renamed" used -> outcome-ok 0 }T
\ Review rvN1 (M1): the generated recursors of a W type (at its own,
\ swapped and concrete universes), of indexed recursive blocks and of
\ reflexive ones. A recursor whose type applies a field with an annotated
\ binder (optParam Nat 0 against Nat) stays unknown until inference
\ unfolds (task 4.2.2's whnf in inference); one whose field's type is a
\ function type only after whnf is decided since that whnf is on main.
T{ s" after.w-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.w-at-swapped" used -> outcome-ok 0 }T
T{ s" after.w-at-concrete" used -> outcome-ok 0 }T
T{ s" after.acc-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.acc-at-concrete" used -> outcome-ok 0 }T
T{ s" after.vec-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.reflexive-indexed-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.indexed-mixed-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.reflexive-indexed-dependent-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.annotated-binders-left-out-then-use-rec" used -> outcome-ok 0 }T
T{ s" after.redex-parameter-left-out-then-use-rec" used -> outcome-ok 0 }T
\ The marks on the slots: the type and constructors, not the recursor.
: added? ( d -- flag ) lf-env lf-env-slot lf-slot-added? ;
: marks ( -- f0 f1 f2 f3 )
  s" after.b3-renamed-then-def-rec" case-path staged ok? must fuel checked
  0 added? 1 added? 2 added? 3 added? finish ;
T{ marks -> true true true false }T
\ The publisher's re-check: def IE.B claimed ok after the B3-rejected
\ block (its name, part 4) is refused.
: claimed-type ( -- outcome outcome )
  s" after.b3-ctor-then-def-type" case-path staged ok? must
  fuel fresh ['] record 0 lf-env-step 2drop
  3 claim lf-env-view ok? must 3 lf-env-outcome finish ;
T{ claimed-type -> outcome-invalid outcome-invalid }T
\ An accepted block's warnings stay on its slots (review rvI21 M2).
: slot-warned ( c-addr u -- bits outcome )
  case-path staged ok? must fuel checked final-decl lf-env-warnings finish ;
T{ s" replay-bool.recursor-left-out" slot-warned -> lf-warn-no-recursor outcome-ok }T
T{ s" ind.bool" slot-warned -> 0 outcome-ok }T

\ 7. Axioms, opaque declarations and quotients (plan tasks 5.3.1, 4.2.6,
\ 5.2.4; rows of the inductive table): Lean's verdicts, and the axiom bits
\ of the case's last declaration (8: an axiom outside the allowlist, so
\ NOT PROVED; the file's own, or propext with another statement).
: bits-of ( c-addr u -- outcome bits )
  case-path staged ok? must fuel checked final-decl dup lf-env-outcome
  swap lf-env-axioms drop finish ;
T{ s" postulate.declared-and-used" bits-of -> outcome-ok 8 }T
T{ s" postulate.propext-altered" bits-of -> outcome-ok 8 }T
T{ s" opaque.accepted" bits-of -> outcome-ok 0 }T
T{ s" opaque.wrong-value" used -> outcome-rejected lf-diag-value-apart }T
\ An opaque declaration never unfolds (Lean's is_delta); its twin, a
\ definition, does.
T{ s" opaque.never-unfolds" used -> outcome-rejected lf-diag-value-apart }T
T{ s" opaque.unfolds-as-definition" used -> outcome-ok 0 }T
\ Quot.lift on Quot.mk reduces (quot_reduce_rec), on a variable it stays.
T{ s" quot.lift-on-mk" used -> outcome-ok 0 }T
T{ s" quot.lift-on-mk-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" quot.lift-stuck-on-variable" used -> outcome-rejected lf-diag-value-apart }T
\ An argument after the major premise goes to the reduct; Quot.lift with
\ five arguments has no rule (eta decides); Quot.ind on Quot.mk; a user's
\ Quot.lift and Quot.mk, with no quotient, are never reduced (review rvAX).
T{ s" quot.lift-extra-argument" used -> outcome-ok 0 }T
T{ s" quot.lift-extra-argument-wrong" used -> outcome-rejected lf-diag-value-apart }T
T{ s" quot.lift-unapplied-eta" used s" quot.ind-on-mk" used -> outcome-ok 0 outcome-ok 0 }T
T{ s" after.user-quot-lift-not-reduced" used -> outcome-rejected lf-diag-value-apart }T
\ add_quot: Eq with Lean's shape, or rejected (check_eq_type, 95).
T{ s" quotinit.with-eq" used -> outcome-ok 0 }T
T{ s" quotinit.eq-wrong-shape" used -> outcome-rejected lf-diag-quot-eq }T
\ A quotient record with another type or other universe parameters than
\ Lean's own is accepted with a warning, as Lean's replay ignores it, and
\ Lean's types are used: IE.mkUse := Quot.mk r a is accepted (ADR 0015 Q1).
: named ( c-addr u -- d )
  lf-input-count 0 ?do
    i lf-input-name 2 pick 2 pick lf-stmt-name? if 2drop i unloop exit then
  loop 2drop -1 ;
: warned-at ( c-addr u name-addr name-u -- bits outcome )
  2swap case-path staged ok? must fuel checked named lf-env-warnings finish ;
: quot-forged ( -- c-addr u ) s" replay-quot.mk-given-quot-type" ;
: mk-warned ( -- bits outcome ) quot-forged s" Quot.mk" warned-at ;
: quot-warned ( -- bits outcome ) quot-forged s" Quot" warned-at ;
: lift-warned ( -- bits outcome )
  s" replay-quot.lift-universe-dropped" s" Quot.lift" warned-at ;
T{ mk-warned quot-warned -> lf-warn-quot-record outcome-ok 0 outcome-ok }T
T{ lift-warned -> lf-warn-quot-record outcome-ok }T
T{ quot-forged used -> outcome-ok 0 }T
\ Fields add_quot never reads (review rvAX M1, L1) only warn too: Quot.lift
\ with universe parameters u, u (no L3 step, and none in the publisher's
\ re-check); Quot.mk whose type is a loose variable (V1) or under mdata
\ (U2), never given to the matcher.
T{ s" replay-quot.lift-params-repeated" s" Quot.lift" warned-at
  -> lf-warn-quot-record outcome-ok }T
T{ s" replay-quot.lift-params-repeated" used -> outcome-ok 0 }T
T{ s" replay-quot.mk-loose-bvar" s" Quot.mk" warned-at -> lf-warn-quot-record outcome-ok }T
T{ s" replay-quot.mk-mdata-type" s" Quot.mk" warned-at -> lf-warn-quot-record outcome-ok }T
T{ s" replay-quot.mk-loose-bvar" used s" replay-quot.mk-mdata-type" used
  -> outcome-ok 0 outcome-ok 0 }T
\ The refused audit's diagnostic is put back: that Quot.mk record (4) is
\ accepted with none left; renamed after the feed (IE.mkUse's name, 7), it
\ is rejected as no constant of Lean's quotient (96), not for its type.
T{ s" replay-quot.mk-loose-bvar" 4 decl-verdict -> outcome-ok 0 }T
: mk-renamed ( -- outcome code )
  s" replay-quot.mk-loose-bvar" case-path staged ok? must
  7 lf-input-name 4 lf-input-decl lf-idecl-name ! fuel checked 4 result drop finish ;
T{ mk-renamed -> outcome-rejected lf-diag-quot-type }T
\ Lean's quotient names (review rvAX): add_quot's check_name on all four
\ (quot.cpp 53-56). A user's Quot.mk (3) before the quotient leaves every
\ quotient record rejected (4-7), so Quot.lift on that Quot.mk is an
\ unknown constant (Lean's unknownConstant), never reduced by name; so
\ with Quot.ind taken. One of the four after the quotient is already
\ declared, its record first or not. A second record of a name, which
\ Lean accepts (add_quot changes nothing), and a use of Quot.mk after a
\ refused declaration of it are unknown (77; a follow-up of task 5.2.4).
: on-user-mk ( -- c-addr u ) s" after.quot-mk-declared-then-lift-on-it" ;
T{ on-user-mk used -> outcome-rejected lf-diag-unknown-constant }T
T{ on-user-mk 3 decl-verdict on-user-mk 4 decl-verdict
  -> outcome-ok 0 outcome-rejected lf-diag-already-declared }T
T{ on-user-mk 5 decl-verdict on-user-mk 6 decl-verdict
  -> outcome-rejected lf-diag-already-declared outcome-rejected lf-diag-already-declared }T
T{ s" quotinit.name-taken" 4 decl-verdict -> outcome-rejected lf-diag-already-declared }T
T{ s" after.quot-then-mk-declared" used -> outcome-rejected lf-diag-already-declared }T
T{ s" after.quot-then-lift-declared" used -> outcome-rejected lf-diag-already-declared }T
T{ s" quotinit.twice" 6 decl-verdict s" quotinit.twice" 7 decl-verdict
  -> outcome-ok 0 outcome-unknown lf-diag-generated-recursor }T
T{ s" after.quot-then-mk-declared-then-used" used
  -> outcome-unknown lf-diag-generated-recursor }T
\ A scheduler waits for the quotient record that holds Quot.mk (3, before
\ the user's Quot.mk, 4).
: quot-ready ( -- flag flag )
  s" after.quot-then-mk-declared" case-path staged ok? must fuel fresh
  4 lf-input-name 4 lf-env-ready? ['] record 0 lf-env-step 2drop ['] record 3 lf-env-step 2drop
  4 lf-input-name 4 lf-env-ready? lf-env-view ok? must finish ;
T{ quot-ready -> false true }T
\ The publisher's re-check: the user's Quot.mk (4), an axiom, claimed ok
\ with its own bit after the quotient record Quot was accepted, is
\ refused (its name, part 4).
: claim-axiom ( d -- outcome )
  lf-env-begin drop lf-axiom-unlisted lf-env-axiom! outcome-ok lf-env-finish
  lf-env-hand-over drop ;
: claimed-mk ( -- outcome outcome )
  s" after.quot-then-mk-declared" case-path staged ok? must
  fuel fresh ['] record 0 lf-env-step 2drop ['] record 3 lf-env-step 2drop
  4 claim-axiom lf-env-view ok? must 4 lf-env-outcome finish ;
T{ claimed-mk -> outcome-invalid outcome-invalid }T
\ propext with Lean's statement about an Iff that is not Lean's: NOT PROVED.
T{ s" postulate.propext-forged-iff" bits-of -> outcome-ok 8 }T
\ So with an Iff of one parameter, in a block with another type, or
\ accepted with a warning (isRec forged, which replay ignores); and
\ Quot.sound about a Quot and Quot.mk that are axioms, not the quotient's
\ (review rvAX test gaps).
T{ s" postulate.propext-iff-one-param" bits-of -> outcome-ok 8 }T
T{ s" postulate.propext-iff-mutual" bits-of -> outcome-ok 8 }T
T{ s" replay-iff.flagged-then-propext" bits-of -> outcome-ok 8 }T
T{ s" postulate.sound-own-quot-names" bits-of -> outcome-ok 8 }T
T{ s" postulate.propext-own-iff" bits-of -> outcome-ok 1 }T
\ The axioms a declaration rests on, in file order (lf-env-axiom-deps, each
\ slot's set worked out once and kept; review rvAX L5), asked for the last
\ declaration first: IE.Secret (0), IE.secret (1, its type IE.Secret),
\ IE.usesSecret (2); each slot number given is one decimal digit here.
variable seen-axioms
: seen ( d -- ) seen-axioms @ 10 * + 1+ seen-axioms ! ;
: rests-on ( d -- n outcome ) 0 seen-axioms ! ['] seen lf-env-axiom-deps seen-axioms @ swap ;
: secret-axioms ( -- n n n outcome )
  s" postulate.declared-and-used" case-path staged ok? must fuel checked
  2 rests-on drop 1 rests-on drop 0 rests-on finish ;
T{ secret-axioms -> 12 12 1 outcome-ok }T

\ 8. The statement matcher (core/statement-match.fs) and the allowlist
\ (core/axiom-allowlist.fs) on Lean's own export of propext,
\ Classical.choice, Quot.sound and the quotient constants: each listed
\ axiom is its entry, with its bit; each quotient constant is Lean's own
\ (quot.fs's entries); another entry, or an altered text, differs.
s" tests/reference/inductive/axioms.ndjson" staged ok? must
: decl-index ( c-addr u -- d )
  lf-input-count 0 ?do
    i lf-input-name 2 pick 2 pick lf-stmt-name? if 2drop i unloop exit then
  loop 2drop -1 ;
: decl-named ( c-addr u -- decl ) decl-index lf-input-decl ;
\ Each listed axiom's set is its own bit: the constants its statement
\ names (Iff, Eq, Nonempty, Quot, Quot.mk) are Lean's own. Outside a
\ check nothing can be looked up, so every axiom is unlisted there.
: bit-of ( c-addr u -- bit outcome ) decl-named 100000 lf-stmt-fuel ! lf-axiom-bit ;
T{ s" propext" bit-of -> 8 outcome-ok }T
fuel checked
: set-of ( c-addr u -- bits outcome ) decl-index lf-env-axioms ;
T{ s" propext" set-of s" Classical.choice" set-of s" Quot.sound" set-of
  -> 1 outcome-ok 2 outcome-ok 4 outcome-ok }T
: is? ( c-addr u entry -- flag outcome ) >r decl-named r> 100000 lf-stmt-fuel ! lf-stmt-is? ;
T{ s" Quot" lf-quot-type is? s" Quot.mk" lf-quot-mk is? -> true outcome-ok true outcome-ok }T
T{ s" Quot.lift" lf-quot-lift is? s" Quot.ind" lf-quot-ind is? -> true outcome-ok true outcome-ok }T
T{ s" Quot.mk" lf-quot-type is? s" Quot.ind" lf-quot-lift is? -> false outcome-ok false outcome-ok }T
\ A text against a declaration's type, with fuel.
: typed ( c-addr u -- term decl ) decl-named dup lf-idecl-type @ swap ;
: fueled ( c-addr u text-addr text-u fuel -- flag outcome )
  lf-stmt-fuel ! 2>r typed 2r> lf-stmt-match ;
: matches? ( c-addr u text-addr text-u -- flag ) 100000 fueled drop ;
: choice ( -- c-addr u ) s" Classical.choice" ;
T{ choice s" P S u0 P A C Nonempty 1 u0 #0 #1" matches? -> true }T
T{ choice s" P S u0 P A C Nonempty 1 u0 #0 #0" matches? -> false }T     \ a variable
T{ choice s" P S u0 P A C Nonempty 1 u0 #0 #1 #1" matches? -> false }T  \ text left over
T{ choice s" P S u0 P A C Nonempty 1 u0 #0" matches? -> false }T        \ nodes left over
T{ choice s" P S z P A C Nonempty 1 u0 #0 #1" matches? -> false }T      \ a level
T{ choice s" P S s u0 P A C Nonempty 1 u0 #0 #1" matches? -> false }T   \ a level
T{ choice s" P S u0 P A C Inhabited 1 u0 #0 #1" matches? -> false }T    \ a name
T{ choice s" P S u0 P A C Nonempty 0 #0 #1" matches? -> false }T        \ an arity
T{ choice s" P S u0 L A C Nonempty 1 u0 #0 #1" matches? -> false }T     \ a binder
T{ choice s" P S u0 P A C Nonempty 1 u0 #0 #1" 5 fueled -> false outcome-exhausted }T
\ Universe parameters by position: Quot.lift's two swapped differ.
: lift-swapped ( -- c-addr u )
  s" P S u1 P P #0 P #1 S z P S u0 P P #2 #1 P P #3 P #4 P A A #4 #1 #0 A A A C Eq 1 u0 #4 A #3 #2 A #3 #1 P A A C Quot 1 u1 #4 #3 #3" ;
T{ s" Quot.lift" lift-swapped matches? -> false }T
\ Dotted names, part by part from the last.
: mk-name ( -- id ) s" Quot.mk" decl-named lf-idecl-name @ ;
T{ mk-name s" Quot.mk" lf-stmt-name? mk-name s" Quit.mk" lf-stmt-name? -> true false }T
T{ mk-name s" mk" lf-stmt-name? mk-name s" A.Quot.mk" lf-stmt-name? -> false false }T
finish

\ 9. Fuel of axioms and quotient records (review rvAX L2): a quotient
\ record's steps all run on the audit's counter, an axiom's step 7 on
\ inference's, and cli/check-run.fs reads that counter (ck-left). Every
\ other declaration of axioms.ndjson gets the full budget and declaration
\ d budget b; d checked with the fuel it used is ok, with one unit less
\ exhausted: propext (6), Classical.choice (10), Quot (11) to Quot.ind
\ (14), Quot.sound (15).
variable at-d  variable at-budget  variable at-left  variable at-step
: at-kept ( -- ) at-d @ ck-left at-left ! lf-check-step@ at-step ! ;
: at-check ( -- )
  lf-env-limit at-d @ = dup if at-budget @ else fuel then lf-check-budget
  record if at-kept then ;
: at-run ( d b -- outcome left )
  at-budget ! at-d ! s" tests/reference/inductive/axioms.ndjson" staged ok? must
  fuel ['] at-check checked-by at-d @ lf-env-outcome at-left @ finish ;
: used-by ( d -- u ) fuel at-run nip fuel swap - ;
: used-exactly? ( d -- flag )
  dup used-by 2dup at-run drop ok? >r 1- at-run drop outcome-exhausted = r> and ;
T{ 6 used-exactly? 10 used-exactly? 15 used-exactly? -> true true true }T
\ One unit short, an axiom runs out in step 7, its statement's comparison,
\ which is charged too.
: short-step ( d -- step ) dup used-by 1- at-run 2drop at-step @ ;
T{ 6 short-step 10 short-step 15 short-step -> 7 7 7 }T
T{ 11 used-exactly? 12 used-exactly? 13 used-exactly? 14 used-exactly?
  -> true true true true }T

cases-done
bye
