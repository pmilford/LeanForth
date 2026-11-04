\ The check of inductive blocks (plan task 5.2.1a; ADR 0015;
\ src/kernel/check-block.fs, inductive-block.fs, inductive-recursor.fs,
\ level-geq.fs) end to end: staged and fed exports, checked by
\ check-declaration, published by the checked environment.
\ 1. Cases of the inductive table (tests/core/check-block-cases/, each the
\    export tests/reference/inductive-expected.lean prints for its row;
\    tests/core/inductive-table.py checks they are still Lean's): every
\    outcome, each rejection with its rule's diagnostic and step, Lean's
\    replay of the Bool block mutated (B3) and its ignored fields (B4).
\ 2. tests/reference/inductive/blocks.ndjson: a block's members published
\    together (every slot final, one outcome, handles, no axioms).
\ 3. That export tampered after the feed, one field at a time (ADR 0015
\    §13, test plan 3): recursors, rules and constructors rejected with
\    the field named; the type's ignored fields accepted with a warning; a
\    malformed block invalid; unsafe members and unsupported forms
\    unsupported; a loose variable invalid.
\ 4. Fuel: every budget gives ok or exhausted, ok from the least on.
\ 5. Room: a term store with no room left gives full, never ok.
\ 6. After a block (review rvI21 B2, M1): Lean's generated recursor
\    T.rec held when the file leaves it out; the type visible only within
\    its own check; the publisher's re-check of members and of T.rec.
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/import/feed.fs
require ../../src/kernel/check-declaration.fs

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

\ Unknown, unsupported and invalid.
T{ s" params.constructor-binder-defeq" verdict nip -> outcome-unknown 9 }T
T{ s" ind.nat" verdict -> outcome-unsupported lf-diag-block-scope 1 }T
T{ s" mutual.single-ctor-props" verdict -> outcome-unsupported lf-diag-block-scope 1 }T
\ An empty block: the importer stages it as one declaration (ADR 0016
\ amendment 1), which the check rejects at step 4 as Lean's kernel does
\ (emptyBlock).
T{ s" names.empty-block" verdict -> outcome-rejected lf-diag-empty-block 4 }T
\ Two variables of a unit-like structure: Lean's is_def_eq_unit_like
\ equates them, so D3/D5 must not call P x and P y apart (P4).
T{ s" unit.punit-variables" verdict nip -> outcome-unknown 8 }T

\ ---------------------------------------------------------------------------
\ 2. blocks.ndjson: N, Nat, the mutual Even/Odd, List and Tree, Point
\ unsupported (recursive, mutual, nested, or using Nat); Both, Same and
\ Either accepted, every member's slot final and accepted, with a handle
\ and no axioms.
: blocks ( -- c-addr u ) s" tests/reference/inductive/blocks.ndjson" ;
: member-ok? ( d -- flag )
  dup lf-env-outcome ok? over lf-env-handle ok? nip nip and
  swap lf-env-axioms ok? swap 0= and and ;
: all-ok? ( from to -- flag ) true -rot swap ?do i member-ok? and loop ;
: all-unsupported? ( from to -- flag )
  true -rot swap ?do i lf-env-outcome outcome-unsupported = and loop ;
T{ blocks staged fuel checked -> outcome-ok }T
T{ 0 4 all-unsupported? 4 14 all-ok? 14 37 all-unsupported? -> true true true }T
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
\ The shape (B0): a constructor naming another type is invalid.
: induct ( -- ) 7 lf-input-name 5 lf-ict-induct cell! ;
T{ ' induct 4 block-verdict drop -> outcome-invalid lf-diag-block-shape }T
\ The audit: an unsafe member, a projection in a rule (U2), a loose
\ variable (V1).
: unsafe ( -- ) lf-safety-unsafe 5 lf-input-decl lf-idecl-safety ! ;
T{ ' unsafe 4 block-verdict drop -> outcome-unsupported lf-diag-unsupported-kind }T
: projected ( -- ) 36 lf-input-decl lf-idecl-value @ 6 0 rhs ! ;
T{ ' projected 4 block-verdict drop -> outcome-unsupported lf-diag-unsupported-form }T
: a-variable ( -- node ) 0 begin dup lf-term-tag@ lf-tag-bvar <> while 1+ repeat ;
: loose ( -- ) a-variable 6 0 rhs ! ;
T{ ' loose 4 block-verdict drop -> outcome-invalid lf-diag-out-of-scope }T

\ ---------------------------------------------------------------------------
\ 4. Fuel: every budget 2^k - 1 gives ok or exhausted; the least budget
\ that gives ok is found by bisection, and one unit less is exhausted.
: bool-at ( budget -- outcome )
  s" ind.bool" case-path staged ok? must checked 0 lf-env-outcome finish ;
: ok-or-exhausted? ( outcome -- flag ) dup ok? swap outcome-exhausted = or ;
: doubling? ( -- flag ) true 21 0 do 1 i lshift 1- bool-at ok-or-exhausted? and loop ;
: middle ( lo hi -- lo hi mid ) 2dup + 2/ ;
: least-ok ( -- budget )
  0 1 20 lshift begin 2dup - -1 < while
    middle dup bool-at ok? if nip else rot drop swap then
  repeat nip ;
T{ doubling? -> true }T
T{ least-ok dup 1- bool-at swap bool-at -> outcome-exhausted outcome-ok }T

\ 5. Room: with the term store's capacity cut to the records in use, the
\ check runs out of room: full, never ok.
: crowded ( -- ) lf-term-count @ lf-term-capacity! drop ;
T{ s" ind.bool" case-path staged ok? must crowded fuel checked 0 lf-env-outcome finish
   -> outcome-full }T

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
: decl-verdict ( c-addr u d -- outcome code )
  >r case-path staged ok? must fuel checked r> result drop finish ;
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
\ or not; T.rec_<digits>, the auxiliary recursors of a nested block, only
\ by a T not accepted (no accepted block is nested yet); no other name.
: held-as ( part-addr part-u c-addr u -- class )
  case-path staged ok? must fuel checked
  0 lf-input-name -rot lf-name-str must lf-env lf-env-length lf-env-reserving nip finish ;
T{ s" rec" s" ind.bool" held-as -> outcome-ok }T
T{ s" rec" s" ind.nat" held-as -> outcome-unsupported }T
T{ s" rec_1" s" ind.nat" held-as -> outcome-unsupported }T
T{ s" rec_1" s" ind.bool" held-as -> outcome-rejected }T
T{ s" recOn" s" ind.bool" held-as -> outcome-rejected }T
T{ s" rec_x" s" ind.nat" held-as -> outcome-rejected }T
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
: used ( c-addr u -- outcome code ) verdict drop ;
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
T{ s" after.recursor-left-out-then-lookup-during-block" used -> outcome-ok 0 }T
T{ s" after.redex-type-left-out-then-use-rec" used
   -> outcome-unknown lf-diag-generated-recursor }T
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

cases-done
bye
