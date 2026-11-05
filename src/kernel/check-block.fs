\ check-block (plan tasks 5.2.1a, 5.2.1b and 5.2.5a; ADR 0015 §3, §4):
\ the check of an inductive block that check-declaration runs when the
\ snapshot's declaration is a block's first member. It runs Lean 4.35.0's
\ add_inductive (inductive.cpp 1235-1350, commit eb6cafb7) for a block of
\ one type or several (mutual), recursive or not, step by step in Lean's
\ order, then compares what it generated with what the file holds as
\ Lean's replay does (Lean/Replay.lean 102-164), and ends with one
\ outcome for every member:
\    1 the audit (inductive-block.fs): B0 shape (invalid), unsafe members
\      and U2 forms (unsupported), V1 (invalid), the scope (unsupported:
\      nested, task 5.2.5b);
\    2 T0 the reserved prefix _nested (1241, 1244);
\    3 C1 uniform occurrences (check_uniform_ind_occs, 134-164);
\    4 T1 at least numParams binders (get_params, 1138-1146);
\    5 T5 universe parameters distinct (check_duplicated_univ_params, 869);
\    then steps 6 to 8 for each type in order (check_inductive_types
\    254-299):
\    6 N2 the type's name and T.rec unused (258-259);
\    7 the type's type inferred (tc().check, 261);
\    8 its telescope, after whnf at each step (263-283): parameters and
\      indices, and a Sort at the end (ensure_sort, 287: T2), whose level
\      is the result level; where Lean's whnf might unfold a constant,
\      unknown (K1, lf-diag-needs-unfolding); a later type's parameters
\      the first's (T3) and its level equivalent (T4);
\    9 each constructor (check_constructors 456-497): C4 duplicate name
\      within its type, N2, its type inferred (the block's types visible
\      to inference, as Lean declares them first, 308-375), then its raw
\      telescope: C2 each parameter's domain against the first type's
\      (is_def_eq, D1-D5 reject, else unknown), U1 each field's universe
\      (Lean's is_geq, level-geq.fs, or a result level that normalizes to
\      zero), then its positivity (P1, P2; check_positivity 436-452), C3
\      the result a valid application of its own type (is_valid_ind_app
\      381-409); numFields its binders after the parameters; then a name
\      of another type's constructor declared already (499-519);
\   10 the elimination level (elim_only_at_universe_zero 522-577, E0-E4;
\      its universe u, or u_1, u_2, ... when taken, 579-592) and K
\      (init_K_target 594-616);
\   11 N2 for each T.rec against the names the block declared (813);
\   12 the recursors and their rules (inductive-recursor.fs, G1, G2);
\   13 B3: each constructor and each exported recursor equal to the one
\      generated, by Lean's ==: every field, universe parameter names
\      included, terms structurally (mixed-compare.fs: binder names and
\      annotations are not stored, as Lean's == ignores them); a recursor
\      Lean does not generate is rejected;
\   14 B4: fields Lean's replay ignores -- the type's numIndices, isRec,
\      isReflexive, numNested, and a recursor missing from the block --
\      never used, never failing; a difference sets a warning bit
\      (lf-block-warnings, owner answer Q2).
\ The first step that does not succeed decides the outcome; every member
\ gets it, through the publisher's block publication (env-publish.fs:
\ the candidate's span). G4 (check_recursors 829-866, a defensive check
\ of Lean's own generation) is not run: each rule's reduct is minor_j b
\ v, v the induction hypotheses fun xs => T.rec As motive minors ks
\ (u xs) of the recursive fields u, whose types are the minor premise's
\ hypotheses by construction, so its type is minor_j's result type,
\ motive js (c_j As b), the type the recursor gives the left side; the
\ generated recursor is compared with Lean's own (B3).
\ Where Lean's add_inductive puts a term in whnf (steps 8, 9's
\ positivity, the recursor's recursive fields), LeanForth uses Lean's
\ whnf (whnf.fs, plan task 4.2.2c, with iota from iota.fs); where that
\ cannot follow Lean yet it fails unknown, and so does the block.
\ [kernel] code: experimental, not through the review gate; not
\ independently audited.
\ State: one record, lf-blk-state (the T.rec name, the constructor and
\ binder being checked, the fields of the elimination test), and the
\ slab lf-blk-positions, members of the checker context, beside the
\ block's record lf-ind-state.

require ../lib/lib.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/levels.fs
require ../core/name-equal.fs
require ../core/names.fs
require ../core/terms.fs
require ./environment.fs
require ./env-signature.fs
require ./generated-recursor.fs
require ./inductive-block.fs
require ./inductive-recursor.fs
require ./infer-proj.fs
require ./iota.fs
require ./level-geq.fs
require ./level-make.fs
require ./mixed-compare.fs
require ./mixed-head.fs
require ./mixed-infer.fs

begin-structure /lf-blkrec
  field: lf-blkrec-type      \ the type being checked, or whose recursor is compared
  field: lf-blkrec-ctor      \ the constructor being checked
  field: lf-blkrec-field     \ its binder whose positivity is checked
  field: lf-blkrec-arity     \ the arguments of the application being tested
  field: lf-blkrec-checks    \ fields whose type is no proposition (E3)
end-structure
/lf-blkrec context-record: lf-blk-state
\ Their binders' positions, as many as there are (plan task 6.2.0).
1 cells context-slab: lf-blk-positions


: lf-blk-site ( -- site ) c" check-block lf-block-check" ;
: lf-blk-type@ ( -- d ) lf-blk-state lf-blkrec-type @ ;
: lf-blk-type! ( d -- ) lf-blk-state lf-blkrec-type ! ;
: lf-blk-rec-id ( d -- name ) lf-ind-ty lf-ty-rec-name @ ;
: lf-blk-ctor@ ( -- j ) lf-blk-state lf-blkrec-ctor @ ;
: lf-blk-level ( -- level ) lf-ind-state lf-ind-level @ ;
\ The block's warnings after its check, and the step it reached (1-14 as
\ above; 15 when every step succeeded).
: lf-block-warnings ( -- bits ) lf-ind-state lf-ind-warned @ ;
: lf-block-step@ ( -- step ) lf-ind-state lf-ind-step-reached @ ;
: lf-blk-reject ( n1 n2 code -- outcome ) lf-blk-site swap lf-diag-note outcome-rejected ;
\ B3's rejections replace what the structural comparison recorded on the
\ way (a difference is undecided there, and decisive here).
: lf-blk-replace ( n1 n2 code -- outcome ) lf-blk-site swap lf-diag! outcome-rejected ;
\ Run xt ( -- outcome ) only when the outcome so far is ok.
: lf-blk-then ( outcome xt -- outcome ) over ok? if nip execute else drop then ;

\ Inference jobs in environment mode on the block's fuel (mixed-infer.fs).
: lf-blk-job ( -- ) lf-ind-fuel @ lf-minfer-start-env ;
: lf-blk-refuel ( outcome -- outcome ) lf-minfer-fuel @ lf-ind-fuel ! ;
: lf-blk-infer ( root -- outcome ) lf-blk-job lf-minfer-walk nip lf-blk-refuel ;
: lf-blk-push ( domain -- outcome ) lf-minfer-push ;

\ While the constructors are checked, the types are constants inference
\ finds (Lean's declare_inductive_types), through env-signature's hook:
\ only within the block's own check (the flag, cleared at its end, and,
\ in depth, the declaration checked being the block's first member;
\ review rvI21 M1).
: lf-blk-visible? ( -- flag ) lf-ind-state lf-ind-visible @ ;
: lf-blk-own? ( -- flag ) lf-blk-visible? lf-env-limit lf-ind-first@ = and ;
: lf-blk-local ( name -- decl true | false )
  lf-blk-own? 0= if drop false exit then
  lf-ind-which-name dup 0< if drop false else lf-ind-type-at true then ;
' lf-blk-local is lf-envsig-local

\ ---------------------------------------------------------------------------
\ Step 5, T5: the universe parameters distinct.
: lf-blk-t5 ( -- outcome )
  lf-ind-lparams lf-params-distinct? if outcome-ok exit then
  lf-ind-first@ 0 lf-diag-duplicate-param lf-blk-reject ;
\ Steps 6 to 8 run for each type d in order, as check_inductive_types
\ does (254-299). Step 6, N2 on the type's name and on T.rec (K5 on
\ undecided ones), as the environment's lookup decides it below the block.
: lf-blk-fresh ( name -- outcome ) lf-env-limit lf-env-fresh ;
: lf-blk-rec-name! ( d -- outcome )
  dup lf-ind-tname s" rec" lf-name-str 0= if drop outcome-full exit then
  swap lf-ind-ty lf-ty-rec-name ! outcome-ok ;
: lf-blk-names ( d -- outcome )
  dup lf-ind-tname lf-blk-fresh ok-then? 0= if exit then
  dup lf-blk-rec-name! ok-then? 0= if exit then lf-blk-rec-id lf-blk-fresh ;
\ Step 7: the type's type.
: lf-blk-type ( d -- outcome ) lf-ind-type-at lf-idecl-type @ lf-blk-infer ;

\ ---------------------------------------------------------------------------
\ Lean's whnf (whnf.fs, with delta, and iota from iota.fs) of a term read
\ under binders the check did not open, on the step's inference job:
\ where it cannot follow Lean yet it fails (unknown: K7, a recursor
\ reduction not ported, K5), never a guess.
: lf-blk-whnf ( node -- node' outcome ) lf-minfer-whnf-job ;
\ The recursor builder's whnf, the same (inductive-recursor.fs).
' lf-whnf-on is lf-rcr-reduce

\ Step 8: the telescope. Each node is put in whnf; a Pi's domain is
\ binder i's; anything else ends it, and must be a Sort (else Lean's
\ typeExpected, rule T2).
: lf-blk-not-sort ( node -- outcome ) 0 lf-diag-block-not-sort lf-blk-reject ;
: lf-blk-sorted ( node -- outcome )
  lf-term-first@ lf-ind-state lf-ind-level ! outcome-ok ;
: lf-blk-end ( node -- outcome )
  dup lf-mhead-kind case
    lf-head-sort of lf-blk-sorted endof
    lf-head-none of drop outcome-invalid endof  >r lf-blk-not-sort r> endcase ;
\ The indices: the binders after the parameters, from domain p on. T1
\ (step 4) leaves at least numParams; fewer, were T1 bypassed, is invalid
\ (review rvI21 L2).
: lf-blk-indices! ( n d -- ) lf-ind-ty lf-ty-indices ! ;
: lf-blk-count ( outcome i -- outcome )
  dup lf-ind-state lf-ind-domains-used ! lf-ind-nparams dup 0 lf-ind-ty lf-ty-domain !
  - dup 0< if 2drop outcome-invalid exit then 0 lf-blk-indices! ;
: lf-blk-pi? ( node -- flag ) lf-mhead-kind lf-head-pi = ;
\ Room for binder i's domain; none (the heap refuses) is full.
: lf-blk-room? ( i -- flag ) 1+ lf-ind-domains slab-hold ok? ;
\ A Pi of the telescope at binder i: its domain recorded, then its body.
: lf-blk-bind ( pi i -- body i+1 )
  2dup swap lf-term-first@ swap lf-ind-domain ! 1+ swap lf-term-second@ swap ;
: lf-blk-tele ( node i -- outcome )
  begin swap lf-blk-whnf ok-then? 0= if nip exit then dup lf-blk-pi? while
    over lf-blk-room? 0= if 2drop outcome-full exit then swap lf-blk-bind
  repeat lf-blk-end swap lf-blk-count ;
\ The first type's telescope gives the parameters and its indices.
: lf-blk-first-telescope ( -- outcome )
  lf-blk-job lf-ind-type lf-idecl-type @ 0 lf-blk-tele lf-blk-refuel ;

\ Another type d of a mutual block (task 5.2.5; 266-296): its first
\ numParams binders, after whnf, each a Pi whose domain the first type's
\ parameter's is (is_def_eq: else "parameters of all inductive datatypes
\ must match", T3, or unknown) and then bound; fewer such binders is
\ "number of parameters mismatch" (T3); the binders after them its
\ indices, recorded after the domains so far; the end a Sort (T2, as for
\ the first type), whose level is Lean's is_equivalent of the first's
\ (else "mutually inductive types must live in the same universe", T4).
: lf-blk-param-dom ( i -- node ) lf-ind-domain @ lf-rcr-consume ;
: lf-blk-param-as ( node i code -- outcome )
  >r 2dup swap lf-term-first@ swap lf-blk-param-dom lf-minfer-agree lf-blk-site r>
  lf-minfer-verdict dup ok? 0= if nip nip exit then
  drop nip lf-blk-param-dom lf-blk-push ;
: lf-blk-used ( -- addr ) lf-ind-state lf-ind-domains-used ;
: lf-blk-index! ( node -- outcome )
  lf-blk-used @ dup lf-blk-room? 0= if 2drop outcome-full exit then
  swap lf-term-first@ swap lf-ind-domain ! 1 lf-blk-used +! outcome-ok ;
: lf-blk-dbinder ( node i -- outcome )
  dup lf-ind-nparams < if lf-diag-mutual-params lf-blk-param-as exit then
  drop lf-blk-index! ;
: lf-blk-member-d ( -- k ) lf-blk-type@ ;
: lf-blk-few-params ( node i -- level outcome )
  nip lf-blk-member-d swap lf-diag-param-count lf-blk-reject no-result ;
: lf-blk-dsort ( node -- level outcome )
  dup lf-mhead-kind lf-head-sort = if lf-term-first@ outcome-ok exit then
  dup lf-mhead-kind lf-head-none = if drop -1 outcome-invalid exit then
  lf-blk-not-sort no-result ;
: lf-blk-dend ( node i -- level outcome )
  dup lf-ind-nparams < if lf-blk-few-params exit then
  lf-ind-nparams - lf-blk-type@ lf-blk-indices! lf-blk-dsort ;
: lf-blk-dtele ( node i -- level outcome )
  begin swap lf-blk-whnf ok-then? 0= if nip no-result exit then dup lf-blk-pi? while
    swap 2dup lf-blk-dbinder dup ok? 0= if nip nip no-result exit then drop
    swap lf-term-second@ swap 1+
  repeat swap lf-blk-dend ;
: lf-blk-same-level ( level -- outcome )
  lf-blk-level swap lf-ind-fuel @ lf-level-equivalent lf-lnorm-fuel @ lf-ind-fuel !
  ok-then? 0= if exit then if outcome-ok exit then
  lf-blk-member-d 0 lf-diag-universe-mismatch lf-blk-reject ;
: lf-blk-other-telescope ( d -- outcome )
  lf-blk-used @ swap lf-ind-ty lf-ty-domain !
  lf-blk-job lf-blk-type@ lf-ind-type-at lf-idecl-type @ 0 lf-blk-dtele lf-blk-refuel
  ok-then? 0= if exit then lf-blk-same-level ;
: lf-blk-telescope ( d -- outcome )
  ?dup if lf-blk-other-telescope else lf-blk-first-telescope then ;
\ Steps 6 to 8 for type d, then for the next, each with its step.
: lf-blk-step! ( step -- ) lf-ind-state lf-ind-step-reached ! ;
: lf-blk-type-steps ( d -- outcome )
  dup lf-blk-type! 6 lf-blk-step! dup lf-blk-names ok-then? 0= if exit then
  7 lf-blk-step! dup lf-blk-type ok-then? 0= if exit then
  8 lf-blk-step! lf-blk-telescope ;
: lf-blk-types ( -- outcome )
  lf-ind-types@ 0 ?do i lf-blk-type-steps dup ok? 0= if unloop exit then drop loop
  outcome-ok ;

\ ---------------------------------------------------------------------------
\ Step 9: the constructors, each against the first type's parameter
\ domains, as their locals have them (consume_type_annotations,
\ inductive-recursor.fs: lf-blk-param-dom).
: lf-blk-ctor-name ( j -- name ) lf-ind-ctor lf-idecl-name @ ;
: lf-blk-member ( -- k ) lf-blk-ctor@ lf-ind-types@ + ;
\ C4: an earlier constructor of its own type with the same name (Lean's
\ name set is per type, 459-465).
: lf-blk-dup ( -- outcome ) lf-blk-member 0 lf-diag-duplicate-ctor lf-blk-reject ;
: lf-blk-first-of ( j -- j0 ) lf-ind-owner lf-ind-ty lf-ty-ctor @ ;
: lf-blk-c4 ( j -- outcome )
  dup lf-blk-ctor-name over dup lf-blk-first-of ?do dup i lf-blk-ctor-name lf-name-same?
    if 2drop lf-blk-dup unloop exit then
  loop 2drop outcome-ok ;
\ C2, parameter i: the constructor's domain against the first type's.
: lf-blk-param ( node i -- outcome ) lf-diag-ctor-param lf-blk-param-as ;
\ U1, a field in a universe the result level covers: Lean's is_geq, or a
\ result that normalizes to zero (an inductive predicate).
: lf-blk-too-big ( -- outcome ) lf-blk-member 0 lf-diag-universe-too-big lf-blk-reject ;
: lf-blk-geq? ( level -- flag outcome )
  lf-blk-level swap lf-minfer-fuel @ lf-level-geq? lf-lnorm-fuel @ lf-minfer-fuel ! ;
: lf-blk-predicate ( -- outcome )
  lf-blk-level lf-minfer-zero? ok-then? 0= if exit then
  if outcome-ok else lf-blk-too-big then ;
: lf-blk-fits ( level -- outcome )
  lf-blk-geq? ok-then? 0= if exit then if outcome-ok else lf-blk-predicate then ;
\ is_valid_ind_app (381-400) of node at binder depth depth, for type d
\ (lf-blk-shape-of?) or for any type of the block (lf-blk-shape?): T_d
\ at the universe parameters, numParams + T_d's numIndices arguments (the
\ arity, kept while the test runs), argument i the variable of parameter
\ i; and indices that mention no type of the block, each counted by xt
\ ( node -- n outcome ).
: lf-blk-arity ( -- n ) lf-blk-state lf-blkrec-arity @ ;
: lf-blk-arity! ( d -- ) lf-ind-n lf-ind-nparams + lf-blk-state lf-blkrec-arity ! ;
: lf-blk-c3-arg? ( node depth i -- flag )
  tuck - 1- >r lf-blk-arity swap lf-ind-arg r> lf-ind-bvar? ;
: lf-blk-c3-params? ( node depth -- flag )
  lf-ind-nparams 0 ?do 2dup i lf-blk-c3-arg? 0= if 2drop false unloop exit then loop
  2drop true ;
: lf-blk-shape-of? ( node depth d -- flag )
  dup lf-blk-arity! >r over lf-ind-spine lf-blk-arity <> if r> 2drop 2drop false exit then
  dup lf-ind-which r> <> if drop 2drop false exit then
  lf-term-first@ lf-ind-levels? 0= if 2drop false exit then
  dup lf-ind-nparams < if 2drop false exit then lf-blk-c3-params? ;
: lf-blk-shape? ( node depth -- flag )
  over lf-ind-spine drop lf-ind-which dup 0< if drop 2drop false exit then
  lf-blk-shape-of? ;
: lf-blk-none? ( n outcome -- flag outcome )
  ok-then? if 0= outcome-ok else false swap then ;
: lf-blk-index-free? ( node i xt -- flag outcome )
  >r lf-blk-arity swap lf-ind-arg r> execute lf-blk-none? ;
: lf-blk-indices-free? ( node xt -- flag outcome )
  lf-blk-arity lf-ind-nparams ?do
    2dup i swap lf-blk-index-free? ok-then? 0= if nip nip false swap unloop exit then
    0= if 2drop false outcome-ok unloop exit then
  loop 2drop true outcome-ok ;
: lf-blk-valid? ( node depth xt -- flag outcome )
  >r over swap lf-blk-shape? 0= if r> 2drop false outcome-ok exit then
  r> lf-blk-indices-free? ;
: lf-blk-valid-of? ( node depth d xt -- flag outcome )
  >r >r over swap r> lf-blk-shape-of? 0= if r> 2drop false outcome-ok exit then
  r> lf-blk-indices-free? ;

\ Positivity (P1, P2; check_positivity 436-452), in step 9's inference
\ job, of field i, whose type node is read under the constructor's i
\ binders: a block's field that mentions its type (no other: reduction
\ never makes an occurrence, the type being in no environment a definition
\ unfolds into, so Lean's test passes on it whatever whnf gives). The type
\ is put in Lean's whnf (lf-blk-whnf, failing where it cannot follow
\ Lean); with no occurrence left it is a non-recursive field;
\ a Pi whose domain mentions the type is nonPositive, else its body is
\ checked one binder deeper; anything else must be a valid application
\ of the type (a recursive field), else nonValidOccurrence. Occurrences
\ are counted on the job's fuel.
: lf-blk-occurs ( node -- n outcome )
  lf-minfer-fuel @ lf-ind-fuel ! lf-ind-occurrences lf-ind-fuel @ lf-minfer-fuel ! ;
: lf-blk-occurs? ( node -- flag outcome )
  lf-blk-occurs ok-then? if 0<> outcome-ok else false swap then ;
: lf-pos-fail ( code -- outcome )
  >r lf-blk-member lf-blk-state lf-blkrec-field @ r> lf-blk-reject ;
: lf-pos-end ( node depth -- outcome )
  ['] lf-blk-occurs lf-blk-valid? ok-then? 0= if exit then
  if outcome-ok else lf-diag-non-valid lf-pos-fail then ;
: lf-pos-pi ( node depth -- node' depth' true | outcome false )
  over lf-term-first@ lf-blk-occurs? ok-then? 0= if nip nip false exit then
  if 2drop lf-diag-non-positive lf-pos-fail false exit then
  1+ swap lf-term-second@ swap true ;
: lf-pos-step ( node depth -- node' depth' true | outcome false )
  swap lf-blk-whnf ok-then? 0= if nip false exit then swap
  over lf-blk-occurs? ok-then? 0= if nip nip false exit then
  0= if 2drop outcome-ok false exit then
  over lf-blk-pi? if lf-pos-pi exit then lf-pos-end false ;
: lf-blk-positive ( node depth -- outcome ) begin lf-pos-step 0= until ;
: lf-blk-positivity ( node i -- outcome )
  lf-ind-recursive? 0= if 2drop outcome-ok exit then
  dup lf-blk-state lf-blkrec-field !
  over lf-blk-occurs? ok-then? 0= if nip nip exit then
  if lf-blk-positive else 2drop outcome-ok then ;
: lf-blk-field ( node i -- outcome )
  swap lf-term-first@ dup lf-minfer-domain ok-then? 0= if nip nip exit then
  lf-blk-fits ok-then? 0= if nip exit then
  dup rot lf-blk-positivity ok-then? 0= if exit then lf-rcr-consume lf-blk-push ;
: lf-blk-binder ( node i -- outcome )
  dup lf-ind-nparams < if lf-blk-param else lf-blk-field then ;
\ The raw telescope: (body k outcome), k its binders.
: lf-blk-binders ( node -- node' k outcome )
  0 begin over lf-tag-pi lf-ind-tag? while
    2dup lf-blk-binder dup ok? 0= if exit then drop swap lf-term-second@ swap 1+
  repeat outcome-ok ;
\ C3: the result is a valid application of the constructor's own type
\ (above, 493-494), its indices counted on the block's fuel.
: lf-blk-c3 ( node depth -- flag outcome )
  lf-blk-ctor@ lf-ind-owner ['] lf-ind-occurrences lf-blk-valid-of? ;
: lf-blk-bad-return ( -- outcome ) lf-blk-member 0 lf-diag-return-type lf-blk-reject ;
: lf-blk-ctor-walk ( j -- outcome )
  lf-blk-job lf-ind-ctor-type lf-blk-binders lf-blk-refuel ok-then2? 0= if exit then
  2dup lf-blk-c3 ok-then? 0= if nip nip exit then
  0= if 2drop lf-blk-bad-return exit then
  nip lf-ind-nparams - lf-blk-ctor@ lf-ind-nfields ! outcome-ok ;
: lf-blk-ctor ( j -- outcome )
  dup lf-blk-state lf-blkrec-ctor !
  dup lf-blk-c4 ok-then? 0= if exit then
  dup lf-blk-ctor-name lf-blk-fresh ok-then? 0= if exit then
  dup lf-ind-ctor-type lf-blk-infer ok-then? 0= if exit then lf-blk-ctor-walk ;
\ declare_constructors (499-519) after every constructor was checked: a
\ name an earlier constructor of another type has is declared already
\ (one of its own type was C4's).
: lf-blk-declared ( j -- outcome )
  lf-ind-types@ + dup lf-ind-name-at swap lf-diag-already-declared lf-blk-reject ;
: lf-blk-ctor-fresh ( j -- outcome )
  dup lf-blk-ctor-name over 0 ?do dup i lf-blk-ctor-name lf-name-same?
    if drop lf-blk-declared unloop exit then
  loop 2drop outcome-ok ;
: lf-blk-ctors-declared ( -- outcome )
  lf-ind-ctors@ 0 ?do i lf-blk-ctor-fresh dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
: lf-blk-ctors ( -- outcome )
  true lf-ind-state lf-ind-visible !
  lf-ind-ctors@ 0 ?do i lf-blk-ctor dup ok? 0= if unloop exit then drop loop
  lf-blk-ctors-declared ;

\ ---------------------------------------------------------------------------
\ Step 10: the elimination level (E0-E4) and K.
\ E3: the one constructor's telescope with its own domains (each a local
\ of its own type, 553-566); a field whose type is no proposition must be
\ an argument of the result, else Prop only (E4).
: lf-blk-checks# ( -- n ) lf-blk-state lf-blkrec-checks @ ;
: lf-blk-check@ ( k -- pos ) cells lf-blk-positions slab-base + @ ;
\ Recording a position: full when the heap cannot hold it.
: lf-blk-check! ( pos -- outcome )
  lf-blk-checks# dup 1+ lf-blk-positions slab-hold ok? 0= if 2drop outcome-full exit then
  cells lf-blk-positions slab-base + !
  1 lf-blk-state lf-blkrec-checks +! outcome-ok ;
: lf-blk-proof? ( domain -- flag status )
  lf-minfer-domain ok-then? 0= if false swap exit then lf-minfer-zero? ;
: lf-blk-e-field ( node i -- node i outcome )
  over lf-term-first@ lf-blk-proof? ok-then? 0= if exit then
  if outcome-ok else dup lf-blk-check! then ;
: lf-blk-e-binder ( node i -- outcome )
  dup lf-ind-nparams < 0= if lf-blk-e-field ok-then2? 0= if exit then then
  drop lf-term-first@ lf-rcr-consume lf-blk-push ;
: lf-blk-e-walk ( node -- node' k outcome )
  0 begin over lf-tag-pi lf-ind-tag? while
    2dup lf-blk-e-binder dup ok? 0= if exit then drop swap lf-term-second@ swap 1+
  repeat outcome-ok ;
\ Whether some argument of node's spine is the variable #index.
: lf-blk-among? ( node index -- flag )
  swap begin dup lf-tag-app lf-ind-tag? while
    2dup lf-term-second@ swap lf-ind-bvar? if 2drop true exit then lf-term-first@
  repeat 2drop false ;
: lf-blk-revealed? ( node k -- flag )
  lf-blk-checks# 0 ?do 2dup 1- i lf-blk-check@ - lf-blk-among? 0=
    if 2drop false unloop exit then
  loop 2drop true ;
: lf-blk-e3 ( -- prop? outcome )
  0 lf-blk-state lf-blkrec-checks !
  lf-blk-job 0 lf-ind-ctor-type lf-blk-e-walk lf-blk-refuel
  ok-then2? 0= if false swap exit then lf-blk-revealed? 0= outcome-ok ;
\ elim_only_at_universe_zero: E0 a result never zero, E1 a mutual block
\ or two or more constructors, E2 none, else E3/E4.
: lf-blk-prop-only? ( -- prop? outcome )
  lf-lmk-forget lf-blk-level lf-lmk-nonzero? if false outcome-ok exit then
  lf-ind-types@ 1 > if true outcome-ok exit then
  lf-ind-ctors@ 1 > if true outcome-ok exit then
  lf-ind-ctors@ 0= if false outcome-ok exit then lf-blk-e3 ;
\ The motive's universe: u, or u_1, u_2, ... the first not among the
\ block's universe parameters (name("u").append_after(i)).
: lf-blk-u ( i -- c-addr u )
  ?dup 0= if s" u" exit then
  base @ >r decimal 0 <# #s [char] _ hold [char] u hold #> r> base ! ;
: lf-blk-taken? ( name -- flag ) lf-ind-lparams lf-ind-in? ;
: lf-blk-elim-name ( -- name true | false )
  0 begin dup lf-blk-u 0 -rot lf-name-str 0= if drop false exit then
    dup lf-blk-taken? while drop 1+ repeat nip true ;
: lf-blk-motive-level ( -- name level true | false )
  lf-blk-elim-name 0= if false exit then
  dup lf-level-param if true else drop false then ;
: lf-blk-elim! ( name level -- )
  lf-ind-state lf-ind-elim ! dup 0<> lf-ind-state lf-ind-large !
  lf-ind-state lf-ind-elim-name ! ;
\ K: a predicate of one type with one constructor that has no fields.
: lf-blk-k-shape? ( -- flag )
  lf-ind-types@ 1 = lf-ind-ctors@ 1 = and if 0 lf-ind-nfields @ 0= else false then ;
: lf-blk-k ( -- outcome )
  false lf-ind-state lf-ind-k ! lf-blk-k-shape? 0= if outcome-ok exit then
  lf-blk-job lf-blk-level lf-minfer-zero? lf-blk-refuel ok-then? 0= if exit then
  lf-ind-state lf-ind-k ! outcome-ok ;
: lf-blk-elim ( -- outcome )
  lf-blk-prop-only? ok-then? 0= if exit then
  if 0 0 else lf-blk-motive-level 0= if outcome-full exit then then
  lf-blk-elim! lf-blk-k ;

\ Step 11: each type's T.rec, in order, is no name the block declared
\ before it (declare_recursors 813: its types and constructors).
: lf-blk-rec-clash ( d k -- outcome )
  swap lf-blk-rec-id swap lf-diag-already-declared lf-blk-reject ;
: lf-blk-rec-name-of ( d -- outcome )
  lf-ind-types@ lf-ind-ctors@ + 0 ?do
    dup lf-blk-rec-id i lf-ind-name-at lf-name-same?
    if i lf-blk-rec-clash unloop exit then
  loop drop outcome-ok ;
: lf-blk-rec-name ( -- outcome )
  lf-ind-types@ 0 ?do i lf-blk-rec-name-of dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
\ Step 12: the recursor (inductive-recursor.fs), and the recipe that lets
\ a later declaration build it again (generated-recursor.fs).
: lf-blk-build ( -- outcome )
  lf-recursor-build dup ok? if lf-genrec-recipe lf-env-recipe! then ;

\ ---------------------------------------------------------------------------
\ Step 13, B3. Name lists equal name by name.
: lf-blk-names= ( items n items' n' -- flag ) lf-ind-names= ;
: lf-blk-params= ( decl -- flag ) lf-idecl-params@ lf-ind-lparams lf-blk-names= ;
\ B3's comparisons of numbers and names: tables of tests ( x -- differs? ),
\ each with the number of the field it compares (its place in Lean's
\ structure, as the diagnostic gives it), run in order; the first field
\ that differs, or 0.
: lf-b3-test ( x entry -- x field|0 ) 2@ >r over r> execute and ;
: lf-b3-scan ( x table n -- field )
  2* cells bounds ?do i lf-b3-test ?dup if nip unloop exit then 2 cells +loop drop 0 ;
\ Constructor j's fields 1 levelParams, 3 cidx, 4 numParams and 5
\ numFields; its name, type (2) and induct are the ones the kernel uses
\ (B0).
: lf-blk-ctor-data ( j -- data ) lf-ind-ctor lf-idecl-data ;
: lf-b3-ctor-lparams? ( j -- flag ) lf-ind-ctor lf-blk-params= 0= ;
: lf-b3-cidx? ( j -- flag )
  dup lf-blk-ctor-data lf-ict-cidx lf-more-field swap dup lf-blk-first-of - <> ;
: lf-b3-ctor-params? ( j -- flag )
  lf-blk-ctor-data lf-ict-params lf-more-field lf-ind-nparams <> ;
: lf-b3-ctor-fields? ( j -- flag )
  dup lf-blk-ctor-data lf-ict-fields lf-more-field swap lf-ind-nfields @ <> ;
create lf-b3-ctor
  ' lf-b3-ctor-lparams? , 1 ,  ' lf-b3-cidx? , 3 ,  ' lf-b3-ctor-params? , 4 ,
  ' lf-b3-ctor-fields? , 5 ,
here lf-b3-ctor - 2 cells / constant lf-b3-ctor#
: lf-blk-ctor-diff ( j -- field ) lf-b3-ctor lf-b3-ctor# lf-b3-scan ;
: lf-blk-ctor-differs ( j field -- outcome )
  swap lf-ind-types@ + swap lf-diag-invalid-constructor lf-blk-replace ;
: lf-blk-ctors-b3 ( -- outcome )
  lf-ind-ctors@ 0 ?do
    i lf-blk-ctor-diff ?dup if i swap lf-blk-ctor-differs unloop exit then
  loop outcome-ok ;
\ Two terms by Lean's ==: (equal ok); a structural difference is (false
\ ok); any other failure passes on.
: lf-blk-same ( generated exported -- flag outcome )
  >r lf-rcr-handle r> lf-rcr-handle lf-ind-fuel @ lf-mixed-compare
  lf-mcompare-fuel @ lf-ind-fuel !
  case outcome-ok of true outcome-ok endof  outcome-unknown of false outcome-ok endof
    >r false r@ r> endcase ;
\ Recursor r: named T_d.rec for a type d of the block, else Lean's "No
\ such recursor"; then the field that differs from type d's generated
\ recursor (2 levelParams, 3 type, 4 all, 5 numParams, 6 numIndices, 7
\ numMotives, 8 numMinors, 9 rules, 10 k), or 0. The type compared is
\ lf-blk-type@ meanwhile.
: lf-blk-rec-lparams= ( decl -- flag )
  lf-idecl-params@ lf-ind-state lf-ind-elim-name @ ?dup 0=
  if lf-ind-lparams lf-blk-names= exit then
  >r dup 0= if 2drop r> drop false exit then
  over @ r> lf-name-same? 0= if 2drop false exit then
  1- swap cell+ swap lf-ind-lparams lf-blk-names= ;
\ A recursor's fields 4 all (the block's types), 5 numParams, 6
\ numIndices, 7 numMotives (one per type) and 8 numMinors (one per
\ constructor of the block) (its data).
: lf-b3-all? ( data -- flag ) lf-irc-all@ lf-ind-all lf-blk-names= 0= ;
: lf-b3-rec-params? ( data -- flag ) lf-irc-params lf-more-field lf-ind-nparams <> ;
: lf-b3-indices? ( data -- flag )
  lf-irc-indices lf-more-field lf-blk-type@ lf-ind-n <> ;
: lf-b3-motives? ( data -- flag ) lf-irc-motives lf-more-field lf-ind-types@ <> ;
: lf-b3-minors? ( data -- flag ) lf-irc-minors lf-more-field lf-ind-ctors@ <> ;
create lf-b3-rec
  ' lf-b3-all? , 4 ,  ' lf-b3-rec-params? , 5 ,  ' lf-b3-indices? , 6 ,
  ' lf-b3-motives? , 7 ,  ' lf-b3-minors? , 8 ,
here lf-b3-rec - 2 cells / constant lf-b3-rec#
: lf-blk-k= ( data -- flag ) lf-irc-k lf-more-field 0<> lf-ind-state lf-ind-k @ 0<> = ;
\ Rule t (field 9), for type d's constructor j = ctor(d) + t: its
\ constructor, its fields, then its right side.
: lf-b3-rule-head? ( rule j -- flag )
  over lf-irule-ctor over lf-blk-ctor-name lf-name-same? 0=
  -rot lf-ind-nfields @ swap lf-irule-nfields <> or ;
: lf-blk-rule-diff ( rules t -- differs? outcome )
  tuck lf-irc-rule swap lf-blk-type@ lf-ind-ty lf-ty-ctor @ +
  2dup lf-b3-rule-head? if 2drop true outcome-ok exit then
  swap lf-irule-rhs swap lf-ind-rule @ swap lf-blk-same >r 0= r> ;
: lf-blk-rules-diff ( data -- field outcome )
  lf-irc-rules@ dup lf-blk-type@ lf-ind-ty lf-ty-ctors @ <>
  if 2drop 9 outcome-ok exit then
  0 ?do dup i lf-blk-rule-diff ok-then? 0= if nip 0 swap unloop exit then
    if drop 9 outcome-ok unloop exit then
  loop drop 0 outcome-ok ;
: lf-blk-data-diff ( data -- field outcome )
  dup lf-b3-rec lf-b3-rec# lf-b3-scan ?dup if nip outcome-ok exit then
  dup lf-blk-rules-diff ok-then? 0= if nip 0 swap exit then
  ?dup if nip outcome-ok exit then
  lf-blk-k= if 0 else 10 then outcome-ok ;
: lf-blk-rec-diff ( r -- field outcome )
  lf-ind-rec dup lf-blk-rec-lparams= 0= if drop 2 outcome-ok exit then
  dup lf-idecl-type @ lf-blk-type@ lf-ind-ty lf-ty-rec-type @ swap lf-blk-same
  ok-then? 0= if nip 0 swap exit then 0= if drop 3 outcome-ok exit then
  lf-idecl-data lf-blk-data-diff ;
: lf-blk-rec-member ( r -- k ) lf-ind-types@ + lf-ind-ctors@ + ;
: lf-blk-no-such ( r -- outcome )
  lf-blk-rec-member 0 lf-diag-no-such-recursor lf-blk-reject ;
: lf-blk-rec-differs ( r field -- outcome )
  swap lf-blk-rec-member swap lf-diag-invalid-recursor lf-blk-replace ;
\ The type whose T.rec is named name: d, or -1.
: lf-blk-rec-of ( name -- d )
  lf-ind-types@ 0 ?do dup i lf-blk-rec-id lf-name-same? if drop i unloop exit then loop
  drop -1 ;
: lf-blk-rec-b3 ( r -- outcome )
  dup lf-ind-rec lf-idecl-name @ lf-blk-rec-of dup 0< if drop lf-blk-no-such exit then
  lf-blk-type! dup lf-blk-rec-diff ok-then? 0= if nip exit then
  ?dup if lf-blk-rec-differs else drop outcome-ok then ;
: lf-blk-recs-b3 ( -- outcome )
  lf-ind-recs@ 0 ?do i lf-blk-rec-b3 dup ok? 0= if unloop exit then drop loop outcome-ok ;
: lf-blk-compare ( -- outcome ) lf-blk-ctors-b3 ['] lf-blk-recs-b3 lf-blk-then ;

\ Step 14, B4: each type's fields Lean's replay ignores, against what
\ LeanForth computed (its numIndices; isRec and isReflexive, the audit's
\ is_rec and is_reflexive of the block; numNested 0, the block not being
\ nested), and a type whose T.rec the block does not hold, as warning
\ bits; never a failure. The bits go to the candidate, and so onto the
\ accepted block's slots (lf-env-warnings). The type tested is
\ lf-blk-type@ meanwhile.
: lf-blk-flag ( data bit -- flag ) swap lf-ity-flags lf-more-field and 0<> ;
: lf-blk-differs? ( flag x -- flag' ) 0<> <> ;
: lf-b4-indices? ( data -- flag )
  lf-ity-indices lf-more-field lf-blk-type@ lf-ind-n <> ;
: lf-b4-rec? ( data -- flag )
  lf-ity-rec-bit lf-blk-flag lf-ind-state lf-ind-is-rec @ lf-blk-differs? ;
: lf-b4-reflexive? ( data -- flag )
  lf-ity-reflexive-bit lf-blk-flag lf-ind-state lf-ind-is-refl @ lf-blk-differs? ;
: lf-b4-nested? ( data -- flag ) lf-ity-nested lf-more-field 0<> ;
: lf-b4-held? ( name -- flag )
  false lf-ind-recs@ 0 ?do over i lf-ind-rec lf-idecl-name @ lf-name-same? or loop nip ;
: lf-b4-no-recursor? ( data -- flag ) drop lf-blk-type@ lf-blk-rec-id lf-b4-held? 0= ;
create lf-b4-tests
  ' lf-b4-indices? , lf-warn-indices ,  ' lf-b4-rec? , lf-warn-rec ,
  ' lf-b4-reflexive? , lf-warn-reflexive ,  ' lf-b4-nested? , lf-warn-nested ,
  ' lf-b4-no-recursor? , lf-warn-no-recursor ,
here lf-b4-tests - 2 cells / constant lf-b4-tests#
: lf-b4-bits ( data -- bits )
  0 swap lf-b4-tests lf-b4-tests# 2* cells bounds
  ?do i lf-b3-test rot or swap 2 cells +loop drop ;
: lf-b4-type ( bits d -- bits' )
  dup lf-blk-type! lf-ind-type-at lf-idecl-data lf-b4-bits or ;
: lf-blk-b4 ( -- outcome )
  0 lf-ind-types@ 0 ?do i lf-b4-type loop dup lf-env-warnings!
  lf-ind-state lf-ind-warned ! outcome-ok ;

\ ---------------------------------------------------------------------------
\ The steps ( -- outcome ), in order.
\ Steps 6 to 8 run as one entry, for each type in turn (lf-blk-types,
\ which sets the step it reaches); the entries of 7 and 8 have nothing
\ left to do.
: lf-blk-done ( -- outcome ) outcome-ok ;
create lf-blk-steps
  ' lf-ind-audit , ' lf-ind-t0 , ' lf-ind-c1 , ' lf-ind-t1 , ' lf-blk-t5 ,
  ' lf-blk-types , ' lf-blk-done , ' lf-blk-done , ' lf-blk-ctors ,
  ' lf-blk-elim , ' lf-blk-rec-name , ' lf-blk-build , ' lf-blk-compare , ' lf-blk-b4 ,
here lf-blk-steps - 1 cells / constant lf-blk-steps#
: lf-blk-do ( k -- outcome ) dup 1+ lf-blk-step! cells lf-blk-steps + @ execute ;
: lf-blk-run ( -- outcome )
  lf-blk-steps# 0 ?do i lf-blk-do dup ok? 0= if unloop exit then drop loop
  lf-blk-steps# 1+ lf-blk-step! outcome-ok ;
\ The block of this context's snapshot: its members as the candidate's
\ span (every member gets the outcome), and the fuel.
: lf-blk-begin ( fuel -- outcome )
  lf-env-checking 0= if drop outcome-invalid exit then nip
  lf-ind-open swap lf-env-span! dup ok? if drop lf-ind-fuel ! outcome-ok else nip then ;
\ Check the block whose first member is this context's snapshot, with
\ fuel: ok when every step succeeded, else the first failure, as above.
\ Afterwards the type is no longer visible to inference.
\ A block rejected at step 13 alone, B3, which Lean's replay runs after its
\ kernel added the block: the publisher marks the members' names taken
\ (lf-env-added!; ADR 0015 decision 11, review rvI21 R2-1).
13 constant lf-blk-b3-step
: lf-blk-added ( outcome -- outcome )
  dup outcome-rejected = lf-block-step@ lf-blk-b3-step = and lf-env-added! ;
\ An empty block: Lean's elim_nested_inductive_fn refuses a declaration
\ without types (inductive.cpp 1153, emptyBlock) before anything else of
\ it, the checks before it having nothing to look at; rejected at step 4.
4 constant lf-blk-t1-step
: lf-blk-empty ( -- outcome )
  lf-blk-t1-step lf-blk-step! lf-ind-first@ 0 lf-diag-empty-block lf-blk-reject ;
: lf-blk-checked ( -- outcome )
  lf-ind-empty? if lf-blk-empty else lf-blk-run lf-blk-added then ;
: lf-block-check ( fuel -- outcome )
  lf-blk-begin dup ok? if drop lf-blk-checked then
  false lf-ind-state lf-ind-visible ! ;
