\ Induction (plan S2, branch s2-tactics; docs/design/S2_INTERFACE.md 4):
\ t by-induction, t by-induction-with and its | alternatives, the rows of
\ their kinds in the runner (tactic-run.fs), after Lean 4.35.0's
\ Elab/Tactic/Induction.lean (evalInduction 1005, evalInductionCore 977,
\ getElimNameInfo 816, getInductiveValFromMajor 770, mkElimApp 165,
\ setMotiveArg 249, checkAltNames 283, getNumExplicitFields 317, evalAlts
\ 340) and Meta/Tactic/ElimInfo.lean (getElimExprInfo, getCustomEliminator?).
\ - The target, in the main goal's context (Lean's focus first): t
\   elaborated with no expected type, a free variable that is not a let
\   (anything else Lean generalizes: 99, FE5).
\ - The eliminator: the elaboration data's induction eliminator for the
\   head constant of the target's type, instantiated and head-beta
\   reduced (getCustomEliminator?: Nat.recAux for Nat); else the type put
\   through whnf must be an inductive type (205, Lean's text, its hints
\   for a proposition or a type universe, and the goal), neither mutual
\   nor nested (209), and its recursor C.rec is used.
\ - Its information (getElimExprInfo), read from its declared type: past
\   its pis, the motive applied to one target, both bound variables (an
\   eliminator with index targets: 99, FE5); the alternatives are the
\   other explicit binders (their kinds from the declaration's data,
\   lf-menv-kinds), each named as its binder, with as many fields as its
\   domain has pis.
\ - mkElimApp: the eliminator at new level metavariables, applied binder
\   by binder (whnf where no pi is left): the motive a new synthetic
\   opaque metavariable; the target, its type defeq the binder's (99
\   otherwise); an alternative a new goal named tag.NAME (Lean's
\   appendTag, tag the goal's); an implicit binder a natural metavariable
\   (an instance binder: 99, FE5).
\ - setMotiveArg: fun x => the goal's type with the target abstracted, x
\   named as the target's local, its type the target's; its type must be
\   defeq the motive's (212); the motive assigned; the goal assigned the
\   eliminator's application. Hypotheses that depend on the target
\   (generalizeVars) are not supported yet (99, FE5).
\ - by-induction-with: the names of its alternatives checked first (a
\   name written twice 213, Lean's "Duplicate alternative name", before a
\   name that is no case of the eliminator, 206 with the cases not
\   written: "Expected `zero` or `succ`"); then its block runs: each |
\   alternative takes its case's goal, at most as many names as the case
\   has explicit fields (208), introduces the fields (Lean's introN: the
\   names in order for the explicit fields, the binder's own name,
\   inaccessible, for the rest), clears the target (tryClear) and runs as
\   a block (unsolved goals at its =>); at the block's end a case no
\   alternative took is 207 at the induction's word (Lean's first message
\   there).
\ - by-induction: every case's goal, its fields introduced with
\   inaccessible names and the target cleared, after the goals left.
\ A case's fields take their kinds from the eliminator's declared type
\ (lf-menv-kinds-in), never from the goal's node: unknown kinds are 99.
\ Errors stop the run (author/errors.fs) at the step's word, an
\ alternative's at its |. Untrusted: the kernel checks the finished term.
\ State: the slabs tind-withs (the open by-induction-with blocks) and
\ tind-alts (their cases), kept in a tactic's saved state on
\ tind-withs-kept and tind-alts-kept (tac-state:), in the checker
\ context (ADR 0009); the step's
\ own fields in its step record (tactic-run.fs, review fe1g3 M2). Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../core/terms.fs
require ../core/names.fs
require ../core/input.fs
require ../core/local-context.fs
require ../present/binder-table.fs
require ../author/errors.fs
require ../author/declarations.fs
require ./mvars.fs
require ./lctx-views.fs
require ./goals.fs
require ./instantiate.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./term-eqv.fs
require ./elab-data.fs
require ./whnf.fs
require ./infer.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./tactic-basic.fs
require ./meta-must.fs
require ./app-builder.fs
require ./telescope.fs

begin-structure /tia      \ a case of the eliminator (Lean's ElimApp.Alt)
  field: tia-name         \ its name: its binder's
  field: tia-pos          \ that binder's position
  field: tia-fields       \ the fields it introduces (numFields)
  field: tia-goal         \ its goal
  field: tia-used         \ true once an alternative took it
end-structure
/tia context-slab: tind-alts
begin-structure /tiw      \ an open by-induction-with block
  field: tiw-first        \ its cases: the first in tind-alts
  field: tiw-target       \ the target's free variable
  field: tiw-elim         \ the eliminator's declaration
end-structure
/tiw context-slab: tind-withs
1 cells context-slab: tind-js   \ a with block's alternatives: their steps
\ The open blocks and their cases in a tactic's saved state (tactic-run.fs's
\ tac-state:; review C2 of 2026-11-18: a failed block left them open).
/tia context-slab: tind-alts-kept
/tiw context-slab: tind-withs-kept
: lfi-keep ( -- outcome )
  tind-alts tind-alts-kept slab-keep dup ok? 0= if exit then drop
  tind-withs tind-withs-kept slab-keep dup ok? if exit then tind-alts-kept slab-forget ;
: lfi-kept ( undo? -- outcome )
  dup tind-alts tind-alts-kept slab-kept
  swap tind-withs tind-withs-kept slab-kept outcome-and ;
' lfi-keep ' lfi-kept tac-state:
begin-structure /tind     \ the step's fields, after tb's
  /tb +field tind-tb
  field: tind-target      \ the target: a free variable
  field: tind-elim        \ the eliminator's declaration
  field: tind-binders     \ how many binders its type has
  field: tind-motive-at   \ the motive's binder position
  field: tind-target-at   \ the target's
  field: tind-first       \ its cases: the first in tind-alts
  field: tind-f           \ the eliminator applied so far (mkElimApp's f)
  field: tind-ftype       \ and its type
  field: tind-motive      \ the motive's metavariable
end-structure
/tind lf-tac-work-cells cells >
[if] .( tactic-induction.fs: its fields are wider than a step record) cr abort [then]
: ti ( -- addr ) lf-tac-record ;

\ ---- The target.
: lfi-arg ( i -- node ) lf-tactic-step tac-first @ lf-tactic-arg drop ;
: lfi-target! ( i -- )
  lfi-arg -1 false lf-tac-elab lf-tac-must dup lf-meta-fvar? 0= if lfa-e-tac-form
    lf-tac-fail
  then dup lf-fvar-let? if lfa-e-tac-form lf-tac-fail then ti tind-target ! ;
: lfi-target-type ( -- t ) ti tind-target @ lf-infer lf-tac-must ;

\ ---- The eliminator: a custom one, else the inductive type's recursor.
: lfi-custom ( name -- d true | false )
  lf-menv-data-decl 0= if false exit then elab-induction elab-eliminator-for
  0= if false exit then elab-eliminator@ nip lf-menv-of-data lf-tac-must true ;
: lfi-custom? ( -- d true | false )
  lfi-target-type lf-instantiate-mvars lf-tac-must lf-meta-head-beta lf-tac-must
  lf-meta-head-name if lfi-custom else false then ;
: lfi-major ( -- t ) lfi-target-type lf-meta-whnf lf-tac-must ;
\ Not an inductive type (205): Lean's text with its hints, then the goal.
\ Lean's majorType.isProp and .isType (Sort 0; a Sort of a succ level).
: lfi-succ-sort? ( t -- flag )
  dup lf-tag-symbolic-sort lf-term-tag? 0= if lf-sort? exit then
  lf-term-first@ lf-level-tag@ lf-level-tag-succ = ;
: lfi-prop-hint. ( -- )
  s\" \n\nConsider using the 'by_cases' tactic, which does true/false " lf-pp-emit
  s" reasoning for propositions." lf-pp-emit ;
: lfi-type-hint. ( -- )
  s\" \n\nType universes are not inductive types, and type-constructor-based " lf-pp-emit
  s" reasoning is not possible. This is a strong limitation. " lf-pp-emit
  s" According to Lean's underlying theory, the only provable " lf-pp-emit
  s" distinguishing feature of types is their cardinalities." lf-pp-emit ;
: lfi-sort-hint. ( t -- )
  dup lf-prop? if drop lfi-prop-hint. exit then lfi-succ-sort? if lfi-type-hint. then ;
: lfi-explanation. ( -- )
  s\" \n\nExplanation: the `induction` tactic is for constructor-based " lf-pp-emit
  s" reasoning as well as for applying custom induction principles with a " lf-pp-emit
  s" 'using' clause or a registered '@[induction_eliminator]' theorem. " lf-pp-emit ;
: lfi-unregistered. ( -- )
  s" The above type neither is an inductive type " lf-pp-emit
  s" nor has a registered theorem." lf-pp-emit ;
: lfi-explain. ( t -- outcome )
  lfi-explanation. lfi-unregistered. lfi-sort-hint. outcome-ok ;
\ (The major premise's type is kept in the step's tb-term for the messages.)
: lfi-major@ ( -- t ) tb tb-term @ ;
: lfi-major. ( x -- outcome )
  drop lfi-major@ lf-tac-indented. dup ok? if
    drop lfi-major@ lfi-explain. ['] lf-tac-goal. ok-and then ;
: lfi-not-inductive ( -- ) ['] lfi-major. lfa-e-tac-not-inductive lf-tac-failed ;
: lfi-inductive ( t -- d true | false )
  lf-meta-head-name 0= if false exit then
  lf-menv-find dup outcome-invalid = if 2drop false exit then
  lf-tac-must dup lf-menv-kind lf-kind-inductive = dup 0= if nip then ;
\ Mutual or nested (209): Lean's text and its hint.
: lfi-kind. ( c-addr u -- outcome )
  s"  `" lf-pp-emit lfi-major@ lf-meta-head-args drop lf-const-name lf-pp-name
  s" ` because it is " lf-pp-emit lf-pp-emit outcome-ok ;
: lfi-mutual. ( x -- outcome ) drop s" mutually inductive" lfi-kind. ;
: lfi-nested. ( x -- outcome ) drop s" a nested inductive type" lfi-kind. ;
: lfi-hint. ( x -- outcome )
  drop s\" \nHint: Consider using the `cases` tactic instead" lf-pp-emit outcome-ok ;
: lfi-unsupported ( xt -- )
  0 swap lf-tac-inline 0 ['] lfi-hint. lf-tac-detail lfa-e-tac-mutual lf-tac-stop ;
: lfi-simple ( d -- d )
  dup lf-menv-data ?dup 0= if lfa-e-tac-meta lf-tac-fail then
  dup lf-ity-all@ nip 1 <> if drop ['] lfi-mutual. lfi-unsupported then
  lf-ity-nested lf-more-field if ['] lfi-nested. lfi-unsupported then ;
: lfi-rec ( d -- d' ) lf-menv-name s" rec" lfa-intern-part lf-menv-find lf-tac-must ;
: lfi-recursor ( -- d )
  lfi-major dup tb tb-term ! lfi-inductive 0= if lfi-not-inductive then lfi-simple
    lfi-rec ;
: lfi-eliminator ( -- d ) lfi-custom? 0= if lfi-recursor then ;

\ ---- Its information (getElimExprInfo), from its declared type.
: lfi-past ( t -- body n ) 0 swap begin dup lf-term-pi? while lf-term-second@ swap 1+ swap
  repeat swap ;
: lfi-shape? ( concl -- flag )   \ a bound variable applied to one
  dup lf-meta-head-args 1 = swap lf-term-bvar? and swap lf-term-second@ lf-term-bvar?
    and ;
: lfi-pos ( bvar -- k ) lf-term-first@ ti tind-binders @ swap - 1- ;
: lfi-ends ( concl -- )
  dup lfi-shape? 0= if lfa-e-tac-form lf-tac-fail then
  dup lf-term-first@ lfi-pos ti tind-motive-at ! lf-term-second@ lfi-pos ti tind-target-at
    ! ;
: lfi-special? ( k -- flag ) dup ti tind-motive-at @ = swap ti tind-target-at @ = or ;
: lfi-kind ( k -- kind ) ti tind-elim @ swap lf-menv-kind@ 0= if lfa-e-tac-form
  lf-tac-fail then ;
: lfi-alt-new ( -- addr ) 1 tind-alts slab-claim lf-tac-must tind-alts slab-at dup /tia
  erase ;
: lfi-case+ ( pi k -- )
  lfi-alt-new tuck tia-pos ! over lf-tac-binder drop over tia-name !
  swap lf-term-first@ lfi-past nip swap tia-fields ! ;
: lfi-binder ( pi k -- )
  dup lfi-special? if 2drop exit then
  dup lfi-kind lf-binder-default = if lfi-case+ else 2drop then ;
: lfi-cases ( -- )
  ti tind-elim @ lf-menv-type ti tind-binders @ 0 ?do dup i lfi-binder lf-term-second@
    loop
  drop ;
: lfi-info ( d -- )
  dup ti tind-elim ! lf-menv-type lfi-past ti tind-binders ! lfi-ends
  tind-alts slab-count ti tind-first ! lfi-cases ;

\ ---- The cases of the step (or of the open block), found by name or place.
: lfi-cases# ( first -- n ) tind-alts slab-count swap - ;
: lfi-case ( first k -- addr ) + tind-alts slab-at ;
: lfi-case-at ( k -- addr )   \ unchecked: a case's binder
  ti tind-first @ begin 2dup tind-alts slab-at tia-pos @ <> while 1+ repeat nip
  tind-alts slab-at ;
\ A case of the step whose field at off (0 tia-pos, 0 tia-name) holds x.
: lfi-at? ( x off k -- flag ) ti tind-first @ swap lfi-case + @ = ;
: lfi-has? ( x off -- flag )
  ti tind-first @ lfi-cases# 0 ?do 2dup i lfi-at? if 2drop true unloop exit then loop
  2drop false ;
: lfi-case? ( k -- flag ) 0 tia-pos lfi-has? ;

\ ---- mkElimApp.
: lfi-tag ( name -- tag )
  tb tb-goal @ lf-mvar-tag drop ?dup 0= if exit then swap lf-name-text lfa-intern-part ;
: lfi-case-goal ( pi k -- arg )
  lfi-case-at >r lf-term-first@ r@ tia-name @ lfi-tag tb tb-view @ lf-goal-new lf-tac-must
  dup r> tia-goal ! ;
: lfi-motive-mvar ( pi -- arg )
  lf-term-first@ mv-opaque lf-mvar-new lf-tac-must dup ti tind-motive ! ;
: lfi-target-arg ( pi -- arg )
  lf-term-first@ lfi-target-type lf-tac-defeq lf-tac-must 0= if lfa-e-tac-form lf-tac-fail
  then ti tind-target @ ;
: lfi-implicit ( pi k -- arg )
  lfi-kind lf-binder-instance = if lfa-e-tac-form lf-tac-fail then
  lf-term-first@ mv-natural lf-mvar-new lf-tac-must ;
: lfi-arg-at ( pi k -- arg )
  dup ti tind-motive-at @ = if drop lfi-motive-mvar exit then
  dup ti tind-target-at @ = if drop lfi-target-arg exit then
  dup lfi-case? if lfi-case-goal else lfi-implicit then ;
: lfi-pi ( -- pi )
  ti tind-ftype @ lf-meta-whnf-forall lf-tac-must dup lf-term-pi? 0= if
    lfa-e-tac-meta lf-tac-fail then ;
: lfi-applied ( pi arg -- )
  dup ti tind-f @ swap lf-mk-app ti tind-f ! lf-meta-open lf-tac-must ti tind-ftype ! ;
: lfi-elim-app ( -- )
  ti tind-elim @ lf-meta-const-fresh lf-tac-must dup ti tind-f ! lf-infer lf-tac-must
  ti tind-ftype ! ti tind-binders @ 0 ?do lfi-pi dup i lfi-arg-at lfi-applied loop ;

\ ---- setMotiveArg: fun x => the goal's type over the target (Lean's
\ mkLambdaFVars targets type, telescope.fs: the binder named and of the
\ kind of the target's local in the goal's context, a target outside it
\ invalid, 93).
: lfi-motive ( -- lam ) tb tb-want @ ti tind-target 1 lf-mk-lambda-fvars ;
: lfi-motive. ( x -- outcome ) drop tb tb-term @ lf-tac-indented. ;
: lfi-motive-fits ( lam -- lam )
  dup lf-infer lf-tac-must ti tind-motive @ lf-mvar-type drop lf-tac-defeq lf-tac-must
  0= if dup tb tb-term ! ['] lfi-motive. lfa-e-tac-elim-motive lf-tac-failed then ;
\ generalizeVars: a hypothesis whose type depends on the target.
: lfi-depends? ( local -- flag )
  lf-local-fvar dup ti tind-target @ = if drop false exit then
  lf-fvar-type ti tind-target @ lf-depends-on? lf-tac-must ;
: lfi-independent ( -- )
  tb tb-view @ dup lf-view-count 0 ?do dup i lf-view-local lfi-depends? if
    lfa-e-tac-form lf-tac-fail then loop drop ;
: lfi-assigned ( -- )
  lfi-motive lfi-motive-fits ti tind-motive @ swap lf-mvar-assign lf-tac-must
  tb tb-goal @ ti tind-f @ lf-mvar-assign lf-tac-must lfb-popped ;
: lfi-setup ( i -- )
  lfi-target! lfi-independent lfi-eliminator lfi-info lfi-elim-app lfi-assigned ;

\ ---- checkAltNames over the with block's alternatives (tind-js: their
\ steps, in text order).
: lfi-alts-of ( i -- )
  tind-js slab-clear lf-tactic-count over 1+ ?do dup i lf-tactic-step tac-parent @ = if
    i tind-js slab-push lf-tac-must then loop drop ;
: lfi-j ( a -- j ) tind-js slab-at @ ;
: lfi-tag-of ( j -- name ) lf-tactic-step tac-name @ ;
: lfi-tag-at ( a -- name ) lfi-j lfi-tag-of ;
: lfi-earlier? ( a -- flag )
  dup lfi-tag-at swap 0 ?do dup i lfi-tag-at = if drop true unloop exit then loop drop
    false ;
: lfi-named? ( name -- flag ) 0 tia-name lfi-has? ;   \ a case of the eliminator has it
: lfi-written? ( name -- flag )
  tind-js slab-count 0 ?do dup i lfi-tag-at = if drop true unloop exit then loop drop
    false ;
\ The cases no alternative names, as Lean's orList: x, x or y, x, y, or z.
: lfi-unhandled? ( k -- flag ) ti tind-first @ swap lfi-case tia-name @ lfi-written? 0= ;
: lfi-unhandled# ( -- n ) 0 ti tind-first @ lfi-cases# 0 ?do i lfi-unhandled? - loop ;
: lfi-.name ( name -- ) s" `" lf-pp-emit lf-pp-name s" `" lf-pp-emit ;
: lfi-sep ( m n -- c-addr u )
  over 0= if 2drop s" " exit then dup 2 = if 2drop s"  or " exit then
  1- = if s" , or " else s" , " then ;
: lfi-listed ( n m k -- n m' )
  >r 2dup swap lfi-sep lf-pp-emit ti tind-first @ r> lfi-case tia-name @ lfi-.name 1+ ;
: lfi-expected. ( -- )
  lfi-unhandled# dup 0= if drop s" There are no unhandled alternatives" lf-pp-emit exit
    then
  s" Expected " lf-pp-emit 0 ti tind-first @ lfi-cases# 0 ?do
    i lfi-unhandled? if i lfi-listed then loop 2drop ;
: lfi-name. ( a -- outcome ) s"  " lf-pp-emit lfi-tag-at lfi-.name outcome-ok ;
: lfi-invalid. ( a -- outcome ) lfi-name. drop s" : " lf-pp-emit lfi-expected.
  outcome-ok ;
: lfi-twice ( -- )
  tind-js slab-count 0 ?do i lfi-earlier? if
    i ['] lfi-name. lf-tac-inline i lfi-j lfa-e-tac-alt-twice lf-tac-stop-at then loop ;
: lfi-unknown ( -- )
  tind-js slab-count 0 ?do i lfi-tag-at lfi-named? 0= if
    i ['] lfi-invalid. lf-tac-inline i lfi-j lfa-e-tac-alt-name lf-tac-stop-at then loop ;
: lfi-names-checked ( i -- ) lfi-alts-of lfi-twice lfi-unknown ;

\ ---- by-induction-with: the block's record, then its block.
: lfi-opened ( -- )
  1 tind-withs slab-claim lf-tac-must tind-withs slab-at ti tind-first @ over tiw-first !
  ti tind-target @ over tiw-target ! ti tind-elim @ swap tiw-elim ! ;
: lfi-with ( i -- ) dup lfi-setup lfi-names-checked lfi-opened ;
: lfi-w-with ( i -- ) lf-tac-focus over ['] lfi-with lf-tac-step-run lf-tac-block ;
\ At its end: a case no alternative took is Lean's first message there.
: lfi-top ( -- addr ) tind-withs slab-last ;
: lfi-open-cases ( -- first n ) lfi-top tiw-first @ dup lfi-cases# ;
: lfi-missing. ( case -- outcome )
  s"  " lf-pp-emit tia-name @ lfi-.name s"  has not been provided" lf-pp-emit outcome-ok ;
: lfi-missing ( i case -- ) ['] lfi-missing. lf-tac-inline lfa-e-tac-alt-missing
  lf-tac-stop-at ;
: lfi-unused ( i first k -- i first )   \ 207 for case k if no alternative took it
  over swap lfi-case dup tia-used @ if drop else rot swap lfi-missing then ;
: lfi-closed ( i -- )
  lfi-open-cases 0 ?do i lfi-unused loop 2drop
  lfi-top tiw-first @ tind-alts slab-cut tind-withs slab-drop ;

\ ---- An alternative: its case, its names, its fields, the target cleared.
begin-structure /talt     \ a case's fields, after the induction's
  /tind +field talt-tind
  field: talt-step        \ the alternative's step (the induction's, without)
  field: talt-case        \ its case
  field: talt-given       \ the names it gave taken so far
  field: talt-elim        \ the eliminator's declaration
end-structure
/talt lf-tac-work-cells cells >
[if] .( tactic-induction.fs: its fields are wider than a step record) cr abort [then]
: ta ( -- addr ) lf-tac-record ;
: lfi-case-named ( name -- case )
  lfi-open-cases 0 ?do 2dup i lfi-case tia-name @ = if dup i lfi-case nip nip unloop exit
  then loop 2drop lfa-e-tac-record lf-tac-stop 0 ;
\ Its fields' kinds, from the eliminator's declared type (unknown: 99).
: lfi-kinds ( case -- addr n ) ta talt-elim @ swap tia-pos @ lf-menv-kinds-in ;
: lfi-field-kind ( case f -- kind )
  swap lfi-kinds rot tuck > 0= if lfa-e-tac-form lf-tac-fail then cells + @ ;
: lfi-explicit? ( case f -- flag ) lfi-field-kind lf-binder-default = ;
: lfi-explicit# ( case -- n )
  0 swap dup tia-fields @ 0 ?do dup i lfi-explicit? if swap 1+ swap then loop drop ;
: lfi-given# ( -- n ) ta talt-step @ lf-tactic-step tac-count @ ;
: lfi-n. ( n -- ) u>decimal lf-pp-emit ;
: lfi-too-many. ( case -- outcome )
  s"  " lf-pp-emit dup tia-name @ lfi-.name s" : " lf-pp-emit lfi-given# lfi-n.
  s"  provided, but " lf-pp-emit lfi-explicit# lfi-n. s"  expected" lf-pp-emit
    outcome-ok ;
: lfi-names-fit ( case -- case )
  dup lfi-explicit# lfi-given# < if dup ['] lfi-too-many. lf-tac-inline
    ta talt-step @ lfa-e-tac-alt-names lf-tac-stop-at then ;
\ introN: the names given for the explicit fields, in order; 0 (the
\ binder's own name, inaccessible) for the others and past the names.
: lfi-next-name ( -- name )
  lfi-given# ta talt-given @ > 0= if 0 exit then
  ta talt-step @ lf-tactic-step tac-first @ ta talt-given @ + lf-tactic-arg drop
  1 ta talt-given +! ;
: lfi-name-for ( kind -- name ) lf-binder-default = if lfi-next-name else 0 then ;
: lfi-field ( f -- )
  ta talt-case @ swap lfi-field-kind dup lfi-name-for swap ta talt-step @
    lf-tac-intro-as ;
: lfi-intros ( case -- ) tia-fields @ 0 ?do i lfi-field loop ;
: lfi-only ( goal -- ) 0 swap run-push lf-tac-must lf-goals! lf-tac-must ;
\ tryClear: a refusal (invalid) keeps the goal; fuel, room or a gap is
\ thrown, as Lean's <|> never catches a runtime exception.
: lfi-cleared ( fvar -- )
  lf-tac-main swap lf-goal-clear dup outcome-invalid = if 2drop exit then
  lf-tac-must lfi-only ;
: lfi-case-goal! ( case fvar -- )
  >r dup tia-goal @ lfi-only lfi-intros r> lfi-cleared ;
: lfi-alt ( j -- )
  dup ta talt-step ! 0 ta talt-given ! lfi-top tiw-elim @ ta talt-elim !
  lfi-tag-of lfi-case-named dup ta talt-case ! lfi-names-fit true over tia-used !
  lfi-top tiw-target @ lfi-case-goal! ;
: lfi-w-alt ( j -- ) lf-goals over ['] lfi-alt lf-tac-in-record lf-tac-block ;

\ ---- by-induction: every case's goal, its fields named inaccessibly,
\ after the goals left (Lean's evalAlts without alternatives): the step's
\ arguments counted as names already taken, so none is given.
: lfi-plain-case ( k -- )
  ti tind-first @ swap lfi-case dup ta talt-case ! lf-tac-step ta talt-step !
  lfi-given# ta talt-given ! ti tind-elim @ ta talt-elim !
  ti tind-target @ lfi-case-goal! ;
\ (The cases run in the step's own record: an alternative's fields; the
\ goals gathered in the step's tb-new as a run.)
: lfi-gather ( -- ) tb tb-new @ lf-tac-main run-push lf-tac-must tb tb-new ! ;
: lfi-plain ( i -- )
  dup lfi-setup drop 0 tb tb-new ! ti tind-first @ lfi-cases# 0 ?do
    i lfi-plain-case lfi-gather loop tb tb-new @ lf-goals! lf-tac-must
  ti tind-first @ tind-alts slab-cut ;
: lfi-w-induction ( i -- ) lf-tac-focus swap ['] lfi-plain lf-tac-step-run
  lf-tac-unfocus ;

' lfi-w-with tac-k-with lf-tactic-action!
' lfi-w-alt tac-k-alt lf-tactic-action!
' lfi-w-induction tac-k-induction lf-tactic-action!
' lfi-closed tac-k-with lf-tactic-end!
base !   \ the BASE this file was loaded with
