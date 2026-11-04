\ An inductive block in the checker's input, and the checks of ADR 0015
\ that read it without typing (plan task 5.2.1a; Lean 4.35.0's
\ inductive.cpp, commit eb6cafb7):
\   B0 the block's shape, as lean4export writes it (invalid otherwise);
\   the audit, before any typing, as check-declaration's audit of a
\     definition: unsafe members (Lean's replay skips them) and the term
\     forms the checker lacks (U2) unsupported; loose variables invalid
\     (V1); and the scope of task 5.2.1a: one type (a mutual block is
\     task 5.2.5) that its constructors mention only as the head of their
\     result (an occurrence in a field's type makes a recursive block,
\     5.2.1b; in a result index, 5.2.1c), else unsupported;
\   T0 no constant named under the reserved prefix _nested
\     (check_no_nested_aux, inductive.cpp 1222-1233, from 1241, 1244);
\   C1 every occurrence of the type in a constructor type applied to the
\     block's universe parameters and exactly its parameters, the bound
\     variables of the first numParams binders (check_uniform_ind_occs,
\     134-164);
\   T1 the type has at least numParams binders before any reduction
\     (get_params, 1138-1146, from 1153).
\ The block is the one whose first member the check names (lf-ind-open):
\ its header in the input's inductive data (core/input.fs) gives its
\ members in input order, types, then constructors, then recursors.
\ check-block.fs runs these checks and Lean's typed steps in Lean's order;
\ inductive-recursor.fs builds the recursor.
\ [kernel] code: experimental, not through the review gate; not
\ independently audited. The exported numbers and flags are read here
\ only for the shape; check-block.fs compares the rest (B3, B4).
\ State: one record, lf-ind-state (the block, the facts computed so far,
\ per constructor its field count, minor premise and rule, the step
\ reached, the fuel, the warnings), and two walk records, lf-ind-walker
\ (U2, T0 and occurrences) and lf-ind-pair-walker (C1, with binder
\ depths), all members of the checker context (lib/context.fs).

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/constant-term-scope.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/levels.fs
require ../core/name-equal.fs
require ../core/names.fs
require ../core/terms.fs
require ../core/unsupported-forms.fs

512 constant lf-ind-ctor-capacity      \ constructors one block may have
lf-depth-limit constant lf-ind-binder-capacity   \ parameters plus indices

begin-structure /lf-ind
  field: lf-ind-first        \ input index of the block's first member
  field: lf-ind-types        \ its members, from the header
  field: lf-ind-ctors
  field: lf-ind-recs
  field: lf-ind-step-reached \ the step of check-block.fs reached
  field: lf-ind-fuel-left    \ fuel left between steps
  field: lf-ind-warned       \ B4 warnings (check-block.fs's lf-warn-* bits)
  field: lf-ind-visible      \ true once the type is visible to inference
  field: lf-ind-indices      \ computed: numIndices
  field: lf-ind-level        \ computed: the result Sort's level
  field: lf-ind-elim         \ computed: the elimination level, 0 for Prop
  field: lf-ind-elim-name    \ its parameter's name ID, 0 for Prop
  field: lf-ind-k            \ computed: K-like reduction target (flag)
  field: lf-ind-rec-type     \ generated: the recursor's type
  field: lf-ind-count        \ occurrences counted by a walk
  lf-ind-binder-capacity cells +field lf-ind-domain-cells \ parameters, then indices
  lf-ind-ctor-capacity cells +field lf-ind-field-cells    \ per constructor: fields
  lf-ind-ctor-capacity cells +field lf-ind-minor-cells    \ per constructor: minor
  lf-ind-ctor-capacity cells +field lf-ind-rule-cells     \ per constructor: rule
end-structure
/lf-ind context-record: lf-ind-state
lf-depth-limit context-walk: lf-ind-walker
lf-depth-limit context-walk2: lf-ind-pair-walker

: lf-ind-site ( -- site ) c" inductive-block lf-ind-audit" ;
: lf-ind-first@ ( -- i ) lf-ind-state lf-ind-first @ ;
: lf-ind-types@ ( -- n ) lf-ind-state lf-ind-types @ ;
: lf-ind-ctors@ ( -- n ) lf-ind-state lf-ind-ctors @ ;
: lf-ind-recs@ ( -- n ) lf-ind-state lf-ind-recs @ ;
: lf-ind-members ( -- n ) lf-ind-types@ lf-ind-ctors@ + lf-ind-recs@ + ;
: lf-ind-fuel ( -- addr ) lf-ind-state lf-ind-fuel-left ;
\ Member k of the block (from 0), the type, constructor j and recursor r.
\ Unchecked: k is below lf-ind-members, which lf-ind-open checked.
: lf-ind-member ( k -- decl ) lf-ind-first@ + lf-input-decl ;
: lf-ind-type ( -- decl ) 0 lf-ind-member ;
: lf-ind-ctor ( j -- decl ) lf-ind-types@ + lf-ind-member ;
: lf-ind-rec ( r -- decl ) lf-ind-types@ + lf-ind-ctors@ + lf-ind-member ;
: lf-ind-type-data ( -- data ) lf-ind-type lf-idecl-data ;
: lf-ind-name ( -- name ) lf-ind-type lf-idecl-name @ ;
: lf-ind-nparams ( -- n ) lf-ind-type-data lf-ity-params lf-more-field ;
: lf-ind-lparams ( -- params n ) lf-ind-type lf-idecl-params@ ;
: lf-ind-lparam ( i -- name ) cells lf-ind-lparams drop + @ ;
: lf-ind-ctor-type ( j -- root ) lf-ind-ctor lf-idecl-type @ ;
: lf-ind-domain ( i -- addr ) cells lf-ind-state lf-ind-domain-cells + ;
: lf-ind-nfields ( j -- addr ) cells lf-ind-state lf-ind-field-cells + ;
: lf-ind-minor-type ( j -- addr ) cells lf-ind-state lf-ind-minor-cells + ;
: lf-ind-rule ( j -- addr ) cells lf-ind-state lf-ind-rule-cells + ;

\ ---------------------------------------------------------------------------
\ Terms the checks read, all validated (V1) before they are read. A raw
\ Pi telescope's body and binder count; an application spine's head and
\ argument count; argument i (from 0) of a spine of n arguments.
: lf-ind-tag? ( node tag -- flag ) swap lf-term-tag@ = ;
: lf-ind-body ( node -- body k )
  0 begin over lf-tag-pi lf-ind-tag? while swap lf-term-second@ swap 1+ repeat ;
: lf-ind-spine ( node -- head n )
  0 begin over lf-tag-app lf-ind-tag? while swap lf-term-first@ swap 1+ repeat ;
: lf-ind-arg ( node n i -- arg ) - 1- 0 ?do lf-term-first@ loop lf-term-second@ ;
: lf-ind-bvar? ( node index -- flag )
  over lf-tag-bvar lf-ind-tag? if swap lf-term-first@ = else 2drop false then ;
\ A constant node's name; whether a node is the block's type, unapplied.
: lf-ind-const-name ( node -- name ) lf-term-first@ lf-cref-slot lf-crec-name @ ;
: lf-ind-type-node? ( node -- flag )
  dup lf-tag-constant lf-ind-tag? if lf-ind-const-name lf-ind-name lf-name-same?
  else drop false then ;
\ Whether a spine's head is the block's type.
: lf-ind-headed? ( node -- flag ) lf-ind-spine drop lf-ind-type-node? ;

\ ---------------------------------------------------------------------------
\ Opening the block of declaration i, the check's: (span ok), its
\ members recorded and span their number; (1 invalid) when i is not a
\ block's first member or its members do not fit in the input.
: lf-ind-take ( header -- )
  lf-ind-state /lf-ind erase
  dup lf-hdr-first lf-more-field lf-ind-state lf-ind-first !
  dup lf-hdr-types lf-more-field lf-ind-state lf-ind-types !
  dup lf-hdr-ctors lf-more-field lf-ind-state lf-ind-ctors !
  lf-hdr-recs lf-more-field lf-ind-state lf-ind-recs ! ;
: lf-ind-fits? ( i -- flag )
  dup lf-ind-first@ = lf-ind-members 0> and lf-ind-types@ 0> and
  swap lf-ind-members + lf-input-count upto? and ;
: lf-ind-open ( i -- span outcome )
  dup lf-input-decl lf-idecl-header ?dup 0= if drop 1 outcome-invalid exit then
  lf-ind-take lf-ind-fits? if lf-ind-members outcome-ok else 1 outcome-invalid then ;
\ Whether a declaration is a member of an inductive block.
: lf-ind-member? ( decl -- flag ) lf-idecl-block @ 0<> ;

\ ---------------------------------------------------------------------------
\ B0, the shape (ADR 0015 §4): every member points at this header and has
\ its kind's data; the type's all list is the type alone, and the
\ constructors are its ctors list in order, each naming the type; every
\ recursor names the type in its all list; the member names are
\ distinct. Anything else cannot come from lean4export: invalid. (Only
\ the kinds and header of a mutual block are checked here; the scope
\ check makes it unsupported.)
: lf-ind-kind-at ( k -- kind )
  dup lf-ind-types@ < if drop lf-kind-inductive exit then
  lf-ind-types@ lf-ind-ctors@ + < if lf-kind-constructor else lf-kind-recursor then ;
: lf-ind-member-ok? ( k -- flag )
  dup lf-ind-kind-at swap lf-ind-member
  dup lf-idecl-more @ 0<> over lf-idecl-block @ lf-ind-type lf-idecl-block @ = and
  swap lf-idecl-kind @ rot = and ;
: lf-ind-members-ok? ( -- flag ) true lf-ind-members 0 ?do i lf-ind-member-ok? and loop ;
\ Whether name is in a list of names.
: lf-ind-in? ( name items n -- flag )
  0 ?do 2dup i cells + @ lf-name-same? if 2drop true unloop exit then loop 2drop false ;
: lf-ind-all-ok? ( -- flag )
  lf-ind-type-data lf-ity-all@ 1 = if @ lf-ind-name lf-name-same? else drop false then ;
\ Constructor j: named as the type's ctors list says, naming the type.
: lf-ind-listed ( j -- name ) cells lf-ind-type-data lf-ity-ctors@ drop + @ ;
: lf-ind-induct ( j -- name ) lf-ind-ctor lf-idecl-data lf-ict-induct lf-more-field ;
: lf-ind-ctor-ok? ( j -- flag )
  dup lf-ind-ctor lf-idecl-name @ over lf-ind-listed lf-name-same?
  swap lf-ind-induct lf-ind-name lf-name-same? and ;
: lf-ind-ctors-ok? ( -- flag )
  lf-ind-type-data lf-ity-ctors@ nip lf-ind-ctors@ <> if false exit then
  true lf-ind-ctors@ 0 ?do i lf-ind-ctor-ok? and loop ;
: lf-ind-rec-ok? ( r -- flag )
  lf-ind-rec lf-idecl-data lf-irc-all@ lf-ind-name -rot lf-ind-in? ;
: lf-ind-recs-ok? ( -- flag ) true lf-ind-recs@ 0 ?do i lf-ind-rec-ok? and loop ;
\ Member names distinct: each against those after it. Two constructors of
\ one name are left to rule C4 (step 9 of check-block.fs): Lean's replay
\ looks both up by name and its kernel rejects the duplicate.
: lf-ind-name-at ( k -- name ) lf-ind-member lf-idecl-name @ ;
: lf-ind-ctor-at? ( k -- flag ) lf-ind-types@ dup lf-ind-ctors@ + within ;
: lf-ind-clash? ( k i -- flag )
  2dup lf-ind-ctor-at? swap lf-ind-ctor-at? and if 2drop false exit then
  lf-ind-name-at swap lf-ind-name-at lf-name-same? ;
: lf-ind-unique? ( k -- flag )
  lf-ind-members over 1+ ?do dup i lf-ind-clash? if drop false unloop exit then loop
  drop true ;
: lf-ind-distinct? ( -- flag ) true lf-ind-members 0 ?do i lf-ind-unique? and loop ;
: lf-ind-shape? ( -- flag )
  lf-ind-members-ok? 0= if false exit then
  lf-ind-types@ 1 > if lf-ind-distinct? exit then
  lf-ind-all-ok? lf-ind-ctors-ok? and lf-ind-recs-ok? and lf-ind-distinct? and ;
: lf-ind-b0 ( -- outcome )
  lf-ind-shape? if outcome-ok exit then
  lf-ind-first@ 0 lf-ind-site lf-diag-block-shape lf-diag-note outcome-invalid ;

\ ---------------------------------------------------------------------------
\ Every term of the block, in input order -- the types and constructor
\ types, the recursor types and their rules' right sides -- given to xt
\ ( root -- outcome ) until one is not ok.
: lf-ind-rhs@ ( rules k -- root ) lf-rule-at 2 cells + @ ;
: lf-ind-rules-each ( xt decl -- outcome )
  lf-idecl-data lf-irc-rules@ 0 ?do
    2dup i lf-ind-rhs@ swap execute dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
: lf-ind-recursor? ( decl -- flag ) lf-idecl-kind @ lf-kind-recursor = ;
: lf-ind-member-each ( xt k -- outcome )
  lf-ind-member 2dup lf-idecl-type @ swap execute dup ok? 0= if nip nip exit then drop
  dup lf-ind-recursor? if lf-ind-rules-each else 2drop outcome-ok then ;
: lf-ind-each ( xt -- outcome )
  lf-ind-members 0 ?do dup i lf-ind-member-each dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;

\ A walk over every node of a root on the block's fuel, with xt ( first
\ second walk tag -- outcome ) in walk-arg for each leaf; binary nodes
\ push their children, which must be earlier nodes.
: lf-ind-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop walk-children exit then over walk-arg @ execute ;
: lf-ind-visit ( walk -- outcome ) lf-terms ['] lf-ind-dispatch walk-visit ;
: lf-ind-walked ( outcome -- outcome )
  lf-ind-walker walk-fuel @ lf-ind-fuel ! lf-ind-walker lf-ind-site lf-diag-walk ;
: lf-ind-walk ( root leaf-xt -- outcome )
  lf-ind-walker walk-arg ! lf-ind-fuel @ lf-ind-walker walk-budget 0=
  if drop outcome-invalid exit then
  ['] lf-ind-visit lf-ind-walker walk-run lf-ind-walked ;

\ U2: no leaf of an unsupported form (core/unsupported-forms.fs).
: lf-ind-form ( first second walk tag -- outcome )
  lf-tag-unsupported = if nip walk-node @ lf-ind-site lf-diag-unsupported-form
    lf-diag-note outcome-unsupported else 2drop drop outcome-ok then ;
: lf-ind-forms ( root -- outcome ) ['] lf-ind-form lf-ind-walk ;
\ V1: a live root whose graph is well formed, every bound variable under
\ its binder.
: lf-ind-closed ( root -- outcome )
  dup lf-term-identity 0= if 0 lf-ind-site lf-diag-malformed lf-diag-note
    outcome-invalid exit then
  0 lf-ind-fuel @ lf-constant-term-scope lf-cts-fuel @ lf-ind-fuel ! ;

\ The scope of task 5.2.1a: one type, mentioned by a constructor type at
\ most once, as the head of its result.
: lf-ind-occurrence ( first second walk tag -- outcome )
  lf-tag-constant = if walk-node @ lf-ind-type-node? 1 and lf-ind-state lf-ind-count +!
  else drop then 2drop outcome-ok ;
: lf-ind-occurrences ( root -- n outcome )
  0 lf-ind-state lf-ind-count ! ['] lf-ind-occurrence lf-ind-walk
  lf-ind-state lf-ind-count @ swap ;
: lf-ind-ctor-scoped ( j -- outcome )
  lf-ind-ctor-type dup lf-ind-occurrences ok-then? 0= if nip exit then
  dup 0= if 2drop outcome-ok exit then
  1 = swap lf-ind-body drop lf-ind-headed? and
  if outcome-ok else outcome-unsupported then ;
: lf-ind-out-of-scope ( reason -- outcome )
  lf-ind-first@ swap lf-ind-site lf-diag-block-scope lf-diag-note outcome-unsupported ;
1 constant lf-scope-mutual
2 constant lf-scope-occurrence
: lf-ind-ctors-scoped ( -- outcome )
  lf-ind-ctors@ 0 ?do i lf-ind-ctor-scoped dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
: lf-ind-scoped ( -- outcome )
  lf-ind-types@ 1 > if lf-scope-mutual lf-ind-out-of-scope exit then
  lf-ind-ctors-scoped dup outcome-unsupported =
  if drop lf-scope-occurrence lf-ind-out-of-scope then ;

\ The audit, in this order: B0; unsafe members; U2, then V1, on every term;
\ the scope.
: lf-ind-safe? ( -- flag )
  true lf-ind-members 0 ?do i lf-ind-member lf-idecl-safety @ lf-safety-safe = and loop ;
: lf-ind-unsafe ( -- outcome )
  lf-kind-inductive lf-safety-unsafe lf-ind-site lf-diag-unsupported-kind lf-diag-note
  outcome-unsupported ;
: lf-ind-audit ( -- outcome )
  lf-ind-b0 dup ok? 0= if exit then drop
  lf-ind-safe? 0= if lf-ind-unsafe exit then
  ['] lf-ind-forms lf-ind-each dup ok? 0= if exit then drop
  ['] lf-ind-closed lf-ind-each dup ok? 0= if exit then drop
  lf-ind-scoped ;

\ ---------------------------------------------------------------------------
\ T0: no constant whose name starts with the component _nested, in the
\ type, then in each constructor type (rejected: Lean's "uses the
\ reserved prefix").
: lf-ind-root ( name -- root ) begin dup lf-name-prefix@ ?dup while nip repeat ;
: lf-ind-reserved? ( name -- flag )
  lf-ind-root dup lf-name-tag@ lf-name-tag-str =
  if lf-name-text s" _nested" compare 0= else drop false then ;
: lf-ind-prefix ( first second walk tag -- outcome )
  lf-tag-constant = 0= if 2drop drop outcome-ok exit then
  walk-node @ nip nip lf-ind-const-name lf-ind-reserved? 0= if outcome-ok exit then
  lf-ind-first@ 0 lf-ind-site lf-diag-reserved-prefix lf-diag-note outcome-rejected ;
: lf-ind-t0-term ( root -- outcome ) ['] lf-ind-prefix lf-ind-walk ;
: lf-ind-t0 ( -- outcome )
  lf-ind-type lf-idecl-type @ lf-ind-t0-term dup ok? 0= if exit then drop
  lf-ind-ctors@ 0 ?do
    i lf-ind-ctor-type lf-ind-t0-term dup ok? 0= if unloop exit then drop
  loop outcome-ok ;

\ C1, a paired walk of each constructor type: (node, binders around it).
\ A spine headed by the type with more arguments than parameters is
\ entered (its indices are checked too); with at most as many, it must
\ have exactly the parameters, at depth >= numParams, the universe
\ parameters as its levels, argument i the variable #(depth-1-i).
: lf-ind-param-level? ( level name -- flag )
  over lf-level-tag@ lf-level-tag-param = if swap lf-level-first@ lf-name-same?
  else 2drop false then ;
: lf-ind-level-at? ( pairs i -- flag )
  tuck lf-cref-pair@ drop swap lf-ind-lparam lf-ind-param-level? ;
: lf-ind-levels? ( cref -- flag )
  lf-cref-slot lf-cref-pairs dup lf-ind-lparams nip <> if 2drop false exit then
  true swap 0 ?do over i lf-ind-level-at? and loop nip ;
: lf-ind-arg-uniform? ( node depth i -- flag )
  tuck - 1- >r lf-ind-nparams swap lf-ind-arg r> lf-ind-bvar? ;
: lf-ind-args-uniform? ( node depth -- flag )
  lf-ind-nparams 0 ?do 2dup i lf-ind-arg-uniform? 0= if 2drop false unloop exit then
  loop 2drop true ;
: lf-c1-ok? ( node n depth -- flag )
  swap lf-ind-nparams <> if 2drop false exit then
  dup lf-ind-nparams < if 2drop false exit then
  over lf-ind-spine drop lf-term-first@ lf-ind-levels? 0= if 2drop false exit then
  lf-ind-args-uniform? ;
: lf-c1-reject ( node depth -- outcome )
  lf-ind-site lf-diag-nonuniform lf-diag-note outcome-rejected ;
: lf-c1-same ( first second walk -- outcome ) dup walk-context @ swap walk-children-at ;
: lf-c1-occurrence ( first second walk n -- outcome )
  dup lf-ind-nparams > if drop lf-c1-same exit then
  >r nip nip dup walk-node @ swap walk-context @ r> over >r
  2 pick swap rot lf-c1-ok? r> swap if 2drop outcome-ok else lf-c1-reject then ;
: lf-c1-app ( first second walk -- outcome )
  dup walk-node @ lf-ind-spine swap lf-ind-type-node? if lf-c1-occurrence
  else drop lf-c1-same then ;
: lf-c1-const ( first second walk -- outcome )
  dup walk-node @ lf-ind-type-node? if 0 lf-c1-occurrence exit then
  2drop drop outcome-ok ;
: lf-c1-binder ( first second walk -- outcome )
  dup walk-context @ 1+ swap walk-children-at ;
: lf-c1-dispatch ( first second walk tag -- outcome )
  case lf-tag-app of lf-c1-app endof  lf-tag-constant of lf-c1-const endof
    lf-tag-lam of lf-c1-binder endof  lf-tag-pi of lf-c1-binder endof
    >r 2drop drop outcome-ok r> endcase ;
: lf-c1-visit ( walk -- outcome ) lf-terms ['] lf-c1-dispatch walk-visit ;
: lf-c1-walked ( outcome -- outcome )
  lf-ind-pair-walker walk-fuel @ lf-ind-fuel !
  lf-ind-pair-walker lf-ind-site lf-diag-walk ;
: lf-c1-ctor ( j -- outcome )
  lf-ind-fuel @ lf-ind-pair-walker walk-budget 0= if drop outcome-invalid exit then
  lf-ind-ctor-type 0 ['] lf-c1-visit lf-ind-pair-walker walk-run-pair lf-c1-walked ;
: lf-ind-c1 ( -- outcome )
  lf-ind-ctors@ 0 ?do i lf-c1-ctor dup ok? 0= if unloop exit then drop loop outcome-ok ;

\ T1: at least numParams raw binders in the type (rejected: Lean's
\ "incorrect number of parameters").
: lf-ind-t1 ( -- outcome )
  lf-ind-type lf-idecl-type @ lf-ind-body nip
  dup lf-ind-nparams < 0= if drop outcome-ok exit then
  lf-ind-nparams lf-ind-site lf-diag-param-binders lf-diag-note outcome-rejected ;
