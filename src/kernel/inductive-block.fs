\ An inductive block in the checker's input, and the checks of ADR 0015
\ that read it without typing (plan tasks 5.2.1a and 5.2.1b; Lean
\ 4.35.0's inductive.cpp, commit eb6cafb7):
\   B0 the block's shape, as lean4export writes it (invalid otherwise);
\   the audit, before any typing, as check-declaration's audit of a
\     definition: a block of unsafe members skipped, as Lean's replay
\     skips them (rejected, reported skipped; with safe ones too,
\     unsupported; two constructors of one name rejected first, as
\     lean4export's parser refuses them), and the term
\     forms the checker lacks (U2) unsupported; loose variables invalid
\     (V1); whether the block may be nested (task 5.2.5b: translated at
\     step 4, inductive-nested.fs); on the way, Lean's is_rec and
\     is_reflexive;
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
\ [kernel] code: not through the review gate (AGENTS.md). The exported
\ numbers and flags are read here
\ only for the shape; check-block.fs compares the rest (B3, B4).
\ State: one record, lf-ind-state (the block, the facts computed so far,
\ the step reached, the fuel, the warnings), five slabs, lf-ind-ctor-cells
\ (per constructor its field count, minor premise, rule and restored
\ name), lf-ind-type-cells (per type its facts), the types' binder domains
\ lf-ind-domains, and a nested block's declarations lf-ind-aux-decls and
\ lf-ind-ctor-decls, and the walk records lf-ind-walker (U2, T0,
\ occurrences, nested occurrences), lf-ind-inner-walker (occurrences
\ within an argument, during a walk of lf-ind-walker) and
\ lf-ind-pair-walker (C1, with binder depths), all members of the
\ checker context (lib/context.fs).

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/constant-term-scope.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/levels.fs
require ../core/name-equal.fs
require ../core/names.fs
require ../core/projections.fs
require ../core/terms.fs
require ../core/unsupported-forms.fs
require ./environment.fs

begin-structure /lf-ind
  field: lf-ind-first        \ input index of the block's first member
  field: lf-ind-types        \ its members, from the header
  field: lf-ind-ctors
  field: lf-ind-recs
  field: lf-ind-step-reached \ the step of check-block.fs reached
  field: lf-ind-fuel-left    \ fuel left between steps
  field: lf-ind-warned       \ B4 warnings (check-block.fs's lf-warn-* bits)
  field: lf-ind-visible      \ true once the types are visible to inference
  field: lf-ind-level        \ computed: the first type's result Sort's level
  field: lf-ind-elim         \ computed: the elimination level, 0 for Prop
  field: lf-ind-elim-name    \ its parameter's name ID, 0 for Prop
  field: lf-ind-k            \ computed: K-like reduction target (flag)
  field: lf-ind-domains-used \ binder domains recorded in lf-ind-domains
  field: lf-ind-count        \ occurrences counted by a walk
  field: lf-ind-is-rec       \ computed: Lean's is_rec (a field mentions the type)
  field: lf-ind-is-refl      \ computed: Lean's is_reflexive
  field: lf-ind-large        \ the recursor has a motive universe of its own
  field: lf-ind-in-types     \ the input's types, constructors (the header's)
  field: lf-ind-in-ctors
  field: lf-ind-maybe        \ the audit met an occurrence that may be nested
  field: lf-ind-xlated       \ the constructors read are the translated ones
  field: lf-ind-aux          \ auxiliary types of a nested block (task 5.2.5b)
  field: lf-ind-leaf         \ the leaf visitor of the walk of lf-ind-walker
end-structure
/lf-ind context-record: lf-ind-state
\ Per constructor of the block, numbered across all its types, four
\ cells: its fields, its minor premise, its rule and, for B3, its name as
\ Lean's restored recursor names it; as many as the block has
\ constructors (plan task 6.2.0).
begin-structure /lf-ind-ctor
  field: lf-ictor-fields
  field: lf-ictor-minor
  field: lf-ictor-rule
  field: lf-ictor-name
end-structure
/lf-ind-ctor context-slab: lf-ind-ctor-cells
\ The B4 warning bits (check-block.fs step 14; on an accepted block's
\ slots, environment.fs lf-env-warnings).
1 constant lf-warn-indices
2 constant lf-warn-rec
4 constant lf-warn-reflexive
8 constant lf-warn-nested
16 constant lf-warn-no-recursor
\ Per type of the block (plan task 5.2.5a: a mutual block has several), as
\ many as it has (no fixed limit); one the heap cannot hold is full.
begin-structure /lf-ty
  field: lf-ty-indices       \ computed: numIndices, binders after the parameters
  field: lf-ty-domain        \ where its first index's domain is in lf-ind-domains
  field: lf-ty-ctor          \ its first constructor's number in the block
  field: lf-ty-ctors         \ its constructors
  field: lf-ty-motive        \ generated: its motive's type
  field: lf-ty-rec-type      \ generated: its recursor's type
  field: lf-ty-rec-name      \ the name T.rec
  field: lf-ty-key           \ an auxiliary type's nested occurrence I Ds
end-structure
/lf-ty context-slab: lf-ind-type-cells
\ A nested block (task 5.2.5b, inductive-nested.fs): the declarations
\ its auxiliary types stand for, and every constructor's with its
\ translated type, records of the input's layout (core/input.fs) that
\ the steps read in place of the input's; as many as it has.
/lf-idecl context-slab: lf-ind-aux-decls
/lf-idecl context-slab: lf-ind-ctor-decls
\ The types' binder domains: the first type's parameters and indices, then
\ each other type's indices; as many as the telescopes have (plan task
\ 6.2.0); one the heap cannot hold is full.
1 cells context-slab: lf-ind-domains
lf-walk-room context-walk: lf-ind-walker
lf-walk-room context-walk: lf-ind-inner-walker
lf-walk-room context-walk2: lf-ind-pair-walker

: lf-ind-site ( -- site ) c" inductive-block lf-ind-audit" ;
: lf-ind-first@ ( -- i ) lf-ind-state lf-ind-first @ ;
: lf-ind-types@ ( -- n ) lf-ind-state lf-ind-types @ ;
: lf-ind-ctors@ ( -- n ) lf-ind-state lf-ind-ctors @ ;
: lf-ind-recs@ ( -- n ) lf-ind-state lf-ind-recs @ ;
\ The block's types and constructors are the input's (lf-ind-in-types@,
\ lf-ind-in-ctors@), and for a nested block, from step 4 on, also its
\ auxiliary types' (lf-ind-types@, lf-ind-ctors@; inductive-nested.fs).
: lf-ind-in-types@ ( -- n ) lf-ind-state lf-ind-in-types @ ;
: lf-ind-in-ctors@ ( -- n ) lf-ind-state lf-ind-in-ctors @ ;
: lf-ind-aux@ ( -- n ) lf-ind-state lf-ind-aux @ ;
: lf-ind-members ( -- n ) lf-ind-in-types@ lf-ind-in-ctors@ + lf-ind-recs@ + ;
: lf-ind-fuel ( -- addr ) lf-ind-state lf-ind-fuel-left ;
\ Member k of the block (from 0), the type, constructor j and recursor r.
\ Unchecked: k is below lf-ind-members, which lf-ind-open checked. A
\ constructor of a translated block is its record in lf-ind-ctor-decls.
: lf-ind-member ( k -- decl ) lf-ind-first@ + lf-input-decl ;
: lf-ind-type ( -- decl ) 0 lf-ind-member ;
: lf-ind-xlated? ( -- flag ) lf-ind-state lf-ind-xlated @ ;
: lf-ind-ctor ( j -- decl )
  lf-ind-xlated? if lf-ind-ctor-decls slab-at exit then lf-ind-in-types@ + lf-ind-member ;
: lf-ind-rec ( r -- decl ) lf-ind-in-types@ + lf-ind-in-ctors@ + lf-ind-member ;
: lf-ind-type-data ( -- data ) lf-ind-type lf-idecl-data ;
: lf-ind-name ( -- name ) lf-ind-type lf-idecl-name @ ;
: lf-ind-nparams ( -- n ) lf-ind-type-data lf-ity-params lf-more-field ;
: lf-ind-lparams ( -- params n ) lf-ind-type lf-idecl-params@ ;
: lf-ind-lparam ( i -- name ) cells lf-ind-lparams drop + @ ;
: lf-ind-ctor-type ( j -- root ) lf-ind-ctor lf-idecl-type @ ;
: lf-ind-domain ( i -- addr ) cells lf-ind-domains slab-base + ;
\ Constructor j's cells; an address is valid until the slab next grows
\ (lf-ind-open).
: lf-ind-nfields ( j -- addr ) lf-ind-ctor-cells slab-at lf-ictor-fields ;
: lf-ind-minor-type ( j -- addr ) lf-ind-ctor-cells slab-at lf-ictor-minor ;
: lf-ind-rule ( j -- addr ) lf-ind-ctor-cells slab-at lf-ictor-rule ;
\ Type d of the block (from 0): its declaration (an auxiliary type's in
\ lf-ind-aux-decls), name, type, record, its number of indices and the
\ domain of its index i.
: lf-ind-aux-decl ( d -- decl ) lf-ind-in-types@ - lf-ind-aux-decls slab-at ;
: lf-ind-type-at ( d -- decl )
  dup lf-ind-in-types@ < if lf-ind-member else lf-ind-aux-decl then ;
: lf-ind-tname ( d -- name ) lf-ind-type-at lf-idecl-name @ ;
: lf-ind-ty ( d -- addr ) lf-ind-type-cells slab-at ;
: lf-ind-n ( d -- n ) lf-ind-ty lf-ty-indices @ ;
: lf-ind-index-domain ( d i -- addr ) swap lf-ind-ty lf-ty-domain @ + lf-ind-domain ;
\ The type that constructor j builds: d with ctor(d) <= j < ctor(d+1).
: lf-ind-owner ( j -- d )
  lf-ind-types@ 1 ?do dup i lf-ind-ty lf-ty-ctor @ < if drop i 1- unloop exit then loop
  drop lf-ind-types@ 1- ;

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
\ A constant node's name; which type of the block a node is, unapplied:
\ d, or -1 for none; whether it is one.
: lf-ind-const-name ( node -- name ) lf-term-first@ lf-cref-slot lf-crec-name @ ;
: lf-ind-which-name ( name -- d )
  lf-ind-types@ 0 ?do dup i lf-ind-tname lf-name-same? if drop i unloop exit then loop
  drop -1 ;
: lf-ind-which ( node -- d )
  dup lf-tag-constant lf-ind-tag? 0= if drop -1 exit then
  lf-ind-const-name lf-ind-which-name ;
: lf-ind-type-node? ( node -- flag ) lf-ind-which 0< 0= ;
\ Whether a spine's head is a type of the block.
: lf-ind-headed? ( node -- flag ) lf-ind-spine drop lf-ind-type-node? ;

\ ---------------------------------------------------------------------------
\ Opening the block of declaration i, the check's: (span ok), its
\ members recorded and span their number, and every constructor's cells
\ zero; (1 invalid) when i is not a block's first member or its members
\ do not fit in the input; (span full) when the heap cannot grow the
\ constructors' cells for them all (no fixed limit since plan task
\ 6.2.0), found before anything is written to them (review rvI21, B1).
\ Each count is first checked to lie within the input, so their sum
\ cannot wrap.
: lf-ind-take ( header -- )
  lf-ind-state /lf-ind erase
  dup lf-hdr-first lf-more-field lf-ind-state lf-ind-first !
  dup lf-hdr-types lf-more-field dup lf-ind-state lf-ind-types !
  lf-ind-state lf-ind-in-types !
  dup lf-hdr-ctors lf-more-field dup lf-ind-state lf-ind-ctors !
  lf-ind-state lf-ind-in-ctors !
  lf-hdr-recs lf-more-field lf-ind-state lf-ind-recs ! ;
: lf-ind-count? ( n -- flag ) lf-input-count upto? ;
: lf-ind-counts? ( -- flag )
  lf-ind-types@ lf-ind-count? lf-ind-ctors@ lf-ind-count? and
  lf-ind-recs@ lf-ind-count? and ;
: lf-ind-fits? ( i -- flag )
  lf-ind-counts? 0= if drop false exit then
  dup lf-ind-first@ = lf-ind-members 0> and lf-ind-types@ 0> and
  swap lf-ind-members + lf-input-count upto? and ;
: lf-ind-crowded ( -- span outcome )
  lf-ind-ctors@ lf-ind-ctor-cells slab-capacity lf-ind-site lf-diag-ctors-full
  lf-diag-note lf-ind-members outcome-full ;
: lf-ind-zeroed ( -- )
  0 lf-ind-ctor-cells slab-at lf-ind-ctors@ /lf-ind-ctor * erase ;
: lf-ind-sized ( -- span outcome )
  lf-ind-ctors@ lf-ind-ctor-cells slab-hold ok? 0= if lf-ind-crowded exit then
  lf-ind-zeroed lf-ind-members lf-ind-types@ lf-ind-type-cells slab-hold ;
\ An empty block (ADR 0016 amendment 1): no member but the one declaration
\ the importer added for it (lf-kind-block), which is the header's first;
\ (1 ok), and check-block.fs rejects it (lf-ind-empty?).
: lf-ind-empty? ( -- flag ) lf-ind-members 0= ;
: lf-ind-open ( i -- span outcome )
  dup lf-input-decl lf-idecl-header ?dup 0= if drop 1 outcome-invalid exit then
  lf-ind-take dup lf-ind-first@ = lf-ind-empty? and if drop 1 outcome-ok exit then
  lf-ind-fits? if lf-ind-sized else 1 outcome-invalid then ;
\ Whether a declaration is a member of an inductive block.
: lf-ind-member? ( decl -- flag ) lf-idecl-block @ 0<> ;

\ ---------------------------------------------------------------------------
\ B0, the shape (ADR 0015 §4): every member points at this header and has
\ its kind's data; each type's all list is the block's types in order, with
\ the first type's universe parameters and numParams; the constructors are
\ the types' ctors lists in order, each naming its type; every recursor
\ names the first type in its all list; the member names are distinct.
\ Anything else cannot come from lean4export: invalid.
: lf-ind-kind-at ( k -- kind )
  dup lf-ind-in-types@ < if drop lf-kind-inductive exit then
  lf-ind-in-types@ lf-ind-in-ctors@ + <
  if lf-kind-constructor else lf-kind-recursor then ;
: lf-ind-member-ok? ( k -- flag )
  dup lf-ind-kind-at swap lf-ind-member
  dup lf-idecl-more @ 0<> over lf-idecl-block @ lf-ind-type lf-idecl-block @ = and
  swap lf-idecl-kind @ rot = and ;
: lf-ind-members-ok? ( -- flag ) lf-ind-members ['] lf-ind-member-ok? all? ;
\ Whether name is in a list of names; two lists equal name by name.
: lf-ind-in-at? ( name items i -- name items flag )
  2dup-under lf-param@ lf-name-same? ;
: lf-ind-in? ( name items n -- flag ) ['] lf-ind-in-at? any? nip nip ;
: lf-ind-same-at? ( items items' i -- items items' flag )
  2dup-under tuck lf-param@ >r lf-param@ r> lf-name-same? ;
: lf-ind-names= ( items n items' n' -- flag )
  rot over <> if drop 2drop false exit then ['] lf-ind-same-at? all? nip nip ;
\ The block's types' names, as the first type's all list holds them once
\ B0 passed.
: lf-ind-all ( -- items n ) lf-ind-type-data lf-ity-all@ ;
: lf-ind-all-at? ( items n -- flag )
  dup lf-ind-types@ <> if 2drop false exit then
  true swap 0 ?do over i cells + @ i lf-ind-tname lf-name-same? and loop nip ;
: lf-ind-type-ok? ( d -- flag )
  lf-ind-type-at dup lf-idecl-data dup lf-ity-all@ lf-ind-all-at?
  swap lf-ity-params lf-more-field lf-ind-nparams = and
  swap lf-idecl-params@ lf-ind-lparams lf-ind-names= and ;
: lf-ind-types-ok? ( -- flag ) lf-ind-types@ ['] lf-ind-type-ok? all? ;
\ Each type's constructors, from its ctors list: the first's number in the
\ block and how many; true when they are the block's constructors.
: lf-ind-ctors-of ( d -- items n ) lf-ind-type-at lf-idecl-data lf-ity-ctors@ ;
: lf-ind-layout ( -- flag )
  0 lf-ind-types@ 0 ?do
    dup i lf-ind-ty lf-ty-ctor ! i lf-ind-ctors-of nip dup i lf-ind-ty lf-ty-ctors ! +
  loop lf-ind-ctors@ = ;
\ Constructor j: named as its type's ctors list says, naming its type.
: lf-ind-listed ( j -- name )
  dup lf-ind-owner tuck lf-ind-ty lf-ty-ctor @ - cells swap lf-ind-ctors-of drop + @ ;
: lf-ind-induct ( j -- name ) lf-ind-ctor lf-idecl-data lf-ict-induct lf-more-field ;
: lf-ind-ctor-ok? ( j -- flag )
  dup lf-ind-ctor lf-idecl-name @ over lf-ind-listed lf-name-same?
  over lf-ind-induct rot lf-ind-owner lf-ind-tname lf-name-same? and ;
: lf-ind-ctors-ok? ( -- flag )
  lf-ind-layout 0= if false exit then
  lf-ind-ctors@ ['] lf-ind-ctor-ok? all? ;
: lf-ind-rec-ok? ( r -- flag )
  lf-ind-rec lf-idecl-data lf-irc-all@ lf-ind-name -rot lf-ind-in? ;
: lf-ind-recs-ok? ( -- flag ) lf-ind-recs@ ['] lf-ind-rec-ok? all? ;
\ Member names distinct: each against those after it. Two constructors of
\ one name are left to rule C4 (step 9 of check-block.fs): Lean's replay
\ looks both up by name and its kernel rejects the duplicate.
: lf-ind-name-at ( k -- name ) lf-ind-member lf-idecl-name @ ;
: lf-ind-ctor-at? ( k -- flag ) lf-ind-in-types@ dup lf-ind-in-ctors@ + within ;
: lf-ind-clash? ( k i -- flag )
  2dup lf-ind-ctor-at? swap lf-ind-ctor-at? and if 2drop false exit then
  lf-ind-name-at swap lf-ind-name-at lf-name-same? ;
: lf-ind-unique? ( k -- flag )
  lf-ind-members over 1+ ?do dup i lf-ind-clash? if drop false unloop exit then loop
  drop true ;
: lf-ind-distinct? ( -- flag ) lf-ind-members ['] lf-ind-unique? all? ;
: lf-ind-shape? ( -- flag )
  lf-ind-members-ok? 0= if false exit then
  lf-ind-types-ok? 0= if false exit then
  lf-ind-ctors-ok? lf-ind-recs-ok? and lf-ind-distinct? and ;
: lf-ind-b0 ( -- outcome )
  lf-ind-shape? if outcome-ok exit then
  lf-ind-first@ 0 lf-ind-site lf-diag-block-shape lf-diag-note outcome-invalid ;

\ ---------------------------------------------------------------------------
\ Every term of the block, in input order -- the types and constructor
\ types, the recursor types and their rules' right sides -- given to xt
\ ( root -- outcome ) until one is not ok.
: lf-ind-rhs@ ( rules k -- root ) lf-irc-rule lf-irule-rhs ;
: lf-ind-rules-each ( xt decl -- outcome )
  lf-idecl-data lf-irc-rules@ 0 ?do
    2dup i lf-ind-rhs@ swap execute dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
: lf-ind-recursor? ( decl -- flag ) lf-idecl-kind @ lf-kind-recursor = ;
: lf-ind-member-each ( xt k -- outcome )
  lf-ind-member 2dup lf-idecl-type @ swap execute dup ok? 0= if nip nip exit then drop
  dup lf-ind-recursor? if lf-ind-rules-each else 2drop outcome-ok then ;
: lf-ind-member-at ( xt i -- xt outcome ) over swap lf-ind-member-each ;
: lf-ind-each ( xt -- outcome ) lf-ind-members ['] lf-ind-member-at ok-each nip ;

\ A walk over every node of a root on the block's fuel, with xt ( first
\ second walk tag -- outcome ) for each leaf (lf-ind-leaf); binary nodes
\ push their children, which must be earlier nodes. Each node is visited
\ once, however many paths reach it (constant-term-boundary.fs's marks):
\ as Lean's find and for_each visit each shared term once
\ (for_each_fn.cpp's caches), so a walk grows with the nodes, never with
\ the paths; a node reached again costs its visit's unit only. Every test
\ these walks make at a node depends on the node alone.
: lf-ind-leaf! ( xt -- ) lf-ind-state lf-ind-leaf ! ;
: lf-ind-branch ( first second walk tag xt -- outcome )
  over lf-term-binary-tag? if 2drop walk-children else execute then ;
: lf-ind-dispatch ( first second walk tag -- outcome )
  lf-ind-state lf-ind-leaf @ lf-ind-branch ;
: lf-ind-once ( first second walk tag -- outcome ) ['] lf-ind-dispatch lf-walk-once ;
: lf-ind-visit ( walk -- outcome ) ['] lf-ind-once lf-term-visit ;
: lf-ind-walked ( outcome -- outcome )
  lf-ind-walker walk-fuel @ lf-ind-fuel ! lf-ind-walker lf-ind-site lf-diag-walk ;
\ A walk of root by the visitor visit-xt ( walk -- outcome ), a run of
\ its own (its marks).
: lf-ind-run ( root visit-xt -- outcome )
  lf-ind-fuel @ lf-ind-walker walk-budget 0= if 2drop outcome-invalid exit then
  lf-ind-walker lf-walk-marking lf-ind-walker walk-run lf-ind-walked ;
: lf-ind-walk ( root leaf-xt -- outcome ) lf-ind-leaf! ['] lf-ind-visit lf-ind-run ;

\ U2: no leaf of an unsupported form (core/unsupported-forms.fs). A root
\ with a data word holds none (core/terms.fs computes the word from the
\ children; such a leaf has none, nor has any node above one), as
\ check-declaration.fs's U2 reads it: it passes at once.
: lf-ind-form ( first second walk tag -- outcome )
  lf-tag-unsupported = if nip walk-node @ lf-ind-site lf-diag-unsupported-form
    lf-diag-note outcome-unsupported else 2drop drop outcome-ok then ;
: lf-ind-forms ( root -- outcome )
  dup lf-term-data@ if 2drop outcome-ok exit then ['] lf-ind-form lf-ind-walk ;
\ V1: a live root whose graph is well formed, every bound variable under
\ its binder.
: lf-ind-closed ( root -- outcome )
  dup lf-term-identity 0= if 0 lf-ind-site lf-diag-malformed lf-diag-note
    outcome-invalid exit then
  0 lf-ind-fuel @ lf-constant-term-scope lf-cts-fuel @ lf-ind-fuel ! ;

\ Occurrences of the block's types in a term, by a walk on the block's
\ fuel: n is zero when root mentions none (Lean's has_ind_occ, a find,
\ inductive.cpp 420-422), else the occurrence nodes the walk reached,
\ each once (not the paths to them).
: lf-ind-occurrence ( first second walk tag -- outcome )
  lf-tag-constant = if walk-node @ lf-ind-type-node? 1 and lf-ind-state lf-ind-count +!
  else drop then 2drop outcome-ok ;
: lf-ind-occurrences ( root -- n outcome )
  0 lf-ind-state lf-ind-count ! ['] lf-ind-occurrence lf-ind-walk
  lf-ind-state lf-ind-count @ swap ;
\ Whether root mentions no type of the block.
: lf-ind-free? ( root -- flag outcome )
  lf-ind-occurrences ok-then? if 0= outcome-ok else false swap then ;
\ The same within a walk of lf-ind-walker, on its fuel: a walk of its own
\ (lf-ind-inner-walker, a run of its own, each node once, Lean's find
\ with its per-call cache), whose fuel goes back to the outer walk;
\ whether root mentions the type. Its marks are kept in the pair set
\ (constant-term-boundary.fs's lf-walk-once-aside), never in the units,
\ so a node the outer walk has visited is not visited by it again (review
\ rvKN 2). A budget the walk refuses (negative, which the outer walk's
\ fuel never is) is invalid, as for lf-ind-run.
: lf-ind-inner-dispatch ( first second walk tag -- outcome )
  ['] lf-ind-occurrence lf-ind-branch ;
: lf-ind-inner-once ( first second walk tag -- outcome )
  ['] lf-ind-inner-dispatch lf-walk-once-aside ;
: lf-ind-inner-visit ( walk -- outcome ) ['] lf-ind-inner-once lf-term-visit ;
: lf-ind-inner-run ( root -- outcome )
  lf-ind-walker walk-fuel @ lf-ind-inner-walker walk-budget 0=
  if drop outcome-invalid exit then
  lf-ind-inner-walker lf-walk-pairing
  ['] lf-ind-inner-visit lf-ind-inner-walker walk-run
  lf-ind-inner-walker walk-fuel @ lf-ind-walker walk-fuel !
  lf-ind-inner-walker lf-ind-site lf-diag-walk ;
: lf-ind-mentions? ( root -- flag outcome )
  0 lf-ind-state lf-ind-count ! lf-ind-inner-run
  lf-ind-state lf-ind-count @ 0<> swap ;

\ Nested occurrences (task 5.2.5b). Lean's elim_nested_inductive
\ (inductive.cpp 1023-1055, 1133-1176) replaces, anywhere in a
\ constructor's type after its parameters, each application I Ds is of an
\ inductive type I of its environment whose parametric arguments Ds
\ mention a type being declared, and checks the block as a mutual one
\ with I's types copied in (inductive-nested.fs, at step 4). The audit
\ only notes whether the block may have one (lf-ind-maybe), by a test
\ that may find more than Lean's, never less: on every application node
\ there (Lean's replace descends into a function that is no such
\ occurrence, so its partial applications are tested too), its head a
\ constant naming an earlier inductive type of the input (Lean's
\ environment holds at most those), the block's type in one of its first
\ numParams arguments -- in any argument when that type is not usable,
\ its numParams then not known to be Lean's. A block without one is
\ checked as before, unchanged. Occurrences in a parameter's domain are
\ left to C1, which rejects them.
\ An earlier inductive type named name: its declaration, or -1.
: lf-ind-earlier ( name -- d ) ['] lf-slot-type? lf-env-limit lf-env-first ;
\ The leading arguments of an application of n arguments, headed by the
\ earlier type d, that may be its parametric ones: numParams when d is
\ usable (B3 compared it with Lean's), none when that is more than n.
: lf-ind-usable? ( d -- flag ) lf-env-readable if lf-slot-usable? else false then ;
: lf-ind-parametric ( n d -- k )
  dup lf-ind-usable? 0= if drop exit then
  lf-input-decl lf-idecl-data lf-ity-params lf-more-field
  2dup < if 2drop 0 else nip then ;
\ Whether one of the first k of the n arguments of node's spine mentions
\ the type.
: lf-ind-arg-mentions? ( node n i -- node n flag outcome )
  2dup-under lf-ind-arg lf-ind-mentions? ;
: lf-ind-some-arg? ( node n k -- flag outcome )
  ['] lf-ind-arg-mentions? ok-any? 2swap 2drop ;
: lf-ind-no-nest ( x -- false outcome ) drop false outcome-ok ;
: lf-ind-nested? ( node -- flag outcome )
  dup lf-ind-spine over lf-tag-constant lf-ind-tag? 0= if 2drop lf-ind-no-nest exit then
  over lf-ind-type-node? if 2drop lf-ind-no-nest exit then
  swap lf-ind-const-name lf-ind-earlier dup 0< if 2drop lf-ind-no-nest exit then
  over swap lf-ind-parametric lf-ind-some-arg? ;
\ The walk: at an application node that may be a nested occurrence, the
\ block is noted and the node's children are not visited; every other
\ node's are (each node once, the test depending on the node alone).
: lf-ind-maybe! ( -- ) true lf-ind-state lf-ind-maybe ! ;
: lf-ind-nest-app ( first second walk -- outcome )
  dup walk-node @ lf-ind-nested? ok-then? 0= if >r 2drop drop r> exit then
  if 2drop drop lf-ind-maybe! outcome-ok else walk-children then ;
: lf-ind-nest-dispatch ( first second walk tag -- outcome )
  dup lf-tag-app = if drop lf-ind-nest-app else lf-ind-dispatch then ;
: lf-ind-nest-once ( first second walk tag -- outcome )
  ['] lf-ind-nest-dispatch lf-walk-once ;
: lf-ind-nest-visit ( walk -- outcome ) ['] lf-ind-nest-once lf-term-visit ;
: lf-ind-no-leaf ( first second walk tag -- outcome ) 2drop 2drop outcome-ok ;
: lf-ind-nests ( root -- outcome )
  ['] lf-ind-no-leaf lf-ind-leaf! ['] lf-ind-nest-visit lf-ind-run ;
\ Constructor j's type after its parameters (where its binders end, if
\ before them: T1 rejects it later).
: lf-ind-after-params ( j -- node )
  lf-ind-ctor-type lf-ind-nparams 0 ?do
    dup lf-tag-pi lf-ind-tag? 0= if leave then lf-term-second@
  loop ;
\ On the way, for B4: Lean's is_rec, a field whose type mentions the type
\ (inductive.cpp 308-329), and is_reflexive, such a field type that is a
\ Pi (337-352), both syntactic.
: lf-ind-flag! ( addr -- ) true swap ! ;
: lf-ind-field-flags ( domain -- outcome )
  dup lf-ind-occurrences ok-then? 0= if nip exit then
  0= if drop outcome-ok exit then lf-ind-state lf-ind-is-rec lf-ind-flag!
  lf-tag-pi lf-ind-tag? if lf-ind-state lf-ind-is-refl lf-ind-flag! then outcome-ok ;
: lf-ind-fields-flags ( node -- outcome )
  begin dup lf-tag-pi lf-ind-tag? while
    dup lf-term-first@ lf-ind-field-flags dup ok? 0= if nip exit then drop lf-term-second@
  repeat drop outcome-ok ;
: lf-ind-ctor-scoped ( j -- outcome )
  lf-ind-after-params dup lf-ind-fields-flags dup ok? 0= if nip exit then
  drop lf-ind-nests ;
\ A block whose constructors mention the type at most once each, as the
\ head of their result, is not nested at once (task 5.2.1a's test): no
\ field mentions the type, and no other occurrence can be nested. Read
\ leaf by leaf: no domain of the constructor's raw telescope mentions a
\ type of the block, nor any argument of its result's spine, nor its
\ head unless the head is such a type.
: lf-ind-domains-free? ( node -- body flag outcome )
  begin dup lf-tag-pi lf-ind-tag? while
    dup lf-term-first@ lf-ind-free? ok-then? 0= if false swap exit then
    0= if false outcome-ok exit then lf-term-second@
  repeat true outcome-ok ;
: lf-ind-arg-free? ( node n i -- node n flag outcome )
  2dup-under lf-ind-arg lf-ind-free? ;
: lf-ind-args-free? ( node n -- flag outcome )
  dup ['] lf-ind-arg-free? ok-all? 2swap 2drop ;
: lf-ind-head-free? ( head -- flag outcome )
  dup lf-ind-type-node? if drop true outcome-ok else lf-ind-free? then ;
: lf-ind-result-plain? ( body -- flag outcome )
  dup lf-ind-spine >r lf-ind-head-free? ok-then? 0= if nip r> drop false swap exit then
  0= if drop r> drop false outcome-ok exit then r> lf-ind-args-free? ;
: lf-ind-plain? ( j -- flag outcome )
  lf-ind-ctor-type lf-ind-domains-free? ok-then? 0= if nip false swap exit then
  if lf-ind-result-plain? else drop false outcome-ok then ;
: lf-ind-ctors-plain? ( -- flag outcome ) lf-ind-ctors@ ['] lf-ind-plain? ok-all? ;
: lf-ind-ctors-scoped ( -- outcome ) lf-ind-ctors@ ['] lf-ind-ctor-scoped ok-each ;
: lf-ind-scoped ( -- outcome )
  lf-ind-ctors-plain? ok-then? 0= if exit then if outcome-ok exit then
  lf-ind-ctors-scoped ;
\ Whether the audit noted a possible nested occurrence.
: lf-ind-maybe? ( -- flag ) lf-ind-state lf-ind-maybe @ ;
\ Whether some field of the block mentions its type (after the audit).
: lf-ind-recursive? ( -- flag ) lf-ind-state lf-ind-is-rec @ ;
\ The same flags again on a translated block (task 5.2.5b), as Lean's
\ add_inductive_fn computes them on the auxiliary block: every
\ constructor's fields, the auxiliary types' too, mentioning any of its
\ types.
: lf-ind-ctor-flags ( j -- outcome ) lf-ind-after-params lf-ind-fields-flags ;
: lf-ind-flags-again ( -- outcome )
  false lf-ind-state lf-ind-is-rec ! false lf-ind-state lf-ind-is-refl !
  lf-ind-ctors@ ['] lf-ind-ctor-flags ok-each ;

\ The audit, in this order: B0; unsafe members; U2, then V1, on every
\ term; the scope. (A member named Nat.pow or Nat.shiftLeft was
\ unsupported until plan task 5.2.3 computed Lean's refusal,
\ kernel/reduce-nat.fs.)
\ Unsafe members (plan task 5.2.7): a block whose members are all unsafe,
\ as Lean writes one, is skipped as Lean's replay skips it (Replay.lean
\ 180-183; environment.fs lf-env-skip); one with both kinds, which Lean
\ never writes, stays unsupported (diagnostic 42): replay would add the
\ block when one type is safe, compare only its safe members, and refuse
\ a safe constructor or recursor of a skipped type (task 5.2.7, part b).
\ Either way, two constructors of one name are rejected first: B0 leaves
\ them to C4 (step 9), which such a block never reaches, and
\ lean4export's parser refuses the file, as it refuses any name given
\ twice (Parse.lean 78-80; review rvUNNI B1). Diagnostic: already
\ declared, the later constructor's name and the earlier's declaration.
: lf-ind-safe-at? ( k -- flag ) lf-ind-member lf-idecl-safety @ lf-safety-safe = ;
: lf-ind-safe? ( -- flag ) lf-ind-members ['] lf-ind-safe-at? all? ;
: lf-ind-any-safe? ( -- flag ) lf-ind-members ['] lf-ind-safe-at? any? ;
: lf-ind-mixed ( -- outcome )
  lf-kind-inductive lf-safety-unsafe lf-ind-site lf-diag-unsupported-kind lf-diag-note
  outcome-unsupported ;
\ Constructor j's member number and name, before any translation.
: lf-ind-ctor-k ( j -- k ) lf-ind-in-types@ + ;
: lf-ind-ctor-named ( j -- name ) lf-ind-ctor-k lf-ind-name-at ;
\ The first constructor before j with j's name, or -1.
: lf-ind-twin ( j -- j'|-1 )
  dup lf-ind-ctor-named swap 0 ?do
    dup i lf-ind-ctor-named lf-name-same? if drop i unloop exit then
  loop drop -1 ;
: lf-ind-given-twice ( j j' -- outcome )
  lf-ind-ctor-k lf-ind-first@ + swap lf-ind-ctor-named swap lf-ind-site
  lf-diag-already-declared lf-diag-note outcome-rejected ;
: lf-ind-ctors-once ( -- outcome )
  lf-ind-in-ctors@ 0 ?do
    i lf-ind-twin dup 0< 0= if i swap lf-ind-given-twice unloop exit then drop
  loop outcome-ok ;
: lf-ind-unsafe ( -- outcome )
  lf-ind-ctors-once dup ok? 0= if exit then drop
  lf-ind-any-safe? if lf-ind-mixed exit then
  lf-kind-inductive lf-safety-unsafe lf-ind-members lf-env-skip ;
: lf-ind-audit ( -- outcome )
  lf-ind-b0 dup ok? 0= if exit then drop
  lf-ind-safe? 0= if lf-ind-unsafe exit then
  ['] lf-ind-forms lf-ind-each dup ok? 0= if exit then drop
  ['] lf-ind-closed lf-ind-each dup ok? 0= if exit then drop
  lf-ind-scoped ;

\ ---------------------------------------------------------------------------
\ T0: no constant whose name starts with the component _nested, and no
\ projection whose structure's name does (the proj clause, 1228: the
\ translation rewrites a nested occurrence to the auxiliary type, so such
\ a projection would type-check against it and name, once restored, a
\ constant that does not exist; review rvUNNI M3), in the type, then in
\ each constructor type (rejected: Lean's "uses the reserved prefix").
: lf-ind-root ( name -- root ) begin dup lf-name-prefix@ ?dup while nip repeat ;
: lf-ind-reserved? ( name -- flag )
  lf-ind-root dup lf-name-tag@ lf-name-tag-str =
  if lf-name-text s" _nested" compare 0= else drop false then ;
\ The name a leaf names, as T0 reads it: a constant's, a projection
\ leaf's structure's (its first field), else 0.
: lf-ind-leaf-name ( first walk tag -- name|0 )
  case lf-tag-constant of nip walk-node @ lf-ind-const-name endof
    lf-tag-proj of drop endof  >r 2drop 0 r> endcase ;
: lf-ind-prefix ( first second walk tag -- outcome )
  rot drop lf-ind-leaf-name ?dup 0= if outcome-ok exit then
  lf-ind-reserved? 0= if outcome-ok exit then
  lf-ind-first@ 0 lf-ind-site lf-diag-reserved-prefix lf-diag-note outcome-rejected ;
: lf-ind-t0-term ( root -- outcome ) ['] lf-ind-prefix lf-ind-walk ;
: lf-ind-t0-type ( k -- outcome ) lf-ind-type-at lf-idecl-type @ lf-ind-t0-term ;
: lf-ind-t0-ctor ( k -- outcome ) lf-ind-ctor-type lf-ind-t0-term ;
: lf-ind-t0-ctors ( -- outcome ) lf-ind-ctors@ ['] lf-ind-t0-ctor ok-each ;
: lf-ind-t0 ( -- outcome )
  lf-ind-types@ ['] lf-ind-t0-type ok-each ['] lf-ind-t0-ctors ok-and ;

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
: lf-ind-arg-uniform-at? ( node depth i -- node depth flag )
  2dup-under lf-ind-arg-uniform? ;
: lf-ind-args-uniform? ( node depth -- flag )
  lf-ind-nparams ['] lf-ind-arg-uniform-at? all? nip nip ;
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
    lf-tag-let of lf-c1-same endof  lf-tag-let-nondep of lf-c1-same endof
    lf-tag-projection of lf-c1-same endof
    >r 2drop drop outcome-ok r> endcase ;
\ Each (node, depth) pair once (constant-term-boundary.fs's exact marks
\ and pair set, as Lean's for_each with an offset visits it,
\ for_each_fn.cpp's cache): the test of an occurrence depends on its
\ depth.
: lf-c1-once ( first second walk tag -- outcome ) ['] lf-c1-dispatch lf-walk-once-at ;
: lf-c1-visit ( walk -- outcome ) ['] lf-c1-once lf-term-visit ;
: lf-c1-walked ( outcome -- outcome )
  lf-ind-pair-walker walk-fuel @ lf-ind-fuel !
  lf-ind-pair-walker lf-ind-site lf-diag-walk ;
: lf-c1-ctor ( j -- outcome )
  lf-ind-fuel @ lf-ind-pair-walker walk-budget 0= if drop outcome-invalid exit then
  lf-ind-pair-walker lf-walk-pairing
  lf-ind-ctor-type 0 ['] lf-c1-visit lf-ind-pair-walker walk-run-pair lf-c1-walked ;
: lf-ind-c1 ( -- outcome ) lf-ind-ctors@ ['] lf-c1-ctor ok-each ;

\ T1: at least numParams raw binders in the type, then in each
\ constructor's type, in that order (get_params, 1138-1146, called from
\ elim_nested_inductive_fn 1151-1166 before anything else of the block;
\ review rvI21 L1). Rejected: Lean's "incorrect number of parameters",
\ the binders found and numParams.
: lf-ind-few ( k -- outcome )
  lf-ind-nparams lf-ind-site lf-diag-param-binders lf-diag-note outcome-rejected ;
: lf-ind-enough ( node -- outcome )
  lf-ind-body nip dup lf-ind-nparams < if lf-ind-few else drop outcome-ok then ;
: lf-ind-ctor-enough ( k -- outcome ) lf-ind-ctor-type lf-ind-enough ;
: lf-ind-ctors-enough ( -- outcome ) lf-ind-ctors@ ['] lf-ind-ctor-enough ok-each ;
: lf-ind-t1 ( -- outcome )
  lf-ind-type lf-idecl-type @ lf-ind-enough ['] lf-ind-ctors-enough ok-and ;
