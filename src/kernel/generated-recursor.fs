\ The recursor Lean's kernel generates for an inductive block, for the
\ declarations after the block (plan task 5.2.1a; ADR 0015 decision 12;
\ the owner's condition of 2026-11-04: with no flags, exactly Lean's
\ verdicts). Lean's add_inductive adds T.rec to its environment whatever
\ the file holds: a file may leave the recursor out (B4) or hold a
\ different one (a block rejected by B3, decision 11), and a later
\ declaration that uses T.rec then meets the kernel's. LeanForth's slots
\ hold only the file's declarations, and the recursor a block check
\ generates is the check's scratch, given back after it. So the block
\ check leaves a recipe on the block's slots (environment.fs
\ lf-env-recipe!), and a later check that looks T.rec up and finds no
\ slot holding it builds the recursor again, in its own scratch, from the
\ block's input declarations: the same builder (inductive-recursor.fs)
\ on the same facts, which the recipe and the input determine.
\ The facts: the type's telescope (parameters and indices, the result
\ Sort) and each constructor's field count are read from the raw input
\ terms; the recipe says whether the recursor eliminates into every
\ universe (its motive universe its first universe parameter) or only
\ into Prop, and that the telescope the check walked after whnf was the
\ raw one (lf-genrec-raw?, tested when the check built the recursor).
\ The recursor is built at the use's universe arguments: the motive's
\ Sort at the first when it has one; the block's constants at the others;
\ and every binder domain read from instances of the block's type and
\ constructor types in which the block's universe parameters are replaced
\ by those same arguments (lf-mixed-level-substitute; review rvI21 R5-1).
\ Since building copies the domains and only adds constants and the
\ motive's Sort, the result is Lean's instantiate_type_lparams of the
\ recursor's type at the use's arguments (rows after.*-at-*: renamed,
\ concrete, swapped and applied universes on Eq, Exists and Pr). No
\ universe name of the recursor's own is ever made (the motive's `u` need
\ not be a name or a level of the file; R4-1), and the number of universe
\ parameters has no limit of its own (R4-3). A block whose
\ telescope only whnf shows has no recipe: a use of its T.rec is then
\ unknown (diagnostic 77) until the rebuild walks the telescope with
\ whnf.fs's whnf too (a follow-up of plan task 5.2.1b; the builder finds
\ the recursive fields with that whnf already). Nothing is trusted from
\ the file beyond
\ what the block check itself read.
\ [kernel] code: experimental, not through the review gate.
\ A recursive block's recursor has its induction hypotheses: the builder
\ finds its recursive fields again on the constructors' instances (plan
\ task 5.2.1b).
\ State: lf-genrec-state, a member of the checker context: the type built
\ and a copy of the block record lf-ind-state, which the build overwrites
\ and gives back (a lookup can happen during another block's check, whose
\ record must survive it), with a copy of that block's binder domains
\ (lf-ind-domains) in lf-genrec-kept-cells, of its type records
\ (lf-ind-type-cells) in lf-genrec-kept-types and of its constructors'
\ records (lf-ind-ctor-cells) in lf-genrec-kept-ctors; the build's own state and
\ level pairs are inductive-recursor.fs's (lf-rcr-state and its slabs),
\ unused while a block's inference steps run.

require ../lib/lib.fs
require ../core/input.fs
require ../core/levels.fs
require ../core/terms.fs
require ./environment.fs
require ./inductive-block.fs
require ./inductive-recursor.fs
require ./mixed-head.fs
require ./mixed-level-substitute.fs

begin-structure /lf-genrec
  field: lf-genrec-root-cell    \ the recursor's type, built
  field: lf-genrec-args         \ the use's arguments for the block's parameters
  field: lf-genrec-which        \ the type whose recursor is built, in its block
  field: lf-genrec-kept         \ the block's domains copied, how many
  field: lf-genrec-kept-ty      \ its type records copied, how many
  field: lf-genrec-kept-ctor    \ its constructors' records copied, how many
  /lf-ind +field lf-genrec-saved \ the block record while the build runs
end-structure
/lf-genrec context-record: lf-genrec-state
\ The constructors' types instantiated, one cell each: a growable array.
1 cells context-slab: lf-genrec-ctor-cells
\ The binder domains, type records and constructors' records of the
\ block whose check the lookup interrupts.
1 cells context-slab: lf-genrec-kept-cells
/lf-ty context-slab: lf-genrec-kept-types
/lf-ind-ctor context-slab: lf-genrec-kept-ctors

\ ---------------------------------------------------------------------------
\ At the block check, after the build (step 12): whether the telescopes it
\ walked, binder by binder after whnf, are the raw ones -- for each type,
\ each recorded domain the raw Pi's own node (the first type's parameters
\ too; another type's parameters only raw binders), the end a raw Sort.
: lf-genrec-step ( node at -- node' flag )
  over lf-tag-pi lf-ind-tag? 0= if drop false exit then
  lf-ind-domain @ over lf-term-first@ = swap lf-term-second@ swap ;
: lf-genrec-skip ( node n -- node' flag )
  0 ?do dup lf-tag-pi lf-ind-tag? 0= if false unloop exit then lf-term-second@ loop true ;
: lf-genrec-sorted? ( node -- flag ) lf-mhead-kind lf-head-sort = ;
: lf-genrec-params? ( node d -- node' flag )
  if lf-ind-nparams lf-genrec-skip exit then
  lf-ind-nparams 0 ?do i lf-genrec-step 0= if false unloop exit then loop true ;
: lf-genrec-indices? ( node d -- node' flag )
  dup lf-ind-n 0 ?do
    dup lf-ind-ty lf-ty-domain @ i + rot swap lf-genrec-step
    0= if nip false unloop exit then swap
  loop drop true ;
: lf-genrec-type-raw? ( d -- flag )
  dup lf-ind-type-at lf-idecl-type @ over lf-genrec-params? 0= if 2drop false exit then
  swap lf-genrec-indices? 0= if drop false exit then lf-genrec-sorted? ;
: lf-genrec-raw? ( -- flag ) true lf-ind-types@ 0 ?do i lf-genrec-type-raw? and loop ;
\ The recipe the block check publishes: lf-recipe-raw, with
\ lf-recipe-large when the motive has a universe of its own; 0 when the
\ telescope is not raw.
: lf-genrec-recipe ( -- bits )
  lf-genrec-raw? 0= if 0 exit then
  lf-recipe-raw lf-ind-state lf-ind-elim-name @ if lf-recipe-large or then ;

\ ---------------------------------------------------------------------------
\ At a lookup: the facts again, from the raw input. The telescopes: the
\ first type's Pis' domains, then its result Sort's level and indices;
\ another type's Pis after its parameters, its indices; invalid when one
\ is not what the recipe says (no raw Sort end, too few binders).
: lf-genrec-bind ( node at -- node' )
  over lf-term-first@ swap lf-ind-domain ! lf-term-second@ ;
: lf-genrec-used ( -- addr ) lf-ind-state lf-ind-domains-used ;
: lf-genrec-pis ( node -- end n outcome )
  0 begin over lf-tag-pi lf-ind-tag? while
    lf-genrec-used @ dup 1+ lf-ind-domains slab-hold ok? 0=
    if drop outcome-full exit then
    >r swap r> lf-genrec-bind swap 1+ 1 lf-genrec-used +!
  repeat outcome-ok ;
: lf-genrec-first ( root -- outcome )
  0 lf-genrec-used ! lf-ind-nparams 0 lf-ind-ty lf-ty-domain !
  lf-genrec-pis dup ok? 0= if nip nip exit then drop
  lf-ind-nparams - dup 0< if 2drop outcome-invalid exit then 0 lf-ind-ty lf-ty-indices !
  dup lf-genrec-sorted? 0= if drop outcome-invalid exit then
  lf-term-first@ lf-ind-state lf-ind-level ! outcome-ok ;
: lf-genrec-other ( root d -- outcome )
  swap lf-ind-nparams lf-genrec-skip 0= if 2drop outcome-invalid exit then
  lf-genrec-used @ 2 pick lf-ind-ty lf-ty-domain !
  lf-genrec-pis dup ok? 0= if nip nip nip exit then drop
  rot lf-ind-ty lf-ty-indices !
  lf-genrec-sorted? if outcome-ok else outcome-invalid then ;
\ Each constructor's fields: its raw binders after the parameters.
: lf-genrec-fields ( -- outcome )
  lf-ind-ctors@ 0 ?do
    i lf-ind-ctor-type lf-ind-body nip lf-ind-nparams - dup 0<
    if drop outcome-invalid unloop exit then i lf-ind-nfields !
  loop outcome-ok ;
\ The recursor's universe parameters (Lean's declare_recursors): the
\ motive's first when it eliminates into every universe, then the
\ block's; their number is what a use must supply (L1).
: lf-genrec-large? ( d -- flag )
  lf-env lf-env-slot lf-slot-recipe @ lf-recipe-large and 0<> ;
: lf-genrec-arity ( d -- n ) dup lf-input-params nip swap lf-genrec-large? 1 and + ;
\ The use's arguments, (index identity) pairs as constant references hold
\ them: the motive's Sort at the first when it has one; the block's
\ constants at the rest, put in the builder's pair cells.
: lf-genrec-elim ( pairs large? -- pairs' )
  if dup 0 lf-cref-pair @ lf-ind-state lf-ind-elim ! 1 lf-cref-pair
  else 0 lf-ind-state lf-ind-elim ! then ;
: lf-genrec-pairs ( pairs -- outcome )
  dup lf-genrec-state lf-genrec-args !
  lf-ind-lparams nip dup lf-rcr-pair-cells slab-hold ok? 0=
  if 2drop outcome-full exit then
  0 ?do dup i lf-cref-pair 2@ i lf-rcr-pair 2! loop drop outcome-ok ;
\ An input root with the block's universe parameters replaced by the
\ use's arguments for them (lf-genrec-args), on the block's fuel; a
\ block without universe parameters keeps the root.
: lf-genrec-subst-run ( root identity -- root' outcome )
  lf-ind-lparams drop lf-genrec-state lf-genrec-args @ lf-ind-lparams nip lf-ind-fuel @
  lf-mixed-level-substitute lf-mls-fuel @ lf-ind-fuel !
  dup ok? if 2drop outcome-ok else -1 swap then ;
: lf-genrec-subst ( root -- root' outcome )
  lf-ind-lparams nip 0= if outcome-ok exit then
  dup lf-term-identity 0= if drop -1 outcome-invalid exit then lf-genrec-subst-run ;
\ Each type's telescope from its instance; each constructor's type
\ instantiated into the array.
: lf-genrec-type ( d -- outcome )
  dup lf-ind-type-at lf-idecl-type @ lf-genrec-subst dup ok? 0= if nip nip exit then drop
  swap ?dup if lf-genrec-other else lf-genrec-first then ;
: lf-genrec-types ( -- outcome )
  lf-ind-types@ 0 ?do i lf-genrec-type dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
: lf-genrec-ctor ( j -- outcome )
  dup lf-ind-ctor-type lf-genrec-subst dup ok? 0= if nip nip exit then drop
  swap lf-genrec-ctor-cells slab-at ! outcome-ok ;
: lf-genrec-ctors ( -- outcome )
  lf-ind-ctors@ 1 max lf-genrec-ctor-cells slab-hold ok? 0= if outcome-full exit then
  lf-ind-ctors@ 0 ?do i lf-genrec-ctor dup ok? 0= if unloop exit then drop loop
  outcome-ok ;

\ The build, between the copy of the block record and its return. The
\ type slot d opens its block (its header's first member), and is the
\ block's type d - first.
: lf-genrec-then ( outcome xt -- outcome ) over ok? if nip execute else drop then ;
: lf-genrec-layout ( -- outcome ) lf-ind-layout if outcome-ok else outcome-invalid then ;
: lf-genrec-facts ( d -- outcome )
  dup lf-input-decl lf-idecl-header dup 0= if 2drop outcome-invalid exit then
  lf-hdr-first lf-more-field tuck - lf-genrec-state lf-genrec-which !
  lf-ind-open nip ['] lf-genrec-layout lf-genrec-then
  ['] lf-genrec-fields lf-genrec-then ;
: lf-genrec-made ( -- outcome )
  0 lf-genrec-ctor-cells slab-at lf-recursor-build-at dup ok? 0= if exit then
  lf-genrec-state lf-genrec-which @ lf-ind-ty lf-ty-rec-type @
  lf-genrec-state lf-genrec-root-cell ! ;
: lf-genrec-run ( d pairs fuel -- fuel' outcome )
  >r over lf-genrec-facts dup ok? 0= if nip nip r> swap exit then drop
  r> lf-ind-fuel ! swap lf-genrec-large? lf-genrec-elim lf-genrec-pairs
  ['] lf-genrec-types lf-genrec-then ['] lf-genrec-ctors lf-genrec-then
  ['] lf-genrec-made lf-genrec-then lf-ind-fuel @ swap ;
\ The block record, and every unit of the domains, type records and
\ constructors' records slabs (the record does not say how many the
\ interrupted check filled): copied aside, full when the heap cannot hold
\ a copy; given back after the build. A slab only grows, so it still holds
\ every unit copied.
: lf-genrec-out ( slab save -- n outcome )
  over slab-capacity dup 2 pick slab-hold ok? 0= if drop 2drop 0 outcome-full exit then
  >r over slab-bytes >r swap slab-base swap slab-base r> move r> outcome-ok ;
: lf-genrec-back ( n save slab -- )
  dup slab-unit >r slab-base swap slab-base swap rot r> * move ;
: lf-genrec-save ( -- outcome )
  lf-ind-domains lf-genrec-kept-cells lf-genrec-out ok-then? 0= if exit then
  lf-genrec-state lf-genrec-kept !
  lf-ind-type-cells lf-genrec-kept-types lf-genrec-out ok-then? 0= if exit then
  lf-genrec-state lf-genrec-kept-ty !
  lf-ind-ctor-cells lf-genrec-kept-ctors lf-genrec-out ok-then? 0= if exit then
  lf-genrec-state lf-genrec-kept-ctor !
  lf-ind-state lf-genrec-state lf-genrec-saved /lf-ind move outcome-ok ;
: lf-genrec-restore ( -- )
  lf-genrec-state lf-genrec-saved lf-ind-state /lf-ind move
  lf-genrec-state lf-genrec-kept @ lf-genrec-kept-cells lf-ind-domains lf-genrec-back
  lf-genrec-state lf-genrec-kept-ty @ lf-genrec-kept-types lf-ind-type-cells
  lf-genrec-back
  lf-genrec-state lf-genrec-kept-ctor @ lf-genrec-kept-ctors lf-ind-ctor-cells
  lf-genrec-back ;

\ Build the recursor of the block whose type is slot d (readable, with a
\ recipe: lf-env-rebuildable?) at the universe arguments at pairs, as
\ many as lf-genrec-arity says (the caller checks them, L1 and L2), in
\ this check's scratch, with fuel: (fuel' ok), its type then
\ lf-genrec-root; or (fuel' failure): full (a full store or pair slab, or
\ no room to keep the domains), exhausted, invalid (an input that is not
\ what the recipe says). The block record and domains are as before.
: lf-genrec ( d pairs fuel -- fuel' outcome )
  lf-genrec-save ok? 0= if nip nip outcome-full exit then
  lf-genrec-run lf-genrec-restore ;
: lf-genrec-root ( -- root ) lf-genrec-state lf-genrec-root-cell @ ;
