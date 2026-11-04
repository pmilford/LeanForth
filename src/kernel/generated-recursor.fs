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
\ The recursor is built at the use's universe arguments directly -- the
\ motive's Sort at the first when it has one, the block's constants at the
\ others -- which is Lean's instantiate_type_lparams of its type; so no
\ universe name of the recursor's own is ever made (the motive's `u` need
\ not be a name or a level of the file; review rvI21 R4-1) and the number
\ of universe parameters has no limit of its own (R4-3). A block whose
\ telescope only whnf shows has no recipe: a use of its T.rec is then
\ unknown (diagnostic 77) until unfolding and whnf at a lookup (plan task
\ 4.2.2, its steps 4.2.2b-e). Nothing is trusted from the file beyond
\ what the block check itself read.
\ [kernel] code: experimental, not through the review gate.
\ State: lf-genrec-state, a member of the checker context: the type built
\ and a copy of the block record lf-ind-state, which the build overwrites
\ and gives back (a lookup can happen during another block's check, whose
\ record must survive it); the build's own state and level pairs are
\ inductive-recursor.fs's (lf-rcr-state, lf-rcr-pair-cells), unused while
\ a block's inference steps run.

require ../lib/lib.fs
require ../core/input.fs
require ../core/levels.fs
require ../core/terms.fs
require ./environment.fs
require ./inductive-block.fs
require ./inductive-recursor.fs
require ./mixed-head.fs

begin-structure /lf-genrec
  field: lf-genrec-root-cell    \ the recursor's type, built
  /lf-ind +field lf-genrec-saved \ the block record while the build runs
end-structure
/lf-genrec context-record: lf-genrec-state

\ ---------------------------------------------------------------------------
\ At the block check, after the build (step 12): whether the telescope it
\ walked, binder by binder after whnf, is the raw one -- each domain the
\ raw Pi's own node, the end a raw Sort of the result level.
: lf-genrec-binders ( -- n ) lf-ind-nparams lf-ind-state lf-ind-indices @ + ;
: lf-genrec-step ( node i -- node' flag )
  over lf-tag-pi lf-ind-tag? 0= if drop false exit then
  lf-ind-domain @ over lf-term-first@ = swap lf-term-second@ swap ;
: lf-genrec-sorted? ( node -- flag ) lf-mhead-kind lf-head-sort = ;
: lf-genrec-sort? ( node -- flag )
  dup lf-genrec-sorted? 0= if drop false exit then
  lf-term-first@ lf-ind-state lf-ind-level @ = ;
: lf-genrec-raw? ( -- flag )
  lf-ind-type lf-idecl-type @ lf-genrec-binders 0 ?do
    i lf-genrec-step 0= if drop false unloop exit then
  loop lf-genrec-sort? ;
\ The recipe the block check publishes: lf-recipe-raw, with
\ lf-recipe-large when the motive has a universe of its own; 0 when the
\ telescope is not raw.
: lf-genrec-recipe ( -- bits )
  lf-genrec-raw? 0= if 0 exit then
  lf-recipe-raw lf-ind-state lf-ind-elim-name @ if lf-recipe-large or then ;

\ ---------------------------------------------------------------------------
\ At a lookup: the facts again, from the raw input. The telescope: each
\ Pi's domain, then the result Sort's level and the indices; invalid when
\ it is not what the recipe says (no raw Sort end, too few binders).
: lf-genrec-bind ( node i -- node' )
  over lf-term-first@ swap lf-ind-domain ! lf-term-second@ ;
: lf-genrec-tele ( -- outcome )
  lf-ind-type lf-idecl-type @ 0 begin over lf-tag-pi lf-ind-tag? while
    dup 1+ lf-ind-domains slab-hold ok? 0= if 2drop outcome-full exit then
    tuck lf-genrec-bind swap 1+
  repeat lf-ind-nparams - dup 0< if 2drop outcome-invalid exit then
  lf-ind-state lf-ind-indices ! dup lf-genrec-sorted? 0= if drop outcome-invalid exit then
  lf-term-first@ lf-ind-state lf-ind-level ! outcome-ok ;
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
  lf-ind-lparams nip dup lf-rcr-pair-cells slab-hold ok? 0=
  if 2drop outcome-full exit then
  0 ?do dup i lf-cref-pair 2@ i lf-rcr-pair 2! loop drop outcome-ok ;

\ The build, between the copy of the block record and its return.
: lf-genrec-then ( outcome xt -- outcome ) over ok? if nip execute else drop then ;
: lf-genrec-facts ( d -- outcome )
  lf-ind-open nip ['] lf-genrec-tele lf-genrec-then ['] lf-genrec-fields lf-genrec-then ;
: lf-genrec-made ( -- outcome )
  lf-recursor-build-at dup ok? 0= if exit then
  lf-ind-state lf-ind-rec-type @ lf-genrec-state lf-genrec-root-cell ! ;
: lf-genrec-run ( d pairs fuel -- fuel' outcome )
  >r over lf-genrec-facts dup ok? 0= if nip nip r> swap exit then drop
  r> lf-ind-fuel ! swap lf-genrec-large? lf-genrec-elim lf-genrec-pairs
  ['] lf-genrec-made lf-genrec-then lf-ind-fuel @ swap ;
: lf-genrec-save ( -- ) lf-ind-state lf-genrec-state lf-genrec-saved /lf-ind move ;
: lf-genrec-restore ( -- ) lf-genrec-state lf-genrec-saved lf-ind-state /lf-ind move ;

\ Build the recursor of the block whose type is slot d (readable, with a
\ recipe: lf-env-rebuildable?) at the universe arguments at pairs, as
\ many as lf-genrec-arity says (the caller checks them, L1 and L2), in
\ this check's scratch, with fuel: (fuel' ok), its type then
\ lf-genrec-root; or (fuel' failure): full (a full store or pair slab),
\ exhausted, invalid (an input that is not what the recipe says). The
\ block record is as before.
: lf-genrec ( d pairs fuel -- fuel' outcome )
  lf-genrec-save lf-genrec-run lf-genrec-restore ;
: lf-genrec-root ( -- root ) lf-genrec-state lf-genrec-root-cell @ ;
