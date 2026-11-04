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
\ terms; the recipe gives the motive's universe (or Prop) and says that
\ the telescope the check walked after whnf was the raw one
\ (lf-genrec-raw?, tested when the check built the recursor). A block
\ whose telescope only whnf shows has no recipe: a use of its T.rec is
\ then unknown (diagnostic 77), never decided. Nothing is trusted from
\ the file beyond what the block check itself read.
\ [kernel] code: experimental, not through the review gate.
\ State: lf-genrec-state, a member of the checker context: the type built,
\ its universe parameters, and a copy of the block record lf-ind-state,
\ which the build overwrites and gives back (a lookup can happen during
\ another block's check, whose record must survive it).

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
  field: lf-genrec-count        \ its universe parameters
  lf-param-capacity cells +field lf-genrec-param-cells
  /lf-ind +field lf-genrec-saved \ the block record while the build runs
end-structure
/lf-genrec context-record: lf-genrec-state

\ ---------------------------------------------------------------------------
\ At the block check, after the build (step 12): whether the telescope it
\ walked, binder by binder after whnf, is the raw one -- each domain the
\ raw Pi's own node, the end a raw Sort of the result level.
: lf-genrec-arity ( -- n ) lf-ind-nparams lf-ind-state lf-ind-indices @ + ;
: lf-genrec-step ( node i -- node' flag )
  over lf-tag-pi lf-ind-tag? 0= if drop false exit then
  lf-ind-domain @ over lf-term-first@ = swap lf-term-second@ swap ;
: lf-genrec-sorted? ( node -- flag ) lf-mhead-kind lf-head-sort = ;
: lf-genrec-sort? ( node -- flag )
  dup lf-genrec-sorted? 0= if drop false exit then
  lf-term-first@ lf-ind-state lf-ind-level @ = ;
: lf-genrec-raw? ( -- flag )
  lf-ind-type lf-idecl-type @ lf-genrec-arity 0 ?do
    i lf-genrec-step 0= if drop false unloop exit then
  loop lf-genrec-sort? ;
\ The recipe the block check publishes: the motive universe's name, or 0
\ for Prop, and lf-recipe-raw (with lf-recipe-large for a name); 0 0
\ when the telescope is not raw.
: lf-genrec-recipe ( -- name bits )
  lf-genrec-raw? 0= if 0 0 exit then
  lf-ind-state lf-ind-elim-name @ dup if lf-recipe-raw lf-recipe-large or
  else lf-recipe-raw then ;

\ ---------------------------------------------------------------------------
\ At a lookup: the facts again, from the raw input. The telescope: each
\ Pi's domain, then the result Sort's level and the indices; invalid when
\ it is not what the recipe says (no raw Sort end, too few binders).
: lf-genrec-bind ( node i -- node' )
  over lf-term-first@ swap lf-ind-domain ! lf-term-second@ ;
: lf-genrec-tele ( -- outcome )
  lf-ind-type lf-idecl-type @ 0 begin over lf-tag-pi lf-ind-tag? while
    dup lf-ind-binder-capacity < 0= if 2drop outcome-full exit then
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
\ The motive's universe: the recipe's name as a level, or Prop.
: lf-genrec-elim ( name bits -- outcome )
  lf-recipe-large and 0= if drop 0 0 else
    dup lf-level-param 0= if drop outcome-full exit then
  then lf-ind-state lf-ind-elim ! lf-ind-state lf-ind-elim-name ! outcome-ok ;
\ The universe parameters: the motive's first when it has one, then the
\ block's (Lean's declare_recursors).
: lf-genrec-param! ( name -- )
  lf-genrec-state dup lf-genrec-count @ cells over lf-genrec-param-cells + rot swap !
  1 swap lf-genrec-count +! ;
: lf-genrec-params! ( -- outcome )
  0 lf-genrec-state lf-genrec-count !
  lf-ind-lparams nip lf-ind-state lf-ind-elim-name @ 0<> - lf-param-capacity >
  if outcome-full exit then
  lf-ind-state lf-ind-elim-name @ ?dup if lf-genrec-param! then
  lf-ind-lparams 0 ?do dup i cells + @ lf-genrec-param! loop drop outcome-ok ;

\ The build, between the copy of the block record and its return.
: lf-genrec-then ( outcome xt -- outcome ) over ok? if nip execute else drop then ;
: lf-genrec-facts ( d -- outcome )
  lf-ind-open nip ['] lf-genrec-tele lf-genrec-then ['] lf-genrec-fields lf-genrec-then ;
: lf-genrec-made ( -- outcome )
  lf-recursor-build dup ok? 0= if exit then drop
  lf-ind-state lf-ind-rec-type @ lf-genrec-state lf-genrec-root-cell ! lf-genrec-params! ;
: lf-genrec-run ( d fuel -- fuel' outcome )
  >r dup lf-genrec-facts dup ok? 0= if nip r> swap exit then drop
  r> lf-ind-fuel ! lf-env lf-env-slot lf-slot-recipe@ lf-genrec-elim
  ['] lf-genrec-made lf-genrec-then lf-ind-fuel @ swap ;
: lf-genrec-save ( -- ) lf-ind-state lf-genrec-state lf-genrec-saved /lf-ind move ;
: lf-genrec-restore ( -- ) lf-genrec-state lf-genrec-saved lf-ind-state /lf-ind move ;

\ Build the recursor of the block whose type is slot d (readable, with a
\ recipe: lf-env-rebuildable?) in this check's scratch, with fuel: (fuel'
\ ok), the type then lf-genrec-root and its universe parameters
\ lf-genrec-params; or (fuel' failure): full (a full store, more
\ parameters than lf-param-capacity), exhausted, invalid (an input that
\ is not what the recipe says). The block record is as before.
: lf-genrec ( d fuel -- fuel' outcome ) lf-genrec-save lf-genrec-run lf-genrec-restore ;
: lf-genrec-root ( -- root ) lf-genrec-state lf-genrec-root-cell @ ;
: lf-genrec-params ( -- params n )
  lf-genrec-state dup lf-genrec-param-cells swap lf-genrec-count @ ;
