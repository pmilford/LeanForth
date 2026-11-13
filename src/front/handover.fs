\ The hand-over of a finished declaration to the kernel (plan row FE1f;
\ ADR 0021 D1-D3; design docs/design/FRONT_END.md section 4.3), after
\ Lean's end of a declaration (Elab/MutualDef.lean): every assigned
\ metavariable instantiated (Lean's instantiateMVars), the declaration
\ refused when a hole is left, then sent to the kernel (addDecl).
\ - The header of a natural declaration is its declaration record
\   (lf-front-header, author/constants.fs): the name, kind and universe
\   parameters the declaration words recorded; the hand-over puts in the
\   type and value the elaborator gives (plan FE1e), each closed over the
\   declaration's parameters, an axiom's value -1.
\ - lf-handover ( decl type value -- outcome ) instantiates both
\   (front/mvars.fs), refuses them when either still reaches a metavariable,
\   term or level (core/reach.fs: only what they reach counts, so a hole
\   left elsewhere in the stores blocks nothing) or when neither uses a
\   universe parameter decl names (Lean's sortDeclLevelParams: "unused
\   universe parameter"; decl's order of them is kept, as Lean keeps the
\   order written), and else records them in decl. A refusal gives back
\   every node, level and constant reference the hand-over made
\   (core/scratch-marks.fs) and leaves decl as it was. Outcomes: ok;
\   invalid for a hole left (elaboration incomplete), an unused universe
\   parameter or a term that is no node; unsupported for an instantiation
\   step not ported yet (the beta step and delayed assignments, plan
\   FE1c); full for no room.
\ - In natural text, end NAME runs the elaborator (lf-front-elaborate, a
\   deferred word plan FE1e sets; until then error 71, not supported yet,
\   as before), then lf-front-hand-over, which stops the run at end NAME on
\   a refusal: error 74 for a hole left (or a term that is no node), 75 for
\   an unused universe parameter, 71 for a step not ported, 60 for no
\   room. The run's records then go to the kernel by the path of every
\   text (cli/check-lf.fs: author/export.fs's lf-author-export-reached,
\   the importer stage's stage-produce, the feed, check-declaration), and
\   the export writer refuses a metavariable it would write whatever this
\   file decided (ADR 0021 D2). Untrusted: only the kernel's check of the
\   records decides anything.
\ State: one context record, lfh (the scratch mark, the declaration and
\ the refusal's error of a hand-over), in the checker context (ADR 0009).

require ../lib/lib.fs
require ../core/scratch-marks.fs
require ../core/reach.fs
require ../author/declarations.fs
require ./mvars.fs

begin-structure /lfh
  /lf-scratch +field lfh-scratch   \ the stores as they stood at the start
  field: lfh-decl                  \ the declaration handed over
  field: lfh-why                   \ the error of the last refusal, for end NAME
end-structure
/lfh context-record: lfh

\ The header: the declaration being made.
: lf-front-header ( -- decl ) lfa-this ;
: lfh-decl@ ( -- decl ) lfh lfh-decl @ ;
: lfh-why! ( code -- ) lfh lfh-why ! ;

\ Instantiation: the type always, the value when there is one.
: lfh-value ( value -- value' outcome )
  dup 0< if outcome-ok exit then lf-instantiate-mvars ;
: lfh-pair ( type value -- type' value' outcome )
  >r lf-instantiate-mvars r> swap dup ok? 0= if exit then drop lfh-value ;
\ What the type and value reach (core/reach.fs): no metavariable, term or
\ level (else invalid, elaboration incomplete, error 74), and every
\ universe parameter the declaration names (else invalid, as Lean's
\ sortDeclLevelParams: "unused universe parameter", error 75).
: lfh-names ( -- addr n ) lfh-decl@ dup lf-fdecl-universe swap lf-fdecl-universes @ ;
: lfh-unused? ( addr n -- flag )
  0 ?do dup @ lf-reach-param? 0= if drop true unloop exit then cell+ loop drop false ;
: lfh-refuse ( code -- outcome ) lfh-why! outcome-invalid ;
: lfh-judge ( -- outcome )
  lf-reach-holes? if lfa-e-incomplete lfh-refuse exit then
  lfh-names lfh-unused? if lfa-e-unused-universe lfh-refuse else outcome-ok then ;
: lfh-reached ( type value -- outcome )
  lf-reach-term lf-reach-term lf-reach-sweep lfh-judge ;
: lfh-checked ( type value -- outcome )
  lf-reach-open 0= if 2drop outcome-full exit then lfh-reached lf-reach-close ;
: lfh-whole ( type value -- type value outcome ) 2dup lfh-checked ;
: lfh-made ( type value -- type' value' outcome )
  lfh-pair dup ok? if drop lfh-whole then ;

\ Kept, or given back: a refusal stands whatever the rollback says.
: lfh-keep ( type value -- ) lfh-decl@ tuck lf-fdecl-value ! lf-fdecl-type ! ;
: lfh-mark ( -- scratch ) lfh lfh-scratch ;
: lfh-back ( type value outcome -- outcome )
  nip nip lfh-mark lf-scratch-rollback drop ;
: lfh-go ( type value -- outcome )
  lfh-made dup ok? if drop lfh-keep outcome-ok else lfh-back then ;
: lfh-start ( decl -- ) lfh lfh-decl ! lfa-e-incomplete lfh-why! ;
: lf-handover ( decl type value -- outcome )
  rot lfh-start lfh-mark lf-scratch-mark dup ok? if drop lfh-go else nip nip then ;

\ ---- Natural text: end NAME.
\ The elaborator (plan FE1e): the declaration's type and value, closed
\ over its parameters, from its syntax (front/reader.fs, lf-front-statement
\ and lf-front-proof); it stops the run with its own error where it fails.
: lfh-later ( -- type value ) lfa-e-elaborate lfa-fail ;
defer lf-front-elaborate ( -- type value )
' lfh-later is lf-front-elaborate
\ A refusal's error at end NAME: the hand-over's own for invalid.
: lfh-code ( outcome -- code )
  case outcome-invalid of lfh lfh-why @ endof outcome-full of lfa-e-terms-full endof
    lfa-e-elaborate swap endcase ;
: lf-front-hand-over ( type value -- )
  lf-front-header -rot lf-handover dup ok? if drop else lfh-code lfa-fail then ;
