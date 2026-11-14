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
\   left elsewhere in the stores blocks nothing) or when a universe
\   parameter decl names is unused (Lean's sortDeclLevelParams: "unused
\   universe parameter"; a definition's counted in its type and value, a
\   theorem's and an axiom's in the type alone; decl's order of them is
\   kept, as Lean keeps the order written), and else records them in
\   decl. A refusal gives back every node, level and constant reference
\   the hand-over made
\   (core/scratch-marks.fs) and leaves decl as it was. Outcomes: ok;
\   invalid for a hole left (elaboration incomplete), an unused universe
\   parameter, a term that is no node, or a value that does not fit decl's
\   kind (a theorem's or definition's must be a node, an axiom's -1);
\   unsupported for an instantiation
\   step not ported yet (the beta step and delayed assignments, plan
\   FE1c); full for no room.
\ - In natural text, end NAME runs the elaborator (lf-front-elaborate, a
\   deferred word front/elab-decl.fs sets; error 71, not supported yet,
\   without it), then lf-front-hand-over, which stops the run at end NAME on
\   a refusal: error 74 for a hole left, 75 for an unused universe
\   parameter, 76 for terms that are malformed (no node, a value unfit for
\   the kind), 77 for an instantiation step not ported yet, 60 for no
\   room. A declaration handed over is made visible to the next, as
\   Lean's addDecl makes it (front/meta-env.fs, lf-menv-add; no room:
\   60). The run's records then go to the kernel by the path of every
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
require ../present/print-forth.fs
require ../author/errors.fs
require ../author/form.fs
require ../author/declarations.fs
require ./mvars.fs
require ./meta-env.fs

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
\ sortDeclLevelParams: "unused universe parameter", error 75), counted as
\ Lean counts them: a definition's in its type and value, a theorem's and
\ an axiom's in the type alone (Lean elaborates a theorem's proof after
\ its header, elabAsync; pinned Lean refuses theorem t.{v} : True :=
\ (fun (_ : Sort v) => True.intro) PUnit.{v}, review fe1f N1). Lean takes
\ that path only when the theorem's header type holds no metavariable
\ once elaborated (MutualDef.lean); plan FE1e's elaborator must say when
\ it does not. The type is marked and swept first, then the value.
: lfh-names ( -- addr n ) lfh-decl@ dup lf-fdecl-universe swap lf-fdecl-universes @ ;
: lfh-unused? ( addr n -- flag )
  0 ?do dup @ lf-reach-param? 0= if drop true unloop exit then cell+ loop drop false ;
: lfh-def? ( -- flag ) lfh-decl@ lf-fdecl-kind @ lf-decl-def = ;
: lfh-unused-of ( type-unused? -- flag ) lfh-def? if drop lfh-names lfh-unused? then ;
: lfh-refuse ( code -- outcome ) lfh-why! outcome-invalid ;
\ An unused parameter is told before a hole, as pinned Lean tells only it
\ for theorem t5.{v} : True := _ and def d3.{v} : Nat := _.
: lfh-judge ( type-unused? -- outcome )
  lfh-unused-of if lfa-e-unused-universe lfh-refuse exit then
  lf-reach-holes? if lfa-e-incomplete lfh-refuse else outcome-ok then ;
: lfh-type-unused? ( type -- flag ) lf-reach-term lf-reach-sweep lfh-names lfh-unused? ;
: lfh-reached ( type value -- outcome )
  swap lfh-type-unused? swap lf-reach-term lf-reach-sweep lfh-judge ;
: lfh-checked ( type value -- outcome )
  lf-reach-open 0= if 2drop outcome-full exit then lfh-reached lf-reach-close ;
: lfh-whole ( type value -- type value outcome ) 2dup lfh-checked ;
: lfh-made ( type value -- type' value' outcome )
  lfh-pair dup ok? if drop lfh-whole then ;

\ Kept, or given back: a refusal stands whatever the rollback says.
: lfh-keep ( type value -- ) lfh-decl@ tuck lf-fdecl-value ! lf-fdecl-type ! ;
: lfh-mark ( -- scratch ) lfh lfh-scratch ;
: lfh-back ( outcome -- outcome ) lfh-mark lf-scratch-rollback drop ;
: lfh-go ( type value -- outcome )
  lfh-made ok-then2? if lfh-keep outcome-ok else lfh-back then ;
: lfh-start ( decl -- ) lfh lfh-decl ! lfa-e-malformed lfh-why! ;
\ A theorem's or definition's value is a node; an axiom has none, -1
\ (review fe1f M1): any other shape is refused, nothing made.
: lfh-axiom? ( -- flag ) lfh-decl@ lf-fdecl-kind @ lf-decl-def > ;
: lfh-shaped? ( value -- flag ) lfh-axiom? if -1 = else 0< 0= then ;
: lfh-marked ( type value -- outcome ) lfh-mark lf-scratch-mark ok-then2? if lfh-go then ;
: lf-handover ( decl type value -- outcome )
  rot lfh-start dup lfh-shaped? if lfh-marked else 2drop outcome-invalid then ;

\ ---- Natural text: end NAME.
\ The elaborator (plan FE1e): the declaration's type and value, closed
\ over its parameters, from its syntax (front/reader.fs, lf-front-statement
\ and lf-front-proof); it stops the run with its own error where it fails.
: lfh-later ( -- type value ) lfa-e-elaborate lfa-fail ;
defer lf-front-elaborate ( -- type value )
' lfh-later is lf-front-elaborate
\ A refusal's error at end NAME: the hand-over's own for invalid (a hole
\ 74, an unused universe parameter 75, else malformed 76), no room 60, an
\ instantiation step not ported 77.
: lfh-code ( outcome -- code )
  case outcome-invalid of lfh lfh-why @ endof outcome-full of lfa-e-terms-full endof
    lfa-e-instantiate swap endcase ;
: lfh-visible ( -- ) lfh-decl@ lf-menv-add ok? 0= if lfa-e-terms-full lfa-fail then ;
: lf-front-hand-over ( type value -- )
  lf-front-header -rot lf-handover dup ok? 0= if lfh-code lfa-fail then
  drop lfh-visible lfa-front-made! ;
