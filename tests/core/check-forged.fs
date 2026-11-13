\ check-declaration's audit (src/kernel/check-declaration.fs, step 1)
\ on records the input reader never makes, forged in place inside the
\ check of a case of tests/core/check-block-cases/ (proj.data, whose
\ target is accepted; tests/support/case-sweeps.fs) and put back after
\ it. Coverage classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 2. Malformed input: a declaration of a kind check-declaration does not
\    check (a recursor's kind with no block header, or no kind at all) is
\    unsupported at U1, diagnostic unsupported-kind with the kind and the
\    safety, never accepted; a negative budget is invalid before any walk.
\ 3. Interfaces: lf-check-no-maker's stack effect ( -- 0 -1 ), the
\    publisher's sign that no context replaces one whose check threw.
\ 6. The same case checks as before once the record is put back.
\ 1, 7. K5 (environment.fs): a dependency's slot forged undecided or
\    unsupported makes the declarations after it unknown or unsupported,
\    never accepted (below).
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

variable kind-was
: decl ( -- d ) cs cs-target @ lf-input-decl ;
: kind! ( kind -- ) decl lf-idecl-kind @ kind-was ! decl lf-idecl-kind ! ;
: as-recursor ( -- ) lf-kind-recursor kind! ;
: as-nothing ( -- ) 99 kind! ;
: unforged ( -- ) kind-was @ decl lf-idecl-kind ! ;
\ The target's outcome and diagnostic with the probe forging it first.
: forged ( xt -- outcome code kind safety )
  s" proj.data" cs-load cs-probe! lf-diag-clear cs-run lf-diag@ nip -rot
  unforged cs-unload ;
T{ ' as-recursor forged -> outcome-unsupported lf-diag-unsupported-kind lf-kind-recursor
   lf-safety-safe }T
T{ ' as-nothing forged
   -> outcome-unsupported lf-diag-unsupported-kind 99 lf-safety-safe }T
: plain ( budget -- outcome ) s" proj.data" cs-load cs-at cs-unload ;
T{ cs-plenty plain -1 plain -> outcome-ok outcome-invalid }T
T{ lf-check-no-maker -> 0 -1 }T

\ ---------------------------------------------------------------------------
\ 1, 7. K5 through Lean's generated recursor: the slot of the type N
\ (declaration 0) forged undecided or unsupported in the probe, as if its
\ block's check had ended so (the run's environment is freed after it).
\ A later definition that uses N.rec, which the export left out, then
\ ends unknown (dependency-undecided, the slot and its outcome) or
\ unsupported (dependency-unsupported), never accepted; one named N.rec
\ itself (N2 against the generated recursor: rejected, already-declared,
\ with the type accepted) the same. With the type accepted, the first is
\ accepted.
: type-as ( outcome -- ) 0 lf-env lf-env-slot lf-slot-outcome ! ;
: as-unknown ( -- ) outcome-unknown type-as ;
: as-unsupported ( -- ) outcome-unsupported type-as ;
: k5-run ( c-addr u xt -- outcome code n1 n2 )
  >r cs-load r> cs-probe! lf-diag-clear cs-run lf-diag@ nip -rot cs-unload ;
: use-rec ( -- c-addr u ) s" after.nat-left-out-then-use-rec" ;
: def-rec ( -- c-addr u ) s" after.recursor-left-out-then-def-rec" ;
T{ use-rec ' as-unknown k5-run
   -> outcome-unknown lf-diag-dependency-undecided 0 outcome-unknown }T
T{ use-rec ' as-unsupported k5-run
   -> outcome-unsupported lf-diag-dependency-unsupported 0 0 }T
T{ def-rec ' as-unknown k5-run
   -> outcome-unknown lf-diag-dependency-undecided 0 outcome-unknown }T
T{ def-rec ' as-unsupported k5-run
   -> outcome-unsupported lf-diag-dependency-unsupported 0 0 }T
: verdict ( c-addr u -- outcome code ) cs-load cs-plenty cs-at lf-diag-code@ cs-unload ;
T{ use-rec verdict nip def-rec verdict
   -> outcome-ok outcome-rejected lf-diag-already-declared }T
bye
