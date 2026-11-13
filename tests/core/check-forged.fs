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
T{ ' as-nothing forged -> outcome-unsupported lf-diag-unsupported-kind 99 lf-safety-safe }T
: plain ( budget -- outcome ) s" proj.data" cs-load cs-at cs-unload ;
T{ cs-plenty plain -1 plain -> outcome-ok outcome-invalid }T
T{ lf-check-no-maker -> 0 -1 }T
bye
