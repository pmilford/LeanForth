\ Inference of a projection (src/kernel/infer-proj.fs; Lean's infer_proj,
\ type_checker.cpp 255-301; plan task 5.2.2, ADR 0015 J2), through
\ mixed-infer.fs's hook, on cases of the inductive table (tests/core/
\ check-block-cases/, each the export pinned Lean printed;
\ tests/core/check-block.fs checks their verdicts): each case's value is
\ fun (p : T) => p.i. Coverage classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 3. Interfaces, in a check: the structure a projection's type names
\    (lf-iproj-checked): Prod's declaration; rejected (invalidProj) for a
\    type whose head is no constant, a constant of another name, or a
\    constructor; rejected (unknownConstant, N1) for a name Lean's
\    environment does not hold; the constructor's declaration; the spine
\    words.
\ 1, 7. The value's type: ok for a field of Prod and for a proof's field
\    of And; invalidProj (rejected, diagnostic invalid-proj) for another
\    structure's projection, an index past the fields, a data field of a
\    proof.
\ 5. Every fuel below the least exhausts the value's inference, the least
\    gives its type; each allocation refused in turn makes it full.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

\ A case's value fun (p : T) => p.i: its binder's type and its body.
: the-value ( -- node ) cs cs-target @ cs-value-of ;
: domain ( -- Ty ) the-value lf-term-first@ ;
: body ( -- node ) the-value lf-term-second@ ;
: leaf ( -- leaf ) body lf-proj-leaf ;
: sort-node ( -- node ) 0 lf-term-sort cs-must ;
: const-of ( name -- node )
  lf-name-generation @ 0 0 lf-cref-new cs-must lf-cterm-new cs-must drop ;
: leaf-of ( name -- leaf ) 0 lf-term-bvar cs-must swap 0 lf-proj-of ok? cs-must lf-proj-leaf ;
: target-name ( -- name ) cs cs-target @ lf-input-decl lf-idecl-name @ ;
\ Inference of a node in a job of its own (environment mode).
: cs-infer ( node fuel -- type outcome ) lf-minfer-start-env lf-minfer-walk ;

\ ---------------------------------------------------------------------------
\ 3. proj.data: fun (p : Nat × Nat) => p.1 (index 0).
: prod-decl ( -- decl ) leaf domain lf-iproj-checked drop ;
: ctor-name ( decl -- name ) lf-idecl-data lf-ity-ctors@ drop @ ;
: structures ( -- )
  T{ leaf domain lf-iproj-checked nip -> outcome-ok }T
  T{ prod-decl lf-idecl-name @ leaf lf-proj-name lf-name-same? -> true }T
  T{ prod-decl lf-iproj-ctor swap lf-idecl-name @ prod-decl ctor-name lf-name-same?
     -> outcome-ok true }T
  T{ leaf sort-node lf-iproj-checked -> -1 outcome-rejected }T
  T{ leaf domain lf-term-second@ lf-iproj-checked -> -1 outcome-rejected }T  \ Nat
  T{ prod-decl ctor-name dup leaf-of swap const-of lf-iproj-checked -> -1 outcome-rejected }T
  T{ target-name dup leaf-of swap const-of lf-iproj-checked nip -> outcome-rejected }T ;
: spines ( -- )
  T{ domain lf-iproj-n domain lf-iproj-head lf-iproj-n -> 2 0 }T
  T{ domain 2 1 lf-ind-arg domain lf-term-second@ = -> true }T
  T{ domain lf-iproj-head lf-iproj-pi? domain lf-iproj-pi? -> false false }T ;
s" proj.data" ' structures outcome-ok cs-probe-gives
s" proj.data" ' spines outcome-ok cs-probe-gives

\ ---------------------------------------------------------------------------
\ 1, 7, 5. The value's inference: its outcome, with the sweeps. Notes: 0
\ the type, 1 the outcome, 2 the fuel sweep, 3 the refusals, 4 the
\ diagnostic of the plenty run.
: inferred ( -- )
  the-value ['] cs-infer cs-pass-sweep cs-note
  the-value ['] cs-infer cs-pass-refusals cs-note
  lf-diag-clear the-value cs-plenty cs-infer 2drop lf-diag-code@ cs-note ;
: inference ( c-addr u outcome -- inferred sweep refusals diag )
  >r ['] inferred r> cs-probe-gives 1 cs-noted 2 cs-noted 3 cs-noted 4 cs-noted ;
T{ s" proj.data" outcome-ok inference drop -> outcome-ok true true }T
T{ s" proj.proof-of-proof" outcome-ok inference drop -> outcome-ok true true }T
\ invalidProj: no allocation is refused before the rejection, or one is
\ (full); the fuel sweep as for ok.
T{ s" proj.wrong-structure" outcome-rejected inference nip
   -> outcome-rejected true lf-diag-invalid-proj }T
T{ s" proj.index-out-of-range" outcome-rejected inference nip
   -> outcome-rejected true lf-diag-invalid-proj }T
T{ s" proj.data-from-proof" outcome-rejected inference nip
   -> outcome-rejected true lf-diag-invalid-proj }T
bye
