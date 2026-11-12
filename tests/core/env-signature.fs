\ The checked environment's answers to inference (src/kernel/
\ env-signature.fs; plan task 2.2.3; ADR 0011 N1, K5, L1, L2; ADR 0015
\ decision 12 and Q1): lf-env-signature asked directly inside a check,
\ as mixed-infer.fs asks it at a constant, on cases of the inductive table
\ (tests/core/check-block-cases/, each the export pinned Lean printed).
\ Coverage classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 3. Interfaces: ( name pairs count fuel deciding -- root identity fuel' 0
\    | status ) for an accepted slot (Bool.rec), Lean's generated
\    recursor that no slot holds (Nat.rec), a quotient constant
\    (Quot.lift); the stored type itself when there are no universe
\    arguments.
\ 1. Outcomes: ok; rejected for too few or too many universe arguments
\    (L1) and for a name Lean's environment does not hold (N1); invalid
\    for negative fuel.
\ 5. Every fuel below the least exhausts the answer (L2's walk, the
\    generated recursor's construction, the quotient's statement), the
\    least gives the type; each allocation refused in turn makes it full.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

\ The constant node's name, universe arguments and their number.
: request ( const -- name pairs count ) lf-whnf-cref dup lf-crec-name @ swap lf-cref-pairs ;
: answer ( root identity fuel' 0 | status -- root|-1 outcome )
  dup ok? if drop drop drop outcome-ok else -1 swap then ;
\ Deciding, in a job of its own (whose mark the pass's rollback uses).
: signature ( const fuel -- root|-1 outcome )
  dup lf-minfer-start-env >r request r> true lf-env-signature answer ;
: aside ( const fuel -- root|-1 outcome )
  dup lf-minfer-start-env >r request r> false lf-env-signature answer ;
\ With count universe arguments instead of the constant's own number.
: miscounted ( const count -- outcome )
  >r request drop r> cs-plenty true lf-env-signature answer nip ;
: const-of ( name -- node )
  lf-name-generation @ 0 0 lf-cref-new cs-must lf-cterm-new cs-must drop ;
: target-name ( -- name ) cs cs-target @ lf-input-decl lf-idecl-name @ ;
: the-value ( -- node ) cs cs-target @ cs-value-of ;
\ An answer and the sweeps on it.
: swept? ( const -- flag ) dup ['] signature cs-pass-sweep swap ['] signature cs-pass-refusals and ;

\ ---------------------------------------------------------------------------
\ Lean's generated recursor: Nat.useRec.{u} := @Nat.rec.{u}, the file
\ without Nat.rec (one universe argument, u, the checked declaration's).
: generated ( -- )
  T{ the-value cs-plenty signature nip the-value cs-plenty aside nip -> outcome-ok outcome-ok }T
  \ the type built is Nat.rec's, which the declaration states as its own
  T{ the-value cs-plenty signature drop cs cs-target @ cs-type-of 100000 lf-expr-equal
     -> true outcome-ok }T
  T{ the-value 0 miscounted the-value 2 miscounted -> outcome-rejected outcome-rejected }T
  T{ the-value -1 signature -> -1 outcome-invalid }T
  T{ the-value swept? -> true }T ;
s" after.nat-left-out-then-use-rec" ' generated outcome-ok cs-probe-gives

\ An accepted slot: Bool.rec.{1} in iota.bool-true's type; the target's
\ own name, which no slot holds yet: N1.
: head ( -- const ) cs-type lf-whnf-head ;
: slots ( -- )
  T{ head cs-plenty signature nip head cs-plenty aside nip -> outcome-ok outcome-ok }T
  T{ head 0 miscounted head 2 miscounted -> outcome-rejected outcome-rejected }T
  T{ target-name const-of cs-plenty signature -> -1 outcome-rejected }T
  T{ head -1 signature -> -1 outcome-invalid }T
  T{ head swept? -> true }T ;
s" iota.bool-true" ' slots outcome-ok cs-probe-gives

\ A quotient constant: Quot.lift.{1, 1}, its type built from Lean's
\ statement (the record's is not read).
: lift ( -- const ) cs-type 4 0 ?do lf-term-second@ loop lf-term-first@ lf-term-second@
  lf-whnf-head ;
: quotients ( -- )
  T{ lift cs-plenty signature nip lift cs-plenty aside nip -> outcome-ok outcome-ok }T
  T{ lift 1 miscounted lift 3 miscounted -> outcome-rejected outcome-rejected }T
  T{ lift swept? -> true }T ;
s" quot.lift-on-mk" ' quotients outcome-ok cs-probe-gives
bye
