\ Quotients (src/kernel/quot.fs; plan task 5.2.4; ADR 0015 Q1, Q2): the
\ reduction quot_reduce_rec of Quot.lift and Quot.ind on Quot.mk, and the
\ check of the quotient records (add_quot's check_eq_type and
\ check_name), on cases of the inductive table (tests/core/
\ check-block-cases/, each the export pinned Lean printed;
\ tests/core/check-block.fs checks their verdicts). Coverage classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 3. Interfaces, in a check: mk_pos by the head's name; the rule of an
\    application (its mk_pos, or -1 for another head, a head Lean's
\    environment does not hold, too few arguments); Quot.mk recognised;
\    argument i of a spine; each answer with its outcome.
\ 1, 7. Lean's whnf of Quot.lift f h (Quot.mk r a) is f a, of the same
\    with an argument after the quotient f a x, of Quot.ind h (Quot.mk r
\    a) h a.
\ 5. Every fuel below the least exhausts those whnfs, the least gives the
\    reduct; each allocation refused in turn makes them full; the check of
\    the Quot record, whose Eq shape and statements the matcher compares,
\    exhausted below its least budget at every budget.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

\ The left side of the equation a case's type states under n binders.
: under ( node n -- body ) 0 ?do lf-term-second@ loop ;
: lhs ( eq -- node ) lf-term-first@ lf-term-second@ ;
: rhs ( eq -- node ) lf-term-second@ ;
variable binders
: equation ( -- eq ) cs-type binders @ under ;
: redex ( -- node ) equation lhs ;
: name-in ( const -- name ) lf-const-name ;
: head-name ( node -- name ) lf-whnf-head name-in ;
: decl-named ( name -- decl|0 )
  lf-input-count 0 ?do
    dup i lf-input-decl lf-idecl-name @ lf-name-same? if drop i lf-input-decl unloop exit then
  loop drop 0 ;
: sort-node ( -- node ) 0 lf-term-sort cs-must ;
: app ( f a -- node ) lf-term-app cs-must ;
: const-of ( name -- node )
  lf-name-generation @ 0 0 lf-cref-new cs-must lf-cterm-new cs-must drop ;
: target-name ( -- name ) cs cs-target @ lf-input-decl lf-idecl-name @ ;

\ ---------------------------------------------------------------------------
\ 3. In a check of quot.lift-on-mk: Quot.lift {Nat} {r} {Nat} f h
\ (Quot.mk r a), six arguments, the quotient sixth (mk_pos 5).
: positions ( -- )
  T{ redex head-name lf-quot-pos -> 5 }T
  T{ redex 5 lf-quot-arg head-name lf-quot-pos -> -1 }T      \ Quot.mk
  T{ redex lf-quot-n -> 6 }T ;
: rules ( -- )
  T{ redex lf-quot-rule -> 5 outcome-ok }T
  T{ sort-node lf-quot-rule -> -1 outcome-ok }T
  T{ equation lf-quot-rule -> -1 outcome-ok }T                \ Eq ...
  T{ redex lf-term-first@ lf-quot-rule -> -1 outcome-ok }T    \ five arguments
  T{ redex lf-whnf-head lf-quot-held -> true outcome-ok }T
  T{ equation lf-whnf-head lf-quot-held -> false outcome-ok }T  \ Eq: no quotient
  T{ target-name const-of lf-quot-held -> false outcome-ok }T ;
: makers ( -- )
  T{ redex 5 lf-quot-arg lf-quot-mk? redex lf-quot-mk? -> true false }T
  T{ 0 lf-term-bvar cs-must lf-quot-mk? -> false }T
  \ three arguments, but a variable's (r r r r): no Quot.mk
  T{ redex 5 lf-quot-arg lf-term-first@ rhs dup >r r@ app r@ app r> app
     lf-quot-mk? -> false }T ;
\ The whnf: f a, a new application of argument 3 (f) to Quot.mk's last
\ argument (a); then the sweeps.
: reduct ( -- )
  T{ redex cs-plenty cs-whnf drop dup lf-term-first@ swap lf-term-second@
     redex 3 lf-quot-arg redex 5 lf-quot-arg lf-term-second@ d= -> true }T
  T{ redex ['] cs-whnf cs-pass-sweep -> true }T
  T{ redex ['] cs-whnf cs-pass-refusals -> true }T ;
4 binders !
: lift-on-mk ( xt -- ) s" quot.lift-on-mk" rot outcome-ok cs-probe-gives ;
' positions lift-on-mk
' rules lift-on-mk
' makers lift-on-mk
' reduct lift-on-mk

\ An argument after the quotient goes to the reduct: f a x (5 binders).
: extra ( -- )
  T{ redex lf-quot-n redex lf-quot-rule -> 7 5 outcome-ok }T
  T{ redex cs-plenty cs-whnf nip -> outcome-ok }T
  T{ redex cs-plenty cs-whnf drop lf-term-second@ redex 6 lf-quot-arg = -> true }T
  T{ redex ['] cs-whnf cs-pass-sweep -> true }T
  T{ redex ['] cs-whnf cs-pass-refusals -> true }T ;
5 binders !
s" quot.lift-extra-argument" ' extra outcome-ok cs-probe-gives

\ Quot.ind {Nat} {r} {β} h (Quot.mk r a): mk_pos 4; h a.
: ind ( -- )
  T{ redex head-name lf-quot-pos redex lf-quot-rule -> 4 4 outcome-ok }T
  T{ redex cs-plenty cs-whnf drop lf-term-first@ redex 3 lf-quot-arg = -> true }T
  T{ redex ['] cs-whnf cs-pass-sweep -> true }T
  T{ redex ['] cs-whnf cs-pass-refusals -> true }T ;
4 binders !
s" quot.ind-on-mk" ' ind outcome-ok cs-probe-gives

\ No quotient in the argument: Quot.lift on a variable stays.
: stuck ( -- )
  T{ redex cs-plenty cs-whnf -> redex outcome-ok }T ;
3 binders !
s" quot.lift-stuck-on-variable" ' stuck outcome-rejected cs-probe-gives

\ ---------------------------------------------------------------------------
\ 3, 1. check_eq_type's pieces in a check of iota.bool-true, whose
\ environment has Bool, Bool.rec and False but no Eq: Eq not found,
\ rejected (95); Bool found, but no Eq's shape (no parameter, two
\ constructors), and Bool.rec no inductive type: rejected; the name being
\ checked, which Lean's environment does not hold: rejected.
: bool-true ( -- node ) cs-type rhs ;
: bool-decl ( -- decl ) bool-true head-name decl-named lf-idecl-type @ head-name decl-named ;
: rec-decl ( -- decl ) cs-type head-name decl-named ;
: eq-pieces ( -- )
  T{ lf-quot-eq -> outcome-rejected }T
  T{ bool-decl lf-idecl-name @ lf-quot-slot nip -> outcome-ok }T
  T{ bool-decl lf-quot-eq-form? rec-decl lf-quot-eq-form? -> false false }T
  T{ bool-decl lf-quot-eq-shape rec-decl lf-quot-eq-shape -> outcome-rejected outcome-rejected }T
  T{ target-name lf-quot-slot nip -> outcome-rejected }T ;
s" iota.bool-true" ' eq-pieces outcome-ok cs-probe-gives

\ ---------------------------------------------------------------------------
\ 5. The Quot record's check (Eq's shape, Eq.refl's, the four names):
\ every budget below the least exhausted, the least and above ok; the
\ wrong Eq rejected from its least on.
: quot-record ( -- ) lf-input-count 4 - cs-target! ;
T{ s" quotinit.with-eq" cs-load quot-record 1 cs-fuel-sweep cs-unload -> true }T
T{ s" quotinit.eq-wrong-shape" cs-load 1 cs-fuel-sweep cs cs-normal @ cs-unload
   -> true outcome-rejected }T

\ 2, 3 (coverage COV2). Step 2 of a quotient record outside any check (no
\ snapshot of the checked environment to look names up in): invalid; so
\ is an inductive block's check (check-block.fs) there, whatever its fuel.
T{ lf-quot-names 1000 lf-block-check -> outcome-invalid outcome-invalid }T
bye
