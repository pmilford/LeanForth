\ Test support for the goals of plan FE1g-1 (src/front/goals.fs,
\ goal-print.fs): terms built with Lean's constants by name (the printer's
\ builder, tests/present/build.fs; no library is needed to print them),
\ free variables with their locals, views and goals, and the printed text
\ captured. Each word aborts the run when a constructor fails. Test-only.

require ../present/build.fs
require ../../src/front/goal-print.fs

\ A fresh session: the printer's stores, the local context and the
\ metavariable context, notation on, the capture as the sink.
: made ( x outcome -- x ) ok? 0= abort" goal-states: not made" ;
: g-room ( -- ) 100000 lf-term-capacity! must-ok 10000 lf-cref-capacity! must-ok ;
: g-fresh ( -- )
  fresh g-room lf-lctx-reset lf-mctx-reset lf-pst-reset
  ['] cap-sink lf-print-unicode lf-print-setup ;

\ Terms: Nat, numerals, a + b, a = b, Nat.succ a, propositions.
: nat ( -- t ) s" Nat" t-const ;
: nlit ( u -- t ) lf-hterm-cell must drop ;
: num ( u -- t )
  s" OfNat.ofNat" t-const nat t-app over nlit t-app s" instOfNatNat" t-const rot nlit t-app t-app ;
: add-inst ( -- t ) s" instHAdd" t-const nat t-app s" instAddNat" t-const t-app ;
: add ( a b -- t )
  2>r s" HAdd.hAdd" t-const nat t-app nat t-app nat t-app add-inst t-app 2r> >r t-app r> t-app ;
: eq ( a b -- t ) 2>r s" Eq" t-const nat t-app 2r> >r t-app r> t-app ;
: succ ( a -- t ) s" Nat.succ" t-const swap t-app ;
: true. ( -- t ) s" True" t-const ;
: arrow ( a b -- t ) t-pi ;

\ Hypotheses: a free variable of a type (or a let, or a have) with its
\ local, pushed on a view; flags as lctx-views.fs's.
: hyp-name ( c-addr u -- name ) nm ;
: local-of ( fvar c-addr u flags -- local ) >r hyp-name r> lf-local-new made ;
: hyp ( view type c-addr u -- view' fvar )
  rot lf-lctx-local made >r r@ -rot 0 local-of lf-view-push made r> ;
: hyp-hidden ( view type c-addr u -- view' fvar )
  rot lf-lctx-local made >r r@ -rot lf-local-inaccessible local-of lf-view-push made r> ;
: hyp-detail ( view type c-addr u -- view' fvar )
  rot lf-lctx-local made >r r@ -rot lf-local-impl-detail local-of lf-view-push made r> ;
: let-hyp ( view type value c-addr u -- view' fvar )
  2>r lf-lctx-let made 2r> rot >r r@ -rot 0 local-of lf-view-push made r> ;
: have-hyp ( view type value c-addr u -- view' fvar )
  2>r lf-lctx-have made 2r> rot >r r@ -rot 0 local-of lf-view-push made r> ;

\ Goals: a type in a view, with a tag (0 for none).
: tag ( c-addr u -- name ) nm ;
: goal ( type tag view -- goal ) lf-goal-new made ;

\ Printing: one goal, or the proof state's goals, captured.
: goal-text ( goal -- c-addr u ) cap-reset lf-goal-print must-ok cap ;
: goals-text ( -- c-addr u ) cap-reset lf-goals-print must-ok cap ;
