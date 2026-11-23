\ Meta cases of the tactic library (plan row TB2, piece E, slice E1;
\ docs/design/TACTIC_PATTERNS.md section 1): Lean 4.35.0's
\ Meta/Tactic/Cases.lean, MVarId.cases (:278-319) on a type whose
\ indices are independent, the simple case (:290-293: inductionCasesOn
\ :252, toCasesSubgoals :220), the split under obtain and rcases
\ (rcases.fs). Each word throws on failure (meta-must.fs), as Lean's do.
\ Public words:
\   lf-goal-cases ( goal major names nat-aux? -- subgoals )  MVarId.cases
\       of goal on the free variable major, in goal's context
\       (checkNotAssigned first): mkCasesContext? (the environment holds
\       Eq and HEq; the major's type through whnf an inductive type I
\       applied to all its parameters and indices; I.casesOn exists),
\       then Meta induction (meta-induction.fs's lf-goal-induction, names
\       its AltVarNames) with I.casesOn, or Nat.casesAuxOn for Nat when
\       nat-aux? is true and the environment has it (useNatCasesAuxOn,
\       :270: rcases' fields show as 0 and n + 1); subgoals as
\       lf-goal-induction's, each one's substitution with the major mapped
\       to its constructor applied (C.{us} params fields: getInductive-
\       UniverseAndParams) instead, and the constructor's name in its
\       fourth cell (the inductive's constructors in order)
\ Not supported yet (thrown unsupported, 99 at a tactic): an indexed
\ family (generalizeIndices and unifyEqs, slice E4); Lean's "not
\ applicable to the given hypothesis" (an export without Eq, HEq or
\ I.casesOn: the major's type is an inductive type whenever rcases asks).
\ Its nested-error wrapper (throwNestedTacticEx) has nothing to wrap
\ while every inner refusal is unsupported.
\ Lean call list: mkCasesContext? -> mcs-context (lf-match-const-induct,
\ lf-menv-data); inductionCasesOn -> mcs-recursor, lf-goal-induction;
\ toCasesSubgoals -> mcs-each (lf-mk-const-id, lf-fsubst-erase,
\ lf-fsubst-insert).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mcs-frames (a frame per call open, meta-must.fs's
\ lf-with-record), in the checker context (ADR 0009); no other. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/bounds.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../core/input.fs
require ../../author/declarations.fs
require ../goals.fs
require ../meta-env.fs
require ../meta-spine.fs
require ../term-eqv.fs
require ../whnf.fs
require ../infer.fs
require ../tactic-run.fs
require ../meta-must.fs
require ../app-builder.fs
require ../fvar-subst.fs
require ./goal.fs
require ./meta-induction.fs

begin-structure /mcs
  field: mcs-major       \ the major premise
  field: mcs-d           \ its inductive type's declaration
  field: mcs-type        \ its type through whnf
  field: mcs-out         \ the subgoals so far, a run
end-structure
/mcs context-slab: mcs-frames
: mcs ( -- frame ) mcs-frames slab-last ;
: mcs+ ( x -- ) mcs mcs-out @ swap lf-run+ mcs mcs-out ! ;

\ ---- mkCasesContext?: the environment's names, the major's type.
: mcs-find ( name -- d true | false ) lf-menv-find ok? dup 0= if nip then ;
: mcs-named ( c-addr u -- d true | false ) lfa-intern mcs-find ;
: mcs-has ( c-addr u -- ) mcs-named 0= if lf-tac-unported then drop ;
: mcs-data ( -- addr ) mcs mcs-d @ lf-menv-data ?dup 0= if lf-tac-unported then ;
: mcs-params# ( -- n ) mcs-data lf-ity-params lf-more-field ;
: mcs-indices# ( -- n ) mcs-data lf-ity-indices lf-more-field ;
: mcs-cases-on ( -- d )
  mcs mcs-d @ lf-menv-name s" casesOn" lfa-intern-part mcs-find 0= if lf-tac-unported then ;
: mcs-arity ( n -- ) mcs-params# mcs-indices# + <> if lf-tac-unported then ;
: mcs-context ( major -- )
  s" Eq" mcs-has s" HEq" mcs-has dup mcs mcs-major ! lf-infer! lf-whnf! dup mcs mcs-type !
  lf-meta-head-args >r lf-match-const-induct 0= if lf-tac-unported then mcs mcs-d ! r> mcs-arity
  mcs-cases-on drop mcs-indices# if lf-tac-unported then ;

\ ---- inductionCasesOn: Nat.casesAuxOn for Nat when asked, else I.casesOn.
: mcs-nat? ( -- flag ) mcs mcs-d @ lf-menv-name s" Nat" lfa-intern lf-name-same? ;
: mcs-recursor ( nat-aux? -- d )
  mcs-nat? and if s" Nat.casesAuxOn" mcs-named if exit then then mcs-cases-on ;
: mcs-split ( goal names nat-aux? -- subgoals )
  mcs-recursor swap mcs mcs-major @ -rot lf-goal-induction ;

\ ---- toCasesSubgoals: constructor i applied, the major mapped to it.
: mcs-ctor ( i -- name ) mcs-data lf-ity-ctors@ drop cell-at@ ;
: mcs-head ( name -- e ) mcs mcs-type @ lf-meta-head lf-const-levels lf-mk-const-id ;
: mcs-param ( e k -- e' ) mcs mcs-type @ swap lf-meta-app-arg lf-mk-app ;
: mcs-field ( e x -- e' outcome ) lf-mk-app outcome-ok ;
: mcs-ctor-app ( name fields -- e )
  swap mcs-head mcs-params# 0 ?do i mcs-param loop swap ['] mcs-field run-each lf-must ;
: mcs-subst ( fs e -- fs' ) >r mcs mcs-major @ lf-fsubst-erase mcs mcs-major @ r> lf-fsubst-insert ;
: mcs-cell ( subgoals i k -- x ) swap 4 * + run@ ;
: mcs-goal+ ( s i -- s i fields ) 2dup 0 mcs-cell mcs+ 2dup 1 mcs-cell dup mcs+ ;
: mcs-one ( s i -- s )
  mcs-goal+ >r 2dup 2 mcs-cell over mcs-ctor r> mcs-ctor-app mcs-subst mcs+ mcs-ctor mcs+ ;
: mcs-each ( subgoals -- subgoals' )
  dup run-count 4 / 0 ?do i mcs-one loop drop mcs mcs-out @ ;
: mcs-run ( goal major names nat-aux? -- subgoals ) rot mcs-context mcs-split mcs-each ;
: mcs-in ( goal major names nat-aux? -- subgoals ) mcs-frames ['] mcs-run lf-with-record ;
: lf-goal-cases ( goal major names nat-aux? -- subgoals )
  2over drop lf-goal-not-assigned ['] mcs-in lf-with-goal ;
base !   \ the BASE this file was loaded with
