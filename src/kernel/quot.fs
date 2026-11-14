\ Quotients as Lean's kernel builds and reduces them (plan task 5.2.4;
\ ADR 0015 rules Q1, Q2): ports of add_quot and check_eq_type
\ (quot.cpp 19-100) and quot_reduce_rec (quot.h 39-66), which
\ reduce_recursor (type_checker.cpp 393-398) tries before iota. [kernel]
\ code: not through the review gate (AGENTS.md).
\
\ Q1. Lean's Declaration.quotDecl carries no data: add_quot checks Eq
\ (check_eq_type) and the four names (check_name), then adds Quot,
\ Quot.mk, Quot.lift and Quot.ind with types it builds itself and marks
\ the quotient initialised; a second add_quot changes nothing (48-49). An
\ export holds the four constants as quotient records, each with its
\ type; Lean's replay adds quotDecl for each (Replay.lean 129-133).
\ check-declaration.fs checks each record: U1, lf-quot-names, lf-quot-eq,
\ the type's audit, then lf-quot-builtin. Steps:
\ - lf-quot-names ( -- outcome ), check_name (review rvAX): while no
\   earlier quotient record is accepted, none of the four names is
\   declared (N2 with K5 on each); once one is (the quotient initialised),
\   only the record's own name, as LeanForth holds one constant per slot.
\   environment.fs holds the four names against every other declaration
\   once the quotient is initialised (lf-env-quot-holding), so a user's
\   Quot.mk is refused then, or, declared first, leaves every quotient
\   record rejected, as in Lean.
\ - lf-quot-eq ( -- outcome ), check_eq_type: Eq, looked up and recorded
\   as a dependency, is an inductive type with one universe parameter and
\   one constructor; its type is {alpha : Sort u} -> alpha -> alpha ->
\   Prop, its constructor's (looked up by the name Eq's record lists)
\   forall {alpha : Sort u} (a : alpha), @Eq.{u} alpha a a, u each one's
\   first universe parameter; any other Eq is rejected (diagnostic 95),
\   none is the lookup's rejection (N1), and an undecided or unsupported
\   one the lookup's outcome (K5).
\ - lf-quot-builtin ( decl well? -- outcome ): the record is one of the
\   four by name (the entries below); with other universe parameters or
\   another type than Lean's (core/statement-match.fs; a type the audit
\   refused, well? false, is another) it is accepted with the warning
\   lf-warn-quot-record, as replay ignores the record, and every use is
\   typed with Lean's own type, built from the entry (lf-envsig-builtin,
\   env-signature.fs). Not yet as Lean (gaps of a follow-up of plan task
\   5.2.4, no export Lean writes reaches them): a record of another name
\   is rejected (diagnostic 96) where replay ignores it; a second record
\   of a name, and a use of one of the four constants that no slot holds
\   while the quotient is initialised, are unknown (diagnostic 77).
\ The comparisons read their fuel from lf-stmt-fuel (exhausted when it
\ runs out).
\
\ Q2. lf-quot-rule ( app -- mk outcome ): the reduction rule for an
\ application whose head is a constant named Quot.lift (mk 5) or Quot.ind
\ (mk 4) that the check's environment holds as a quotient record (Lean's
\ is_quot_initialized: no other declaration can then hold the name, Q1),
\ with more than mk arguments; -1 for none (any other head, fewer
\ arguments, outside a check); or the head's lookup's failure. Then
\ lf-quot-reduce ( app mk frames -- ... frames next ), a step of whnf.fs's
\ pass that ends the iota hook's visit: argument mk is put in Lean's whnf
\ (a child visit); when that is Quot.mk (by name, as Lean: with the
\ quotient initialised the name is Lean's constant, Q1) applied to
\ exactly three arguments, argument 3 of app, the function, applied to
\ the third, then to app's arguments after mk, is the reduct; otherwise
\ no rule applies (-1 ok).
\ State: none of its own; the matcher's record is core/statement-match.fs's,
\ the frames whnf.fs's.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/names.fs
require ../core/terms.fs
require ./environment.fs
require ./mixed-head.fs
require ../core/statement-match.fs
require ./whnf.fs

\ Lean's four constants (quot.cpp 54-97), entries of core/statement-match.fs.
\ Quot.{u} : {alpha : Sort u} -> (alpha -> alpha -> Prop) -> Sort u
0 1 lf-stmt: lf-quot-type  s" Quot" lf-text,
  lf-statement: P S u0 P P #0 P #1 S z S u0 end-statement
\ Quot.mk.{u} : {alpha : Sort u} -> (r : alpha -> alpha -> Prop) -> alpha
\   -> @Quot.{u} alpha r
1 1 lf-stmt: lf-quot-mk  s" Quot.mk" lf-text,
  lf-statement: P S u0 P P #0 P #1 S z P #1 A A C Quot 1 u0 #2 #1 end-statement
\ Quot.lift.{u, v} : {alpha : Sort u} -> {r : alpha -> alpha -> Prop}
\   -> {beta : Sort v} -> (f : alpha -> beta)
\   -> (forall a b : alpha, r a b -> f a = f b) -> @Quot.{u} alpha r -> beta
2 2 lf-stmt: lf-quot-lift  s" Quot.lift" lf-text,
  lf-statement: P S u0 P P #0 P #1 S z P S u1 P P #2 #1
    P P #3 P #4 P A A #4 #1 #0 A A A C Eq 1 u1 #4 A #3 #2 A #3 #1
    P A A C Quot 1 u0 #4 #3 #3 end-statement
\ Quot.ind.{u} : {alpha : Sort u} -> {r : alpha -> alpha -> Prop}
\   -> {beta : @Quot.{u} alpha r -> Prop}
\   -> (forall a : alpha, beta (@Quot.mk.{u} alpha r a))
\   -> forall q : @Quot.{u} alpha r, beta q
3 1 lf-stmt: lf-quot-ind  s" Quot.ind" lf-text,
  lf-statement: P S u0 P P #0 P #1 S z P P A A C Quot 1 u0 #1 #0 S z
    P P #2 A #1 A A A C Quot.mk 1 u0 #3 #2 #0
    P A A C Quot 1 u0 #3 #2 A #2 #0 end-statement
create lf-quot-entries lf-quot-type , lf-quot-mk , lf-quot-lift , lf-quot-ind ,
\ Eq's type and its constructor's (quot.cpp 29-42), u the first parameter.
: lf-quot-eq-text ( -- c-addr u ) s" P S u0 P #0 P #1 S z" ;
: lf-quot-refl-text ( -- c-addr u ) s" P S u0 P #0 A A A C Eq 1 u0 #1 #0 #0" ;

: lf-quot-site ( -- site ) c" quot lf-quot-check" ;
: lf-quot-not-eq ( -- outcome )
  lf-env-limit 0 lf-quot-site lf-diag-quot-eq lf-diag-note outcome-rejected ;
: lf-quot-forged ( -- outcome )
  lf-env-limit 0 lf-quot-site lf-diag-quot-type lf-diag-note outcome-rejected ;

\ check_eq_type. A constant found by name, recorded as a dependency: its
\ declaration, read in the snapshot; Lean's generated recursor is no
\ inductive type.
: lf-quot-slot ( name -- decl outcome )
  lf-env-resolve ok-then? 0= if -1 swap exit then
  dup 0< if drop -1 lf-quot-not-eq exit then
  lf-env-usable ok-then? if lf-slot-decl outcome-ok else -1 swap then ;
: lf-quot-ctors ( decl -- items n )
  lf-idecl-data lf-ity-all cells + lf-more-next lf-more-list ;
: lf-quot-eq-form? ( decl -- flag )
  dup lf-idecl-kind @ lf-kind-inductive = 0= if drop false exit then
  dup lf-idecl-arity @ 1 = swap lf-quot-ctors nip 1 = and ;
: lf-quot-typed ( decl c-addr u -- flag outcome )
  2>r dup lf-idecl-type @ swap 2r> lf-stmt-match ;
\ A shape's comparison: ok, rejected (95), or the matcher's exhausted.
: lf-quot-matched ( flag outcome -- outcome )
  ok-then? if if outcome-ok else lf-quot-not-eq then then ;
: lf-quot-refl ( eq-decl -- outcome )
  lf-quot-ctors drop @ lf-quot-slot ok-then? 0= if exit then
  lf-quot-refl-text lf-quot-typed lf-quot-matched ;
: lf-quot-eq-shape ( decl -- outcome )
  dup lf-quot-eq-form? 0= if drop lf-quot-not-eq exit then
  dup lf-quot-eq-text lf-quot-typed lf-quot-matched
  dup ok? if drop lf-quot-refl else nip then ;
: lf-quot-eq-name ( -- name outcome )
  0 s" Eq" lf-name-str room-result ;
: lf-quot-eq ( -- outcome )
  lf-quot-eq-name ok-then? 0= if exit then
  lf-quot-slot ok-then? if lf-quot-eq-shape then ;

\ check_name in add_quot (quot.cpp 53-56): none of the four names is
\ declared below the record (environment.fs lf-env-unheld, with K5 and
\ Lean's generated recursors); a name that cannot be made is full.
: lf-quot-fresh ( limit -- outcome )
  4 0 ?do
    i lf-env-quot-text lf-stmt-intern 0= if 2drop outcome-full unloop exit then
    over lf-env-unheld dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
\ Once the quotient is initialised (an earlier quotient record accepted)
\ add_quot returns at once (48-49) and checks nothing. LeanForth holds one
\ constant per slot, so it checks the record's own name: ok when no slot
\ of it is usable; a second record of a name, which Lean accepts, is
\ unknown (diagnostic 77; a gap of the follow-up of plan task 5.2.4).
: lf-quot-own ( limit -- outcome )
  dup lf-input-name swap 2dup lf-env-find
  dup ok? if drop nip lf-env-generated exit then lf-env-n2 nip nip ;
\ The quotient below limit (environment.fs lf-env-quot-held, d class),
\ whatever the record's own name, decides: initialised, the record's own
\ name; not, the four names; K5, too early or full as the quotient
\ records below say (an earlier record not rejected holds its own name,
\ so the four names' check could not pass then).
: lf-quot-held-as ( limit d class -- outcome )
  dup ok? if 2drop lf-quot-own exit then
  dup outcome-rejected = if 2drop lf-quot-fresh exit then
  rot drop lf-env-n2-quot ;
: lf-quot-names-pass ( -- outcome )
  lf-env-checking 0= if outcome-invalid exit then nip
  lf-name-storage-valid? 0= if drop outcome-invalid exit then
  dup lf-env-quot-held lf-quot-held-as ;
\ Step 2 of a quotient record (check-declaration.fs), logged as N2.
: lf-quot-names ( -- outcome )
  lf-log? 0= if lf-quot-names-pass exit then
  lf-env-limit lf-log-none lf-rule-fresh-name ['] lf-quot-names-pass lf-env-logged ;

\ The entry of Lean's constant a record names, by name alone; it also
\ gives inference the constant's type (env-signature.fs).
: lf-quot-at ( k -- entry ) cells lf-quot-entries + @ ;
: lf-quot-named? ( decl entry -- flag )
  lf-stmt-named rot lf-idecl-name @ -rot lf-stmt-name? ;
: lf-quot-named ( decl -- entry|0 )
  4 0 ?do dup i lf-quot-at lf-quot-named? if drop i lf-quot-at unloop exit then loop
  drop 0 ;
:noname ( decl -- entry|0 )
  dup lf-idecl-kind @ lf-kind-quotient = if lf-quot-named else drop 0 then
  ; is lf-envsig-builtin
\ The record is one of Lean's four constants by name; with other universe
\ parameters or another type it is accepted with a warning, as Lean's
\ replay ignores the record (B4; ADR 0015 Q1, owner answer Q2). A type the
\ audit refused (well? false: a loose variable, an unsupported form) is
\ another type, never given to the matcher, which needs an audited root
\ (review rvAX L1).
32 constant lf-warn-quot-record   \ beside inductive-block.fs's B4 bits
: lf-quot-compared ( decl entry well? -- flag outcome )
  if lf-stmt-is? else 2drop false outcome-ok then ;
: lf-quot-builtin ( decl well? -- outcome )
  over lf-quot-named ?dup 0= if 2drop lf-quot-forged exit then
  swap lf-quot-compared ok-then? 0= if exit then
  0= if lf-warn-quot-record lf-env-warnings! then outcome-ok ;

\ ---------------------------------------------------------------------------
\ Q2, quot_reduce_rec. mk_pos by the head's name, arg_pos always 3.
: lf-quot-pos ( name -- mk|-1 )
  dup s" Quot.lift" lf-stmt-name? if drop 5 exit then
  s" Quot.ind" lf-stmt-name? if 4 else -1 then ;
\ The head's lookup: a quotient record of the environment, or no rule.
: lf-quot-held ( const -- flag outcome )
  lf-whnf-lookup ok-then? 0= if false swap exit then
  dup 0< if drop false outcome-ok exit then
  lf-whnf-decl ok-then? 0= if false swap exit then
  lf-idecl-kind @ lf-kind-quotient = outcome-ok ;
: lf-quot-n ( app -- n ) lf-mhead-spine nip ;
: lf-quot-applied ( app mk -- mk|-1 ) swap lf-quot-n over > 0= if drop -1 then ;
: lf-quot-headed ( app const -- mk outcome )
  dup lf-whnf-cref lf-crec-name @ lf-quot-pos dup 0< if nip nip outcome-ok exit then
  swap lf-quot-held ok-then? 0= if nip nip -1 swap exit then
  if lf-quot-applied else 2drop -1 then outcome-ok ;
: lf-quot-rule ( app -- mk outcome )
  lf-whnf-env? 0= if drop -1 outcome-ok exit then
  dup lf-whnf-head dup lf-whnf-const? if lf-quot-headed else 2drop -1 outcome-ok then ;

\ Argument i of app, which has n arguments (Lean's args[i]).
: lf-quot-peel ( node k -- node' ) 0 ?do lf-term-first@ loop ;
: lf-quot-arg ( app i -- arg ) over lf-quot-n swap - 1- lf-quot-peel lf-term-second@ ;
: lf-quot-mk? ( node -- flag )
  dup lf-quot-n 3 = 0= if drop false exit then
  lf-whnf-head dup lf-whnf-const? 0= if drop false exit then
  lf-whnf-cref lf-crec-name @ s" Quot.mk" lf-stmt-name? ;
\ f, app's argument 3, applied to mk's last argument, then to app's k
\ arguments after mk_pos; a full store is full.
: lf-quot-made ( mk' app mk -- reduct outcome )
  rot dup lf-quot-mk? 0= if drop 2drop -1 outcome-ok exit then
  lf-term-second@ 2 pick 3 lf-quot-arg swap lf-term-app 0=
  if 2drop lf-rebuild-full exit then
  -rot over lf-quot-n swap - 1- lf-whnf-apply-last ;
\ The hook's step: argument mk in whnf (a child visit), app and mk saved
\ across it.
: lf-quot-back ( mk' outcome frames -- ... frames next )
  >r ok-then? 0= if 2 r@ frame-drop r> lf-whnf-failed exit then
  r@ frame-restore r@ frame-restore swap lf-quot-made r> 0 ;
: lf-quot-reduce ( app mk frames -- ... frames next )
  >r over r@ frame-save dup r@ frame-save lf-quot-arg r> ['] lf-quot-back lf-whnf-call ;
