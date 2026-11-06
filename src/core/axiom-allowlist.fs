\ The axiom allowlist, version 1 (plan task 5.3.1; owner decision 4 as
\ amended 2026-11-03 and 2026-11-04, docs/project/OWNER_DECISIONS.md;
\ ADR 0006 amendment 2026-11-05). [axiom] [format] data: a change to it
\ needs the owner's approval and a new version.
\
\ An axiom declaration gets Lean's verdict: add_axiom (environment.cpp
\ 152-158) accepts any axiom whose type is well formed, and so does
\ LeanForth (check-declaration.fs). Proof status is apart from that
\ verdict: only the axioms listed here, with exactly the name, number of
\ universe parameters and statement given (statement-match.fs: binder and
\ universe parameter names aside), count as proved. Every other axiom --
\ sorryAx, an axiom a file declares, or one of these names with another
\ statement or other universe parameters -- is unlisted, and a declaration
\ that depends on one is marked NOT PROVED (exit 0 as Lean, 6 under
\ --strict-axioms). Lean.ofReduceBool and Lean.trustCompiler are never on
\ the list (owner decision 4). The statements name Iff, Eq, Nonempty,
\ Quot and Quot.mk, and a statement means Lean's only with Lean's
\ constants: a listed axiom counts as proved only when every constant its
\ statement names is Lean's 4.35.0 own (lf-lean-own?, below). Quot and
\ Quot.mk must be quotient constants, whose types are Lean's own
\ (kernel/quot.fs, ADR 0015 Q1); Eq, Iff and Nonempty inductive types
\ exactly as Lean's Init declares them: universe parameters, type and
\ numParams, a block of their own with one constructor of Lean's name,
\ universe parameters and type, accepted without a B4 warning (so their
\ numIndices and isRec are Lean's too). Otherwise the axiom is unlisted:
\ an export whose Iff is another type keeps Lean's verdict for propext,
\ marked NOT PROVED.
\
\ Each axiom is one bit of a slot's axiom set (environment.fs): the three
\ listed ones and one bit for every unlisted axiom. lf-axiom-bit ( decl
\ -- bit outcome ) gives an axiom declaration's bit (its outcome
\ exhausted when lf-stmt-fuel runs out), within a check's snapshot,
\ where lf-allow-found ( id -- decl|0 bits ), set by environment.fs,
\ looks the constants up (outside one, every axiom is unlisted);
\ lf-allowlist-bits are the bits that count as proved; lf-axiom-name (
\ bit -- c-addr u ) names a listed bit. State: one module record,
\ lf-allow-state (the names a matched statement met), a member of the
\ checker context; the entries are read-only data made while loading.

require ./statement-match.fs

1 constant lf-allowlist-version
1 constant lf-axiom-propext
2 constant lf-axiom-choice
4 constant lf-axiom-sound
8 constant lf-axiom-unlisted     \ any other axiom: NOT PROVED
lf-axiom-propext lf-axiom-choice or lf-axiom-sound or constant lf-allowlist-bits

\ The entries: Lean 4.35.0's statement (Init/Prelude.lean, Init/Core.lean),
\ in ASCII, then its name, universe parameters and statement as LeanForth
\ compares them.
\ propext : forall {a b : Prop}, (a <-> b) -> a = b
lf-axiom-propext 0 lf-stmt: lf-allow-propext  s" propext" lf-text,
  lf-statement: P S z P S z P A A C Iff 0 #1 #0 A A A C Eq 1 s z S z #2 #1 end-statement
\ Classical.choice.{u} : {alpha : Sort u} -> Nonempty alpha -> alpha
lf-axiom-choice 1 lf-stmt: lf-allow-choice  s" Classical.choice" lf-text,
  lf-statement: P S u0 P A C Nonempty 1 u0 #0 #1 end-statement
\ Quot.sound.{u} : forall {alpha : Sort u} {r : alpha -> alpha -> Prop}
\   {a b : alpha}, r a b -> Quot.mk r a = Quot.mk r b
lf-axiom-sound 1 lf-stmt: lf-allow-sound  s" Quot.sound" lf-text,
  lf-statement: P S u0 P P #0 P #1 S z P #1 P #2 P A A #2 #1 #0
    A A A C Eq 1 u0 A A C Quot 1 u0 #4 #3
      A A A C Quot.mk 1 u0 #4 #3 #2 A A A C Quot.mk 1 u0 #4 #3 #1 end-statement

create lf-allowlist lf-allow-propext , lf-allow-choice , lf-allow-sound ,
here lf-allowlist - 1 cells / constant lf-allowlist#
: lf-allow-at ( k -- entry ) cells lf-allowlist + @ ;

\ Lean's own constants. The lookup: the accepted declaration named id and
\ its slot's warning bits, or 0 0 (none, or no check's snapshot).
defer lf-allow-found ( id -- decl|0 bits )
:noname ( id -- 0 0 ) drop 0 0 ; is lf-allow-found
\ Lean 4.35.0's inductive types the statements name (Init/Prelude.lean,
\ Init/Core.lean): each type's entry, its constructor's and numParams.
\ Eq.{u} : {alpha : Sort u} -> alpha -> alpha -> Prop
0 1 lf-stmt: lf-lean-eq  s" Eq" lf-text,
  lf-statement: P S u0 P #0 P #1 S z end-statement
\ Eq.refl.{u} : forall {alpha : Sort u} (a : alpha), @Eq.{u} alpha a a
0 1 lf-stmt: lf-lean-eq-refl  s" Eq.refl" lf-text,
  lf-statement: P S u0 P #0 A A A C Eq 1 u0 #1 #0 #0 end-statement
\ Iff : Prop -> Prop -> Prop
0 0 lf-stmt: lf-lean-iff  s" Iff" lf-text,  lf-statement: P S z P S z S z end-statement
\ Iff.intro : forall {a b : Prop}, (a -> b) -> (b -> a) -> Iff a b
0 0 lf-stmt: lf-lean-iff-intro  s" Iff.intro" lf-text,
  lf-statement: P S z P S z P P #1 #1 P P #1 #3 A A C Iff 0 #3 #2 end-statement
\ Nonempty.{u} : Sort u -> Prop
0 1 lf-stmt: lf-lean-nonempty  s" Nonempty" lf-text,
  lf-statement: P S u0 S z end-statement
\ Nonempty.intro.{u} : forall {alpha : Sort u}, alpha -> Nonempty.{u} alpha
0 1 lf-stmt: lf-lean-nonempty-intro  s" Nonempty.intro" lf-text,
  lf-statement: P S u0 P #0 A C Nonempty 1 u0 #1 end-statement
create lf-lean-types
  lf-lean-eq , lf-lean-eq-refl , 2 ,  lf-lean-iff , lf-lean-iff-intro , 2 ,
  lf-lean-nonempty , lf-lean-nonempty-intro , 1 ,
3 constant lf-lean-types#
: lf-lean-type ( k -- spec ) 3 * cells lf-lean-types + ;
: lf-lean-named? ( id k -- flag ) lf-lean-type @ lf-stmt-named lf-stmt-name? ;
: lf-lean-spec ( id -- spec|0 )
  lf-lean-types# 0 ?do
    dup i lf-lean-named? if drop i lf-lean-type unloop exit then
  loop drop 0 ;
\ The type's data: alone in its block, with Lean's numParams.
: lf-lean-data? ( data spec -- flag )
  2 cells + @ over lf-ity-params lf-more-field = swap lf-ity-all@ nip 1 = and ;
: lf-lean-shape? ( decl spec -- flag )
  over lf-idecl-kind @ lf-kind-inductive = 0= if 2drop false exit then
  swap lf-idecl-data ?dup 0= if drop false exit then swap lf-lean-data? ;
\ Its one constructor, looked up by the name the data gives, is Lean's.
: lf-lean-ctor-decl ( data -- decl|0 )
  lf-ity-ctors@ 1 = if @ lf-allow-found drop else drop 0 then ;
: lf-lean-ctor? ( data spec -- flag outcome )
  swap lf-lean-ctor-decl ?dup 0= if drop false outcome-ok exit then
  dup lf-idecl-kind @ lf-kind-constructor = 0= if 2drop false outcome-ok exit then
  swap cell+ @ lf-stmt-is? ;
: lf-lean-inductive? ( decl spec -- flag outcome )
  2dup lf-lean-shape? 0= if 2drop false outcome-ok exit then
  2dup @ lf-stmt-is? ok-then? 0= if nip nip false swap exit then
  0= if 2drop false outcome-ok exit then
  swap lf-idecl-data swap lf-lean-ctor? ;
\ Whether the constant named id is Lean's own: a quotient constant, or
\ one of the types above, accepted without a warning.
: lf-lean-quot? ( decl -- flag ) lf-idecl-kind @ lf-kind-quotient = ;
: lf-lean-own? ( id -- flag outcome )
  dup lf-allow-found >r ?dup 0= if r> 2drop false outcome-ok exit then
  dup lf-lean-quot? if r> 2drop drop true outcome-ok exit then
  r> if 2drop false outcome-ok exit then
  swap lf-lean-spec ?dup 0= if drop false outcome-ok exit then lf-lean-inductive? ;

\ The names the matched statement met, copied, as each test above runs
\ the matcher again.
begin-structure /lf-allow
  lf-stmt-room cells +field lf-allow-ids
end-structure
/lf-allow context-record: lf-allow-state
: lf-allow-id ( k -- addr ) cells lf-allow-state lf-allow-ids + ;
: lf-allow-keep ( -- n ) lf-stmt-met@ dup 0 ?do i lf-stmt-id @ i lf-allow-id ! loop ;
: lf-allow-lean? ( -- flag outcome )
  lf-allow-keep 0 ?do
    i lf-allow-id @ lf-lean-own? ok-then? 0= if false swap unloop exit then
    0= if false outcome-ok unloop exit then
  loop true outcome-ok ;
\ A listed bit stays when its statement's constants are Lean's own.
: lf-allow-checked ( bit -- bit' outcome )
  lf-allow-lean? ok-then? 0= if nip -1 swap exit then
  0= if drop lf-axiom-unlisted then outcome-ok ;

\ An axiom declaration's bit: its entry's when it is one, else unlisted.
: lf-allow-of ( decl k -- bit|0 outcome )
  lf-allow-at tuck lf-stmt-is? ok-then? 0= if nip 0 swap exit then
  if lf-stmt-code else drop 0 then outcome-ok ;
: lf-axiom-bit ( decl -- bit outcome )
  lf-allowlist# 0 ?do
    dup i lf-allow-of ok-then? 0= if nip -1 swap unloop exit then
    ?dup if nip lf-allow-checked unloop exit then
  loop drop lf-axiom-unlisted outcome-ok ;
\ The name of a listed bit.
: lf-axiom-name ( bit -- c-addr u )
  lf-allowlist# 0 ?do
    i lf-allow-at dup lf-stmt-code 2 pick = if nip lf-stmt-named unloop exit then drop
  loop drop s" ?" ;
