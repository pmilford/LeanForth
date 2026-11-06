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
\ Quot and Quot.mk by name; the file's own declarations of those names
\ are checked by the kernel, Eq and the quotient constants against Lean's
\ shapes too (quot.fs), Iff and Nonempty not yet (a gap of plan task
\ 5.3.1: an export whose Iff or Nonempty is another type keeps propext's
\ or Classical.choice's mark).
\
\ Each axiom is one bit of a slot's axiom set (environment.fs): the three
\ listed ones and one bit for every unlisted axiom. lf-axiom-bit ( decl
\ -- bit outcome ) gives an axiom declaration's bit (its outcome
\ exhausted when lf-stmt-fuel runs out); lf-allowlist-bits are the bits
\ that count as proved; lf-axiom-name ( bit -- c-addr u ) names a listed
\ bit. State: none; the entries are read-only data made while loading.

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

\ An axiom declaration's bit: its entry's when it is one, else unlisted.
: lf-allow-of ( decl k -- bit|0 outcome )
  lf-allow-at tuck lf-stmt-is? ok-then? 0= if nip 0 swap exit then
  if lf-stmt-code else drop 0 then outcome-ok ;
: lf-axiom-bit ( decl -- bit outcome )
  lf-allowlist# 0 ?do
    dup i lf-allow-of ok-then? 0= if nip -1 swap unloop exit then
    ?dup if nip outcome-ok unloop exit then
  loop drop lf-axiom-unlisted outcome-ok ;
\ The name of a listed bit.
: lf-axiom-name ( bit -- c-addr u )
  lf-allowlist# 0 ?do
    i lf-allow-at dup lf-stmt-code 2 pick = if nip lf-stmt-named unloop exit then drop
  loop drop s" ?" ;
