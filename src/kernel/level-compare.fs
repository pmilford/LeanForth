\ Level equality as Lean's kernel decides it (ADR 0011, Amendment 1):
\ is_equivalent (level.cpp 518-521) -- structurally equal, or so after
\ Lean's normalize (level-normalize.fs) -- after a scope check of both
\ roots. Conversion uses it for two Sorts and for constants' levels, as
\ Lean's quick_is_def_eq and is_def_eq(levels) do (type_checker.cpp
\ 781-799, 810-811). Equal is Lean's true, and an experimental
\ diagnostic, never a theorem or type judgment by itself; Lean's false is
\ unknown here (conversion never treats unknown as inequality), and
\ lf-level-inequivalent? gives it to rule D1. It assumes a store and
\ context unchanged during a call, and that equal parameter IDs denote the
\ same Lean name and different IDs different names.
\ State: one record, lf-lcmp-state, holding the fuel left after a
\ comparison, which mixed-convert reads, whether an undecided comparison
\ keeps that fuel, and whether the last comparison was decided unequal;
\ and the column lf-lcmp-scoped of the level store (the scope checks'
\ memo, below); members of the checker context (lib/context.fs).
\ Single-threaded within one context.

require ../lib/lib.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/constant-term-boundary.fs
require ../core/level-scope.fs
require ../core/levels.fs
require ./level-normalize.fs

: lf-lcmp-site ( -- site ) c" level-compare lf-level-compare" ;

begin-structure /lf-lcrec
  field: lf-lcrec-fuel          \ visits left after a comparison
  field: lf-lcrec-keep          \ true: an undecided comparison keeps its fuel
  field: lf-lcrec-apart         \ true: the last comparison found Lean's false
end-structure
/lf-lcrec context-record: lf-lcmp-state

: lf-lcmp-fuel ( -- addr ) lf-lcmp-state lf-lcrec-fuel ;
: lf-lcmp-keep ( -- addr ) lf-lcmp-state lf-lcrec-keep ;
: lf-lcmp-apart ( -- addr ) lf-lcmp-state lf-lcrec-apart ;
\ Any failure except an undecided comparison leaves no fuel: mixed-convert
\ continues with lf-lcmp-fuel whatever the outcome. In keeping mode
\ (lf-level-compare-keeping) an undecided comparison -- Lean's false, or
\ names that cannot be ordered -- keeps the fuel its decision left, so
\ that the caller's rejection analysis (ADR 0011, mixed-infer.fs) can go
\ on with it.
: lf-lcmp-fail ( status -- status ) 0 lf-lcmp-fuel ! ;
: lf-lcmp-kept? ( status -- flag ) dup ok? swap outcome-unknown = lf-lcmp-keep @ and or ;
: lf-lcmp-settle ( status -- status ) dup lf-lcmp-kept? 0= if lf-lcmp-fail then ;

\ Scope-check a root with the fuel left, continuing with what it leaves.
\ A memo per level (compact-store plan step S4; ADR 0014 Amendment 4's
\ note): while the audit memo is on (core/constant-term-boundary.fs's
\ lf-audit-on?, in a check), a root found in scope is kept in a column
\ of the level store with its identity, the parameter context's
\ generation and the audit memo's closed epoch, and is not walked again
\ while all three hold: its graph cannot change (records are never
\ written, children come earlier, a rollback gives back a suffix, an
\ index made again has a new identity) and every change of the parameter
\ context advances the generation. The epoch is new with every check
\ (lf-audit-renew), so the memo lasts one check, as the audit memo does:
\ a check's fuel never depends on which checks its context ran before
\ (plan task 7.3.1: a parallel check's worker runs other declarations
\ than the serial run's context; before, an input level checked in an
\ earlier check cost no fuel in later ones). A kept root costs no fuel;
\ a check that fails keeps nothing.
/slab context-record: lf-lcmp-scoped
3 cells ' lf-lcmp-scoped lf-level-columns column-add
: lf-lcmp-unit ( level -- addr ) lf-lcmp-scoped column-at ;
: lf-lcmp-epoch ( -- epoch ) lf-audit-state lf-aud-closed @ ;
: lf-lcmp-stamp ( level -- identity generation )
  lf-level-identity drop lf-lscope-generation @ ;
: lf-lcmp-held? ( level unit -- flag )
  dup 2 cells + @ lf-lcmp-epoch = if 2@ rot lf-lcmp-stamp d= else 2drop false then ;
\ A context whose count is not valid (corrupted) is never trusted from the
\ memo: the walk then refuses it (review rvS4 L1).
: lf-lcmp-scoped? ( level -- flag )
  lf-audit-on? 0= if drop false exit then
  dup lf-level-valid? lf-lscope-count-valid? and 0= if drop false exit then
  dup lf-lcmp-unit lf-lcmp-held? ;
: lf-lcmp-keep-scope ( level -- )
  lf-audit-on? 0= if drop exit then
  dup lf-lcmp-stamp rot lf-lcmp-unit dup >r 2! lf-lcmp-epoch r> 2 cells + ! ;
: lf-lcmp-scope ( root -- status )
  dup lf-lcmp-scoped? if drop outcome-ok exit then
  dup lf-lcmp-fuel @ lf-lscope-check lf-lscope-fuel @ lf-lcmp-fuel !
  dup ok? if over lf-lcmp-keep-scope then nip ;
: lf-lcmp-scopes ( left right -- status )
  swap lf-lcmp-scope ok-then? if lf-lcmp-scope then ;
\ An undecided comparison is recorded with both roots (unless something
\ more specific was recorded first).
: lf-lcmp-undecided ( left right -- )
  lf-lcmp-site lf-diag-undecided lf-diag-note ;
\ Lean's is_equivalent with the fuel left: equal is ok; Lean's false is
\ unknown and marks the comparison apart; any failure passes on, an
\ undecided one (unknown) recorded with both roots.
: lf-lcmp-failed ( left right outcome -- status )
  dup outcome-unknown = if -rot lf-lcmp-undecided else nip nip then ;
: lf-lcmp-different ( left right -- status )
  true lf-lcmp-apart ! lf-lcmp-undecided outcome-unknown ;
: lf-lcmp-verdict ( left right flag outcome -- status )
  dup ok? 0= if nip lf-lcmp-failed exit then
  drop if 2drop outcome-ok else lf-lcmp-different then ;
: lf-lcmp-decide ( left right -- status )
  2dup lf-lcmp-fuel @ lf-level-equivalent lf-lnorm-fuel @ lf-lcmp-fuel !
  lf-lcmp-verdict lf-lcmp-settle ;
: lf-lcmp-negative ( left right fuel -- status )
  0 lf-lcmp-site lf-diag-bad-argument lf-diag-note 2drop outcome-invalid lf-lcmp-fail ;

\ Compare two roots against one explicit parameter context. Scope checks run
\ before any equality shortcut and share fuel with the decision. Only one
\ status is returned; this word cannot register a declaration.
\ lf-level-compare-keeping differs only in the fuel an undecided comparison
\ leaves (see lf-lcmp-fail).
: lf-lcmp-pass ( left right fuel keep -- status )
  lf-lcmp-keep ! false lf-lcmp-apart ! dup 0< if lf-lcmp-negative exit then
  lf-lcmp-fuel ! 2dup lf-lcmp-scopes
  dup ok? if drop lf-lcmp-decide else nip nip lf-lcmp-fail then ;
\ The derivation log (ADR 0013): with it on, a comparison is one level-eq
\ step of the two levels; both paths run the same pass.
: lf-lcmp-logged ( left right fuel keep -- status )
  3 pick 3 pick lf-rule-level-eq lf-log-open lf-lcmp-pass lf-log-decided ;
: lf-level-compare-run ( left right fuel keep -- status )
  lf-log? if lf-lcmp-logged else lf-lcmp-pass then ;
: lf-level-compare ( left right fuel -- status ) false lf-level-compare-run ;
: lf-level-compare-keeping ( left right fuel -- status ) true lf-level-compare-run ;
\ Rule D1 (ADR 0011, Amendment 1): whether Lean's is_equivalent is false.
\ (flag ok) when decided; otherwise (false status) with the failure (unknown
\ for names that cannot be ordered). The fuel left is in lf-lcmp-fuel, kept
\ as in keeping mode.
: lf-lcmp-unequal ( -- flag status )
  lf-lcmp-apart @ dup if outcome-ok else outcome-unknown then ;
: lf-level-inequivalent? ( left right fuel -- flag status )
  lf-level-compare-keeping case outcome-ok of false outcome-ok endof
    outcome-unknown of lf-lcmp-unequal endof >r false r@ r> endcase ;
