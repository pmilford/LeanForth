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
\ keeps that fuel, and whether the last comparison was decided unequal; a
\ member of the checker context (lib/context.fs). Single-threaded within
\ one context.

require ../lib/lib.fs
require ../core/diagnostics.fs
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
: lf-lcmp-scope ( root -- status )
  lf-lcmp-fuel @ lf-lscope-check lf-lscope-fuel @ lf-lcmp-fuel ! ;
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
: lf-level-compare-run ( left right fuel keep -- status )
  lf-lcmp-keep ! false lf-lcmp-apart ! dup 0< if lf-lcmp-negative exit then
  lf-lcmp-fuel ! 2dup lf-lcmp-scopes
  dup ok? if drop lf-lcmp-decide else nip nip lf-lcmp-fail then ;
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
