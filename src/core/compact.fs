\ The compact store for Mathlib-scale input (ADR 0016, accepted
\ 2026-11-03): loads its families and makes input tiers. Untrusted; not
\ yet used by the kernel or loaded by src/main.fs (ADR 0016 C9 step 3).
\
\ tier-init makes an empty input tier whose tables start at 2^log2 slots
\ (they grow by doubling; pre-size them from the export's size to avoid
\ most rehashing) and makes its first records: the anonymous name and the
\ universe level zero, both number 0. Fill it with the builders of
\ compact-names.fs, compact-levels.fs, lib/pools.fs (tuple-start ...
\ tuple-end, text-intern on tier-tuples and tier-texts) and
\ compact-exprs.fs, then tier-seal it; then make a scratch tier over it
\ per check with tier-extend, and tier-reset that after each check.
\
\ Example: Nat.succ and an application of it in an input tier, found again
\ through a scratch tier.
\   create input /tier allot   create check /tier allot
\   16 input tier-init drop
\   name-anonymous s" Nat" input name-str drop s" succ" input name-str drop  ( n )
\   input tier-tuples tuple-start drop input tier-tuples tuple-end drop     ( n [] )
\   input expr-const drop                                                  ( c )
\   0 input expr-bvar drop input expr-app drop  input tier-seal drop       ( app )
\   input check tier-extend drop
\   0 0 input expr-const ...   \ see tests/core/compact.fs for the full form
\
\ Interface: tier-init, and everything the modules below give. State: none.

require ../lib/outcome.fs
require ../lib/cons.fs
require ../lib/pools.fs
require ./compact-tier.fs
require ./compact-names.fs
require ./compact-levels.fs
require ./compact-exprs.fs

\ The classes of the five families, in tier order (compact-tier.fs).
create tier-classes name-class , level-class , tuple-class , text-class , expr-class ,
: tier-class ( i -- class ) cells tier-classes + @ ;
: tier-init-family ( log2 tier i -- outcome ) tuck swap tier-family >r tier-class r> cons-init ;
: tier-families-init ( log2 tier -- outcome )
  tier-families 0 do
    2dup i tier-init-family dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
\ An empty input tier with tables of 2^log2 slots and its two first
\ records: ok, or full (tier-free then frees what was made). The record
\ must not hold memory: tier-free first.
: tier-init ( log2 tier -- outcome )
  dup /tier erase tuck tier-families-init dup ok? 0= if nip exit then drop
  dup name-anon-make nip dup ok? 0= if nip exit then drop
  >r tag-level-zero 0 0 r> level-build nip ;
