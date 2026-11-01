\ Untrusted, bounded index of candidate declaration signatures. This is NOT
\ a declaration environment, importer, axiom allowlist, proof checker, or
\ theorem registry. Entries carry an interned name and a structurally checked
\ term handle ONLY: no scope, type, proof or dependency validity is established.
\ Load names, terms, levels, level-scope, tagged representation, session and
\ handles first. Globals are non-reentrant; no raw/concurrent mutation allowed.
\ Do not use a returned signature as an assumption or confer theorem validity.
\ Name arguments are bare IDs: callers must bind them to the name-table
\ generation themselves. After a reset and fresh begin, an old numeric ID
\ can designate an unrelated new name and is not automatically detected.

32 constant lf-rawdecl-capacity
0 constant lf-rawdecl-ok
1 constant lf-rawdecl-invalid
2 constant lf-rawdecl-exhausted
3 constant lf-rawdecl-unknown
create lf-rawdecl-names lf-rawdecl-capacity cells allot
create lf-rawdecl-types lf-rawdecl-capacity cells allot
create lf-rawdecl-identities lf-rawdecl-capacity cells allot
variable lf-rawdecl-count
variable lf-rawdecl-active
variable lf-rawdecl-name-generation
variable lf-rawdecl-term-generation
variable lf-rawdecl-level-generation
variable lf-rawdecl-context-generation
variable lf-rawdecl-name
variable lf-rawdecl-type
variable lf-rawdecl-identity
variable lf-rawdecl-fuel
0 lf-rawdecl-active !
0 lf-rawdecl-count !

\ Start a fresh index against one live name table and symbolic session.
\ Prior entries are discarded; failure leaves the index inactive and empty.
: lf-rawdecl-begin ( -- flag )
  0 lf-rawdecl-active ! 0 lf-rawdecl-count !
  lf-name-storage-valid? lf-ssession-current? and 0= if false exit then
  lf-name-generation @ lf-rawdecl-name-generation !
  lf-term-generation @ lf-rawdecl-term-generation !
  lf-level-generation @ lf-rawdecl-level-generation !
  lf-lscope-generation @ lf-rawdecl-context-generation !
  true dup lf-rawdecl-active ! ;

\ Check current mutable boundaries before addressing the index. Session checks
\ already detect term, level and parameter-context resets; names are separate.
: lf-rawdecl-current? ( -- flag )
  lf-rawdecl-active @ 0= if false exit then
  lf-rawdecl-count @ dup 0< 0= swap lf-rawdecl-capacity <= and
  lf-name-storage-valid? and lf-ssession-current? and
  lf-name-generation @ lf-rawdecl-name-generation @ = and
  lf-term-generation @ lf-rawdecl-term-generation @ = and
  lf-level-generation @ lf-rawdecl-level-generation @ = and
  lf-lscope-generation @ lf-rawdecl-context-generation @ = and ;

\ Locate a name within a validated index; -1 means absent. Interning supplies
\ equal IDs only within the same unmodified name table and lifetime.
: lf-rawdecl-position ( name -- index | -1 )
  lf-rawdecl-count @ 0 ?do
    dup i cells lf-rawdecl-names + @ = if drop i unloop exit then
  loop drop -1 ;

\ Add an unchecked candidate signature. Full representation/level validation
\ uses the supplied finite fuel; invalid, duplicate and exhausted insertions
\ leave all entries and the count unchanged. No typing or proof is checked.
: lf-rawdecl-put ( name type identity fuel -- status )
  dup 0< if drop 2drop drop lf-rawdecl-invalid exit then lf-rawdecl-fuel !
  lf-rawdecl-identity ! lf-rawdecl-type ! lf-rawdecl-name !
  lf-rawdecl-current? 0= if lf-rawdecl-invalid exit then
  lf-rawdecl-name @ dup 0<= swap lf-name-valid? 0= or if lf-rawdecl-invalid exit then
  lf-rawdecl-name @ lf-rawdecl-position 0>= if lf-rawdecl-invalid exit then
  lf-rawdecl-count @ lf-rawdecl-capacity >= if lf-rawdecl-exhausted exit then
  lf-rawdecl-type @ lf-rawdecl-identity @ lf-rawdecl-fuel @ lf-hterm-check
  ?dup if exit then
  lf-rawdecl-name @ lf-rawdecl-count @ cells lf-rawdecl-names + !
  lf-rawdecl-type @ lf-rawdecl-count @ cells lf-rawdecl-types + !
  lf-rawdecl-identity @ lf-rawdecl-count @ cells lf-rawdecl-identities + !
  1 lf-rawdecl-count +! lf-rawdecl-ok ;

\ Find a candidate by name and revalidate its stored type handle. An absent
\ name is unknown, not evidence of nonexistence in Lean or an external module.
\ Results are untrusted data: ( name fuel -- type identity status ).
: lf-rawdecl-find ( name fuel -- type identity status )
  dup 0< if 2drop -1 0 lf-rawdecl-invalid exit then lf-rawdecl-fuel !
  lf-rawdecl-current? 0= if drop -1 0 lf-rawdecl-invalid exit then
  dup 0<= over lf-name-valid? 0= or if drop -1 0 lf-rawdecl-invalid exit then
  lf-rawdecl-position dup 0< if drop -1 0 lf-rawdecl-unknown exit then
  dup cells lf-rawdecl-types + @ swap cells lf-rawdecl-identities + @
  2dup lf-rawdecl-fuel @ lf-hterm-check
  ?dup if >r 2drop -1 0 r> exit then lf-rawdecl-ok ;
