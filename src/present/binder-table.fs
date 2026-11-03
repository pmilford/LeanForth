\ Presentation side table (plan task 2.4.2): for each term, its binder name,
\ binder kind and source record ID; for each named constant, its declared
\ type. Printing reads it; nothing else does. Untrusted. The checker never
\ loads this module, so no entry can change a verdict: a wrong or missing
\ entry changes only how a term is printed. Requires terms.fs and names.fs.
\ An importer (the coming Forth NDJSON reader) or a test fills it with
\ lf-pres-binder! and lf-pres-source! per term and lf-pres-declare per
\ declaration. A term entry is stamped with the term's identity and the
\ name store's generation, a declaration with its type's identity and that
\ generation, so after a reset of either store a stale entry reads as
\ absent instead of describing another term.
\ State: one context record, lf-pres (ADR 0009). Each context has its own
\ table; one context is single-threaded.

require ../lib/lib.fs
require ../core/terms.fs
require ../core/names.fs

0 constant lf-binder-default    \ (x : A), explicit
1 constant lf-binder-implicit   \ {x : A}
2 constant lf-binder-strict     \ strict implicit, written with double braces
3 constant lf-binder-instance   \ [x : A], instance implicit
32 constant lf-pres-declaration-capacity

begin-structure /lf-pterm
  field: lf-pterm-identity   \ identity of the term when recorded; 0 when empty
  field: lf-pterm-name       \ binder name ID, or -1 for none
  field: lf-pterm-names      \ name-store generation of that ID
  field: lf-pterm-kind       \ binder kind
  field: lf-pterm-source     \ source record ID, or -1 for none
end-structure

begin-structure /lf-pdecl
  field: lf-pdecl-name       \ the constant's name ID
  field: lf-pdecl-names      \ name-store generation of that ID
  field: lf-pdecl-type       \ term index of the declared type
  field: lf-pdecl-identity   \ that term's identity
end-structure

begin-structure /lf-pres
  field: lf-pres-count       \ declaration records in use
  lf-term-capacity /lf-pterm * +field lf-pres-terms
  lf-pres-declaration-capacity /lf-pdecl * +field lf-pres-decls
end-structure
/lf-pres context-record: lf-pres

: lf-pres-entry ( term -- entry ) /lf-pterm * lf-pres lf-pres-terms + ;
: lf-pres-decl ( i -- decl ) /lf-pdecl * lf-pres lf-pres-decls + ;
\ The number of declaration records, clamped into range so that a
\ corrupted count can never address outside the table.
: lf-pres-count@ ( -- n ) lf-pres lf-pres-count @ 0 max lf-pres-declaration-capacity min ;

\ Forget every entry.
: lf-pres-reset ( -- ) lf-pres /lf-pres erase ;

\ Term entries. A live term's entry is claimed for it: an entry stamped for
\ an earlier term at the same index is cleared first. Term identities start
\ at 1, so an empty entry never matches.
: lf-pres-blank ( identity entry -- )
  dup /lf-pterm erase -1 over lf-pterm-name ! -1 over lf-pterm-source ! lf-pterm-identity
  ! ;
: lf-pres-claim ( term -- entry true | false )
  dup lf-term-identity 0= if drop false exit then
  swap lf-pres-entry 2dup lf-pterm-identity @ = if nip else tuck lf-pres-blank then true ;
\ The entry of a live term, only when it was recorded for that term.
: lf-pres-current ( term -- entry true | false )
  dup lf-term-identity 0= if drop false exit then
  swap lf-pres-entry tuck lf-pterm-identity @ = dup 0= if nip then ;
: lf-pres-known ( n -- n true | false ) dup 0< if drop false else true then ;

\ Record a binder's name ID and kind on a live lambda or Pi node. The name
\ must be a valid ID of the current name store (0, anonymous, is valid).
\ Anything else is invalid and changes nothing.
: lf-pres-kind? ( kind -- flag ) lf-binder-default lf-binder-instance between? ;
: lf-pres-naming? ( name kind -- flag ) lf-pres-kind? swap lf-name-valid? and ;
: lf-pres-binder-node? ( term -- flag )
  lf-term-read if 2drop lf-tag-lam lf-tag-pi 1+ within else false then ;
: lf-pres-node ( term -- entry true | false )
  dup lf-pres-binder-node? if lf-pres-claim else drop false then ;
: lf-pres-binder-set ( name kind entry -- )
  tuck lf-pterm-kind ! lf-name-generation @ over lf-pterm-names ! lf-pterm-name ! ;
: lf-pres-binder-to ( name kind term -- outcome )
  lf-pres-node if lf-pres-binder-set outcome-ok else 2drop outcome-invalid then ;
: lf-pres-binder! ( term name kind -- outcome )
  2dup lf-pres-naming? if rot lf-pres-binder-to else 2drop drop-invalid then ;

\ A binder's name ID and kind, when recorded for this term and the name is
\ still live in the same name-store generation.
: lf-pres-name-live? ( entry -- flag )
  dup lf-pterm-names @ lf-name-generation @ = swap lf-pterm-name @ lf-name-valid? and ;
: lf-pres-binder@ ( term -- name kind true | false )
  lf-pres-current 0= if false exit then
  dup lf-pres-name-live?
  if dup lf-pterm-name @ swap lf-pterm-kind @ true else drop false then ;

\ Source record ID of any live term: an opaque nonnegative number chosen
\ by the importer, such as the NDJSON line or expression index.
: lf-pres-source! ( term source -- outcome )
  dup 0< if 2drop outcome-invalid exit then
  swap lf-pres-claim if lf-pterm-source ! outcome-ok else drop-invalid then ;
: lf-pres-source@ ( term -- source true | false )
  lf-pres-current if lf-pterm-source @ lf-pres-known else false then ;

\ Lean's export spelling of a binder kind ("default", "implicit",
\ "strictImplicit" or "instImplicit"); anything else is refused.
: lf-pres-is? ( c-addr u c-addr2 u2 -- c-addr u flag ) 2over compare 0= ;
: lf-pres-kind-text ( c-addr u -- kind true | false )
  s" default" lf-pres-is? if 2drop lf-binder-default true exit then
  s" implicit" lf-pres-is? if 2drop lf-binder-implicit true exit then
  s" strictImplicit" lf-pres-is? if 2drop lf-binder-strict true exit then
  s" instImplicit" lf-pres-is? if 2drop lf-binder-instance true exit then 2drop false ;

\ Declarations: a constant's name and the term of its declared type, so
\ the printer knows which arguments Lean shows. Declaring a name again
\ replaces its type, and a record that went stale is reused. A table full
\ of live records is exhausted; bad input is invalid.
: lf-pres-decl-name? ( decl -- flag )
  dup lf-pdecl-names @ lf-name-generation @ = swap lf-pdecl-name @ lf-name-valid? and ;
: lf-pres-decl-type? ( decl -- flag )
  dup lf-pdecl-type @ lf-term-identity
  if swap lf-pdecl-identity @ = else drop false then ;
: lf-pres-decl-live? ( decl -- flag ) dup lf-pres-decl-name? swap lf-pres-decl-type? and ;
: lf-pres-match? ( name decl -- flag )
  tuck lf-pdecl-name @ = swap lf-pres-decl-live? and ;
: lf-pres-find ( name -- decl true | false )
  lf-pres-count@ 0 ?do dup i lf-pres-decl lf-pres-match?
    if drop i lf-pres-decl true unloop exit then loop drop false ;
: lf-pres-type@ ( name -- type true | false )
  lf-pres-find if lf-pdecl-type @ true else false then ;

: lf-pres-append ( -- decl true | false )
  lf-pres-count@ dup lf-pres-declaration-capacity < 0= if drop false exit then
  dup 1+ lf-pres lf-pres-count ! lf-pres-decl true ;
\ A record whose name or type went stale is reused before a new one.
: lf-pres-dead ( -- decl true | false )
  lf-pres-count@ 0 ?do i lf-pres-decl dup lf-pres-decl-live? 0= if true unloop exit then
  drop
  loop false ;
: lf-pres-slot ( name -- decl true | false )
  lf-pres-find if true exit then lf-pres-dead if true else lf-pres-append then ;
: lf-pres-decl-set ( name type decl -- )
  >r dup lf-term-identity drop r@ lf-pdecl-identity ! r@ lf-pdecl-type !
  lf-name-generation @ r@ lf-pdecl-names ! r> lf-pdecl-name ! ;
: lf-pres-decl-args? ( name type -- flag ) lf-term-valid? swap lf-name-valid? and ;
: lf-pres-declare ( name type -- outcome )
  2dup lf-pres-decl-args? 0= if 2drop outcome-invalid exit then
  over lf-pres-slot if lf-pres-decl-set outcome-ok else 2drop outcome-exhausted then ;
