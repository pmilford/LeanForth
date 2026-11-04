\ Comparing whole contexts whose members own heap memory (ADR 0009,
\ Amendment 1; ADR 0016 C9 step 3). The term, level, name, reference and
\ input stores are heap stores (src/lib/store.fs) and the per-index
\ columns and the reference pool are slabs (src/lib/slab.fs): their
\ records in a context hold heap addresses, which differ from context to
\ context. canon-zero blanks those fields in a byte copy of a context, so
\ the rest compares byte for byte; canon-digest folds what they hold
\ (shape, counters and every byte of every block) in the current context.
\ Test-only; requires the modules whose members it names (core/input.fs
\ and everything below it).

\ A member's address in a copy at dst of the current context.
: canon-at ( dst member -- addr ) lf-context @ - + ;
\ A heap store: its block address and the seal, which covers it.
: canon-store ( dst store -- ) canon-at 0 over store-block ! 0 swap store-seal ! ;
\ A slab: the whole record (its public state goes into the digest).
: canon-slab ( dst slab -- ) canon-at /slab erase ;
: canon-column ( dst column -- dst ) column-slab over swap canon-slab ;
create canon-stores ' lf-terms , ' lf-levels , ' lf-names , ' lf-crefs , ' lf-inputs ,
5 constant canon-stores#
: canon-store# ( i -- store ) cells canon-stores + @ execute ;
: canon-mix ( h x -- h' ) swap 31 * + ;
\ The derivation log's pools (src/core/derivation-log.fs, when loaded): a
\ heap block only while a log is on, its unused parts never cleared; its
\ address is blanked, and only whether it exists goes into the digest
\ (the log's counts are in the context record itself).
[defined] lf-log-state [if]
: canon-log ( dst -- ) lf-log-state lf-logs-pools canon-at 0 swap ! ;
: canon-log-digest ( h -- h' ) lf-log-pools 0<> canon-mix ;
[else]
: canon-log ( dst -- ) drop ;
: canon-log-digest ( h -- h' ) ;
[then]
\ Blank every heap field in the copy at dst.
: canon-zero ( dst -- )
  canon-stores# 0 do dup i canon-store# canon-store loop
  dup lf-cref-pool canon-slab
  ['] canon-column lf-term-columns columns-each ['] canon-column lf-level-columns columns-each
  canon-log ;

\ The digest: shape, counters and contents.
: canon-bytes ( h addr u -- h' ) 0 ?do dup i + c@ rot swap canon-mix swap loop drop ;
: canon-store-digest ( h store -- h' )
  >r r@ store-capacity @ canon-mix r@ store-limit @ canon-mix
  r@ store-identities r> store-bytes canon-bytes ;
: canon-slab-digest ( h slab -- h' )
  >r r@ slab-capacity canon-mix r@ slab-count canon-mix r@ slab-unit canon-mix
  r@ slab-limit canon-mix r@ slab-generation canon-mix 0 r@ slab-at r> slab-bytes canon-bytes ;
: canon-column-digest ( h column -- h' ) column-slab canon-slab-digest ;
: canon-digest ( -- h )
  0 canon-stores# 0 do i canon-store# canon-store-digest loop
  lf-cref-pool canon-slab-digest
  lf-term-columns group-newest @ begin ?dup while tuck canon-column-digest swap column-link @
  repeat
  lf-level-columns group-newest @ begin ?dup while tuck canon-column-digest swap column-link @
  repeat canon-log-digest ;
