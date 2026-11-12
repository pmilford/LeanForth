\ Comparing whole contexts whose members own heap memory (ADR 0009,
\ Amendment 1; ADR 0016 C9 step 3). The term, level, name, reference and
\ input stores and the local context (core/local-context.fs) are heap
\ stores (src/lib/store.fs) and the per-index
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
  ' lf-lctx ,
\ And, when loaded (src/main.fs since plan task 8.2.1c), the authoring
\ words' binders (src/author/scopes.fs).
[defined] lfa-binders [if] ' lfa-binders , [then]
here canon-stores - 1 cells / constant canon-stores#
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
\ The growable arrays of context-slab: (lib/context.fs, plan task 6.2.0),
\ found through its list of their offsets.
: canon-listed-at ( node -- slab ) cell+ @ lf-context @ + ;
: canon-listed ( dst -- dst )
  context-slabs @ begin ?dup while >r dup r@ canon-listed-at canon-slab r> @ repeat ;
\ Hash tables (lib/htab.fs; compact-store plan step S3): the term store's
\ hash-consing table (core/terms.fs), the level store's and the
\ references' (core/levels.fs, core/constant-references.fs; step S4), the
\ stamps' table (core/generation-handles.fs) and, when loaded, the reached
\ set of universe substitution (kernel/mixed-level-substitute.fs): the
\ block address, a table record's first field.
: canon-htab ( dst htab -- ) canon-at 0 swap ! ;
: canon-core-htabs ( dst -- dst )
  dup lf-term-table canon-htab dup lf-stamp-table canon-htab
  dup lf-level-table canon-htab dup lf-cref-table canon-htab ;
\ And, when loaded, the pairs == met (kernel/mixed-compare.fs, step S4)
\ and the pairs a walk's run reached (core/constant-term-boundary.fs's
\ pair set; review rvKN).
[defined] lf-pair-table [if]
: canon-pair-htab ( dst -- dst ) dup lf-pair-table canon-htab ;
[else]
: canon-pair-htab ( dst -- dst ) ;
[then]
[defined] lf-meq-table [if]
: canon-kernel-htabs ( dst -- dst ) canon-pair-htab dup lf-meq-table canon-htab ;
[else]
: canon-kernel-htabs ( dst -- dst ) canon-pair-htab ;
[then]
[defined] lf-mls-set [if]
: canon-htabs ( dst -- dst ) canon-core-htabs canon-kernel-htabs dup lf-mls-set canon-htab ;
[else]
: canon-htabs ( dst -- dst ) canon-core-htabs canon-kernel-htabs ;
[then]
\ Blank every heap field in the copy at dst.
: canon-zero ( dst -- )
  canon-stores# 0 do dup i canon-store# canon-store loop
  canon-htabs
  dup lf-cref-pool canon-slab
  ['] canon-column lf-term-columns columns-each ['] canon-column lf-level-columns columns-each
  canon-listed canon-log ;

\ The digest: shape, counters and contents.
: canon-bytes ( h addr u -- h' ) 0 ?do dup i + c@ rot swap canon-mix swap loop drop ;
: canon-store-digest ( h store -- h' )
  >r r@ store-capacity @ canon-mix r@ store-limit @ canon-mix
  r@ store-identities r> store-bytes canon-bytes ;
: canon-slab-digest ( h slab -- h' )
  >r r@ slab-capacity canon-mix r@ slab-count canon-mix r@ slab-unit canon-mix
  r@ slab-limit canon-mix r@ slab-generation canon-mix 0 r@ slab-at r> slab-bytes canon-bytes ;
: canon-column-digest ( h column -- h' ) column-slab canon-slab-digest ;
\ Their units hold nothing until written (a count or index elsewhere says
\ how many are in use), so only their shape goes into the digest.
: canon-shape-digest ( h slab -- h' )
  >r r@ slab-capacity canon-mix r@ slab-unit canon-mix r> slab-limit canon-mix ;
: canon-listed-digest ( h -- h' )
  context-slabs @ begin ?dup while >r r@ canon-listed-at canon-shape-digest r> @ repeat ;
\ The table's size and entries (its slots' order follows its history).
: canon-htab-digest ( h htab -- h' ) dup htab-slots rot swap canon-mix swap htab-count canon-mix ;
: canon-core-digest ( h -- h' )
  lf-term-table canon-htab-digest lf-stamp-table canon-htab-digest
  lf-level-table canon-htab-digest lf-cref-table canon-htab-digest ;
[defined] lf-pair-table [if]
: canon-pair-digest ( h -- h' ) lf-pair-table canon-htab-digest ;
[else]
: canon-pair-digest ( h -- h' ) ;
[then]
[defined] lf-meq-table [if]
: canon-kernel-digest ( h -- h' ) canon-pair-digest lf-meq-table canon-htab-digest ;
[else]
: canon-kernel-digest ( h -- h' ) canon-pair-digest ;
[then]
[defined] lf-mls-set [if]
: canon-htabs-digest ( h -- h' )
  canon-core-digest canon-kernel-digest lf-mls-set canon-htab-digest ;
[else]
: canon-htabs-digest ( h -- h' ) canon-core-digest canon-kernel-digest ;
[then]
: canon-digest ( -- h )
  0 canon-stores# 0 do i canon-store# canon-store-digest loop
  canon-htabs-digest
  lf-cref-pool canon-slab-digest
  ['] canon-column-digest lf-term-columns columns-each
  ['] canon-column-digest lf-level-columns columns-each canon-listed-digest
  canon-log-digest ;
