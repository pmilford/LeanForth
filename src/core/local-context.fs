\ The local context of a check: free variables and what they stand for
\ (ADR 0014 Q2; plan task 4.2.2a). When the checker steps inside a lambda,
\ a Pi or (later) a let, it names the bound variable with a new free
\ variable instead of counting binders, as Lean's kernel does
\ (type_checker.cpp 125-230 with local_ctx.cpp 59-69, at the referee
\ commit eb6cafb7; see the ADR's Reproduction). A free variable is a term
\ node of tag lf-tag-fvar whose first field is its number n and whose
\ second is 0; entry n of the local context, an array in the checker
\ context, holds that node, its type and, for a let variable, its value.
\ Entries are appended in the order of their nodes. Inference empties the
\ local context when a job starts (lf-lctx-reset), and when it discards
\ scratch it drops the entries whose nodes went with it (lf-lctx-drop), so
\ a later entry may take a dropped number: a node of the old entry is dead
\ (node identities never repeat), never the new entry's free variable. Lean also keeps the binder name and
\ annotation for printing; the term store has neither, so neither is kept.
\
\ A node is a live free variable (lf-fvar-live?) only when its own entry
\ names it with its current identity: a node of this tag that some other
\ code made, or one whose entry was rolled back, is no free variable, and
\ every audit that meets it fails (constant-term-boundary.fs: invalid).
\ An export never holds free variables (core/unsupported-forms.fs) and the
\ checker's input is audited before the local context has an entry, so
\ only a check's own scratch holds them.
\
\ Entries live in a heap store (lib/store.fs) that grows up to a limit, a
\ setting of each context: lf-lctx-capacity reads it, lf-lctx-capacity!
\ sets it. A live entry names a live node, so the entries in use never
\ outnumber the term store's nodes. The default limit is the largest a
\ store of entries can count (lf-lctx-default-limit), so only the heap
\ limits the local context (plan task 6.2.0), as Lean's has no limit of
\ its own; a caller may set a lower one. Running out is full, never ok. Words: lf-lctx-local and lf-lctx-let ( Lean's mk_local_decl
\ ), lf-lctx-have (a let variable whose value is hidden: Lean's ldecl
\ with nondep := true, which only the front end makes, plan FE1g-1),
\ lf-fvar-live?, lf-fvar-number, lf-fvar-type, lf-fvar-value,
\ lf-fvar-let? (Lean's LocalDecl.isLet: a value that is not hidden),
\ lf-fvar-nondep?, lf-fvar-depth and lf-fvar-depth! (where its binder
\ stands, for the derivation log), lf-lctx-count, lf-lctx-reset,
\ lf-lctx-drop. The kernel never makes a have, so for its entries
\ lf-fvar-let? is whether there is a value.
\ Outcomes: ok, invalid, full. Untrusted; part of the checker's [kernel]
\ path, not yet through the review gate.
\ Example: in a check, x : A is ( A ) lf-lctx-local -> ( x ok ); then
\ x lf-fvar-type gives A and x lf-fvar-live? is true until the check's
\ scratch is rolled back below x.
\ State: the store header lf-lctx, a member of the checker context
\ (lib/context.fs) whose block is on the heap, freed by its teardown
\ word. Single-threaded within one context; numbers mean something only
\ in their own context and check.

require ../lib/lib.fs
require ./diagnostics.fs
require ./terms.fs

9 constant lf-tag-fvar
\ A free variable's node is never shared (terms.fs): its entry names it
\ by its identity, and a dead node must never come back as a new
\ entry's free variable.
lf-tag-fvar lf-term-unshare
64 constant lf-lctx-default          \ entries a new context's block holds at first

begin-structure /lf-ldecl
  field: lf-ldecl-fvar       \ the free variable's node
  field: lf-ldecl-identity   \ that node's identity
  field: lf-ldecl-type       \ its type, a term node
  field: lf-ldecl-value      \ a let variable's value, or -1
  field: lf-ldecl-nondep     \ true for a have: the value is hidden (Lean's nondep)
  field: lf-ldecl-depth      \ binders around its binder, or -1 (see below)
end-structure

\ The largest limit a store of entries takes (lib/store.fs, store-plan?).
max-n store-header - /lf-ldecl cell+ / constant lf-lctx-default-limit
store-header context-record: lf-lctx
: lf-lctx-make ( -- )
  lf-lctx-default /lf-ldecl 0 lf-lctx store-heap-init ok? 0= abort" lctx: no heap"
  lf-lctx-default-limit lf-lctx store-limit! ok? 0= abort" lctx: limit" ;
' lf-lctx-make context-setup
:noname ( -- ) lf-lctx store-heap-free ; context-teardown

\ The capacity setting of this context, and setting it (as for terms).
: lf-lctx-capacity ( -- n ) lf-lctx store-limit @ ;
: lf-lctx-capacity! ( n -- outcome ) lf-lctx store-limit! ;
: lf-lctx-count ( -- addr ) lf-lctx store-count ;
\ Discard every entry (a new check).
: lf-lctx-reset ( -- ) lf-lctx store-clear ;
\ Entry n's record. Unchecked: n is below the count.
: lf-ldecl ( n -- addr ) lf-lctx store-slot ;

\ A new entry for type and value (-1 for none), with its node: ok, or -1
\ and full when the local context (recorded as a full binder context, with
\ its count and capacity) or the term store (recorded by terms.fs) has no
\ room, or invalid for a type that is no live node. A failure changes
\ nothing but, at worst, leaves a node that no entry names.
: lf-lctx-site ( -- site ) c" local-context lf-lctx-local" ;
: lf-lctx-refused ( -- -1 outcome )
  lf-lctx lf-lctx-site lf-diag-binders-full lf-diag-store -1 outcome-full ;
: lf-lctx-room? ( -- flag )
  lf-lctx store-grow ok? if lf-lctx store-open? else false then ;
: lf-lctx-node ( -- fvar true | false ) lf-tag-fvar lf-lctx-count @ 0 lf-term-add ;
: lf-ldecl-fill ( type value fvar addr -- )
  >r dup r@ lf-ldecl-fvar ! lf-term-identity drop r@ lf-ldecl-identity !
  r@ lf-ldecl-value ! r@ lf-ldecl-type ! r> -1 over lf-ldecl-depth !
  false swap lf-ldecl-nondep ! ;
\ The entry is charged to a check's memory limit (core/scratch-meter.fs)
\ just before it is made, after its node, as the stores charge theirs, so
\ that no reading misses a charged record (review rvRS F4); a refused one
\ is full, and the check then ends full (kernel/check-declaration.fs).
: lf-lctx-claim ( type value fvar -- fvar outcome )
  lf-meter-local? 0= if drop 2drop lf-lctx-refused exit then
  lf-lctx store-new 0= if drop 2drop lf-lctx-refused exit then
  over >r lf-ldecl lf-ldecl-fill r> outcome-ok ;
: lf-lctx-made ( type value -- fvar outcome )
  lf-lctx-node if lf-lctx-claim else 2drop -1 outcome-full then ;
: lf-lctx-add ( type value -- fvar outcome )
  over lf-term-valid? 0= if 2drop -1 outcome-invalid exit then
  lf-lctx-room? if lf-lctx-made else 2drop lf-lctx-refused then ;
\ Lean's mk_local_decl (local_ctx.cpp 65-69): a free variable of type.
: lf-lctx-local ( type -- fvar outcome ) -1 lf-lctx-add ;
\ The same with a value (local_ctx.cpp 59-63): a let variable, which
\ whnf will replace by its value (plan task 4.2.3; unused before it).
: lf-lctx-let ( type value -- fvar outcome )
  dup lf-term-valid? if lf-lctx-add else 2drop -1 outcome-invalid then ;

\ Whether node is a live free variable: a valid node of tag lf-tag-fvar,
\ second field 0, whose number is an entry that names this node with its
\ current identity.
: lf-fvar-shape ( tag first second -- n true | false )
  0= rot lf-tag-fvar = and if dup lf-lctx store-valid? dup 0= if nip then
  else drop false then ;
: lf-ldecl-names? ( node n -- flag )
  lf-ldecl 2dup lf-ldecl-fvar @ = if lf-ldecl-identity @ swap lf-term-identity drop =
  else 2drop false then ;
: lf-fvar-live? ( node -- flag )
  dup lf-term-read if lf-fvar-shape if lf-ldecl-names? exit then then drop false ;

\ Discarding scratch above a term-store mark (the term count a scratch
\ mark gives back to, core/scratch-marks.fs): the entries whose nodes lie
\ at or above the mark go too. They are the newest, as entries are made
\ in node order.
: lf-lctx-above? ( mark -- flag )
  lf-lctx-count @ ?dup if 1- lf-ldecl lf-ldecl-fvar @ <= else drop false then ;
: lf-lctx-drop ( mark -- ) begin dup lf-lctx-above? while -1 lf-lctx-count +! repeat drop ;

\ A live free variable's number, entry, type and value (-1 for none).
\ Unchecked: fvar passed lf-fvar-live?.
: lf-fvar-number ( fvar -- n ) lf-term-first@ ;
: lf-fvar-decl ( fvar -- addr ) lf-fvar-number lf-ldecl ;
: lf-fvar-type ( fvar -- type ) lf-fvar-decl lf-ldecl-type @ ;
: lf-fvar-value ( fvar -- value ) lf-fvar-decl lf-ldecl-value @ ;
\ A have's value is hidden: Lean's whnf leaves the variable as it is and
\ its isLet is false (LocalContext.lean, LocalDecl.isLet, value?).
: lf-fvar-nondep? ( fvar -- flag ) lf-fvar-decl lf-ldecl-nondep @ ;
: lf-fvar-let? ( fvar -- flag ) dup lf-fvar-value 0< 0= swap lf-fvar-nondep? 0= and ;
\ Lean's mkLetDecl with nondep := true: a let variable whose value is
\ hidden (a have), made as lf-lctx-let makes one.
: lf-lctx-have ( type value -- fvar outcome )
  lf-lctx-let dup ok? if over lf-fvar-decl lf-ldecl-nondep true swap ! then ;
\ Where the free variable's binder stands: how many binders surround it,
\ as the checker that made it records (inference: its scope's depth), or
\ -1 when none was recorded. The derivation log (derivation-log.fs) reads
\ it to write a free variable as the bound variable it stands for in a
\ step's scope; nothing in the checker reads it.
: lf-fvar-depth ( fvar -- depth ) lf-fvar-decl lf-ldecl-depth @ ;
: lf-fvar-depth! ( depth fvar -- ) lf-fvar-decl lf-ldecl-depth ! ;
