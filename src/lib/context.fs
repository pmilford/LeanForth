\ Checker contexts (ADR 0009): one record per worker holding all of a
\ check's mutable state, so that several checks can run in one Forth image.
\ The current task reaches its context through one pointer, lf-context: a
\ USER variable on Gforth, so each task has its own, and a plain variable
\ on other hosts, which then have one worker. Requires: store.fs, walk.fs.
\
\ Modules declare their state as members of the context layout while they
\ load: context-record: (a zeroed record), context-store:, context-walk: and
\ context-walk2: each define name ( -- addr ), the member's address in the
\ current context; context-setup registers a word that sets a module's
\ state up, such as clearing a base-1 store. Each declaration grows the
\ main context, which the main task uses from the start, and initialises
\ the new member in it at once, so a program that never makes another
\ context runs as before.
\
\ context-new seals the layout: no member can be declared afterwards, so
\ every context has the same layout. A new context is ALLOCATEd, zeroed and
\ selected while every member's initialiser and every setup word run, in
\ declaration order; it then holds exactly the state the main context had
\ right after loading. State a module changes by other means while it
\ loads is not repeated in new contexts.
\
\ State: the layout record, context-layout (shared; read-only once sealed,
\ and only the main task declares members), the main context it points to,
\ and lf-context (per task). Never keep a member's address across a
\ context switch or a declaration: while modules load, each declaration
\ may move the main context. Never ALLOT or compile after tasks start.
\ Untrusted. The layout is host-specific and must never be serialized.

begin-structure /context-header
  field: context-size      \ bytes in the context; 0 once freed
end-structure

begin-structure /context-layout
  field: layout-bytes      \ size of every context so far
  field: layout-first      \ first member declared, or 0
  field: layout-last       \ last member declared, or 0
  field: layout-main       \ the main context
  field: layout-sealed     \ true once a context is made or a task started
end-structure
create context-layout /context-layout allot
context-layout /context-layout erase
/context-header context-layout layout-bytes !

\ A member, laid down in the dictionary when it is declared; a named
\ member is the body of its name.
begin-structure /member
  field: member-offset     \ address units from the start of a context
  field: member-init       \ xt ( addr member -- ), throws on failure
  field: member-link       \ next member declared, or 0
  3 cells +field member-args   \ the initialiser's arguments
end-structure

\ The current task's context.
[defined] udp [defined] next-task and
[if] user lf-context [else] variable lf-context [then]

: context-bytes ( -- u ) context-layout layout-bytes @ ;
: context-main ( -- context ) context-layout layout-main @ ;
: context-first ( -- addr ) context-layout layout-first ;
: context-last ( -- addr ) context-layout layout-last ;
: context-seal ( -- ) true context-layout layout-sealed ! ;
: context-sealed? ( -- flag ) context-layout layout-sealed @ ;

\ Selecting a context. context? is true for a live context of the current
\ layout (a sanity check: it cannot recognise every bad address).
\ context-use aborts on any other address.
: context? ( addr -- flag ) ?dup if context-size @ context-bytes = else false then ;
: context-use ( context -- )
  dup context? 0= abort" context-use: not a context" lf-context ! ;

\ The main context, grown and zero-extended by each declaration.
: context-blank ( addr -- ) dup context-bytes erase context-bytes swap context-size ! ;
: context-main! ( context -- ) dup context-layout layout-main ! lf-context ! ;
context-bytes allocate throw dup context-blank context-main!
: context-tail ( context -- addr u ) dup context-size @ tuck + swap context-bytes swap - ;
: context-grow ( -- )
  context-main context-bytes resize abort" context: out of memory"
  dup context-tail erase context-bytes over context-size ! context-main! ;

\ Declaring members. context-open aborts, before anything is defined, once
\ the layout is sealed or for a size that would not fit; a member's size is
\ rounded up to whole cells.
: context-open ( size -- size )
  context-sealed? abort" context: layout sealed after context-new"
  dup 0 max-n 1 cells - context-bytes - between? 0= abort" context: bad size" ;
: context-reserve ( size -- offset )
  context-bytes tuck + aligned context-layout layout-bytes ! ;
: member, ( xt size -- member ) context-reserve here >r , , 0 , r> ;
: member-args, ( a b c -- ) rot , swap , , ;
: member-args@ ( member -- a b c ) member-args dup @ over cell+ @ rot 2 cells + @ ;
: member-addr ( member -- addr ) member-offset @ lf-context @ + ;
: member-run ( member -- ) dup member-addr swap dup member-init @ execute ;
: member-append ( member -- )
  dup context-last @ ?dup if member-link ! else context-first ! then context-last ! ;
: member-add ( member -- ) dup member-append context-grow member-run ;
\ The run-time action of every named member: its address in the current context.
: member-does ( -- ) does> member-addr ;

\ Initialisers ( addr member -- ). The context is zeroed beforehand.
: member-zeroed ( addr member -- ) 2drop ;
: member-store ( addr member -- )
  swap >r member-args@ r> store-init 0= abort" context: bad store" ;
: member-walk ( addr member -- )
  swap >r member-args@ drop r> walk-sized-init 0= abort" context: bad walk" ;
: member-setup ( addr member -- ) nip member-args @ execute ;

\ Declaring words. A bad shape or capacity aborts, as for store: and walk:.
: context-record: ( size "name" -- )
  context-open create member-does
  ['] member-zeroed swap member, 0 0 0 member-args, member-add ;
: context-store: ( capacity width base "name" -- )
  >r 2dup r@ store-plan? 0= abort" context-store: bad shape"
  2dup store-size context-open create member-does
  ['] member-store swap member, -rot r> member-args, member-add ;
: context-walked ( capacity width "name" -- )
  2dup walk-plan? 0= abort" context-walk: bad capacity"
  2dup walk-span context-open create member-does
  ['] member-walk swap member, -rot 0 member-args, member-add ;
: context-walk: ( capacity "name" -- ) 1 context-walked ;
: context-walk2: ( capacity "name" -- ) 2 context-walked ;
\ Run xt ( -- ) now in the main context, and in every new context after
\ the members declared before it are initialised.
: context-setup ( xt -- )
  0 context-open ['] member-setup swap member, swap 0 0 member-args, member-add ;

\ Making and freeing contexts. context-new gives a new context and 0, or 0
\ and the ior of a failed ALLOCATE or the THROW code of a failed
\ initialiser or setup word, freeing what it allocated. The current
\ context is unchanged either way.
: context-members ( -- )
  context-first @ begin ?dup while dup member-run member-link @ repeat ;
: context-fill ( context -- ior )
  lf-context @ >r lf-context ! ['] context-members catch r> lf-context ! ;
: context-release ( context -- ior ) 0 over context-size ! free ;
: context-made ( context -- context ior )
  dup context-blank dup context-fill dup if swap context-release drop 0 swap then ;
: context-new ( -- context ior )
  context-seal context-bytes allocate ?dup if nip 0 swap exit then context-made ;
\ Free a context made by context-new and give FREE's ior. If it is the
\ current task's context, the task returns to the main context (so another
\ task must not free its own context and go on checking). Aborts on the
\ main context or an address that is not a context.
: context-free ( context -- ior )
  dup context? 0= abort" context-free: not a context"
  dup context-main = abort" context-free: the main context"
  dup lf-context @ = if context-main lf-context ! then context-release ;
