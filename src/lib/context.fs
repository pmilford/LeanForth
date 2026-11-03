\ Checker contexts (ADR 0009): one record per worker holding all of a
\ check's mutable state, so that several checks can run in one Forth image.
\ The current task reaches its context through one pointer, lf-context: a
\ USER variable on Gforth, so each task has its own, and a plain variable on
\ other hosts, which then have one worker.
\
\ Modules declare their state as members of the context layout while they
\ load: context-record: (a zeroed record), context-store:, context-walk:,
\ context-walk2: and context-frames: each define name ( -- addr ), the
\ member's address in the current context; context-setup registers a word
\ that sets a module's state up, such as clearing a base-1 store. Each
\ declaration grows the main context, which the main task uses from the
\ start, and initialises the new member in it at once, so a program that
\ never makes another context runs as before. A declaration that is
\ refused aborts before it defines or grows anything; a setup word that
\ throws is not registered.
\
\ context-new seals the layout: no member can be declared afterwards, so
\ every context has the same layout. A new context is ALLOCATEd, zeroed and
\ selected while every member's initialiser and every setup word run, in
\ declaration order; it then holds exactly the state the main context had
\ right after loading. State a module changes by other means while it
\ loads is not repeated in new contexts.
\
\ Ownership: a context is idle or owned by one job (task.fs claims it when
\ the job is submitted and releases it when the job has been waited for).
\ Each task has an owner token, lf-owner: 0, or while it runs a job, that
\ job. A task may select only a context whose owner is its own token: the
\ main task only idle contexts, a job only its own. An owned context cannot
\ be freed, and contexts are made and freed only outside jobs.
\
\ Handles: a context's address is its handle, valid from context-new until
\ context-free. A handle must never be used after context-free: context?
\ cannot recognise every stale one, because FREE may reuse the block's
\ first cells and context-new may give the same address again. Handles
\ into a context's stores (indices and identities) mean something only in
\ that context: every new context restarts its stores' serial numbers, so
\ such handles must never cross contexts.
\
\ Modules also state, while they load, how deep their checks nest on the
\ host stacks (context-need); the job pool refuses smaller worker stacks.
\
\ State: the layout record, context-layout, with the stated stack needs
\ (shared; read-only once sealed, and only the main task declares members
\ and needs), the main context it points to,
\ and lf-context and lf-owner (per task). Never keep a member's address
\ across a context switch or a declaration: while modules load, each
\ declaration may move the main context. Never ALLOT or compile after
\ tasks start. Untrusted. The layout is host-specific and must never be
\ serialized.

require ./bounds.fs
require ./portability.fs
require ./store.fs
require ./walk.fs
require ./frame.fs

begin-structure /context-header
  field: context-size      \ bytes in the context; zeroed by context-free
  field: context-owner     \ the owner's token, or 0 while idle
end-structure

begin-structure /context-layout
  field: layout-bytes      \ size of every context so far
  field: layout-first      \ first member declared, or 0
  field: layout-last       \ last member declared, or 0
  field: layout-main       \ the main context
  field: layout-sealed     \ true once a context is made or a job submitted
  field: layout-data-need  \ deepest data-stack nesting a module states
  field: layout-return-need \ deepest return-stack nesting a module states
end-structure
create context-layout /context-layout allot
context-layout /context-layout erase
/context-header context-layout layout-bytes !

\ A member, laid down in the dictionary when it is declared, right after
\ its name's definition. Which argument fields are used depends on the
\ initialiser.
begin-structure /member
  field: member-offset     \ address units from the start of a context
  field: member-init       \ xt ( addr member -- ) of the initialiser
  field: member-link       \ next member declared, or 0
  field: member-capacity   \ store or walk capacity, or frames limit
  field: member-width      \ store record width, or walk width (1 or 2)
  field: member-base       \ store index base
  field: member-xt         \ setup word, or frames visitor
end-structure

\ The current task's context and owner token.
[defined] udp [defined] next-task and
[if] user lf-context user lf-owner [else] variable lf-context variable lf-owner [then]
0 lf-owner !

\ ALLOCATE u zeroed address units: the address and 0, or an undefined
\ address and the ior.
: allocate0 ( u -- addr ior ) dup allocate ?dup if rot drop exit then tuck swap erase 0 ;

: context-bytes ( -- u ) context-layout layout-bytes @ ;
: context-main ( -- context ) context-layout layout-main @ ;
: context-first ( -- addr ) context-layout layout-first ;
: context-last ( -- addr ) context-layout layout-last ;
: context-seal ( -- ) true context-layout layout-sealed ! ;
: context-sealed? ( -- flag ) context-layout layout-sealed @ ;

\ Selecting a context. context? is true for a live context of the current
\ layout (a sanity check: it cannot recognise every bad address).
\ context-use aborts on any other address and on a context owned by
\ another token than the current task's.
: context? ( addr -- flag ) ?dup if context-size @ context-bytes = else false then ;
: context-idle? ( context -- flag ) context-owner @ 0= ;
: context-mine? ( context -- flag ) context-owner @ lf-owner @ = ;
: context-use ( context -- )
  dup context? 0= abort" context-use: not a context"
  dup context-mine? 0= abort" context-use: owned by another job" lf-context ! ;

\ The main context. Each declaration first RESIZEs it to the new layout
\ size and zeroes the new tail, so a failure changes nothing.
: context-sized ( context -- ) context-bytes swap context-size ! ;
: context-main! ( context -- ) dup context-layout layout-main ! lf-context ! ;
context-bytes allocate0 throw dup context-sized context-main!
: context-tail ( u context -- addr n ) dup context-size @ rot over - >r + r> ;
: context-layout! ( u context -- ) context-main! context-layout layout-bytes ! ;
: context-grow ( u -- )
  context-main over resize abort" context: out of memory"
  2dup context-tail erase 2dup context-size ! context-layout! ;

\ Opening a member of size address units: aborts, before anything is
\ defined or grown, once the layout is sealed or for a size that would
\ not fit; otherwise grows the main context, rounding up to whole cells,
\ and gives the member's offset.
: context-open ( size -- offset )
  context-sealed? abort" context: layout sealed after context-new"
  dup 0 max-n 1 cells - context-bytes - between? 0= abort" context: bad size"
  context-bytes tuck + aligned context-grow ;

\ Laying down a member, aligned, with its other fields zero.
: member, ( offset init -- member )
  align here /member allot dup /member erase tuck member-init ! tuck member-offset ! ;
: member-shape! ( capacity width member -- member )
  tuck member-width ! tuck member-capacity ! ;
: member-shape@ ( member -- capacity width ) dup member-capacity @ swap member-width @ ;
: member-addr ( member -- addr ) member-offset @ lf-context @ + ;
: member-run ( member -- ) dup member-addr swap dup member-init @ execute ;
\ Define name ( -- addr ), the member's address in the current context: a
\ colon definition that adds the offset, compiled as a literal, to
\ lf-context @. An offset never changes once given (the layout only grows,
\ and is sealed at the first context-new), and the context is read afresh
\ at every call, so the main context may move while modules load.
\ member-body compiles the body after : and ends the definition, taking
\ the offset from above the colon-sys that : left.
: member-body ( colon-sys offset -- )
  postpone lf-context postpone @ postpone literal postpone + postpone ; ;
: member-colon ( offset "name" -- offset ) dup >r : r> member-body ;
\ Grow the layout by size, then define name as a member with initialiser init.
: member: ( size init "name" -- member )
  swap context-open member-colon swap member, ;
\ Initialise a member in the main context, then link it last, so that a
\ member whose initialiser throws is never run in a new context.
: member-append ( member -- )
  dup context-last @ ?dup if member-link ! else context-first ! then context-last ! ;
: member-add ( member -- ) dup member-run member-append ;

\ Initialisers ( addr member -- ). The context is zeroed beforehand.
: member-zeroed ( addr member -- ) 2drop ;
: member-store ( addr member -- )
  swap >r dup member-shape@ rot member-base @ r> store-init
  0= abort" context: bad store" ;
: member-walk ( addr member -- )
  member-shape@ rot walk-sized-init 0= abort" context: bad walk" ;
: member-frames ( addr member -- ) dup member-capacity @ swap member-xt @ rot frame-init ;
: member-setup ( addr member -- ) nip member-xt @ execute ;

\ Declaring words. A bad size, shape, capacity or limit aborts and defines
\ nothing, as for store:, walk: and frames:.
: context-record: ( size "name" -- )
  dup 1 < abort" context-record: bad size" ['] member-zeroed member: member-add ;
: context-store: ( capacity width base "name" -- )
  >r 2dup r@ store-plan? 0= abort" context-store: bad shape"
  2dup store-size ['] member-store member: member-shape!
  r> over member-base ! member-add ;
: context-walked ( capacity width "name" -- )
  2dup walk-plan? 0= abort" context-walk: bad capacity"
  2dup walk-span ['] member-walk member: member-shape! member-add ;
: context-walk: ( capacity "name" -- ) 1 context-walked ;
: context-walk2: ( capacity "name" -- ) 2 context-walked ;
\ A frames record (frame.fs) allowing limit nested visits of the visitor
\ xt, which reaches the record through its frames argument.
: context-frames: ( limit xt "name" -- )
  over 1 < abort" context-frames: bad limit"
  /frames ['] member-frames member: tuck member-xt ! tuck member-capacity ! member-add ;
\ Run xt ( -- ) now in the main context, and in every new context after
\ the members declared before it are initialised.
: context-setup ( xt -- )
  0 context-open ['] member-setup member, tuck member-xt ! member-add ;

\ Stack needs: the deepest nesting, in data and return-stack cells, that
\ any module states for one of its checks (such as mixed-beta.fs's nested
\ passes). Stated while modules load, like members (afterwards it aborts);
\ the largest of each is kept, and task.fs's pool-start refuses worker
\ stacks that do not cover it.
: context-max! ( n addr -- ) dup @ rot max swap ! ;
: context-need ( data-cells return-cells -- )
  context-sealed? abort" context: need stated after context-new"
  context-layout layout-return-need context-max!
  context-layout layout-data-need context-max! ;
: context-needs ( -- data-cells return-cells )
  context-layout dup layout-data-need @ swap layout-return-need @ ;

\ Making and freeing contexts, only outside jobs (these abort inside one).
\ context-new gives a new, idle context and 0, or 0 and the ior of a
\ failed ALLOCATE or the THROW code of a failed initialiser or setup word,
\ freeing what it allocated. The current context is unchanged either way.
: context-outside-job ( -- ) lf-owner @ abort" context: not allowed inside a job" ;
: context-members ( -- )
  context-first @ begin ?dup while dup member-run member-link @ repeat ;
: context-fill ( context -- ior )
  lf-context @ >r lf-context ! ['] context-members catch r> lf-context ! ;
: context-discard ( context -- ior ) 0 over context-size ! free ;
: context-made ( context -- context ior )
  dup context-fill dup if swap context-discard drop 0 swap then ;
: context-new ( -- context ior )
  context-outside-job context-seal
  context-bytes allocate0 ?dup if nip 0 swap exit then dup context-sized context-made ;
\ Free an idle context made by context-new and give FREE's ior. If it is
\ the current task's context, the task returns to the main context. Aborts
\ on the main context, an owned context or an address that is not a
\ context.
: context-freeable ( context -- context )
  dup context? 0= abort" context-free: not a context"
  dup context-main = abort" context-free: the main context"
  dup context-idle? 0= abort" context-free: owned by a job" ;
: context-free ( context -- ior )
  context-outside-job context-freeable
  dup lf-context @ = if context-main lf-context ! then context-discard ;

\ Claiming for a job (task.fs). context-claim makes owner, a nonzero
\ token, the owner of an idle context and gives true; it gives false and
\ changes nothing for an address that is not a context, the main context,
\ the current task's context or a context already owned. context-release
\ makes a context idle again.
: context-claimable? ( context -- flag )
  dup context? 0= if drop false exit then
  dup context-main <> over lf-context @ <> and swap context-idle? and ;
: context-claim ( owner context -- flag )
  dup context-claimable? if context-owner ! true else 2drop false then ;
: context-release ( context -- ) 0 swap context-owner ! ;
