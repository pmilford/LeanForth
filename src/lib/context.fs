\ Checker contexts (ADR 0009): one record per worker holding all of a
\ check's mutable state, so that several checks can run in one Forth image.
\ The current task reaches its context through one pointer, lf-context: a
\ USER variable on Gforth, so each task has its own, and a plain variable on
\ other hosts, which then have one worker.
\
\ Modules declare their state as members of the context layout while they
\ load: context-record: (a zeroed record), context-store:, context-walk:,
\ context-walk2:, context-frames: and context-slab: each define name
\ ( -- addr ), the member's address in the current context; context-setup
\ registers a word that sets a module's state up, such as clearing a
\ base-1 store. Each
\ declaration grows the main context, which the main task uses from the
\ start, and initialises the new member in it at once, so a program that
\ never makes another context runs as before. A declaration that is
\ refused aborts before it defines or grows anything; a setup word that
\ throws is not registered.
\
\ Heap memory (the release hook; ADR 0009, amended 2026-11-03). A member
\ may own heap blocks, such as a growable scratch store (ADR 0016 C3),
\ only if its module registers with context-teardown a word ( -- ) that
\ frees them. context-free runs every teardown word in the context being
\ freed, selected as the current context afresh before each, newest
\ first, before it frees the context's own block; context-new runs them
\ too when a setup word fails, before it gives the block back. A teardown
\ word must free exactly what the member holds, whatever happened to it:
\ after a THROW in the middle of a check, and also on a member its setup
\ word never reached (zeroed), so it frees only blocks it finds and zeroes
\ what it freed. It
\ must not make, free, claim or select contexts. Each runs balanced under
\ CATCH, so one that throws or changes the stack does not stop the others
\ or keep the context's block: context-free then gives the first THROW
\ code (context-unbalanced for a wrong stack effect) instead of FREE's
\ ior. The main context is never freed, so its members keep their blocks
\ until the program ends.
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
\ job, or context-check-owner while it runs a check outside the job pool
\ (the checked environment's serial driver, kernel/env-publish.fs). A
\ task may select only a context whose owner is its own token: the main
\ task only idle contexts, a job only its own, a check outside the pool
\ none. An owned context cannot be freed, and contexts are made, freed,
\ claimed and released only outside jobs; context-in-job? counts such a
\ check as inside one.
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
\ Example: a module's growable walk and a record that owns a heap block,
\ declared while it loads; a new context, used and freed.
\   8 context-walk: my-walk              \ my-walk ( -- walk ), in every context
\   1 cells context-record: my-buffer    \ a heap block, or 0
\   : my-buffer-free ( -- ) my-buffer @ ?dup if free drop then 0 my-buffer ! ;
\   ' my-buffer-free context-teardown
\   context-new throw constant my-context
\   my-context context-use  64 allocate throw my-buffer !  context-main context-use
\   my-context context-free throw        \ runs my-buffer-free, frees the walk's block
\
\ Interface: lf-context lf-owner context-check-owner context-in-job?
\ context-unbalanced ?call-balanced call-balanced allocate0 /context-header
\ context-owner context-bytes context-main context-seal context-sealed?
\ context? context-idle? context-use context-record: context-store:
\ context-walk: context-walk2: context-frames: context-slab: context-setup
\ context-teardown context-need context-needs context-new context-free
\ context-claim context-release context-catch. Every other word is private
\ (lf-lib-private; ADR 0010): tests reach it with `lf-lib-private order+`.
\
\ State: the layout record, context-layout, with the stated stack needs
\ and the teardown words, and the lists of walk, frames and slab members
\ (shared; read-only once sealed, and only the main task declares members,
\ needs and teardowns), the main context it points to,
\ and lf-context and lf-owner (per task). Never keep a member's address
\ across a context switch or a declaration: while modules load, each
\ declaration may move the main context. Never ALLOT or compile after
\ tasks start. Untrusted. The layout is host-specific and must never be
\ serialized.

require ./blocks.fs
require ./bounds.fs
require ./portability.fs
require ./module.fs
require ./store.fs
require ./walk.fs
require ./frame.fs
require ./slab.fs

lf-lib-private module-open

\ Every word below is private (lf-lib-private) except those defined
\ after an `lf-lib set-current` and before the next `lf-lib-private
\ set-current`: the Interface list of the header.
lf-lib set-current
begin-structure /context-header
lf-lib-private set-current
  field: context-size      \ bytes in the context; zeroed by context-free
lf-lib set-current
  field: context-owner     \ the owner's token, or 0 while idle
end-structure
lf-lib-private set-current

begin-structure /context-layout
  field: layout-bytes      \ size of every context so far
  field: layout-first      \ first member declared, or 0
  field: layout-last       \ last member declared, or 0
  field: layout-main       \ the main context
  field: layout-sealed     \ true once a context is made or a job submitted
  field: layout-data-need  \ deepest data-stack nesting a module states
  field: layout-return-need \ deepest return-stack nesting a module states
  field: layout-teardowns  \ teardown words, newest first, or 0
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
  field: member-capacity   \ store capacity, or a walk's first room
  field: member-width      \ store record width, or walk width (1 or 2)
  field: member-base       \ store index base
  field: member-xt         \ setup word, or frames visitor
end-structure

lf-lib set-current
\ The current task's context and owner token.
[defined] udp [defined] next-task and
[if] user lf-context user lf-owner [else] variable lf-context variable lf-owner [then]
0 lf-owner !
\ The token of a check that runs outside the job pool, as a job's word
\ does but in the driving task: no job and no context has it, so every
\ guard that refuses a job refuses that check too.
-1 constant context-check-owner
\ Whether the current task runs a job, or such a check: its token is not 0.
: context-in-job? ( -- flag ) lf-owner @ 0<> ;

\ Running a word with its stack checked, as task.fs runs a job's word and
\ kernel/env-publish.fs a check. call-balanced runs xt ( -- ) above x and
\ throws context-unbalanced when xt changed the stack depth or x, so a word
\ with a wrong stack effect never goes unnoticed, even one that consumes
\ and replaces the cell below it. The code, outside Forth-2012's reserved
\ range, is task.fs's task-unbalanced.
-4096 constant context-unbalanced
: ?call-balanced ( flag -- ) 0= if context-unbalanced throw then ;
: call-balanced ( x xt -- )
  over >r depth >r execute depth r> 1- = ?call-balanced r> = ?call-balanced ;

\ allocate0 ( u -- addr ior ), ALLOCATE of zeroed memory, is blocks.fs's.

: context-bytes ( -- u ) context-layout layout-bytes @ ;
: context-main ( -- context ) context-layout layout-main @ ;
lf-lib-private set-current
: context-first ( -- addr ) context-layout layout-first ;
: context-last ( -- addr ) context-layout layout-last ;
lf-lib set-current
: context-seal ( -- ) true context-layout layout-sealed ! ;
: context-sealed? ( -- flag ) context-layout layout-sealed @ ;

\ Selecting a context. context? is true for a live context of the current
\ layout (a sanity check: it cannot recognise every bad address).
\ context-use aborts on any other address and on a context owned by
\ another token than the current task's.
: context? ( addr -- flag ) ?dup if context-size @ context-bytes = else false then ;
: context-idle? ( context -- flag ) context-owner @ 0= ;
lf-lib-private set-current
: context-mine? ( context -- flag ) context-owner @ lf-owner @ = ;
lf-lib set-current
: context-use ( context -- )
  dup context? 0= abort" context-use: not a context"
  dup context-mine? 0= abort" context-use: owned by another job" lf-context ! ;
lf-lib-private set-current

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
\ Lists of members of one kind (walks, frames records, slabs) whose blocks
\ a teardown word frees: nodes laid down in the dictionary, newest first.
begin-structure /listed
  field: listed-next       \ the node added before, or 0
  field: listed-offset     \ the member's offset in a context
end-structure
0 listed-next 0<> 0 listed-offset cell <> or /listed 2 cells <> or
[if] .( context.fs: member-listed lays down /listed out of order) cr abort [then]
\ Add a member to a list: its node's fields laid down in their order.
: member-listed ( member list -- member ) here over @ , swap ! dup member-offset @ , ;
\ A listed member's address in the current context.
: listed-member ( node -- addr ) listed-offset @ lf-context @ + ;
\ Run xt ( addr -- ) on each member of the list, newest first.
: listed-each ( list xt -- )
  swap @ begin ?dup while 2dup listed-member swap execute listed-next @ repeat drop ;

\ Initialisers ( addr member -- ). The context is zeroed beforehand.
: member-zeroed ( addr member -- ) 2drop ;
: member-store ( addr member -- )
  swap >r dup member-shape@ rot member-base @ r> store-init
  0= abort" context: bad store" ;
: member-walk ( addr member -- )
  member-shape@ 2 pick walk-sized-init 0= abort" context: bad walk" walk-growable ;
: member-frames ( addr member -- ) member-xt @ swap frame-init ;
: member-setup ( addr member -- ) nip member-xt @ execute ;

lf-lib set-current
\ Declaring words. A bad size, shape or capacity aborts and defines
\ nothing, as for store: and walk:.
: context-record: ( size "name" -- )
  dup 1 < abort" context-record: bad size" ['] member-zeroed member: member-add ;
: context-store: ( capacity width base "name" -- )
  >r 2dup r@ store-plan? 0= abort" context-store: bad shape"
  2dup store-size ['] member-store member: member-shape!
  r> over member-base ! member-add ;
lf-lib-private set-current
\ A context's walks are growable (walk.fs): capacity is their first room;
\ their heap blocks are freed with the context (walks-free, below).
variable context-walks
: walk-listed ( member -- member ) context-walks member-listed ;
: context-walked ( capacity width "name" -- )
  2dup walk-plan? 0= abort" context-walk: bad capacity"
  2dup walk-span ['] member-walk member: member-shape! walk-listed member-add ;
lf-lib set-current
: context-walk: ( capacity "name" -- ) 1 context-walked ;
: context-walk2: ( capacity "name" -- ) 2 context-walked ;
lf-lib-private set-current
\ A frames record (frame.fs) of the visitor xt, which reaches the record
\ through its frames argument; its stack is freed with the context
\ (frames-free, below). A module that embeds frames in a record of its own
\ registers a teardown that frees them (mixed-shift.fs).
variable context-frame-list
: frames-listed ( member -- member ) context-frame-list member-listed ;
lf-lib set-current
: context-frames: ( xt "name" -- )
  /frames ['] member-frames member: tuck member-xt ! frames-listed member-add ;
\ Run xt ( -- ) now in the main context, and in every new context after
\ the members declared before it are initialised.
: context-setup ( xt -- )
  0 context-open ['] member-setup member, tuck member-xt ! member-add ;
lf-lib-private set-current

\ Teardown words, laid down in the dictionary as they are registered and
\ linked newest first, so that a member registered later is torn down
\ before the ones it may depend on.
begin-structure /teardown
  field: teardown-link     \ the teardown registered before, or 0
  field: teardown-xt       \ xt ( -- ) that frees what a member holds
end-structure
: teardown-link-in ( teardown -- )
  context-layout layout-teardowns 2dup @ swap teardown-link ! ! ;
lf-lib set-current
\ Run xt ( -- ) in every context that is freed (see the header); aborts
\ once the layout is sealed, like every declaration.
: context-teardown ( xt -- )
  context-sealed? abort" context: teardown declared after context-new"
  align here /teardown allot tuck teardown-xt ! teardown-link-in ;
lf-lib-private set-current
\ Running them. teardown-call runs xt balanced and gives 0 or its THROW
\ code; ior-earlier keeps the first nonzero code. Each teardown word runs
\ with the context selected afresh, so that one which threw while another
\ context was selected cannot make the next free that context's blocks.
: teardown-call ( xt -- ior ) 0 swap ['] call-balanced catch dup if nip nip then ;
: ior-earlier ( ior1 ior2 -- ior ) over if drop else nip then ;
: teardown-in ( context teardown -- ior ) swap lf-context ! teardown-xt @ teardown-call ;
: teardowns-run ( context -- ior )
  0 context-layout layout-teardowns @ begin ?dup while
    dup >r 2 pick swap teardown-in ior-earlier r> teardown-link @
  repeat nip ;
\ Every teardown word in context; the current context is restored
\ afterwards.
: context-torn ( context -- ior ) lf-context @ >r teardowns-run r> lf-context ! ;

\ Growable arrays (plan task 6.2.0): context-slab: ( width "name" -- )
\ defines name ( -- slab ), a slab (slab.fs) of units of width address
\ units, empty in every context; slab-reserve grows it to n units (ok, or
\ full when the heap has no room), slab-at gives unit i's address, valid
\ until it next grows. Every context's slab members are freed with it.
\ The list of their offsets is laid down while loading, read-only after.
variable context-slabs
: member-slab ( addr member -- )
  member-width @ max-n over / rot slab-init ok? 0= abort" context: bad slab" ;
: slabs-free ( -- ) context-slabs ['] slab-free listed-each ;
' slabs-free context-teardown
: walks-free ( -- ) context-walks ['] walk-free listed-each ;
' walks-free context-teardown
: frames-free ( -- ) context-frame-list ['] frame-free listed-each ;
' frames-free context-teardown
: slab-listed ( member -- member ) context-slabs member-listed ;
lf-lib set-current
: context-slab: ( width "name" -- )
  dup 1 < abort" context-slab: bad width"
  /slab ['] member-slab member: tuck member-width ! slab-listed member-add ;
lf-lib-private set-current

\ Stack needs: the deepest nesting, in data and return-stack cells, that
\ any module states for one of its checks (such as mixed-beta.fs's nested
\ passes). Stated while modules load, like members (afterwards it aborts);
\ the largest of each is kept, and task.fs's pool-start refuses worker
\ stacks that do not cover it.
: context-max! ( n addr -- ) dup @ rot max swap ! ;
lf-lib set-current
: context-need ( data-cells return-cells -- )
  context-sealed? abort" context: need stated after context-new"
  context-layout layout-return-need context-max!
  context-layout layout-data-need context-max! ;
: context-needs ( -- data-cells return-cells )
  context-layout dup layout-data-need @ swap layout-return-need @ ;
lf-lib-private set-current

\ Making and freeing contexts, only outside jobs (these abort inside one).
\ context-new gives a new, idle context and 0, or 0 and the ior of a
\ failed ALLOCATE or the THROW code of a failed initialiser or setup word,
\ freeing what it allocated, the members' heap blocks through their
\ teardown words. Of that code, a teardown word's and FREE's, it gives
\ the earliest nonzero one: the setup word's, which came first. The
\ current context is unchanged either way.
: context-outside-job ( -- ) context-in-job? abort" context: not allowed inside a job" ;
: context-members ( -- )
  context-first @ begin ?dup while dup member-run member-link @ repeat ;
: context-fill ( context -- ior )
  lf-context @ >r lf-context ! ['] context-members catch r> lf-context ! ;
: context-discard ( context -- ior ) 0 over context-size ! free ;
\ Undo a context whose filling failed with ior: tear it down and free it.
: context-undo ( context ior -- ior' )
  over context-torn ior-earlier swap context-discard ior-earlier ;
: context-made ( context -- context ior )
  dup context-fill dup 0= if exit then context-undo 0 swap ;
lf-lib set-current
: context-new ( -- context ior )
  context-outside-job context-seal
  context-bytes allocate0 ?dup if nip 0 swap exit then dup context-sized context-made ;
lf-lib-private set-current
\ Free an idle context made by context-new: run its teardown words, then
\ free its block, and give the first teardown word's THROW code, or else
\ FREE's ior. If it is the current task's context, the task returns to
\ the main context. Aborts on the main context, an owned context or an
\ address that is not a context.
: context-freeable ( context -- context )
  dup context? 0= abort" context-free: not a context"
  dup context-main = abort" context-free: the main context"
  dup context-idle? 0= abort" context-free: owned by a job" ;
lf-lib set-current
: context-free ( context -- ior )
  context-outside-job context-freeable
  dup lf-context @ = if context-main lf-context ! then
  dup context-torn swap context-discard ior-earlier ;
lf-lib-private set-current

\ Claiming for a job (task.fs). context-claim makes owner, a nonzero
\ token, the owner of an idle context and gives true; it gives false and
\ changes nothing for an address that is not a context, the main context,
\ the current task's context or a context already owned, and inside a job
\ or a check, where it reads nothing at the address. context-release
\ makes a context idle again; it aborts inside a job or a check. Both are
\ refused there like context-new and context-free: otherwise a check
\ could claim a context with its own token and select it, or release
\ another job's context. task.fs, which alone calls them, claims in
\ job-submit and releases in job-submit and job-wait, each after refusing
\ a call inside a job, so it needs no unguarded copy.
\ An idle context other than the main and the current one.
: context-other? ( context -- flag )
  dup context-main <> over lf-context @ <> and swap context-idle? and ;
: context-claimable? ( context -- flag )
  context-in-job? if drop false exit then
  dup context? if context-other? else drop false then ;
lf-lib set-current
: context-claim ( owner context -- flag )
  dup context-claimable? if context-owner ! true else 2drop false then ;
: context-release ( context -- ) context-outside-job 0 swap context-owner ! ;

\ CATCH that restores the current task's context afterwards, whatever xt
\ selected or threw: ior is 0 or xt's THROW code, as for CATCH. The owner
\ token, lf-owner, is not restored.
: context-catch ( i*x xt -- j*x ior ) lf-context @ >r catch r> lf-context ! ;

module-close
