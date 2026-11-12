\ Dependent exports checked against a snapshot (ADR 0020 D5; plan task
\ 6.2.5, step SN4). [kernel][import] code: experimental, not through the
\ review gate, not independently audited; LeanForth-specific.
\
\ check --snapshot S EXPORT (cli/check-run.fs ck-snapshot-import): S's
\ tier is loaded (import/snapshot-tier.fs) and the export staged on into
\ it (stage-continue), so that a record of the export equal to one of S
\ has S's number; S's declarations are kept aside here first (imp-keep)
\ and the export's become the checker's input. Then, before any check,
\ one pass over the input in order (imp-pass) takes from S every
\ declaration for which the import rule I1 holds, publishing its slot
\ with S's outcome and fields and provenance snapshot; the run then
\ checks the others as usual (serially or with --jobs), their lookups
\ seeing the taken slots as final.
\
\ The rule I1, for input declaration k and S's slot d of its name:
\ 1. same content: their staged records equal field for field but the
\    chain (name, kind and flags but the mdata mark, parameters, type,
\    value, hint, kind data), as numbers of the one tier; a block's
\    member only when the whole block is equal (its block record and every
\    member) and k and d hold the same place in it;
\ 2. a reproducible verdict: d's outcome is neither full nor invalid, nor
\    exhausted (fuel used depends on the tier's numbering too; below);
\ 3. the same answers: every lookup S recorded for d, asked again in k's
\    snapshot by the environment's own code (environment.fs
\    lf-env-replay), gives the recorded answer, every slot it returns
\    taken from the slot S recorded; a lookup that meets a slot not taken
\    (not final: it is checked in this run) is no match (lf-env-early?);
\    and every dependency of d was taken, so it has a slot here.
\ Several S declarations of one name are tried newest first; two equal
\ ones are told apart by their own-name lookups. A slot S published with
\ the one before (a block's member after its first) is taken only with
\ that first, as its span; a member S checked alone, only when its
\ block's first member was taken here (so that a check here of the first
\ cannot span it). A taken slot is published by the publisher's own
\ serial step (env-publish.fs lf-env-step) with imp-fill as its check:
\ the lookups asked again (recorded with this run's answers), d's
\ dependencies as their slots here, its marks, warnings, recipe, axiom
\ bits, span and shapes, provenance snapshot (lf-env-saved!), so that the
\ publisher re-checks it as a check's. A publication with another outcome
\ than S's, or a fault, stops the pass (invalid).
\
\ Why a taken slot holds what a fresh check of the export would publish
\ (I2, ADR 0020 D5): a check's outcome, fuel and recorded fields depend
\ only on its declaration's content, the verdict settings and version
\ (the snapshot's header, compared when it was opened) and its lookups'
\ answers with the slots they return; by induction over the input's order
\ every slot those answers return was taken from the one S's check saw.
\ It vouches for nothing more than ADR 0020 D4 says a snapshot does. A
\ taken slot's diagnostic is S's (information only, never compared). I2
\ does not hold for fuel used today: checked against Init's snapshot, a
\ Mathlib prefix's checks used a few percent more or less fuel than in its
\ fresh check (the tier numbers its records otherwise), with the same
\ verdicts; so a taken slot reports S's run's fuel, and an exhausted one
\ is never taken (I1.2). Making fuel independent of the numbering is a
\ kernel task for the review.
\
\ Counts: imp-taken# (slots taken), imp-other# (declarations that share a
\ name with one of S and match none of S's of that name in content).
\ Outcomes (ADR 0008): ok; full for no heap; invalid for a stage or input
\ that does not match (a fault of the caller) or a taken slot published
\ otherwise. State: one /imp record per run, its heap blocks freed by
\ imp-free, used by the driving task; imp-current, the record imp-fill
\ reads (one pass at a time). S's slot fields are read from the snapshot
\ record env-snapshot.fs reads (snap-loading), which the caller sets.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/u32.fs
require ../lib/bytes.fs
require ../import/stage.fs
require ./environment.fs
require ./env-publish.fs
require ./env-snapshot.fs

begin-structure /imp
  field: imp-stage       \ the stage: S's tier, the export read on into it
  field: imp-sdecls      \ S's staged declarations, copied, /staged each
  field: imp-sdecls#     \ how many
  field: imp-slot-of     \ per S declaration: its slot + 1; 0 for a block record
  field: imp-newest      \ per name of S's tier: its newest S declaration + 1, or 0
  field: imp-names#      \ the names of S's tier
  field: imp-sn          \ S's slots
  field: imp-staged-of   \ per input declaration: its staged number
  field: imp-n           \ the input's declarations
  field: imp-from        \ per input declaration: the S slot taken + 1, or 0
  field: imp-to          \ per S slot: the input declaration that took it + 1, or 0
  field: imp-taken       \ slots taken
  field: imp-other       \ declarations of S's names, none of the same content
  field: imp-seen        \ imp-unit: a declaration of the same content was met
  field: imp-k           \ imp-fill: the declaration taking
  field: imp-d           \ and the S slot taken
  8 cells +field imp-firsts   \ the first number of tier sections 1-8 after S's
  field: imp-renum       \ a layer: per input declaration, its number in S and the layer
  field: imp-lslots      \ per slot of the layer: its input declaration
  field: imp-ln          \ the layer's slots
  field: imp-ldecls      \ its declarations, /staged each
  field: imp-ldn         \ how many
  field: imp-llines      \ their lines
  field: imp-lnewest     \ per name: its newest layer declaration + 1, numbered after S's
  field: imp-blk         \ while writing: the block met is in the layer
end-structure
variable imp-current
: imp@ ( -- imp ) imp-current @ ;

\ ---- Arrays of 32-bit numbers in heap blocks the record owns.
: ua@ ( i addr -- u ) swap u32s + u32@ ;
: ua! ( u i addr -- ) swap u32s + u32! ;
\ A zeroed array of n numbers at the cell addr: ok, or full.
: ua-new ( n addr -- outcome )
  >r u32s 1 max dup allocate if 2drop r> drop outcome-full exit then
  dup rot erase r> ! outcome-ok ;
: imp-free ( imp -- )
  dup imp-sdecls heap-release dup imp-slot-of heap-release dup imp-newest heap-release
  dup imp-staged-of heap-release dup imp-from heap-release dup imp-to heap-release
  dup imp-renum heap-release dup imp-lslots heap-release dup imp-ldecls heap-release
  dup imp-llines heap-release dup imp-lnewest heap-release /imp erase ;

\ ---- S kept aside, from a stage tier-read filled, before the export is
\ read into it: its declarations, each one's slot, and each name's newest
\ declaration (its chain, staged-prev, leads to the others).
: s-decl ( sd imp -- addr ) imp-sdecls @ swap /staged * + ;
: s-count ( imp -- n ) imp-sdecls# @ ;
: s-kind ( sd imp -- kind ) s-decl staged-head u32@ head-tag ;
: s-name ( sd imp -- name ) s-decl staged-name u32@ ;
: s-prev ( sd imp -- u ) s-decl staged-prev u32@ ;
: s-slot ( sd imp -- d ) imp-slot-of @ ua@ 1- ;
: block? ( kind -- flag ) kind-inductive = ;
\ A staged record that has a slot: any but a block record, and an empty
\ block's (no type, constructor or recursor), which the feed makes one
\ declaration (import/feed.fs feed-empty-block).
: block-empty? ( addr stage -- flag )
  swap staged-more u32@ swap stage-tuples 0 3 0 do i 3 pick 3 pick tuple-item + loop
  nip nip 0= ;
: slot-record? ( addr stage -- flag )
  over staged-head u32@ head-tag block? if block-empty? else 2drop true then ;
: s-bytes ( imp -- u ) s-count /staged * ;
: s-source ( imp -- addr ) 0 swap imp-stage @ staged-at ;
: keep-copy ( imp -- outcome )
  dup imp-stage @ stage-decls over imp-sdecls# !
  dup s-bytes 1 max allocate if 2drop outcome-full exit then
  over imp-sdecls ! dup s-source over imp-sdecls @ rot s-bytes move outcome-ok ;
\ Declaration sd gets slot n, unless it is a block record (no slot).
: keep-slot ( n sd imp -- n' )
  2dup s-decl over imp-stage @ slot-record? 0= if 2drop exit then
  >r over 1+ swap r> imp-slot-of @ ua! 1+ ;
: keep-slots ( imp -- outcome )
  dup s-count over imp-slot-of ua-new dup ok? 0= if nip exit then drop
  0 over s-count 0 ?do i 2 pick keep-slot loop swap imp-sn ! outcome-ok ;
: keep-name ( sd imp -- )
  2dup s-name ?dup if >r swap 1+ r> rot imp-newest @ ua! else 2drop then ;
: keep-names ( imp -- outcome )
  dup imp-stage @ stage-tier tier-names cons-numbers over imp-names# !
  dup imp-names# @ over imp-newest ua-new dup ok? 0= if nip exit then drop
  dup s-count 0 ?do i over keep-name loop drop outcome-ok ;
\ Keep S's declarations of stage aside (see above): ok, or full. S's slots
\ are then imp-sn, the count the snapshot's own sections must have.
\ The first number of each tier section 1-8 after S's (a layer's own
\ records are numbered on from them).
: keep-firsts ( imp -- )
  8 0 do
    i 1+ over imp-stage @ tier-slab slab-count over imp-firsts i cells + !
  loop drop ;
: imp-keep ( stage imp -- outcome )
  dup /imp erase tuck imp-stage ! dup keep-firsts
  dup keep-copy dup ok? 0= if nip exit then drop
  dup keep-slots dup ok? 0= if nip exit then drop keep-names ;
: imp-sn@ ( imp -- n ) imp-sn @ ;

\ ---- The input, after the export was read, sealed and fed: each
\ declaration's staged number (a block record gives none), and the maps
\ of what is taken. Invalid unless the input is the stage's.
: e-staged ( k imp -- ie ) imp-staged-of @ ua@ ;
: e-kind ( ie imp -- kind ) imp-stage @ staged-kind@ ;
: input-slot ( n ie imp -- n' )
  2dup imp-stage @ staged-at over imp-stage @ slot-record? 0= if 2drop exit then
  >r over r> imp-staged-of @ ua! 1+ ;
: e-count ( imp -- n ) imp-stage @ stage-decls ;
: imp-input ( imp -- outcome )
  dup e-count over imp-staged-of ua-new dup ok? 0= if nip exit then drop
  0 over e-count 0 ?do i 2 pick input-slot loop
  dup lf-input-count <> if 2drop outcome-invalid exit then
  over imp-n ! dup imp-n @ over imp-from ua-new dup ok? 0= if nip exit then drop
  dup imp-sn @ swap imp-to ua-new ;

\ ---- I1.1, the same content.
: e-decl ( ie imp -- addr ) imp-stage @ staged-at ;
: head-of ( addr -- u ) staged-head u32@ staged-marked-bit invert and ;
\ Two staged records alike in every field but the chain and the mdata
\ mark (set when the stage is sealed).
: decl-same? ( a1 a2 -- flag )
  2dup head-of swap head-of = >r
  staged-name 6 u32s rot staged-name 6 u32s compare 0= r> and ;
: decls-alike? ( ie sd imp -- flag ) tuck s-decl >r e-decl r> decl-same? ;
\ n declarations from ie and from sd alike.
: span-same? ( ie sd n imp -- flag )
  swap >r true r> 0 ?do 3 pick i + 3 pick i + 3 pick decls-alike? and loop nip nip nip ;
\ A member's block record: the nearest block record before it; -1 for
\ none (S's declarations are never fed, so the loader checked no block).
: s-block ( sd imp -- sb|-1 )
  begin over 0< 0= while 2dup s-kind block? if drop exit then swap 1- swap repeat drop ;
: e-block ( ie imp -- eb|-1 )
  begin over 0< 0= while 2dup e-kind block? if drop exit then swap 1- swap repeat drop ;
: blocks-of ( ie sd imp -- eb sb ) tuck s-block >r e-block r> ;
\ The members of the input's block eb: its types, constructors, recursors.
: block-size ( eb imp -- m )
  imp-stage @ 0 3 0 do i 3 pick 3 pick staged-item + loop nip nip ;
: places-same? ( ie sd eb sb -- flag ) rot swap - -rot - = ;
: s-fits? ( sb n imp -- flag ) >r + r> s-count swap < 0= ;
: block-same? ( ie sd imp -- flag )
  >r 2dup r@ blocks-of dup 0< if 2drop 2drop r> drop false exit then
  2swap 2over places-same? 0= if 2drop r> drop false exit then
  over r@ block-size 1+ 2dup r@ s-fits? 0= if 2drop drop r> drop false exit then
  r> span-same? ;
: unit-same? ( ie sd imp -- flag )
  2 pick over e-kind member-kind? if block-same? else decls-alike? then ;
: content? ( k sd imp -- flag ) rot over e-staged -rot unit-same? ;

\ ---- I1.2 and I1.3, in k's snapshot. S's fields are read through
\ env-snapshot.fs (saved, start@, dep@, look-key, look-answer).
: d-outcome ( d -- outcome ) sl-outcome swap saved ;
\ Full and invalid depend on memory or a fault; exhausted on fuel, which
\ (measured on a Mathlib prefix against Init's snapshot) also depends on
\ the tier's numbering, not only on content and lookups.
: unrepeatable? ( outcome -- flag )
  dup outcome-full = over outcome-invalid = or swap outcome-exhausted = or ;
: reproducible? ( d -- flag ) d-outcome unrepeatable? 0= ;
: d-trailing? ( d -- flag ) sl-marks swap saved mark-with and 0<> ;
\ Slots k .. k+n-1 in the input and not final.
: e-final? ( k -- flag ) lf-env lf-env-slot lf-slot-state @ lf-state-final = ;
: e-open? ( k n -- flag )
  over + dup lf-env lf-env-length > if 2drop false exit then
  true -rot swap ?do i e-final? 0= and loop ;
\ A member after its block's first: only when the first was taken here.
: e-first ( k imp -- k' ) 2dup e-staged tuck swap e-block 1+ - - ;
: first-taken? ( k imp -- flag )
  2dup e-staged over e-kind member-kind? 0= if 2drop true exit then
  2dup e-first rot over = if 2drop true exit then swap imp-from @ ua@ 0<> ;
: saved-looks ( d -- j n ) dup start@ nip swap sl-looks swap saved ;
: saved-deps ( d -- j n ) dup start@ drop swap sl-deps swap saved ;
: dep-taken ( s imp -- e+1|0 ) imp-to @ ua@ ;
: deps-taken? ( d imp -- flag )
  swap saved-deps bounds ?do
    i snap@ dep@ over dep-taken 0= if drop false unloop exit then
  loop drop true ;
\ Every saved lookup of d asked again, recorded in the candidate.
: replay-all ( d -- flag )
  saved-looks bounds ?do
    i snap@ look-key lf-env-replay 0= if false unloop exit then
  loop true ;
\ An answer of this run in S's terms: the slot it gives, taken from S's.
: answer-taken ( answer imp -- answer' true | false )
  over lf-look-slot+1 ?dup 0= if drop true exit then
  1- swap imp-from @ ua@ ?dup 0= if drop false exit then
  4 lshift swap 15 and or true ;
\ The candidate's entry i against S's entry j.
: entry-same? ( i j imp -- flag )
  rot lf-look-at 2@ swap rot answer-taken 0= if 2drop false exit then
  rot dup >r snap@ look-answer = swap r> snap@ look-key = and ;
: answers-same? ( d imp -- flag )
  swap saved-looks dup lf-cand-looked@ <> if 2drop drop false exit then
  0 ?do i over i + 3 pick entry-same? 0= if 2drop false unloop exit then loop 2drop true ;
: asked? ( d imp -- flag )
  over replay-all if lf-env-early? 0= if answers-same? exit then then 2drop false ;
\ The lookups asked in k's snapshot, which is then cleared, the scratch
\ the queries made rolled back.
: replayed? ( k d imp -- flag )
  rot lf-env-begin ok? 0= if 2drop false exit then
  asked? lf-env-clear lf-input-rollback drop ;
: takable? ( k d imp -- flag )
  over reproducible? 0= if 2drop drop false exit then
  over d-trailing? if 2drop drop false exit then
  2 pick over first-taken? 0= if 2drop drop false exit then
  2dup deps-taken? 0= if 2drop drop false exit then
  2 pick 2 pick fill-span e-open? 0= if 2drop drop false exit then
  replayed? ;

\ ---- Taking. imp-fill is the check word of the publication.
: depend-all ( d imp -- flag )
  swap saved-deps bounds ?do
    i snap@ dep@ over dep-taken 1- lf-env-depend ok? 0= if drop false unloop exit then
  loop drop true ;
: imp-fill ( -- )
  imp@ dup imp-d @ swap over replay-all drop
  2dup depend-all 0= if 2drop outcome-invalid lf-env-finish exit then
  drop dup fill-marks dup fill-span dup lf-env-span! over swap fill-shapes lf-env-saved!
  sl-outcome swap saved lf-env-finish ;
: take-mark ( k d imp -- )
  >r 2dup 1+ swap r@ imp-from @ ua! dup r@ imp-to @ ua@ if 2drop r> drop exit then
  swap 1+ swap r> imp-to @ ua! ;
: take-marks ( k d n imp -- )
  swap 0 ?do 2 pick i + 2 pick i + 2 pick take-mark loop 2drop drop ;
: take ( k d imp -- outcome )
  dup imp-current ! >r 2dup r@ imp-d ! r@ imp-k !
  ['] imp-fill 2 pick lf-env-step if 2drop drop r> drop outcome-invalid exit then
  over d-outcome <> if 2drop r> drop outcome-invalid exit then
  dup fill-span dup r@ imp-taken +! r> take-marks outcome-ok ;

\ ---- The pass.
: e-name ( k imp -- name ) tuck e-staged swap imp-stage @ staged-name@ ;
: first-cand ( k imp -- sd+1|0 )
  tuck e-name 2dup swap imp-names# @ u< if swap imp-newest @ ua@ else 2drop 0 then ;
\ S's declaration sd tried for k: taken (an outcome), or not (-1).
: cand-try ( k sd imp -- outcome|-1 )
  2 pick 2 pick 2 pick content? 0= if 2drop drop -1 exit then
  true over imp-seen ! tuck s-slot swap
  2 pick 2 pick 2 pick takable? if take else 2drop drop -1 then ;
\ Declaration k: S's declarations of its name tried, newest first; one
\ that shares its name, none its content, counted.
: imp-unit ( k imp -- outcome )
  false over imp-seen ! 2dup first-cand dup >r
  begin ?dup while
    1- 2 pick over 3 pick cand-try dup -1 <> if nip nip nip r> drop exit then drop
    over s-prev
  repeat
  r> if dup imp-seen @ 0= if 1 over imp-other +! then then 2drop outcome-ok ;
\ Take what can be taken (see the header), in a current environment over
\ the input imp-input read, before any check: ok, or the first failure.
: imp-pass ( imp -- outcome )
  dup imp-n @ 0 ?do
    i e-final? 0= if i over imp-unit dup ok? 0= if nip unloop exit then drop then
  loop drop outcome-ok ;

\ ---- What the run reads afterwards.
: imp-taken# ( imp -- n ) imp-taken @ ;
: imp-other# ( imp -- n ) imp-other @ ;
\ The S slot input declaration k was taken from, or -1.
: imp-source ( k imp -- d|-1 ) imp-from @ ?dup if ua@ 1- else drop -1 then ;
: imp-firsts@ ( imp -- addr ) imp-firsts ;

\ ---- A layer of this run (ADR 0020 amendment 1, F5; plan step SN4),
\ after a run whose every slot is final: the input declarations not
\ taken from S, its slots numbered on from S's (imp-renumber gives every
\ input declaration's number in S and the layer, imp-which a layer slot's
\ input declaration), and their staged declarations, each block with its
\ block record, in input order, their chains numbered on from S's
\ declarations, with their lines. A block whose first member was taken
\ but not every member (S checked them apart) cannot be written: invalid.
: lslot! ( k imp -- ) dup >r imp-ln @ r@ imp-lslots @ ua! 1 r> imp-ln +! ;
: layer-number ( imp -- n ) dup imp-sn @ swap imp-ln @ + ;
: renum! ( s k imp -- ) imp-renum @ ua! ;
: lkept? ( k imp -- flag ) imp-source 0< ;
: renum-one ( k imp -- )
  2dup imp-source dup 0< 0= if -rot renum! exit then drop
  2dup dup layer-number -rot renum! lslot! ;
: imp-which ( j -- k ) imp@ imp-lslots @ ua@ ;
: imp-renumber ( k -- s ) imp@ imp-renum @ ua@ ;
: ldecl ( ld imp -- addr ) imp-ldecls @ swap /staged * + ;
: base-newest ( name imp -- u )
  2dup imp-names# @ u< if imp-newest @ ua@ else 2drop 0 then ;
: lchain ( name imp -- u ) 2dup imp-lnewest @ ua@ ?dup if nip nip exit then base-newest ;
: lname! ( ld name imp -- ) >r swap r@ imp-sdecls# @ + 1+ swap r> imp-lnewest @ ua! ;
: ldecl-add ( ie imp -- )
  >r dup r@ e-decl r@ imp-ldn @ r@ ldecl /staged move
  r@ imp-stage @ staged-line@ r@ imp-ldn @ r@ imp-llines @ ua!
  r@ imp-ldn @ r@ ldecl dup staged-name u32@ dup if dup r@ lchain else 0 then
  rot staged-prev u32! ?dup if r@ imp-ldn @ swap r@ lname! then 1 r> imp-ldn +! ;
\ Input declaration ie of the stage, slot k next.
: lblock ( k ie imp -- k outcome )
  2 pick over lkept? dup >r over imp-blk ! r> if ldecl-add else 2drop then outcome-ok ;
: lmember ( k ie imp -- k' outcome )
  2 pick over lkept? over imp-blk @ <> if 2drop 1+ outcome-invalid exit then
  2 pick over lkept? if ldecl-add else 2drop then 1+ outcome-ok ;
: llone ( k ie imp -- k' outcome )
  2 pick over lkept? if ldecl-add else 2drop then 1+ outcome-ok ;
: lstep ( k ie imp -- k' outcome )
  2dup e-decl over imp-stage @ slot-record? 0= if lblock exit then 2dup e-kind
  member-kind? if lmember else llone then ;
: layer-decls ( imp -- outcome )
  0 over e-count 0 ?do i 2 pick lstep dup ok? 0= if nip nip unloop exit then drop loop
  2drop outcome-ok ;
: imp-block ( u addr -- outcome )
  >r 1 max dup allocate if 2drop r> drop outcome-full exit then
  tuck swap erase r> ! outcome-ok ;
: layer-room ( imp -- outcome )
  dup imp-n @ over imp-renum ua-new dup ok? 0= if nip exit then drop
  dup imp-n @ over imp-lslots ua-new dup ok? 0= if nip exit then drop
  dup e-count /staged * over imp-ldecls imp-block dup ok? 0= if nip exit then drop
  dup e-count over imp-llines ua-new dup ok? 0= if nip exit then drop
  dup imp-stage @ stage-tier tier-names cons-numbers swap imp-lnewest ua-new ;
: imp-layer ( imp -- outcome )
  dup imp-current ! dup layer-room dup ok? 0= if nip exit then drop
  0 over imp-ln ! 0 over imp-ldn ! dup imp-n @ 0 ?do i over renum-one loop layer-decls ;
\ The layer's slots and declarations, as env-snapshot.fs's snap-layer-slots!
\ and snap-layer-decls! take them.
: imp-layer-slots ( imp -- n which renum ) imp-ln @ ['] imp-which ['] imp-renumber ;
: imp-layer-decls ( imp -- decls n lines )
  dup imp-ldecls @ over imp-ldn @ rot imp-llines @ ;

base !   \ the BASE this file was loaded with
