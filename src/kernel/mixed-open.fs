\ Opening and closing binders with free variables (ADR 0014 Q2; plan task
\ 4.2.2a): ports of Lean's instantiate and instantiate_rev
\ (instantiate.cpp 15-39, 99-118), which put terms (such as the free
\ variables that name a binder's variables) for a body's loose bound
\ variables, abstract (abstract.cpp 14-32), which turns free variables
\ back into bound variables, and mk_pi (local_ctx.cpp 93-125), which wraps
\ a term in the Pis of free variables of the local context
\ (core/local-context.fs). Lean's files at the referee commit eb6cafb7
\ (ADR 0014, Reproduction).
\
\ The passes walk a term on a frames record's explicit stack
\ (lib/frame.fs), the binders entered so far (Lean's offset) as the
\ frames' context, and rebuild it as Lean's replace (replace_fn.cpp 32-75)
\ does with update_app and update_binding: a node whose children come back
\ unchanged is kept, so nothing is copied that does not change. With n
\ terms s0 .. s(n-1) (Lean's subst array):
\ - instantiate at offset d: a bound variable i < d is kept; i - d < n
\   becomes s(i - d); a larger one becomes bound variable i - n;
\ - instantiate_rev: the same with s(n - (i - d) - 1) (s0 names the
\   outermost binder);
\ - abstract at offset d: the free variable s(i), the last match from the
\   right as Lean searches, becomes bound variable d + n - i - 1; any other
\   free variable is kept.
\ The terms put in must be closed (no loose bound variables), as every
\ term the checker infers or compares is (mixed-infer.fs): Lean's
\ lift_loose_bvars then changes nothing and is not needed. That is the
\ callers' invariant, as it is Lean's; for abstract the n must be live
\ free variables (checked). n = 0 gives the term itself, unvisited, as
\ in Lean.
\
\ The passes are Lean's replace (replace_fn.cpp 16-75; compact-store plan
\ step S6, plan task 6.5.5). A binary node whose data word (core/terms.fs,
\ ADR 0016 C1: Lean's loose_bvar_range and has_fvar, kept in each node)
\ shows that the pass gives it back unchanged is kept without a visit
\ below it, as Lean's function returns it at once (instantiate.cpp 103:
\ no loose bound variable at or beyond the offset; abstract.cpp 19: no
\ free variable). A node whose word names a free variable is kept so by
\ instantiate only when the hook lf-open-unchanged? says so
\ (kernel/caches.fs, while the caches are on: its memo knows a free
\ variable only while it is live in this job's local context), and is
\ otherwise visited, as is a node without data: so a dead free variable
\ is met and refused as before. Every other result is kept for the rest
\ of the call in the replace memo (replace-memo.fs: Lean's m_cache, keyed
\ by the node and its offset) and given back when the node is met again
\ at that offset: a pass grows with the nodes and their offsets, never
\ with the paths, and a node shared in the input is shared in the result.
\ Closing a term with an inference scope's free variables
\ (lf-instantiate-scope, mixed-infer.fs) keeps its results beyond the
\ call, for every later closing under the same scope: the result for a
\ node and offset is then a function of the scope, which its innermost
\ free variable names (each binder gets a new one), so an argument that
\ inference closed is not closed again inside a larger one (ADR 0014,
\ Amendment 3). A new bound variable reuses the live leaf of its index
\ that a pass made before, if any: leaves never change, so this shares an
\ equal term (it saves room in a small term store).
\ Fuel: each visit costs one unit and one frame, on a stack that grows
\ with the depth (plan task 6.2.0): no fuel left is exhausted, a stack the
\ heap cannot grow full. A node kept by its data word or given back by the
\ memo ends its visit there, for its one unit. Only nodes older than
\ the pass are read, children before parents; a bound variable must be a
\ well-formed leaf and a free variable live, else the pass is invalid. Any
\ failure discards the nodes the pass made. n may be as large as the heap
\ holds a copy of (no room is full; negative invalid), and each of the n a
\ live node.
\
\ Words: lf-instantiate, lf-instantiate-rev, lf-instantiate-scope,
\ lf-abstract ( node subst n -- node' outcome ) and lf-mk-pi ( body fvars
\ n -- pi outcome ), each running on the fuel in lf-open-fuel and leaving
\ there what is left; subst and fvars are the address of n cells;
\ lf-open-forget ( -- ) empties the memo of closings (inference does when
\ a job starts). Outcomes: ok, invalid,
\ exhausted, full, and unsupported from lf-mk-pi for a let variable
\ (inference closes its let variables itself, as infer_let's mk_pi with
\ remove_dead_let does: mixed-infer.fs, plan task 4.2.3; lf-mk-pi has no
\ caller in the checker).
\ Example: with x the free variable of A (lf-lctx-local) in a cell at
\ addr, 100 lf-open-fuel !  body addr 1 lf-instantiate-rev gives the body
\ with bound variable 0 replaced by x, and that addr 1 lf-mk-pi gives
\ the Pi over x : A of the body back.
\ Untrusted; [kernel] code, not yet through the review gate.
\ State: one job record, lf-open-job (fields lf-openjob-*): the pass's
\ frames (fuel, nesting, the offset as context), its mode, the term count
\ before it, the bound-variable leaves it made, its copy of the n terms in
\ a growable array (lf-open-terms), and the replace memo lf-open-memo
\ (replace-memo.fs); members of the checker
\ context (lib/context.fs), whose frames a set-up word prepares in every
\ context. Single-threaded within one
\ context; a pass refuses to start inside another (invalid).

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/local-context.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./mixed-rebuild.fs
require ./replace-memo.fs

0 constant lf-open-mode-instantiate
1 constant lf-open-mode-rev
2 constant lf-open-mode-abstract
3 constant lf-open-mode-scope   \ instantiate_rev with an inference scope
128 constant lf-open-leaves   \ bound-variable indices whose leaf is kept

\ The frames come first, so the visitor finds the job record at the
\ address of the frames it is given (checked here), as in mixed-shift.fs.
begin-structure /lf-openjob
  /frames +field lf-openjob-frames     \ fuel, nesting, the offset as context
  field: lf-openjob-mode               \ one of the lf-open-mode-* constants
  /store-mark +field lf-openjob-start  \ the term store before the pass
  field: lf-openjob-count              \ n
  lf-open-leaves 2* cells +field lf-openjob-leaves  \ per index: node, identity
end-structure
0 lf-openjob-frames 0<> [if] .( mixed-open.fs: frames come first) cr abort [then]
/lf-openjob context-record: lf-open-job
\ s0 .. s(n-1), copied: as many as there are (no fixed limit).
1 cells context-slab: lf-open-terms
\ The replace memo, freed with the context.
/lf-rmemo context-record: lf-open-memo
:noname ( -- ) lf-open-memo lf-rmemo-release ; context-teardown

: lf-open-frames ( -- frames ) lf-open-job lf-openjob-frames ;
\ The fuel of the next pass, and what the last one left.
: lf-open-fuel ( -- addr ) lf-open-frames frame-fuel ;

\ Reading the job from the frames of the visit.
: lf-open-n ( frames -- n ) lf-openjob-count @ ;
: lf-open-s ( i frames -- node ) drop lf-open-terms slab-base swap cells + @ ;
: lf-open-mode ( frames -- mode ) lf-openjob-mode @ ;
: lf-open-abstract? ( frames -- flag ) lf-open-mode lf-open-mode-abstract = ;

\ Only nodes older than the pass, with children before them, are read:
\ nodes below the term store's mark taken when the pass starts (a store
\ mark, lib/store.fs: a boundary to read below, never rolled back to; the
\ pass's rollback is the rebuild's scratch mark, mixed-rebuild.fs).
: lf-open-readable? ( node frames -- flag )
  lf-openjob-start mark-count @ over 0 rot within swap lf-term-valid? and ;
: lf-open-below? ( child node -- flag ) 0 swap within ;
: lf-open-children? ( node -- flag )
  dup lf-term-first@ over lf-open-below?
  swap dup lf-term-second@ swap lf-open-below? and ;

\ Lean's replace keeps the result of each node per offset for the rest of
\ the call and gives it back when the node is met again at that offset
\ (replace_fn.cpp 26-40, m_cache): the replace memo (replace-memo.fs),
\ keyed by the node and the offset of its visit.
: lf-open-known? ( node frames -- result true | false )
  frame-context @ lf-open-memo lf-rmemo@ ;
: lf-open-keep ( result node frames -- ) frame-context @ lf-open-memo lf-rmemo! ;

\ update_app and update_binding (replace-memo.fs), the result kept for
\ the node at the offset of its visit.
: lf-open-update ( r1 node r2 -- result outcome )
  over >r lf-replace-update dup ok? if over r@ lf-open-frames lf-open-keep then r> drop ;
\ A binary node: the first child at this offset, the second one binder
\ deeper for a lambda or Pi (mixed-rebuild.fs's limits apply).
: lf-open-updated ( r2 outcome frames -- result outcome frames 0 )
  ['] lf-open-update lf-rebuild-joined ;
: lf-open-second ( r1 outcome frames -- second frames next | -1 outcome frames 0 )
  ['] lf-open-updated lf-rebuild-next ;
: lf-open-binary ( node frames -- ... frames next )
  over lf-open-children? 0= if lf-rebuild-refuse exit then
  2dup lf-rebuild-stuck? if nip >r lf-rebuild-deep r> 0 exit then
  ['] lf-open-second lf-rebuild-first ;

\ A bound-variable leaf of index i: the live one an earlier pass made for
\ i, else a new one, then kept for i; no room is full. While the term
\ store hash-conses (core/terms.fs, compact-store plan step S3) it gives
\ the live leaf back itself, so the leaves are not kept: what a pass makes
\ then never depends on what an earlier check left in this record.
: lf-open-slot ( i -- addr ) 2* cells lf-open-job lf-openjob-leaves + ;
: lf-open-kept? ( addr -- node true | false )
  dup @ dup lf-term-identity if rot cell+ @ = dup 0= if nip then else 2drop false then ;
: lf-open-remember ( node i -- node )
  over dup lf-term-identity drop rot lf-open-slot tuck cell+ ! ! ;
: lf-open-leaf-at ( i -- node outcome )
  dup 0 lf-open-leaves within 0= lf-term-sharing? or
  if lf-term-bvar lf-rebuild-allocated exit then
  dup lf-open-slot lf-open-kept? if nip outcome-ok exit then
  dup lf-term-bvar if swap lf-open-remember outcome-ok else drop lf-rebuild-full then ;

\ instantiate and instantiate_rev on bound variable i at offset d
\ (instantiate.cpp 22-33, 103-114): kept below d; for k = i - d < n the
\ term s(k), or s(n - k - 1) reversed; else bound variable i - n.
: lf-open-rev? ( frames -- flag )
  lf-open-mode dup lf-open-mode-rev = swap lf-open-mode-scope = or ;
: lf-open-k ( k frames -- j ) dup lf-open-rev? if lf-open-n swap - 1- else drop then ;
: lf-open-put ( k frames -- result outcome ) tuck lf-open-k swap lf-open-s outcome-ok ;
: lf-open-outer ( i frames -- result outcome )
  2dup frame-context @ - over lf-open-n <
  if tuck frame-context @ - swap lf-open-put else lf-open-n - lf-open-leaf-at then ;
: lf-open-loose ( node frames -- result outcome )
  over lf-term-first@ over frame-context @ < if lf-rebuild-keep exit then
  >r lf-term-first@ r> lf-open-outer ;
\ abstract on a free variable at offset d (abstract.cpp 21-28): the index
\ i of its last match among the n, or false; matched, bound variable
\ d + n - i - 1.
: lf-open-match ( fvar frames -- i true | false )
  dup lf-open-n begin dup while 1- >r 2dup r@ swap lf-open-s =
    if 2drop r> true exit then r> repeat drop 2drop false ;
: lf-open-bound ( i frames -- result outcome )
  dup lf-open-n rot - 1- swap frame-context @ + lf-open-leaf-at ;
: lf-open-abstract-fvar ( node frames -- result outcome )
  2dup lf-open-match if rot drop swap lf-open-bound else lf-rebuild-keep then ;

\ Leaves. A bound variable is a well-formed leaf (first field
\ nonnegative, second zero); a free variable is live; constants and Sorts
\ are kept, as Lean's replace keeps every leaf it is not asked to change.
: lf-open-bvar? ( node -- flag ) dup lf-term-first@ swap lf-term-second@ lf-repr-leaf? ;
: lf-open-bvar ( node frames -- result outcome )
  over lf-open-bvar? 0= if lf-rebuild-bad exit then
  dup lf-open-abstract? if lf-rebuild-keep else lf-open-loose then ;
: lf-open-free ( node frames -- result outcome )
  over lf-fvar-live? 0= if lf-rebuild-bad exit then
  dup lf-open-abstract? if lf-open-abstract-fvar else lf-rebuild-keep then ;
: lf-open-leaf ( node frames tag -- result outcome )
  case lf-tag-bvar of lf-open-bvar endof  lf-tag-fvar of lf-open-free endof
    lf-tag-constant of lf-rebuild-keep endof  lf-tag-proj of lf-rebuild-keep endof
    lf-tag-lit of lf-rebuild-keep endof  lf-tag-let of lf-rebuild-keep endof
    lf-tag-str of lf-rebuild-keep endof
    lf-tag-symbolic-sort of lf-rebuild-keep endof
    >r lf-rebuild-bad r> endcase ;
\ Whether a binary node comes back unchanged, so that Lean's replace
\ keeps it without a visit below it (instantiate.cpp 103: its
\ loose_bvar_range at most the offset; abstract.cpp 19: no free
\ variable), read from its data word (see the header): decided (flag
\ true), or false when the word has no data, or names a free variable a
\ kept node would hide from instantiate's liveness check. Undecided, the
\ hook answers: by default never unchanged; the caches set it
\ (kernel/caches.fs), whose memo checks that the free variables are live.
: lf-open-inst-word ( data offset -- flag true | false )
  over lf-data-loose < if drop false true exit then
  lf-data-fvar? if false else true true then ;
: lf-open-abs-word ( data -- flag true ) lf-data-fvar? 0= true ;
: lf-open-mode-word ( data frames -- flag true | false )
  dup lf-open-abstract? if drop lf-open-abs-word else frame-context @ lf-open-inst-word then ;
: lf-open-word ( node frames -- flag true | false )
  swap lf-term-data@ 0= if drop false exit then swap lf-open-mode-word ;
defer lf-open-unchanged? ( node frames -- flag )
:noname ( node frames -- flag ) 2drop false ; is lf-open-unchanged?
: lf-open-skip? ( node frames -- flag )
  2dup lf-open-word if nip nip else lf-open-unchanged? then ;
\ A node rebuilt before at this offset in this call: its result again,
\ for the visit's unit of fuel only.
: lf-open-again ( node frames -- ... frames next )
  2dup lf-open-known? if lf-replace-recall else lf-open-binary then ;
: lf-open-pair ( node frames -- ... frames next )
  2dup lf-open-skip? if lf-replace-same else lf-open-again then ;
\ The visit's first step (lib/frame.fs).
: lf-open-visit ( node frames -- ... frames next )
  2dup lf-open-readable? lf-rebuild-tag
  dup lf-term-binary-tag? if drop lf-open-pair else over >r lf-open-leaf r> 0 then ;
\ The frames and their visitor, set up once in every context; their stack
\ is freed with the context.
: lf-open-setup ( -- ) ['] lf-open-visit lf-open-frames frame-init ;
' lf-open-setup context-setup
: lf-open-release ( -- ) lf-open-frames frame-free ;
' lf-open-release context-teardown
\ Recovery after a THROW out of a pass (which leaves the record busy, so
\ that every later pass refuses as invalid): the record made idle again;
\ lf-mixed-rebuild-reset (mixed-beta.fs) resets all four rebuilding passes.
\ The memo is emptied too: the pass's own entries are stale.
: lf-open-reset ( -- ) lf-open-frames frame-reset lf-open-memo lf-rmemo-empty ;
\ Emptying the memo of closings (a new inference job's scope is new).
: lf-open-forget ( -- ) lf-open-memo lf-rmemo-empty ;

\ Running a pass: the n terms checked (live nodes, or live free variables
\ for abstract) and copied into the job, then the root visited at offset
\ 0 from the current term count; any failure discards what the pass made
\ (mixed-rebuild.fs). A pass in progress refuses another, changing
\ nothing: invalid. Running out of fuel or frames is recorded as a
\ diagnostic.
: lf-open-site ( -- site ) c" mixed-open lf-instantiate" ;
: lf-open-explain ( outcome -- outcome ) lf-open-frames lf-open-site lf-diag-frames ;
: lf-open-test ( mode -- xt )
  lf-open-mode-abstract = if ['] lf-fvar-live? else ['] lf-term-valid? then ;
: lf-open-all? ( subst n xt -- flag )
  true 2swap cells over + swap ?do over i @ swap execute and 1 cells +loop nip ;
: lf-open-count ( n -- outcome )
  dup 0< if drop outcome-invalid else lf-open-terms slab-hold then ;
: lf-open-copy ( subst n -- )
  dup lf-open-job lf-openjob-count ! cells lf-open-terms slab-base swap move ;
: lf-open-load ( subst n mode -- outcome )
  over lf-open-count dup ok? 0= if nip nip nip exit then drop
  lf-open-test >r 2dup r> lf-open-all? if lf-open-copy outcome-ok
  else 2drop outcome-invalid then ;
: lf-open-ready ( subst n mode -- outcome )
  lf-open-frames frame-busy? if drop 2drop outcome-invalid exit then
  dup lf-open-job lf-openjob-mode ! lf-open-load ;
: lf-open-marked ( -- outcome ) lf-open-job lf-openjob-start lf-terms store-mark ;
\ The call's stamp in the memo (replace-memo.fs): 0, so that the call
\ keeps nothing beyond itself; a closing with a scope's free variables,
\ the innermost of which is live, is stamped with its identity plus one.
: lf-open-top ( -- fvar ) lf-open-job lf-openjob-count @ 1- lf-open-job lf-open-s ;
: lf-open-stamp-of ( fvar -- stamp )
  dup lf-fvar-live? if lf-term-identity drop 1+ else drop 0 then ;
: lf-open-scope-stamp ( -- stamp ) lf-open-top lf-open-stamp-of ;
: lf-open-stamp ( -- stamp )
  lf-open-job lf-open-mode lf-open-mode-scope = if lf-open-scope-stamp else 0 then ;
: lf-open-begin ( -- ) lf-open-stamp lf-open-memo lf-rmemo-begin ;
: lf-open-end ( node' outcome -- node' outcome ) dup lf-open-memo lf-rmemo-end ;
: lf-open-run ( node subst n mode -- node' outcome )
  lf-open-ready dup ok? 0= if nip no-result exit then drop
  lf-open-marked dup ok? 0= if nip no-result exit then drop
  lf-open-begin 0 lf-open-frames lf-rebuild-run nip lf-open-explain lf-open-end ;
: lf-open-pass ( node subst n mode -- node' outcome )
  over 0= if 2drop drop outcome-ok else lf-open-run then ;
\ instantiate: node with s(k) for its loose bound variable k.
: lf-instantiate ( node subst n -- node' outcome ) lf-open-mode-instantiate lf-open-pass ;
\ instantiate_rev: node with s(n - k - 1) for its loose bound variable k.
: lf-instantiate-rev ( node subst n -- node' outcome ) lf-open-mode-rev lf-open-pass ;
\ instantiate_rev with the free variables of an inference scope, from its
\ outermost (mixed-infer.fs's closing), or only its innermost n when the
\ node needs no more: the result for a node and offset is then that of
\ the whole scope, which its innermost free variable names, and the call
\ keeps its results in the memo for later closings under that scope (see
\ the header). The caller promises this; for any other substitution it
\ must use lf-instantiate-rev. A node closed before under the same scope
\ is given back before any pass runs, for no fuel, as Lean has the term
\ it opened at hand (the memo's lookups cost nothing); not while a pass is
\ in progress, which then refuses the call.
: lf-open-scope-top ( subst n -- fvar ) 1- cells + @ ;
: lf-open-remembered ( node subst n -- node' true | false )
  dup 1 < lf-open-frames frame-busy? or if 2drop drop false exit then
  lf-open-scope-top lf-open-stamp-of ?dup 0= if drop false exit then
  lf-open-memo lf-rmemo-stamp ! 0 lf-open-memo lf-rmemo@ ;
: lf-instantiate-scope ( node subst n -- node' outcome )
  2 pick 2 pick 2 pick lf-open-remembered if >r 2drop drop r> outcome-ok exit then
  lf-open-mode-scope lf-open-pass ;
\ abstract: node with the n free variables at fvars made bound variables.
: lf-abstract ( node fvars n -- node' outcome ) lf-open-mode-abstract lf-open-pass ;

\ mk_pi (local_ctx.cpp 93-125, mk_binding without let variables): the
\ body abstracted over the n free variables, then wrapped, innermost
\ first, in the Pi of each x(i) whose domain is its type abstracted over
\ the i before it. Each step runs on the fuel left by the last; a failed
\ step ends it, leaving what earlier steps made for the caller to discard.
\ The first abstract checks that every x(i) is live, so the later steps
\ may read their entries. A let variable would need a let term:
\ unsupported here (mixed-infer.fs's infer_let makes it). A full term
\ store is full.
: lf-open-at ( fvars i -- fvar ) cells + @ ;
: lf-close-type ( fvars i -- type' outcome )
  2dup lf-open-at dup lf-fvar-let? if drop 2drop -1 outcome-unsupported exit then
  lf-fvar-type -rot lf-abstract ;
: lf-close-pi ( body fvars i -- body' outcome )
  lf-close-type ok-then? 0= if nip no-result exit then
  swap lf-term-pi if outcome-ok else -1 outcome-full then ;
: lf-close-all ( body fvars n -- body' outcome )
  swap >r begin ?dup while
    1- tuck r@ swap lf-close-pi ok-keep? 0= if r> drop exit then swap
  repeat r> drop outcome-ok ;
: lf-mk-pi ( body fvars n -- pi outcome )
  >r tuck r@ lf-abstract ok-then? 0= if nip r> drop no-result exit then
  swap r> lf-close-all ;
