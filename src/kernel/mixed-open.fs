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
\ The passes walk a term on the host stacks with a frames record
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
\ in Lean. Lean skips the subterms whose cached loose-bound-variable range
\ or free-variable flag shows them unchanged (instantiate.cpp 103,
\ abstract.cpp 19); this store keeps no such data, so the passes visit
\ them, keep them and pay fuel for them (ADR 0014 Q12 plans the data and
\ a memo). A new bound variable reuses the live leaf of its index that a
\ pass made before, if any: leaves never change, so this shares an equal
\ term (it saves room in a small term store).
\ Each visit costs one unit of fuel and one frame (at most lf-depth-limit
\ nested): no fuel left is exhausted, no frame full. Only nodes older than
\ the pass are read, children before parents; a bound variable must be a
\ well-formed leaf and a free variable live, else the pass is invalid. Any
\ failure discards the nodes the pass made. n is at most lf-depth-limit
\ (more is full; negative invalid), and each of the n a live node.
\
\ Words: lf-instantiate, lf-instantiate-rev, lf-abstract ( node subst n --
\ node' outcome ) and lf-mk-pi ( body fvars n -- pi outcome ), each
\ running on the fuel in lf-open-fuel and leaving there what is left;
\ subst and fvars are the address of n cells. Outcomes: ok, invalid,
\ exhausted, full, and unsupported from lf-mk-pi for a let variable (no
\ let terms before plan task 4.2.3).
\ Example: with x the free variable of A (lf-lctx-local) in a cell at
\ addr, 100 lf-open-fuel !  body addr 1 lf-instantiate-rev gives the body
\ with bound variable 0 replaced by x, and that addr 1 lf-mk-pi gives
\ the Pi over x : A of the body back.
\ Untrusted; [kernel] code, not yet through the review gate.
\ State: one job record, lf-open-job (fields lf-openjob-*): the pass's
\ frames (fuel, nesting, the offset as context), its mode, the term count
\ before it, its copy of the n terms and the bound-variable leaves it
\ made; a member of the checker context (lib/context.fs), whose frames a
\ set-up word prepares in every context. Single-threaded within one
\ context; a pass refuses to start inside another (invalid).

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/local-context.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./mixed-rebuild.fs

0 constant lf-open-mode-instantiate
1 constant lf-open-mode-rev
2 constant lf-open-mode-abstract
lf-depth-limit 2* constant lf-open-leaves   \ bound-variable indices whose leaf is kept

\ The frames come first, so the visitor finds the job record at the
\ address of the frames it is given (checked here), as in mixed-shift.fs.
begin-structure /lf-openjob
  /frames +field lf-openjob-frames     \ fuel, nesting, the offset as context
  field: lf-openjob-mode               \ one of the lf-open-mode-* constants
  field: lf-openjob-start              \ term count before the pass
  field: lf-openjob-count              \ n
  lf-depth-limit cells +field lf-openjob-subst      \ s0 .. s(n-1)
  lf-open-leaves 2* cells +field lf-openjob-leaves  \ per index: node, identity
end-structure
0 lf-openjob-frames 0<> [if] .( mixed-open.fs: frames come first) cr abort [then]
/lf-openjob context-record: lf-open-job

: lf-open-frames ( -- frames ) lf-open-job lf-openjob-frames ;
\ The fuel of the next pass, and what the last one left.
: lf-open-fuel ( -- addr ) lf-open-frames frame-fuel ;

\ Reading the job from the frames of the visit.
: lf-open-n ( frames -- n ) lf-openjob-count @ ;
: lf-open-s ( i frames -- node ) lf-openjob-subst swap cells + @ ;
: lf-open-mode ( frames -- mode ) lf-openjob-mode @ ;
: lf-open-abstract? ( frames -- flag ) lf-open-mode lf-open-mode-abstract = ;

\ Only nodes older than the pass, with children before them, are read.
: lf-open-readable? ( node frames -- flag )
  lf-openjob-start @ over 0 rot within swap lf-term-valid? and ;
: lf-open-below? ( child node -- flag ) 0 swap within ;
: lf-open-children? ( node -- flag )
  dup lf-term-first@ over lf-open-below?
  swap dup lf-term-second@ swap lf-open-below? and ;

\ update_app and update_binding (Lean's expr.cpp): the node itself when
\ both children came back unchanged, otherwise a new node of its tag.
: lf-open-update ( r1 node r2 -- result outcome )
  >r 2dup lf-term-first@ = over lf-term-second@ r@ = and
  if nip r> drop outcome-ok else r> lf-rebuild-build then ;
\ A binary node: the first child at this offset, the second one binder
\ deeper for a lambda or Pi (mixed-rebuild.fs's limits apply).
: lf-open-join ( r1 node frames -- result outcome )
  >r dup lf-term-second@ over lf-rebuild-descend r> swap execute
  ok-keep2? if lf-open-update then ;
: lf-open-binary ( node frames -- result outcome )
  over lf-open-children? 0= if lf-rebuild-bad exit then
  2dup lf-rebuild-stuck? if 2drop lf-rebuild-deep exit then
  over lf-term-first@ over frame-call ok-keep2? if -rot lf-open-join then ;

\ A bound-variable leaf of index i: the live one an earlier pass made for
\ i, else a new one, then kept for i; no room is full.
: lf-open-slot ( i -- addr ) 2* cells lf-open-job lf-openjob-leaves + ;
: lf-open-kept? ( addr -- node true | false )
  dup @ dup lf-term-identity if rot cell+ @ = dup 0= if nip then else 2drop false then ;
: lf-open-remember ( node i -- node )
  over dup lf-term-identity drop rot lf-open-slot tuck cell+ ! ! ;
: lf-open-leaf-at ( i -- node outcome )
  dup 0 lf-open-leaves within 0= if lf-term-bvar lf-rebuild-allocated exit then
  dup lf-open-slot lf-open-kept? if nip outcome-ok exit then
  dup lf-term-bvar if swap lf-open-remember outcome-ok else drop lf-rebuild-full then ;

\ instantiate and instantiate_rev on bound variable i at offset d
\ (instantiate.cpp 22-33, 103-114): kept below d; for k = i - d < n the
\ term s(k), or s(n - k - 1) reversed; else bound variable i - n.
: lf-open-rev? ( frames -- flag ) lf-open-mode lf-open-mode-rev = ;
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
    lf-tag-constant of lf-rebuild-keep endof
    lf-tag-symbolic-sort of lf-rebuild-keep endof
    >r lf-rebuild-bad r> endcase ;
: lf-open-visit ( node frames -- result outcome )
  2dup lf-open-readable? lf-rebuild-tag
  dup lf-term-binary-tag? if drop lf-open-binary else lf-open-leaf then ;
\ The frames and their visitor, set up once in every context.
: lf-open-setup ( -- ) lf-depth-limit ['] lf-open-visit lf-open-frames frame-init ;
' lf-open-setup context-setup
\ Recovery after a THROW out of a pass (which leaves the record busy, so
\ that every later pass refuses as invalid): the record made idle again;
\ lf-mixed-rebuild-reset (mixed-beta.fs) resets all four rebuilding passes.
: lf-open-reset ( -- ) lf-open-frames frame-reset ;

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
  dup 0< if drop outcome-invalid else lf-depth-limit > 0= room>outcome then ;
: lf-open-copy ( subst n -- )
  dup lf-open-job lf-openjob-count ! cells lf-open-job lf-openjob-subst swap move ;
: lf-open-load ( subst n mode -- outcome )
  over lf-open-count dup ok? 0= if nip nip nip exit then drop
  lf-open-test >r 2dup r> lf-open-all? if lf-open-copy outcome-ok
  else 2drop outcome-invalid then ;
: lf-open-ready ( subst n mode -- outcome )
  lf-open-frames frame-busy? if drop 2drop outcome-invalid exit then
  dup lf-open-job lf-openjob-mode ! lf-open-load ;
: lf-open-run ( node subst n mode -- node' outcome )
  lf-open-ready dup ok? 0= if nip no-result exit then drop
  lf-term-count @ lf-open-job lf-openjob-start !
  0 lf-open-frames lf-rebuild-run nip lf-open-explain ;
: lf-open-pass ( node subst n mode -- node' outcome )
  over 0= if 2drop drop outcome-ok else lf-open-run then ;
\ instantiate: node with s(k) for its loose bound variable k.
: lf-instantiate ( node subst n -- node' outcome ) lf-open-mode-instantiate lf-open-pass ;
\ instantiate_rev: node with s(n - k - 1) for its loose bound variable k.
: lf-instantiate-rev ( node subst n -- node' outcome ) lf-open-mode-rev lf-open-pass ;
\ abstract: node with the n free variables at fvars made bound variables.
: lf-abstract ( node fvars n -- node' outcome ) lf-open-mode-abstract lf-open-pass ;

\ mk_pi (local_ctx.cpp 93-125, mk_binding without let variables): the
\ body abstracted over the n free variables, then wrapped, innermost
\ first, in the Pi of each x(i) whose domain is its type abstracted over
\ the i before it. Each step runs on the fuel left by the last; a failed
\ step ends it, leaving what earlier steps made for the caller to discard.
\ The first abstract checks that every x(i) is live, so the later steps
\ may read their entries. A let variable would need a let term:
\ unsupported. A full term store is full.
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
