\ Untrusted same-session simultaneous universe substitution for mixed
\ syntax. The current session context must contain every source parameter
\ and every actual parameter. Every source parameter must also occur in the
\ formal list; actuals are not recursively substituted. This is not type or
\ proof checking. Exclude reset, raw mutation and callbacks during a call.
\ Caller arrays must be aligned, readable and disjoint from the stores,
\ contexts and module data. Handles are forgeable. On failure the stores
\ roll back to a scratch mark, but identities never rewind.
\ State: one walk record, lf-mls-walker (the source audit and the fuel left,
\ shared by every pass), one job record, lf-mls-job (the substitution, the
\ mark to roll back to, the count of reached terms and their sorter), the replacement
\ levels, new level pairs, reached terms and their images
\ (lf-mls-actual-cells, lf-mls-arg-pairs, lf-mls-reached-cells,
\ lf-mls-image-cells), and the set of reached terms, a hash table
\ lf-mls-set (lib/htab.fs), all members of the checker context
\ (lib/context.fs). Single-threaded within one context.
\ mixed-signature-audit runs the source audit alone through
\ lf-mls-audit-formals.
\ Cost (plan task 6.5.5; steps S0 and S3 of the compact-store plan): a
\ call's work and room are proportional to the terms it reaches, not to
\ the store's size: the audit keeps the terms it reached in a set of the
\ call, emptied after it, and the build visits only the reached terms,
\ sorted, finding a child's image by binary search, instead of every index
\ up to the root. Nothing is kept per index of the whole store (before
\ step S3, two columns of it). Since step S4 a term whose data word shows
\ no universe parameter is neither audited nor rebuilt (Lean's
\ has_param_univ test, lf-mls-closed?).

require ../lib/lib.fs
require ../lib/bits.fs
require ../lib/slab.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ../lib/sort.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/generation-handles.fs
require ../core/levels.fs
require ../core/scratch-marks.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./level-substitute.fs

begin-structure /lf-mlsrec
  field: lf-mlsrec-formals     \ address of the formal parameter IDs
  field: lf-mlsrec-count       \ number of formals
  /lf-scratch +field lf-mlsrec-mark  \ the stores to roll back to
  field: lf-mlsrec-reached     \ terms it reached (lf-mls-reached-cells)
  /sorter +field lf-mlsrec-sorter  \ their sort (lib/sort.fs)
end-structure
lf-walk-room context-walk: lf-mls-walker
/lf-mlsrec context-record: lf-mls-job
\ The replacement levels, a rebuilt reference's new level pairs, the
\ terms the audit reached, each listed once, and their images, in the
\ same order: growable arrays with no fixed limit (plan task 6.2.0); one
\ the heap cannot grow is full.
1 cells context-slab: lf-mls-actual-cells
2 cells context-slab: lf-mls-arg-pairs
1 cells context-slab: lf-mls-reached-cells
1 cells context-slab: lf-mls-image-cells
\ The set of the terms an audit reached: entry n is the n-th listed term,
\ found by its index (a hash is only a hint, an entry is equal only when
\ its term is the one sought).
/htab context-record: lf-mls-set
: lf-mls-node ( i -- node ) lf-mls-reached-cells slab-at @ ;
: lf-mls-set-rehash ( n htab -- h ) drop lf-mls-node hash-fmix ;
: lf-mls-set-same ( n key htab -- flag ) drop swap lf-mls-node = ;
create lf-mls-set-hooks /htab-hooks allot
' lf-mls-set-rehash ' lf-mls-set-same lf-mls-set-hooks htab-hooks!
: lf-mls-set-make ( -- ) 4 lf-mls-set-hooks lf-mls-set htab-init drop ;
' lf-mls-set-make context-setup
: lf-mls-sorter ( -- sorter ) lf-mls-job lf-mlsrec-sorter ;
:noname ( -- ) ['] sort-signed lf-mls-sorter sorter-cells drop ; context-setup
:noname ( -- ) lf-mls-set htab-free ; context-teardown

\ Fuel left after a call; the signature probe continues with it, and tests
\ read it. Every helper this module calls reports only ok, invalid,
\ exhausted or full, and so does every word here.
: lf-mls-fuel ( -- addr ) lf-mls-walker walk-fuel ;
: lf-mls-formals ( -- addr ) lf-mls-job lf-mlsrec-formals ;
: lf-mls-count ( -- addr ) lf-mls-job lf-mlsrec-count ;
\ The arrays' first units, valid while they do not grow (never during a
\ pass, which reserves first).
: lf-mls-actuals ( -- addr ) 0 lf-mls-actual-cells slab-at ;
: lf-mls-args ( -- addr ) 0 lf-mls-arg-pairs slab-at ;

\ The rollback point: a scratch mark of the term, level and reference
\ stores (core/scratch-marks.fs), taken before the replacements are read
\ and given back after a failed build: ok, or invalid. LIFO: nothing this
\ module calls between the two takes a mark of its own except level
\ substitution, whose level mark is younger and given back first, and a
\ substitution never runs inside another (its walk is busy: refused
\ before the mark is taken). A refused rollback makes the outcome
\ invalid.
: lf-mls-scratch ( -- scratch ) lf-mls-job lf-mlsrec-mark ;
: lf-mls-snapshot ( -- outcome ) lf-mls-scratch lf-scratch-mark ;
: lf-mls-rollback ( status -- status )
  lf-mls-scratch lf-scratch-rollback lf-scratch-settled ;

\ Level passes of level-substitute, charging this module's fuel. The full
\ substitution revalidates every actual on each call, as metered work.
: lf-mls-reclaim ( -- ) lf-lsubst-fuel @ lf-mls-fuel ! ;
: lf-mls-substitution ( -- formals actuals count )
  lf-mls-formals @ lf-mls-actuals lf-mls-count @ ;
: lf-mls-inputs ( -- outcome )
  lf-mls-substitution lf-lsubst-use lf-mls-walker lf-lsubst-inputs ;
: lf-mls-level ( root -- result outcome )
  lf-mls-substitution lf-mls-fuel @ lf-lsubst lf-mls-reclaim
  dup ok? 0= if 0 swap then ;

\ The audit marks every reachable term and checks every source level
\ against the formals before anything is allocated: a symbolic Sort's level
\ and each level of a constant's reference. The whole graph was validated
\ first, so children are earlier nodes. A term is marked as reached by
\ listing it and entering it in the set, the first time the audit
\ reaches it; then its levels are checked and its children pushed. Every
\ occurrence costs a unit of fuel, but a term reached again by another
\ path is skipped: its checks read only the term, never the path or the
\ binders around it, and were made at its first visit. So a shared term
\ costs its nodes and edges, not its paths, as in Lean's
\ instantiate_lparams (instantiate.cpp 236-253), whose replace caches a
\ shared node's result per binder offset (replace_fn.cpp 16-40); the
\ offset changes nothing here, so one visit per node is enough.
: lf-mls-site ( -- site ) c" mixed-level-substitute lf-mixed-level-substitute" ;
: lf-mls-reached ( -- addr ) lf-mls-job lf-mlsrec-reached ;
: lf-mls-find ( index -- n true | slot false ) dup hash-fmix lf-mls-set htab-find ;
: lf-mls-reached? ( index -- flag ) lf-mls-find nip ;
\ A list or set the heap cannot grow is full, recorded with its count and
\ room.
: lf-mls-crowded ( n -- n )
  dup lf-mls-reached-cells slab-capacity lf-mls-site
  lf-diag-work-stack-full lf-diag-note ;
: lf-mls-list ( index -- outcome )
  lf-mls-reached @ lf-mls-reached-cells lf-cells-add
  dup outcome-full = if swap lf-mls-crowded swap then swap lf-mls-reached ! ;
: lf-mls-set-full ( -- outcome )
  lf-mls-reached @ lf-mls-set htab-slots lf-mls-site lf-diag-work-stack-full
  lf-diag-note outcome-full ;
\ Marking a term not reached before: listed as entry n, entered at the
\ set's empty slot that the find gave (the list's growth leaves the set
\ alone).
: lf-mls-enter ( slot n outcome -- outcome )
  dup ok? if drop swap lf-mls-set htab-put outcome-ok else nip nip then ;
: lf-mls-mark ( index -- outcome )
  lf-mls-set htab-ready ok? 0= if drop lf-mls-set-full exit then
  dup lf-mls-find if 2drop outcome-ok exit then
  lf-mls-reached @ rot lf-mls-list lf-mls-enter ;
: lf-mls-sources ( addr count walk -- outcome )
  swap 0 ?do over i lf-cref-pair@ drop over lf-lsubst-walk-source dup ok? 0=
    if nip nip unloop exit then drop loop 2drop outcome-ok ;
: lf-mls-reference ( first second walk -- outcome )
  >r lf-cterm-pair lf-cref-levels if r> lf-mls-sources else r> drop outcome-invalid then ;
: lf-mls-refused ( first second walk tag outcome -- outcome ) >r 2drop 2drop r> ;
\ Lean's has_param_univ test (instantiate.cpp 232-237, the skip at line
\ 236; compact-store plan step S4): a term without universe parameters
\ is its own image, so the
\ audit neither visits nor lists it (it costs no unit as a child, one as
\ the root) and the build gives it back unchanged (lf-mls-image@). Its
\ data word tells (core/terms.fs: the parameter bit, from its levels when
\ they were made); a term without a data word is walked as before. Its
\ levels need no check against the formals (none is a parameter); their
\ shape, and the rest of its graph, the graph audit (lf-cterm-check)
\ checked before.
: lf-mls-closed? ( node -- flag ) lf-term-data@ if lf-data-params? 0= else false then ;
: lf-mls-children ( first second walk -- outcome )
  ['] lf-mls-closed? walk-children-unless ;
\ The first visit of a term: mark it, check it, push its children.
: lf-mls-first ( first second walk tag -- outcome )
  over walk-node @ lf-mls-mark dup ok? 0= if lf-mls-refused exit then drop
  dup lf-term-binary-tag? if drop lf-mls-children exit then
  case lf-tag-symbolic-sort of nip lf-lsubst-walk-source endof
    lf-tag-constant of lf-mls-reference endof
    lf-tag-bvar of drop 2drop outcome-ok endof
    lf-tag-proj of drop 2drop outcome-ok endof
    lf-tag-lit of drop 2drop outcome-ok endof
    lf-tag-str of drop 2drop outcome-ok endof
    walk-bad-tag endcase ;
: lf-mls-again? ( walk -- flag ) walk-node @ lf-mls-reached? ;
: lf-mls-skip? ( walk -- flag ) walk-node @ dup lf-mls-reached? swap lf-mls-closed? or ;
: lf-mls-dispatch ( first second walk tag -- outcome )
  over lf-mls-skip? if lf-walk-skip else lf-mls-first then ;
: lf-mls-visit ( walk -- outcome ) ['] lf-mls-dispatch lf-term-visit ;
\ A new audit starts with an empty set and lists nothing yet; it empties
\ the set when it ends, each entry taken out (Algorithm R) or, when the
\ set has few slots for its entries, the whole table cleared, so that an
\ audit costs the terms it reaches. A set an audit left with entries (a
\ THROW out of it) is cleared when the next one starts; a set without a
\ table (no heap at its making) is made again, or the audit is full.
: lf-mls-set-ready ( -- outcome )
  lf-mls-set htab-live? 0= if lf-mls-set-make then
  lf-mls-set htab-live? 0= if lf-mls-set-full exit then
  lf-mls-set htab-count if lf-mls-set htab-clear then outcome-ok ;
: lf-mls-unseen ( -- outcome ) 0 lf-mls-reached ! lf-mls-set-ready ;
: lf-mls-unlist ( i -- ) dup lf-mls-node hash-fmix lf-mls-set htab-remove drop ;
: lf-mls-forget ( -- )
  lf-mls-set htab-slots lf-mls-reached @ 4 * <
  if lf-mls-set htab-clear exit then
  lf-mls-reached @ 0 ?do i lf-mls-unlist loop ;
\ The formals and count are those last given to lf-lsubst-use.
: lf-mls-walk ( root -- status )
  ['] lf-mls-visit lf-mls-walker lf-mls-site lf-diag-run ;
: lf-mls-audit-from ( root -- status )
  lf-mls-unseen ok-then? if lf-mls-walk lf-mls-forget then ;

\ The source audit alone, as mixed-signature-audit runs it on a candidate
\ signature: every term reachable from root and every source level against
\ count formal IDs at formals, with the given fuel; gives the fuel left.
\ The caller has validated root's graph (lf-cterm-check). An audit reads
\ no actuals, so none are given. Nothing is allocated. Negative fuel or a
\ negative count is invalid and spends nothing.
: lf-mls-audit-input? ( count fuel -- flag ) 0< 0= swap 0< 0= and ;
: lf-mls-audit-formals ( root formals count fuel -- fuel' status )
  2dup lf-mls-audit-input? 0= if nip nip nip outcome-invalid exit then
  lf-mls-fuel ! 0 swap lf-lsubst-use lf-mls-audit-from lf-mls-fuel @ swap ;

\ Building, in index order, so children come before parents: each reached
\ term gets an image, the term itself when nothing under it changes. Every
\ input of a constructor here is live, so a failed allocation means a full
\ store or a spent serial: full.
: lf-mls-made ( index identity true | false -- index outcome )
  if drop outcome-ok else 0 outcome-full then ;
: lf-mls-failed ( x y outcome -- 0 outcome ) nip nip 0 swap ;
\ A symbolic Sort over its substituted level.
: lf-mls-new-sort ( level -- index outcome )
  dup lf-level-identity
  if lf-hterm-sort lf-mls-made else drop 0 outcome-invalid then ;
: lf-mls-sort ( node level -- index outcome )
  dup lf-mls-level ok-then? 0= if lf-mls-failed exit then
  tuck = if drop outcome-ok else nip lf-mls-new-sort then ;
\ A constant over a new reference whose levels are the substituted ones in
\ lf-mls-args; the levels are unchanged exactly when the pairs are equal,
\ since a live level's identity does not change during a call.
: lf-mls-pair ( level -- index identity outcome )
  lf-mls-level ok-then? 0= if 0 0 rot exit then
  dup lf-level-identity if outcome-ok else 0 outcome-invalid then ;
: lf-mls-arg! ( index identity position -- )
  >r swap lf-mls-args r> lf-cref-pair 2! ;
: lf-mls-arg ( addr position -- outcome )
  tuck lf-cref-pair@ drop lf-mls-pair ok-then?
  if rot lf-mls-arg! outcome-ok else nip nip then ;
: lf-mls-arg-at ( addr i -- addr outcome ) over swap lf-mls-arg ;
: lf-mls-args! ( addr count -- outcome ) ['] lf-mls-arg-at ok-each nip ;
: lf-mls-changed? ( addr count -- flag ) 2* lf-mls-args swap cells= 0= ;
: lf-mls-arg-room ( addr count -- addr count outcome )
  dup lf-mls-arg-pairs slab-hold ;
: lf-mls-substituted ( slot -- changed outcome )
  lf-cref-pairs lf-mls-arg-room ok-then? 0= if nip false swap exit then
  2dup lf-mls-args! dup ok?
  if drop lf-mls-changed? outcome-ok else nip nip false swap then ;
: lf-mls-new-constant ( slot -- index outcome )
  dup lf-cref-name@ rot lf-crec-arity @ >r lf-mls-args r> lf-cref-new
  if lf-cterm-new lf-mls-made else 0 outcome-full then ;
: lf-mls-rebuild ( node slot -- index outcome )
  dup lf-mls-substituted ok-then? 0= if lf-mls-failed exit then
  if nip lf-mls-new-constant else drop outcome-ok then ;
: lf-mls-constant ( node first second -- index outcome )
  lf-cterm-pair lf-cref-record if lf-mls-rebuild else drop 0 outcome-invalid then ;
\ An application, lambda or Pi over the images of its children. A child
\ of a reached term is reached, so it is in the sorted list: found by
\ binary search, its image at the same place.
: lf-mls-image-cell ( i -- addr ) lf-mls-image-cells slab-at ;
: lf-mls-below? ( node i -- node flag ) lf-mls-node over < ;
: lf-mls-search ( node lo hi -- i ) ['] lf-mls-below? lower-bound nip ;
\ A reached term's image, or the term itself when the audit did not list
\ it (no universe parameter, lf-mls-closed?).
: lf-mls-listed? ( node i -- flag )
  dup lf-mls-reached @ < if lf-mls-node = else 2drop false then ;
: lf-mls-image@ ( node -- image )
  dup 0 lf-mls-reached @ lf-mls-search 2dup lf-mls-listed?
  if nip lf-mls-image-cell @ else drop then ;
: lf-mls-images ( first second -- first' second' )
  lf-mls-image@ swap lf-mls-image@ swap ;
: lf-mls-kept? ( first second -- flag ) 2dup lf-mls-images rot = >r = r> and ;
: lf-mls-binary ( node first second tag -- index outcome )
  >r 2dup lf-mls-kept? if 2drop r> drop outcome-ok exit then
  rot drop lf-mls-images r> lf-term-binary
  if outcome-ok else 0 outcome-full then ;
: lf-mls-image-of ( node first second tag -- index outcome )
  case lf-tag-symbolic-sort of drop lf-mls-sort endof
    lf-tag-constant of lf-mls-constant endof
    lf-tag-bvar of 2drop outcome-ok endof  lf-tag-proj of 2drop outcome-ok endof
    lf-tag-lit of 2drop outcome-ok endof
    lf-tag-str of 2drop outcome-ok endof
    dup >r lf-mls-binary r> endcase ;
: lf-mls-image ( node -- index outcome )
  dup lf-term-read if rot lf-mls-image-of else drop 0 outcome-invalid then ;
: lf-mls-build-at ( i -- outcome )
  dup lf-mls-node lf-mls-image ok-then?
  if swap lf-mls-image-cell ! outcome-ok else nip then ;
\ The reached terms, sorted: the order of every index up to the root,
\ skipping the terms not reached, at a cost of the terms reached. Room
\ for their images first (none is full). The audit listed each term once,
\ so the indices are distinct and any sort gives the one ascending order;
\ lib/sort.fs sorts up to 32 of them by insertion, more by a merge whose
\ scratch is the images' cells, not written yet (so never full).
: lf-mls-sort-buffer! ( -- )
  0 lf-mls-image-cells slab-at lf-mls-reached @ cells lf-mls-sorter sorter-buffer! ;
: lf-mls-sorted ( -- outcome )
  lf-mls-sort-buffer! 0 lf-mls-reached-cells slab-at lf-mls-reached @ lf-mls-sorter
  sort-records ;
: lf-mls-image-room ( -- outcome )
  lf-mls-reached @ lf-mls-image-cells slab-hold dup outcome-full = if
    lf-mls-reached @ lf-mls-image-cells slab-capacity lf-mls-site
    lf-diag-work-stack-full lf-diag-note then ;
: lf-mls-ready ( -- outcome ) lf-mls-image-room dup ok? if drop lf-mls-sorted then ;
: lf-mls-build-all ( -- outcome ) lf-mls-reached @ ['] lf-mls-build-at ok-each ;
: lf-mls-build ( -- outcome ) lf-mls-ready ['] lf-mls-build-all ok-and ;

\ The passes in order: the root handle and stores, the replacements (live,
\ and in level scope), the whole graph (lf-cterm-check), the source audit,
\ then the build. A failed build rolls the stores back to the snapshot.
: lf-mls-serials? ( -- flag ) lf-term-serial @ 0< 0= lf-level-serial @ 0< 0= and ;
: lf-mls-ready? ( index id -- flag )
  lf-hterm-valid? lf-cref-state-valid? and lf-mls-serials? and ;
: lf-mls-actual ( pairs position -- flag )
  tuck lf-cref-pair@ 2dup lf-hlevel-valid?
  if drop swap cells lf-mls-actuals + ! true else 2drop drop false then ;
: lf-mls-actual-at ( pairs i -- pairs flag ) over swap lf-mls-actual ;
: lf-mls-actuals! ( pairs count -- flag ) ['] lf-mls-actual-at all? nip ;
: lf-mls-graph ( index id -- outcome )
  lf-mls-fuel @ lf-cterm-check lf-cterm-fuel @ lf-mls-fuel ! ;
: lf-mls-checks ( index id -- index id outcome )
  lf-mls-inputs dup ok? if drop 2dup lf-mls-graph then
  dup ok? if drop over lf-mls-audit-from then ;
: lf-mls-finish ( index -- index id 0 | status )
  lf-mls-image@ dup lf-term-identity
  if outcome-ok else drop outcome-invalid lf-mls-rollback then ;
: lf-mls-apply ( index -- index id 0 | status )
  lf-mls-build dup ok? if drop lf-mls-finish else nip lf-mls-rollback then ;
: lf-mls-run ( index id -- index id 0 | status )
  lf-mls-checks dup ok? if 2drop lf-mls-apply else nip nip then ;
: lf-mls-use ( formals pairs count -- pairs count )
  dup lf-mls-count ! rot lf-mls-formals ! ;
: lf-mls-prepare ( index id pairs count -- index id outcome )
  2over lf-mls-ready? 0= if 2drop outcome-invalid exit then
  dup lf-mls-actual-cells slab-hold ok-then? 0= if nip exit then
  lf-mls-snapshot ok-then2? if lf-mls-actuals! flag>outcome then ;

\ Substitute count actual (index identity) level pairs for count formal IDs
\ in a live term. All syntax, source levels and replacements are audited
\ before allocation.
\ Audit and substitution share fuel; each term/level occurrence consumes fuel
\ (one reached before only its unit), and so does each repeated replacement
\ validation. Bounded list scans, identity
\ checks and topological staging are additional bounded work. Status is invalid
\ for malformed, stale or out-of-scope input, exhausted when the fuel runs
\ out, and full for a full work stack or store or a spent identity serial.
: lf-mls-pass
  ( index id formals actual-pairs count fuel -- index id 0 | status )
  lf-mls-walker walk-budget 0= if 2drop 2drop drop outcome-invalid exit then
  dup 0< if 2drop 2drop drop outcome-invalid exit then
  lf-mls-use lf-mls-prepare dup ok? if drop lf-mls-run else nip nip then ;
\ The derivation log (ADR 0013): with it on, the substitution is one
\ instantiate-levels step of the type with count levels; both paths run
\ the same pass.
: lf-mls-logged ( index id formals actual-pairs count fuel -- index id 0 | status )
  5 pick 2 pick lf-rule-instantiate-levels lf-log-open lf-mls-pass lf-log-close-maybe ;
: lf-mixed-level-substitute
  ( index id formals actual-pairs count fuel -- index id 0 | status )
  lf-log? if lf-mls-logged else lf-mls-pass then ;
\ A successful substitution's result with the fuel it left (for the
\ callers that report it: env-signature.fs, mixed-signature-probe.fs).
: lf-mls-left ( root identity 0 | status -- root identity fuel' 0 | status )
  dup ok? if drop lf-mls-fuel @ outcome-ok then ;
