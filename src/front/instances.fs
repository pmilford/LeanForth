\ The instance table (plan FE1e3; docs/design/FE1E_APPLICATIONS.md §3.2,
\ §3.3 and §4; S1_INTERFACE.md §9): Lean 4.35.0's global instance index
\ (Lean/Meta/Instances.lean, a DiscrTree) rebuilt from the elaboration
\ data, its getUnify (DiscrTree/Main.lean:567), getInstances
\ (SynthInstance.lean:202), isClass?'s quick test (Meta/Basic.lean:1384)
\ and the check of each instance against its type (§4).
\ - lf-inst-telescope ( type -- body outcome ): forallMetaTelescopeReducing
\   (Basic.lean): a new natural metavariable for each binder, whnf where
\   no pi is left (a pi it makes is entered, else the type as it was).
\ - lf-class? ( type -- class true outcome | false outcome ): isClass?
\   through isClassQuick?: the class (its declaration in the data's stage)
\   at the head past the pis; false for a head that is no class; where
\   Lean would go on to isClassExpensive? (a definition the transparency
\   may unfold, a let, a projection, a lambda head) unsupported (plan S2,
\   with delta).
\ - lf-inst-unify ( type -- addr n outcome ): getUnify at reducible
\   transparency: the values whose keys may unify with type, in Lean's
\   order, as cells: an instance i (0 or more) or a left-out instance j
\   as j invert (below 0: lf-inst-left-out?). A root's tree is built at
\   its first query, its values inserted in rank order so that every
\   child list is in Lean's stored order (§3.2), after each instance of
\   the root is checked (§4 steps 1-2, at default transparency in a new
\   depth): its class and its keys recomputed (front/discr-keys.fs) must
\   equal the record's, else invalid and the data refused (error 112 or
\   113); a check that cannot finish marks the instance unverified, which
\   answers unsupported only when a search tries it (S1 §9). A star root
\   key (a bare metavariable goal) is unsupported: never an instance
\   problem.
\ - lf-inst-candidates ( type -- addr n outcome ): getInstances: the goal
\   past its pis must be a class application (else invalid, error 110,
\   "type class instance expected"); getUnify; stably sorted by priority,
\   ascending; erased values dropped. A search tries them from the last.
\   Unsupported: a goal that is or becomes a pi and a local instance of
\   the class (FE1E §2.7).
\ - lf-inst-priority ( v -- p ), lf-inst-left-out? ( v -- flag ),
\   lf-inst-verified? ( i -- flag ) (false before its root's check),
\   lf-inst-check ( i -- outcome ) (§4 steps 1-2 alone: ok, invalid on a
\   difference, else why it could not finish), lf-inst-checked# and
\   lf-inst-unverified# ( -- n ): the checks done and those unverified.
\ - lf-default-instances ( class -- addr n outcome ): getDefaultInstances
\   (Instances.lean:430): the class's default-instance records (elab-default@)
\   in rank order.
\ - lf-inst-error ( -- code ): the last error code; lf-inst-reset ( -- )
\   forgets the trees and checks (after a new read of the data).
\ Outcomes: ok; invalid as above; lf-meta-stuck from a query key (Meta
\ layer only); unsupported; exhausted; full when a slab cannot grow.
\ Untrusted. State: the record it (the last error, the counts, the query
\ step) and the slabs it-roots (root key, node), it-nodes (key, first
\ child, next sibling, first value, last value), it-vals (value, next),
\ it-status (per instance: unchecked, ok or unverified), it-ranked (a
\ root's values by rank), it-stack (the walk's frames: skip, todo, node)
\ and it-out (a query's values), in the checker context (ADR 0009).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./discr-keys.fs
require ./lctx-views.fs

110 constant lf-e-not-class   112 constant lf-e-inst-class   113 constant lf-e-inst-keys
114 constant lf-e-inst-wide
0 constant it-unchecked   1 constant it-ok   2 constant it-unverified
begin-structure /it
  field: it-error      \ the last error code, or 0
  field: it-checked    \ instances checked
  field: it-unverified-n \ of which unverified
  field: it-root       \ the root node being built
  field: it-k          \ a query step: the subterm's key
  field: it-args       \ the todo list with its arguments
  field: it-rest       \ the todo list without them
  field: it-dk   field: it-dn   \ a check: the recorded keys
  field: it-ck   field: it-cn   \ and the recomputed
  field: it-i    field: it-j    \ the walk's places in each
  field: it-wide       \ true once a recorded star covered a term
end-structure
/it context-record: it
2 cells context-slab: it-roots
5 cells context-slab: it-nodes
2 cells context-slab: it-vals
1 cells context-slab: it-status
1 cells context-slab: it-ranked
3 cells context-slab: it-stack
1 cells context-slab: it-out

: lf-inst-reset ( -- )
  it-roots slab-clear it-nodes slab-clear it-vals slab-clear it-status slab-clear
  0 it it-checked ! 0 it it-unverified-n ! 0 it it-error ! ;
: lf-inst-error ( -- code ) it it-error @ ;
: it-fail ( code -- outcome ) it it-error ! outcome-invalid ;
: lf-inst-checked# ( -- n ) it it-checked @ ;
: lf-inst-unverified# ( -- n ) it it-unverified-n @ ;
: lf-inst-left-out? ( v -- flag ) 0< ;
: lf-inst-priority ( v -- p )
  dup lf-inst-left-out? if invert elab-left-out@ 2drop else elab-instance@ nip nip then ;
: it-keys ( v -- k n ) dup lf-inst-left-out? if invert elab-left-out-keys else
  elab-instance-keys then ;
: it-rank ( v -- rank )
  dup lf-inst-left-out? if invert elab-left-out@ drop nip else elab-instance-rank then ;
: it-erased? ( v -- flag )
  dup lf-inst-left-out? if invert elab-left-out@ nip nip elab-erased = else drop false
  then ;

\ ---- forallMetaTelescopeReducing.
: it-pi? ( e -- flag ) lf-term-tag@ lf-tag-pi = ;
: it-enter ( pi -- body outcome )
  dup lf-term-first@ mv-natural lf-mvar-new ok-then? 0= if nip no-result exit then
  swap lf-term-second@ swap lf-meta-instantiate1 ;
: it-whnf-pi ( e -- e' more? outcome )
  dup lf-meta-whnf ok-then? 0= if nip -1 false rot exit then
  dup it-pi? if nip true outcome-ok else drop false outcome-ok then ;
: it-step ( e -- e' more? outcome ) dup it-pi? if it-enter true swap else it-whnf-pi
  then ;
: lf-inst-telescope ( type -- body outcome )
  begin it-step ok-then? 0= if nip no-result exit then while repeat outcome-ok ;

\ ---- isClass? by isClassQuick? (an undefined answer is unsupported).
: it-defn-temp? ( d -- flag )   \ getConstTemp? gives a definition
  dup lf-menv-kind lf-kind-definition <> if drop false exit then
  lf-defeq-mode dup lf-tr-all = swap lf-tr-default = or if drop true exit then
  lf-menv-status drop elab-reducible = ;
: it-not-class ( const -- false outcome )
  lf-meta-const-decl 0= if false outcome-invalid exit then
  it-defn-temp? if false outcome-unsupported else false outcome-ok then ;
: it-class-const ( const -- class true outcome | false outcome )
  dup dk-name elab-decl-of 0= if drop false outcome-invalid exit then
  dup elab-class-of if drop nip true outcome-ok else drop it-not-class then ;
: it-assigned-head ( mvar -- head true | false )
  lf-mvar-value if lf-meta-head true else false then ;
: it-head-const ( head -- const true | false )
  dup lf-term-tag@ lf-tag-constant = if true else drop false then ;
\ An application's head: a constant, an assigned metavariable's value's
\ constant head (else undefined), a lambda undefined; anything else none.
: it-mvar-head ( mvar -- class true outcome | false outcome )
  it-assigned-head 0= if false outcome-ok exit then
  it-head-const if it-class-const else false outcome-unsupported then ;
: it-quick-head ( head -- class true outcome | false outcome )
  dup lf-term-tag@ case
    lf-tag-constant of it-class-const endof   lf-tag-mvar of it-mvar-head endof
    lf-tag-lam of drop false outcome-unsupported endof   >r drop false outcome-ok r>
    endcase ;
: it-quick-none? ( tag -- flag )
  dup lf-tag-bvar = over lf-tag-lit = or over lf-tag-fvar = or over lf-tag-sort = or
  swap lf-tag-lam = or ;
: it-quick-undef? ( tag -- flag )
  dup lf-tag-let = over lf-tag-let-nondep = or swap lf-tag-projection = or ;
: it-past-pis ( e -- e' ) begin dup it-pi? while lf-term-second@ repeat ;
: lf-class? ( type -- class true outcome | false outcome )
  it-past-pis dup lf-term-tag@ dup it-quick-none? if 2drop false outcome-ok exit then
  it-quick-undef? if drop false outcome-unsupported exit then lf-meta-head it-quick-head ;

\ ---- The check of instance i (§4 steps 1 and 2).
: it-decl ( i -- d outcome ) elab-instance@ 2drop elab-decl-name lf-menv-find ;
: it-record-class ( i -- class ) elab-instance@ drop nip ;
: it-class-same? ( body i -- flag outcome )
  swap lf-class? ok-then? 0= if nip false swap exit then
  if swap it-record-class = else drop false then outcome-ok ;
\ The recorded keys against the recomputed: the same; wider, the record
\ has a star where the type gives a term (Lean saw a no_index annotation,
\ an mdata node the export drops: unverified, error 114); or different
\ (invalid, error 113).
0 constant it-same   1 constant it-wider   2 constant it-differ
: it-d ( -- k ) it it-dk @ it it-i @ + ;
: it-c ( -- k ) it it-ck @ it it-j @ + ;
: it-skip ( -- ) 1 begin it-c elab-key-arity 1- + 1 it it-j +! dup 0= until drop ;
: it-star-over? ( -- flag )
  it-d elab-key-tag elab-key-star = it-c elab-key-tag elab-key-star <> and ;
: it-advance ( -- flag )
  it-star-over? if it-skip true it it-wide ! 1 it it-i +! true exit then
  it-d it-c elab-key= dup if 1 it it-i +! 1 it it-j +! then ;
: it-more? ( -- flag ) it it-i @ it it-dn @ < it it-j @ it it-cn @ < and ;
: it-ends? ( -- flag ) it it-i @ it it-dn @ = it it-j @ it it-cn @ = and ;
: it-walk-keys ( -- result )
  begin it-more? while it-advance 0= if it-differ exit then repeat
  it-ends? 0= if it-differ exit then it it-wide @ if it-wider else it-same then ;
: it-compare ( kc nc i -- result )
  elab-instance-keys it it-dn ! it it-dk ! it it-cn ! it it-ck !
  0 it it-i ! 0 it it-j ! false it it-wide ! it-walk-keys ;
: it-path-result ( body i -- result outcome )
  swap lf-dt-path ok-then? if rot it-compare outcome-ok else nip nip -1 swap then ;
: it-verdict ( result -- outcome )
  dup it-same = if drop outcome-ok exit then
  it-wider = if lf-e-inst-wide it it-error ! outcome-unsupported else lf-e-inst-keys
  it-fail then ;
: it-body ( i -- body outcome )
  it-decl ok-then? 0= if no-result exit then lf-menv-type lf-inst-telescope ;
: it-class-step ( body i -- body i outcome )
  2dup it-class-same? ok-then? 0= if exit then
  if outcome-ok else lf-e-inst-class it-fail then ;
: it-body-check ( i -- outcome )
  dup it-body ok-then? 0= if nip exit then swap
  it-class-step dup ok? 0= if nip nip exit then drop
  it-path-result ok-then? if it-verdict then ;
: it-scoped ( i -- outcome )
  false lf-mctx-depth{ ok-then? 0= if nip exit then
  swap lf-dt-mark 2>r >r it-body-check r> 2r> lf-dt-release
  swap }lf-mctx-depth outcome-and ;
: lf-inst-check ( i -- outcome )
  lf-meta-config 2>r lf-meta-default lf-tr-default lf-meta-config!
  it-scoped 2r> lf-meta-config! ;
: it-status-ready ( -- outcome )
  it-status slab-count if outcome-ok exit then
  elab-instance elab-count dup it-status slab-claim nip ok-then?
  if it-status slab-base swap cells erase outcome-ok then ;
: it-count ( status -- ) 1 it it-checked +! it-unverified = negate it it-unverified-n +! ;
: it-record ( outcome i -- outcome )
  over ok? if it-ok else it-unverified then dup it-count swap it-status slab-at ! ;
: it-fatal? ( outcome -- flag ) dup outcome-invalid = swap outcome-full = or ;
: it-check ( i -- outcome )
  dup lf-inst-check dup it-fatal? if nip exit then swap it-record drop outcome-ok ;
: lf-inst-verified? ( i -- flag )
  dup it-status slab-count < if it-status slab-at @ it-ok = else drop false then ;

\ ---- The trees: a node is (key, first child, next sibling, first value,
\ last value), -1 for none; a value cell (value, next).
: it-node ( n -- addr ) it-nodes slab-at ;
: it-key@ ( n -- k ) it-node @ ;
: it-child ( n -- c ) it-node cell+ @ ;
: it-sibling ( n -- s ) it-node 2 cells + @ ;
: it-values ( n -- v ) it-node 3 cells + @ ;
: it-node-new ( k -- n outcome )
  1 it-nodes slab-claim ok-then? 0= if nip no-result exit then
  tuck it-node dup 5 cells -1 fill ! outcome-ok ;
: it-find-child ( k n -- c true | false )
  it-child begin dup 0< 0= while 2dup it-key@ elab-key= if nip true exit then
  it-sibling repeat
  2drop false ;
: it-last-sibling ( c -- addr )
  begin dup it-sibling dup 0< 0= while nip repeat drop it-node 2 cells + ;
: it-link ( c n -- ) dup it-child 0< if it-node cell+ ! else it-child it-last-sibling !
  then ;
: it-descend ( k n -- c outcome )
  2dup it-find-child if nip nip outcome-ok exit then
  swap it-node-new ok-then? 0= if nip no-result exit then tuck swap it-link outcome-ok ;
: it-val-new ( v -- cell outcome )
  1 it-vals slab-claim ok-then? 0= if nip no-result exit then
  tuck it-vals slab-at tuck ! -1 swap cell+ ! outcome-ok ;
: it-append ( v n -- outcome )
  swap it-val-new ok-then? 0= if nip exit then swap it-node 3 cells +
  dup @ 0< if 2dup ! else 2dup cell+ @ it-vals slab-at cell+ ! then cell+ ! outcome-ok ;
\ A value goes in by its keys after the root key.
: it-insert ( v -- outcome )
  it it-root @ over it-keys 1 /string bounds ?do
    i swap it-descend ok-then? 0= if nip unloop exit then
  loop it-append ;

\ ---- A root's tree: its values placed by rank, checked, inserted.
: it-root-of? ( v k -- flag ) swap it-keys drop elab-key= ;
: it-grow-to ( n -- outcome )
  it-ranked slab-count - dup 0> 0= if drop outcome-ok exit then
  dup it-ranked slab-claim ok-then? 0= if nip exit then
  it-ranked slab-at swap cells -1 fill outcome-ok ;
: it-place ( v -- outcome )
  dup it-rank 1+ it-grow-to dup ok? 0= if nip exit then
  drop dup it-rank it-ranked slab-at ! outcome-ok ;
: it-gather ( k v -- k outcome ) over 2dup it-root-of? if drop it-place else 2drop
  outcome-ok then ;
: it-gather-instances ( k -- k outcome )
  elab-instance elab-count 0 ?do i it-gather dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
: it-gather-left ( k -- k outcome )
  elab-left-out elab-count 0 ?do i invert it-gather dup ok? 0= if unloop exit then drop
  loop
  outcome-ok ;
: it-ranked@ ( r -- v ) it-ranked slab-at @ ;
: it-check-ranked ( -- outcome )
  it-ranked slab-count 0 ?do i it-ranked@ dup 0< if drop else it-check
    dup ok? 0= if unloop exit then drop then loop outcome-ok ;
: it-insert-ranked ( -- outcome )
  it-ranked slab-count 0 ?do i it-ranked@ it-insert dup ok? 0= if unloop exit then drop
  loop
  outcome-ok ;
: it-entry ( k node -- outcome )
  swap 1 it-roots slab-claim ok-then? 0= if nip nip exit then it-roots slab-at 2!
  outcome-ok ;
: it-root-node ( -- node outcome )   \ keyed by the first value's root key
  0 it-ranked@ it-keys drop dup it-node-new ok-then? 0= if nip no-result exit then
  tuck it-entry dup ok? if drop dup it it-root ! outcome-ok then ;
: it-gathered ( k -- outcome )
  it-ranked slab-clear it-gather-instances dup ok? if drop it-gather-left else nip exit
  then nip ;
: it-root-made ( -- node outcome )
  it-root-node ok-then? 0= if no-result exit then
  it-insert-ranked dup ok? 0= if nip no-result then ;
: it-ranked-ready ( k -- outcome ) it-status-ready dup ok? if drop it-gathered else nip
  then ;
: it-root-build ( k -- node outcome )
  it-ranked-ready dup ok? 0= if no-result exit then drop
  it-ranked slab-count 0= if -1 outcome-ok exit then
  it-check-ranked dup ok? if drop it-root-made else no-result then ;
: it-root-find ( k -- node true | false )
  it-roots slab-count 0 ?do dup i it-roots slab-at @ elab-key=
    if drop i it-roots slab-at cell+ @ true unloop exit then loop drop false ;
: it-root-get ( k -- node outcome )
  dup it-root-find if nip outcome-ok else it-root-build then ;

\ ---- getUnify's process (Main.lean:577-605) on a heap stack of frames
\ (todo, node, skip): skip 0 or more visits a node; skip below 0 visits
\ the siblings from node, each with skip (skip invert) plus its arity.
: it-push ( todo node skip -- outcome )
  1 it-stack slab-claim ok-then? 0= if >r 2drop drop r> exit then
  it-stack slab-at tuck ! tuck 2 cells + ! cell+ ! outcome-ok ;
: it-pop ( -- todo node skip )
  it-stack slab-count 1- it-stack slab-at dup cell+ @ over 2 cells + @ rot @
  -1 it-stack slab-commit ;
: it-values-out ( node -- outcome )
  it-values begin dup 0< 0= while
    dup it-vals slab-at @ it-out lf-meta-push dup ok? 0= if nip exit then drop
    it-vals slab-at cell+ @ repeat drop outcome-ok ;
: it-visit-skip ( todo node skip -- outcome )
  swap it-child dup 0< if drop 2drop outcome-ok exit then >r 1- invert r> swap it-push ;
: it-push-visit ( todo node -- outcome ) 0 it-push ;
: it-star-child ( node -- c true | false )
  it-child dup it-key@ elab-key-tag elab-key-star = if true else drop false then ;
: it-push-match ( node -- outcome )
  it it-k @ swap it-find-child if it it-args @ swap it-push-visit else outcome-ok then ;
: it-push-star ( node -- outcome )
  it-star-child if it it-rest @ swap it-push-visit else outcome-ok then ;
: it-star-key? ( -- flag ) it it-k @ elab-key-tag elab-key-star = ;
: it-on-key ( node -- outcome )
  it-star-key? if it-child it it-rest @ swap -1 it-push exit then
  dup it-push-match dup ok? if drop it-push-star else nip then ;
: it-keyed ( todo -- outcome )
  dup lf-dt-rest dup it it-rest ! swap lf-dt-first false rot lf-dt-key
  ok-then2? if it it-args ! it it-k ! outcome-ok then ;
: it-visit-zero ( todo node -- outcome )
  over lf-dt-nil = if nip it-values-out exit then
  dup it-child 0< if 2drop outcome-ok exit then
  swap it-keyed dup ok? if drop it-on-key else nip then ;
: it-arity ( s -- n ) it-key@ elab-key-arity ;
\ The next sibling's frame goes on first, so that s is visited first.
: it-siblings ( todo s base -- outcome )
  over 0< if drop 2drop outcome-ok exit then
  >r 2dup it-sibling r@ invert it-push dup ok? 0= if nip nip r> drop exit then drop
  dup it-arity r> + it-push ;
: it-frame ( todo node skip -- outcome )
  dup 0< if invert it-siblings exit then ?dup if it-visit-skip else it-visit-zero then ;
: it-walk ( -- outcome )
  begin it-stack slab-count while it-pop it-frame dup ok? 0= if exit then drop repeat
  outcome-ok ;

\ ---- getUnify.
: it-star-root? ( k -- flag ) elab-key-tag elab-key-star = ;
: it-walk-from ( list node -- outcome )
  dup 0< if 2drop outcome-ok exit then 0 it-push dup ok? if drop it-walk then ;
: it-unify-run ( type -- outcome )
  true lf-dt-nil lf-dt-key ok-then2? 0= if exit then
  over it-star-root? if 2drop outcome-unsupported exit then
  swap it-root-get ok-then? if it-walk-from else nip then ;
: it-reducible ( xt -- outcome )
  lf-defeq-mode >r lf-tr-reducible lf-defeq-mode! execute r> lf-defeq-mode! ;
: it-out-cells ( outcome -- addr n outcome ) it-out slab-base it-out slab-count rot ;
: lf-inst-unify ( type -- addr n outcome )
  it-out slab-clear it-stack slab-clear lf-dt-mark 2>r >r
  ['] it-unify-run it-reducible r> 2r> lf-dt-release it-out-cells ;

\ ---- getInstances.
: it-goal-body ( type -- body outcome )
  dup it-pi? if drop -1 outcome-unsupported exit then
  dup lf-meta-whnf ok-then? 0= if nip no-result exit then
  it-pi? if drop -1 outcome-unsupported else outcome-ok then ;
: it-local? ( name view i -- flag ) lf-view-local lf-local-class = ;
: it-locals-of? ( class -- flag )
  elab-decl-name lf-mctx-view dup lf-view-valid? 0= if 2drop false exit then
  dup lf-view-count 0 ?do 2dup i it-local? if 2drop true unloop exit then loop 2drop
  false ;
: it-prio@ ( j -- p ) it-out slab-at @ lf-inst-priority ;
: it-swap ( j -- ) it-out slab-at dup 2@ swap rot 2! ;
: it-out-of-order? ( j -- flag ) dup 0< if drop false exit then dup it-prio@ swap 1+
  it-prio@ > ;
: it-sink ( i -- ) 1- begin dup it-out-of-order? while dup it-swap 1- repeat drop ;
: it-sort ( -- ) it-out slab-count 1 ?do i it-sink loop ;
: it-keep ( w v -- w' ) dup it-erased? if drop else over it-out slab-at ! 1+ then ;
: it-drop-erased ( -- )
  0 it-out slab-count 0 ?do i it-out slab-at @ it-keep loop
  it-out slab-count - it-out slab-commit ;
: it-class-body ( type -- body class outcome )
  it-goal-body ok-then? 0= if -1 -1 rot exit then
  dup lf-class? ok-then? 0= if nip -1 -1 rot exit then
  if outcome-ok else lf-e-not-class it-fail -1 swap then ;
: it-candidates ( type -- outcome )
  it-class-body ok-then2? 0= if exit then
  it-locals-of? if drop outcome-unsupported exit then
  lf-inst-unify nip nip dup ok? if it-sort it-drop-erased then ;
: lf-inst-candidates ( type -- addr n outcome ) it-candidates it-out-cells ;

\ ---- Default instances, by rank.
: it-default-of? ( class i -- flag ) elab-default@ 2drop = ;
: it-default-place ( i -- outcome )
  dup elab-default-rank 1+ it-grow-to dup ok? 0= if nip exit then
  drop dup elab-default-rank it-ranked slab-at ! outcome-ok ;
: lf-default-instances ( class -- addr n outcome )
  it-ranked slab-clear elab-default elab-count 0 ?do
    dup i it-default-of? if i it-default-place dup ok? 0= if nip 0 0 rot unloop exit
    then drop then
  loop drop it-ranked slab-base it-ranked slab-count outcome-ok ;

base !   \ the BASE this file was loaded with
