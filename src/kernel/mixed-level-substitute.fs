\ Untrusted same-session simultaneous universe substitution for mixed
\ syntax. The current session context must contain every source parameter
\ and every actual parameter. Every source parameter must also occur in the
\ formal list; actuals are not recursively substituted. This is not type or
\ proof checking. Exclude reset, raw mutation and callbacks during a call.
\ Caller arrays must be aligned, readable and disjoint from the stores,
\ contexts and module data. Handles are forgeable. On failure all three
\ store counts roll back, but identities never rewind.
\ State: one walk record, lf-mls-walker (the source audit and the fuel left,
\ shared by every pass), and one job record, lf-mls-job (the substitution,
\ the counts to roll back to, reached terms and their images), both
\ members of the checker context (lib/context.fs). Single-threaded within
\ one context. mixed-signature-audit runs the source audit alone through
\ lf-mls-audit-formals.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/generation-handles.fs
require ../core/levels.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./level-substitute.fs

begin-structure /lf-mlsrec
  field: lf-mlsrec-formals     \ address of the formal parameter IDs
  field: lf-mlsrec-count       \ number of formals
  field: lf-mlsrec-terms       \ store counts to roll back to
  field: lf-mlsrec-levels
  field: lf-mlsrec-crefs
  lf-level-capacity cells +field lf-mlsrec-actuals    \ replacement levels
  lf-cref-argument-capacity 2* cells +field lf-mlsrec-args  \ new level pairs
  lf-term-capacity cells +field lf-mlsrec-seen        \ reached by the audit
  lf-term-capacity cells +field lf-mlsrec-results     \ each reached term's image
end-structure
lf-term-capacity context-walk: lf-mls-walker
/lf-mlsrec context-record: lf-mls-job

\ Fuel left after a call; the signature probe continues with it, and tests
\ read it. Every helper this module calls reports only ok, invalid,
\ exhausted or full, and so does every word here.
: lf-mls-fuel ( -- addr ) lf-mls-walker walk-fuel ;
: lf-mls-formals ( -- addr ) lf-mls-job lf-mlsrec-formals ;
: lf-mls-count ( -- addr ) lf-mls-job lf-mlsrec-count ;
: lf-mls-actuals ( -- addr ) lf-mls-job lf-mlsrec-actuals ;
: lf-mls-args ( -- addr ) lf-mls-job lf-mlsrec-args ;
: lf-mls-seen ( index -- addr ) cells lf-mls-job lf-mlsrec-seen + ;
: lf-mls-result ( index -- addr ) cells lf-mls-job lf-mlsrec-results + ;

\ The rollback point: the counts of the term, level and reference stores.
: lf-mls-snapshot ( -- )
  lf-term-count @ lf-mls-job lf-mlsrec-terms !
  lf-level-count @ lf-mls-job lf-mlsrec-levels !
  lf-cref-count @ lf-mls-job lf-mlsrec-crefs ! ;
: lf-mls-rollback ( status -- status )
  lf-mls-job lf-mlsrec-terms @ lf-term-count !
  lf-mls-job lf-mlsrec-levels @ lf-level-count !
  lf-mls-job lf-mlsrec-crefs @ lf-cref-count ! ;

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
\ first, so children are earlier nodes. Occurrences, including repeated DAG
\ edges, each consume fuel.
: lf-mls-mark ( walk -- ) true swap walk-node @ lf-mls-seen ! ;
: lf-mls-sources ( addr count walk -- outcome )
  swap 0 ?do over i lf-cref-pair@ drop over lf-lsubst-walk-source dup ok? 0=
    if nip nip unloop exit then drop loop 2drop outcome-ok ;
: lf-mls-reference ( cref identity walk -- outcome )
  >r lf-cref-levels if r> lf-mls-sources else r> drop outcome-invalid then ;
: lf-mls-dispatch ( first second walk tag -- outcome )
  over lf-mls-mark dup lf-term-binary-tag? if drop walk-children exit then
  case lf-tag-symbolic-sort of nip lf-lsubst-walk-source endof
    lf-tag-constant of lf-mls-reference endof
    lf-tag-bvar of drop 2drop outcome-ok endof walk-bad-tag endcase ;
: lf-mls-visit ( walk -- outcome ) lf-terms ['] lf-mls-dispatch walk-visit ;
: lf-mls-unseen ( -- ) 0 lf-mls-seen lf-term-capacity cells erase ;
\ The formals and count are those last given to lf-lsubst-use.
: lf-mls-audit-from ( root -- status )
  lf-mls-unseen ['] lf-mls-visit lf-mls-walker walk-run ;

\ The source audit alone, as mixed-signature-audit runs it on a candidate
\ signature: every term reachable from root and every source level against
\ count formal IDs at formals, with the given fuel; gives the fuel left.
\ The caller has validated root's graph (lf-cterm-check). An audit reads
\ no actuals, so none are given. Nothing is allocated. Negative fuel or a
\ count outside 0..lf-level-capacity is invalid and spends nothing.
: lf-mls-audit-input? ( count fuel -- flag ) 0< 0= swap lf-level-capacity upto? and ;
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
: lf-mls-args! ( addr count -- outcome )
  0 ?do dup i lf-mls-arg dup ok? 0= if nip unloop exit then drop loop
  drop outcome-ok ;
\ Cell arrays compared cell by cell (never as bytes); n <= 0 is equal.
: lf-mls-cell= ( addr addr' i -- flag ) cells tuck + @ -rot + @ = ;
: lf-mls-cells= ( addr addr' n -- flag )
  0 max 0 ?do 2dup i lf-mls-cell= 0= if 2drop false unloop exit then loop 2drop true ;
: lf-mls-changed? ( addr count -- flag ) 2* lf-mls-args swap lf-mls-cells= 0= ;
: lf-mls-substituted ( slot -- changed outcome )
  lf-cref-pairs 2dup lf-mls-args! dup ok?
  if drop lf-mls-changed? outcome-ok else nip nip false swap then ;
: lf-mls-new-constant ( slot -- index outcome )
  dup lf-cref-name@ rot lf-crec-arity @ >r lf-mls-args r> lf-cref-new
  if lf-cterm-new lf-mls-made else 0 outcome-full then ;
: lf-mls-rebuild ( node slot -- index outcome )
  dup lf-mls-substituted ok-then? 0= if lf-mls-failed exit then
  if nip lf-mls-new-constant else drop outcome-ok then ;
: lf-mls-constant ( node cref identity -- index outcome )
  lf-cref-record if lf-mls-rebuild else drop 0 outcome-invalid then ;
\ An application, lambda or Pi over the images of its children.
: lf-mls-images ( first second -- first' second' )
  lf-mls-result @ swap lf-mls-result @ swap ;
: lf-mls-kept? ( first second -- flag ) 2dup lf-mls-images rot = >r = r> and ;
: lf-mls-binary ( node first second tag -- index outcome )
  >r 2dup lf-mls-kept? if 2drop r> drop outcome-ok exit then
  rot drop lf-mls-images r> lf-term-binary
  if outcome-ok else 0 outcome-full then ;
: lf-mls-image-of ( node first second tag -- index outcome )
  case lf-tag-symbolic-sort of drop lf-mls-sort endof
    lf-tag-constant of lf-mls-constant endof
    lf-tag-bvar of 2drop outcome-ok endof
    dup >r lf-mls-binary r> endcase ;
: lf-mls-image ( node -- index outcome )
  dup lf-term-read if rot lf-mls-image-of else drop 0 outcome-invalid then ;
: lf-mls-build-node ( node -- outcome )
  dup lf-mls-image ok-then? if swap lf-mls-result ! outcome-ok else nip then ;
: lf-mls-build-at ( node -- outcome )
  dup lf-mls-seen @ if lf-mls-build-node else drop outcome-ok then ;
: lf-mls-build ( root -- outcome )
  1+ 0 ?do i lf-mls-build-at dup ok? 0= if unloop exit then drop loop outcome-ok ;

\ The passes in order: the root handle and stores, the replacements (live,
\ and in level scope), the whole graph (lf-cterm-check), the source audit,
\ then the build. A failed build rolls the counts back to the snapshot.
: lf-mls-serials? ( -- flag ) lf-term-serial @ 0< 0= lf-level-serial @ 0< 0= and ;
: lf-mls-ready? ( index id -- flag )
  lf-hterm-valid? lf-cref-state-valid? and lf-mls-serials? and ;
: lf-mls-actual ( pairs position -- flag )
  tuck lf-cref-pair@ 2dup lf-hlevel-valid?
  if drop swap cells lf-mls-actuals + ! true else 2drop drop false then ;
: lf-mls-actuals! ( pairs count -- flag )
  0 ?do dup i lf-mls-actual 0= if drop false unloop exit then loop drop true ;
: lf-mls-graph ( index id -- outcome )
  lf-mls-fuel @ lf-cterm-check lf-cterm-fuel @ lf-mls-fuel ! ;
: lf-mls-checks ( index id -- index id outcome )
  lf-mls-inputs dup ok? if drop 2dup lf-mls-graph then
  dup ok? if drop over lf-mls-audit-from then ;
: lf-mls-finish ( index -- index id 0 | status )
  lf-mls-result @ dup lf-term-identity
  if outcome-ok else drop outcome-invalid lf-mls-rollback then ;
: lf-mls-apply ( index -- index id 0 | status )
  dup lf-mls-build dup ok? if drop lf-mls-finish else nip lf-mls-rollback then ;
: lf-mls-run ( index id -- index id 0 | status )
  lf-mls-checks dup ok? if 2drop lf-mls-apply else nip nip then ;
: lf-mls-use ( formals pairs count -- pairs count )
  dup lf-mls-count ! rot lf-mls-formals ! ;
: lf-mls-prepare ( index id pairs count -- index id outcome )
  2over lf-mls-ready? 0= if 2drop outcome-invalid exit then
  lf-mls-snapshot lf-mls-actuals! flag>outcome ;

\ Substitute count actual (index identity) level pairs for count formal IDs
\ in a live term. All syntax, source levels and replacements are audited
\ before allocation.
\ Audit and substitution share fuel; each term/level occurrence consumes fuel,
\ including repeated replacement validation. Bounded list scans, identity
\ checks and topological staging are additional bounded work. Status is invalid
\ for malformed, stale or out-of-scope input, exhausted when the fuel runs
\ out, and full for a full work stack or store or a spent identity serial.
: lf-mixed-level-substitute
  ( index id formals actual-pairs count fuel -- index id 0 | status )
  lf-mls-walker walk-budget 0= if 2drop 2drop drop outcome-invalid exit then
  dup lf-level-capacity upto? 0= if 2drop 2drop drop outcome-invalid exit then
  lf-mls-use lf-mls-prepare dup ok? if drop lf-mls-run else nip nip then ;
