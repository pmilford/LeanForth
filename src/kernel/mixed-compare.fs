\ Untrusted syntactic comparison of mixed terms: equal means the same
\ constructors, bound variables, constant names and ordered universe
\ arguments, and the same level syntax without normalization; any difference
\ is unknown, never a proof of inequality. Not a typing or proof judgment.
\ Equal opaque level parameter IDs are assumed to denote the same Lean name.
\ State: two paired walk records, lf-mcompare-walker (left and right terms)
\ and lf-mcompare-level-walker (left and right levels); level comparisons
\ charge the term walk's fuel; and Lean's == per-call pair set (the table
\ lf-meq-table over the slab lf-meq-pairs, its count lf-meq-count and
\ candidate lf-meq-key). All are members of the checker context
\ (lib/context.fs). Single-threaded within one context; exclude arena,
\ parameter-context and name mutation during a call. mixed-convert.fs
\ reuses the pair-visiting, name, reference and audit words with its own
\ walk.

require ../lib/lib.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ../lib/slab.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs

lf-walk-room context-walk2: lf-mcompare-walker
lf-level-walk-room context-walk2: lf-mcompare-level-walker

\ Fuel left after a comparison; zero after negative fuel or a failed audit.
: lf-mcompare-fuel ( -- addr ) lf-mcompare-walker walk-fuel ;
: lf-mcompare-level-fuel ( -- addr ) lf-mcompare-level-walker walk-fuel ;

\ Visiting a pair of nodes of one store, the left in walk-node and the
\ right in walk-context: an unallocated node is invalid (valid ( left
\ right -- flag ) checks both, with one header check), different tags are
\ unknown, and otherwise xt ( a b walk tag -- outcome ) gets both nodes as
\ records of three cells (lib/node.fs) and their tag: fetch ( left right
\ -- a b ) gives them, a level's in its store, a term's copied into two
\ records of the context (term records are packed: core/terms.fs). Fields
\ are then read without further checks.
/node context-record: lf-mcompare-left
/node context-record: lf-mcompare-right
: lf-mcompare-pair@ ( walk -- left right ) dup walk-node @ swap walk-context @ ;
: lf-mcompare-slots ( left right store -- a b ) tuck store-slot >r store-slot r> ;
: lf-mcompare-level-slots ( left right -- a b ) lf-levels lf-mcompare-slots ;
: lf-mcompare-copy ( index record -- ) >r lf-term-fields r> node! ;
: lf-mcompare-term-slots ( left right -- a b )
  lf-mcompare-right lf-mcompare-copy lf-mcompare-left lf-mcompare-copy
  lf-mcompare-left lf-mcompare-right ;
: lf-mcompare-nodes ( walk valid fetch -- a b true | false )
  >r >r lf-mcompare-pair@ 2dup r> execute
  if r> execute true else 2drop r> drop false then ;
: lf-mcompare-tags? ( a b -- flag ) node-tag @ swap node-tag @ = ;
: lf-mcompare-tagged ( a b walk xt -- outcome )
  >r >r over node-tag @ r> swap r> execute ;
: lf-mcompare-match ( a b walk xt -- outcome )
  2over lf-mcompare-tags? if lf-mcompare-tagged else 2drop 2drop outcome-unknown then ;
: lf-mcompare-visit-pair ( walk valid fetch xt -- outcome )
  >r >r over swap r> lf-mcompare-nodes
  if rot r> lf-mcompare-match else drop r> drop outcome-invalid then ;

\ The fields of both nodes, left first. Pushing the first fields as a pair,
\ or both pairs with the second fields underneath, visits the children in
\ order; a full work stack is full.
: lf-mcompare-firsts ( a b -- x y ) node-first @ swap node-first @ swap ;
: lf-mcompare-seconds ( a b -- x y ) node-second @ swap node-second @ swap ;
: lf-mcompare-first ( a b walk -- outcome ) >r lf-mcompare-firsts r> walk-pair-outcome ;
: lf-mcompare-children ( a b walk -- outcome )
  >r 2dup lf-mcompare-seconds r@ walk-push-pair
  if r> lf-mcompare-first else 2drop r> drop outcome-full then ;
\ Equal syntax is ok; a difference is unknown.
: lf-mcompare-verdict ( flag -- outcome ) if outcome-ok else outcome-unknown then ;
: lf-mcompare-same-first ( a b walk -- outcome )
  drop lf-mcompare-firsts = lf-mcompare-verdict ;

\ Names. Both passed the name-table audit with their references, so every
\ ID and prefix is readable. Components are compared from the last back to
\ the anonymous root, by kind and then by number or bytes, even when the
\ IDs coincide; each component costs one unit of the given walk's fuel.
: lf-mcompare-payloads? ( a b -- flag )
  over lf-name-num? if lf-name-num= else lf-name-str= then ;
: lf-mcompare-components? ( a b -- flag )
  2dup lf-name-tags= if lf-mcompare-payloads? else 2drop false then ;
\ One component decides when both names are anonymous (ok) or the
\ components differ (unknown); otherwise both prefixes come next.
: lf-mcompare-component ( a b -- a' b' false | outcome true )
  2dup or 0= if 2drop outcome-ok true exit then
  2dup lf-mcompare-components?
  if lf-name-prefixes false else 2drop outcome-unknown true then ;
: lf-mcompare-names ( a b walk -- outcome )
  >r begin r@ walk-spend? 0= if 2drop r> drop outcome-exhausted exit then
    lf-mcompare-component until r> drop ;

\ Levels, in order and without normalization. Both graphs passed the
\ level-scope audit, so children come earlier and every tag is known. The
\ work stack holds one pending pair per node on a path: at the default
\ capacities never more than its room; at a raised level capacity a
\ deeper pair fills it, and the walk is full (never another outcome). A
\ level walk runs on the term walk's fuel and continues with what it leaves.
: lf-mcompare-level-dispatch ( a b walk tag -- outcome )
  dup lf-level-binary-tag? if drop lf-mcompare-children exit then
  case lf-level-tag-zero of drop 2drop outcome-ok endof
    lf-level-tag-param of lf-mcompare-same-first endof
    lf-level-tag-succ of lf-mcompare-first endof walk-bad-tag endcase ;
: lf-mcompare-level-visit ( walk -- outcome )
  ['] lf-level-pair-valid? ['] lf-mcompare-level-slots ['] lf-mcompare-level-dispatch
  lf-mcompare-visit-pair ;
: lf-mcompare-site ( -- site ) c" mixed-compare lf-mixed-compare" ;
: lf-mcompare-level-run ( a b -- outcome )
  ['] lf-mcompare-level-visit lf-mcompare-level-walker lf-mcompare-site lf-diag-run-pair ;
: lf-mcompare-level ( a b -- outcome )
  lf-mcompare-fuel @ lf-mcompare-level-fuel ! lf-mcompare-level-run
  lf-mcompare-level-fuel @ lf-mcompare-fuel ! ;

\ Constant references, already audited, as reference records. The heads
\ match when the arities are equal (checked first, at no cost) and the
\ names are, charging the given walk's fuel; each module then compares the
\ ordered level arguments its own way. lf-mcompare-args,
\ lf-mcompare-constant and lf-mcompare-sort charge levels to compare's own
\ term walk (through lf-mcompare-level), so only compare may call them;
\ convert reuses lf-mcompare-heads and compares levels with its own walk.
: lf-mcompare-crefs ( a b -- slot slot )
  lf-mcompare-firsts lf-cref-slot swap lf-cref-slot swap ;
: lf-mcompare-arity? ( slot slot -- flag ) lf-crec-arity @ swap lf-crec-arity @ = ;
: lf-mcompare-name-ids ( slot slot -- name name )
  lf-crec-name @ swap lf-crec-name @ swap ;
: lf-mcompare-heads ( slot slot walk -- slot slot true | outcome false )
  >r 2dup lf-mcompare-arity? 0= if 2drop r> drop outcome-unknown false exit then
  2dup lf-mcompare-name-ids r> lf-mcompare-names ok-then2? ;
\ The level arrays of two references of equal arity, and their level
\ indices at one position.
: lf-mcompare-arrays ( slot slot -- addr addr count )
  lf-cref-pairs >r swap lf-cref-pairs drop swap r> ;
: lf-mcompare-arg ( addr addr i -- level level )
  tuck lf-cref-pair@ drop >r lf-cref-pair@ drop r> ;
: lf-mcompare-arg-at ( slot slot i -- slot slot outcome )
  2dup-under lf-mcompare-arg lf-mcompare-level ;
: lf-mcompare-args ( slot slot -- outcome )
  lf-mcompare-arrays ['] lf-mcompare-arg-at ok-each nip nip ;
: lf-mcompare-constant ( a b walk -- outcome )
  >r lf-mcompare-crefs r> lf-mcompare-heads if lf-mcompare-args then ;

\ Terms. Both graphs passed the full audit, so only binary nodes, bound
\ variables, live free variables, symbolic Sorts and constants occur, and
\ children come earlier; the work stack overflows only at a raised term
\ capacity, and is then full, as for levels. Two free variables are equal
\ when their numbers are (one node per entry of the local context). Each
\ visit costs one unit of fuel.
: lf-mcompare-sort ( a b walk -- outcome ) drop lf-mcompare-firsts lf-mcompare-level ;
\ Two projection leaves (core/projections.fs): the same field index, then
\ the same structure name (Lean's proj: idx, then struct name).
: lf-mcompare-seconds? ( a b -- flag ) lf-mcompare-seconds = ;
: lf-mcompare-proj ( a b walk -- outcome )
  >r 2dup lf-mcompare-seconds? 0= if 2drop r> drop outcome-unknown exit then
  lf-mcompare-firsts r> lf-mcompare-names ;
\ Two literals (core/literals.fs): the same value, read from the nodes'
\ indices.
: lf-mcompare-lit ( a b walk -- outcome )
  nip nip lf-mcompare-pair@ lf-lit-same? lf-mcompare-verdict ;
\ Two string literals (core/string-literals.fs): the same bytes.
: lf-mcompare-str ( a b walk -- outcome )
  nip nip lf-mcompare-pair@ lf-str-same? lf-mcompare-verdict ;
\ Binary nodes compare their children, after their tags: two lets
\ (core/let-terms.fs) so also their nonDep flags, which Lean's ==
\ compares (binder names it ignores, and LeanForth drops).
: lf-mcompare-dispatch ( a b walk tag -- outcome )
  dup lf-term-binary-tag? if drop lf-mcompare-children exit then
  case lf-tag-constant of lf-mcompare-constant endof
    lf-tag-bvar of lf-mcompare-same-first endof
    lf-tag-fvar of lf-mcompare-same-first endof
    lf-tag-symbolic-sort of lf-mcompare-sort endof
    lf-tag-proj of lf-mcompare-proj endof
    lf-tag-lit of lf-mcompare-lit endof  lf-tag-str of lf-mcompare-str endof
    walk-bad-tag endcase ;
\ A term pair's visit with the dispatch xt (the comparison's, or the
\ equality's below).
: lf-mcompare-term-visit ( walk dispatch -- outcome )
  >r ['] lf-term-pair-valid? ['] lf-mcompare-term-slots r> lf-mcompare-visit-pair ;
: lf-mcompare-visit ( walk -- outcome ) ['] lf-mcompare-dispatch lf-mcompare-term-visit ;
: lf-mcompare-run ( left right -- outcome )
  ['] lf-mcompare-visit lf-mcompare-walker lf-mcompare-site lf-diag-run-pair ;

\ Lean's structural equality, operator== on terms (expr_eq_fn.cpp
\ 123-125; ADR 0014 Q3, plan task 4.2.2b): the same constructors, bound
\ and free variables, constant names and ordered universe arguments, and
\ the same level syntax; binder names and annotations are not stored, so
\ they never differ (Lean's == ignores them, 98-103). (flag ok), with
\ flag Lean's answer, or (false outcome) for a failure: exhausted, full
\ or invalid, recorded as a diagnostic; an answer leaves the diagnostic
\ as it was (two levels that differ note themselves inside the walk), as
\ == is no failure. Each visit costs one unit of fuel; the fuel left is
\ in lf-mcompare-fuel. Unchecked: both roots are audited live terms
\ (lf-cterm-check), as every term conversion compares; open terms
\ compare their loose bound variables by index.
\ As Lean's apply (expr_eq_fn.cpp 44-58; ADR 0014, compact-store plan
\ step S4), at every pair, the root included: the same node is equal at
\ once (is_eqp); two nodes whose data words (core/terms.fs: loose range,
\ the two flags and the depth, each a function of the term's structure,
\ as Lean's hash is) are known and differ are apart at once (Lean's
\ hash test); a pair met before in this call is not walked again (Lean's
\ per-call cache, check_cache: had it differed, the call would have
\ ended); two constants of one interned reference, or two Sorts of one
\ hash-consed level, are equal at once (is_eqp on the name and levels).
\ None of these is pushed, so none costs a unit.
: lf-meq-word ( node -- data|-1 ) lf-term-data@ 0= if -1 then ;
: lf-meq-apart? ( x y -- flag )
  lf-meq-word swap lf-meq-word over -1 = over -1 = or if 2drop false else <> then ;
\ The pairs met in this call: a hash table over a slab of (left right)
\ entries, emptied when a call starts; one that cannot grow keeps
\ nothing more (more work, never another answer).
/htab context-record: lf-meq-table
2 cells context-slab: lf-meq-pairs
1 cells context-record: lf-meq-count
2 cells context-record: lf-meq-key
: lf-meq-pair ( n -- addr ) lf-meq-pairs slab-at ;
: lf-meq-hash ( x y -- h ) swap hash-fmix swap hash-step ;
: lf-meq-rehash ( n htab -- h ) drop lf-meq-pair 2@ lf-meq-hash ;
: lf-meq-same ( n key htab -- flag ) drop swap lf-meq-pair 2@ rot 2@ d= ;
create lf-meq-hooks /htab-hooks allot
' lf-meq-rehash ' lf-meq-same lf-meq-hooks htab-hooks!
: lf-meq-table-make ( -- ) 4 lf-meq-hooks lf-meq-table htab-init drop ;
' lf-meq-table-make context-setup
:noname ( -- ) lf-meq-table htab-free ; context-teardown
: lf-meq-reset ( -- ) 0 lf-meq-count ! lf-meq-table ['] lf-meq-table-make htab-renew ;
: lf-meq-keep ( x y i -- )
  lf-meq-count @ 1+ lf-meq-pairs slab-hold ok? 0= if drop 2drop exit then
  >r lf-meq-count @ lf-meq-pair 2! lf-meq-count @ r> lf-meq-table htab-put
  1 lf-meq-count +! ;
: lf-meq-seen? ( x y -- flag )
  lf-meq-table htab-ready ok? 0= if 2drop false exit then
  2dup lf-meq-key 2! 2dup lf-meq-hash lf-meq-key swap lf-meq-table htab-find
  if drop 2drop true else lf-meq-keep false then ;
\ A child pair: equal, apart, met, or pushed.
: lf-meq-push ( x y walk -- outcome )
  >r 2dup = if 2drop r> drop outcome-ok exit then
  2dup lf-meq-apart? if 2drop r> drop outcome-unknown exit then
  2dup lf-meq-seen? if 2drop r> drop outcome-ok exit then
  r> walk-pair-outcome ;
: lf-meq-children ( a b walk -- outcome )
  >r 2dup lf-mcompare-seconds r@ lf-meq-push dup ok?
  if drop lf-mcompare-firsts r> lf-meq-push else nip nip r> drop then ;
: lf-meq-one-head? ( a b tag -- flag )
  dup lf-tag-constant = swap lf-tag-symbolic-sort = or
  if lf-mcompare-firsts = else 2drop false then ;
: lf-meq-dispatch ( a b walk tag -- outcome )
  dup lf-term-binary-tag? if drop lf-meq-children exit then
  2over 2 pick lf-meq-one-head? if 2drop 2drop outcome-ok exit then
  lf-mcompare-dispatch ;
: lf-meq-visit ( walk -- outcome ) ['] lf-meq-dispatch lf-mcompare-term-visit ;
: lf-mcompare-equal ( outcome -- flag outcome )
  dup outcome-unknown = if drop false outcome-ok exit then
  dup ok? if true swap exit then
  lf-mcompare-walker lf-mcompare-site lf-diag-walk false swap ;
: lf-mcompare-same? ( left right -- flag outcome )
  lf-meq-reset lf-diag@ 2>r 2>r ['] lf-meq-visit lf-mcompare-walker walk-run-pair
  lf-mcompare-equal dup ok? if 2r> 2r> lf-diag! else 2r> 2r> 2drop 2drop then ;
: lf-expr-equal ( left right fuel -- flag outcome )
  lf-mcompare-walker walk-budget 0= if 2drop false outcome-invalid exit then
  2dup = if 2drop true outcome-ok exit then
  2dup lf-meq-apart? if 2drop false outcome-ok exit then
  lf-mcompare-same? ;

\ Audit both roots completely, left first, with the walk's fuel; a failed
\ audit leaves no fuel. In a check each node is audited once per check
\ (core/constant-term-boundary.fs's memo, compact-store plan step S6 (c)):
\ a root audited before costs nothing. lf-cterm-check fails only as invalid, exhausted or
\ full. Five inputs: two handles and the walk. Shared with mixed-convert.fs,
\ as is the refusal of negative fuel, which also leaves no fuel.
: lf-mcompare-refuel ( outcome walk -- )
  swap ok? if lf-cterm-fuel @ else 0 then swap walk-fuel ! ;
: lf-mcompare-audit ( root identity walk -- outcome )
  >r r@ walk-fuel @ lf-cterm-check dup r> lf-mcompare-refuel ;
: lf-mcompare-audits ( left lid right rid walk -- outcome )
  >r 2swap r@ lf-mcompare-audit dup ok?
  if drop r> lf-mcompare-audit else nip nip r> drop then ;
: lf-mcompare-roots ( left lid right rid walk -- left right outcome )
  >r 2over 2over r> lf-mcompare-audits >r drop nip r> ;
: lf-mcompare-refused ( left lid right rid walk -- outcome )
  0 swap walk-fuel ! 2drop 2drop outcome-invalid ;

\ ( left identity right identity fuel -- status ) Both complete structural
\ audits precede comparison and share its fuel. Scope of term binders, typing,
\ declaration lookup and Lean string encoding are not checked. Negative fuel
\ and failed audits leave zero fuel. Running out of fuel (exhausted) or room
\ (full) can prevent discovery of a later invalidity.
: lf-mixed-compare ( left lid right rid fuel -- status )
  lf-mcompare-walker tuck walk-budget 0= if lf-mcompare-refused exit then
  lf-mcompare-roots ok-then? if lf-mcompare-run else nip then ;

\ ( left identity right identity fuel -- flag outcome ) Lean's == on two
\ roots after the same two audits on the same fuel: (flag ok), flag Lean's
\ answer, as lf-expr-equal gives it, so each shared pair is walked once
\ (expr_eq_fn's per-call cache), never once per path as lf-mixed-compare
\ walks a graph; or (false outcome) for negative fuel (invalid, no fuel
\ left), a failed audit or a failed comparison. The fuel left is in
\ lf-mcompare-fuel. For the comparisons Lean makes by ==, such as its
\ replay's of a generated recursor with the exported one
\ (Lean/Replay.lean, checkPostponedRecursors: info == info').
: lf-mixed-equal ( left lid right rid fuel -- flag outcome )
  lf-mcompare-walker tuck walk-budget 0= if lf-mcompare-refused false swap exit then
  lf-mcompare-roots ok-then? 0= if nip false swap exit then
  lf-mcompare-fuel @ lf-expr-equal ;
