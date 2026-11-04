\ Untrusted syntactic comparison of mixed terms: equal means the same
\ constructors, bound variables, constant names and ordered universe
\ arguments, and the same level syntax without normalization; any difference
\ is unknown, never a proof of inequality. Not a typing or proof judgment.
\ Equal opaque level parameter IDs are assumed to denote the same Lean name.
\ State: two paired walk records, lf-mcompare-walker (left and right terms)
\ and lf-mcompare-level-walker (left and right levels); level comparisons
\ charge the term walk's fuel. Both are members of the checker context
\ (lib/context.fs). Single-threaded within one context; exclude arena,
\ parameter-context and name mutation during a call. mixed-convert.fs
\ reuses the pair-visiting, name, reference and audit words with its own
\ walk.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/names.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs

lf-depth-limit context-walk2: lf-mcompare-walker
lf-level-depth-limit context-walk2: lf-mcompare-level-walker

\ Fuel left after a comparison; zero after negative fuel or a failed audit.
: lf-mcompare-fuel ( -- addr ) lf-mcompare-walker walk-fuel ;
: lf-mcompare-level-fuel ( -- addr ) lf-mcompare-level-walker walk-fuel ;

\ Visiting a pair of nodes of one store, the left in walk-node and the
\ right in walk-context: an unallocated node is invalid, different tags are
\ unknown, and otherwise xt ( a b walk tag -- outcome ) gets both node
\ addresses and their tag. Fields are then read without further checks.
: lf-mcompare-pair@ ( walk -- left right ) dup walk-node @ swap walk-context @ ;
: lf-mcompare-slots ( left right store -- a b ) tuck store-slot >r store-slot r> ;
: lf-mcompare-nodes ( walk store -- a b true | false )
  >r lf-mcompare-pair@ 2dup r@ store-pair-valid?
  if r> lf-mcompare-slots true else 2drop r> drop false then ;
: lf-mcompare-tags? ( a b -- flag ) node-tag @ swap node-tag @ = ;
: lf-mcompare-tagged ( a b walk xt -- outcome )
  >r >r over node-tag @ r> swap r> execute ;
: lf-mcompare-match ( a b walk xt -- outcome )
  2over lf-mcompare-tags? if lf-mcompare-tagged else 2drop 2drop outcome-unknown then ;
: lf-mcompare-visit-pair ( walk store xt -- outcome )
  >r over swap lf-mcompare-nodes
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
: lf-mcompare-kinds? ( a b -- flag ) lf-name-tag@ swap lf-name-tag@ = ;
: lf-mcompare-numbers? ( a b -- flag ) lf-name-payload swap lf-name-payload = ;
: lf-mcompare-bytes? ( a b -- flag ) lf-name-text rot lf-name-text compare 0= ;
: lf-mcompare-payloads? ( a b -- flag )
  over lf-name-tag@ lf-name-tag-num =
  if lf-mcompare-numbers? else lf-mcompare-bytes? then ;
: lf-mcompare-components? ( a b -- flag )
  2dup lf-mcompare-kinds? if lf-mcompare-payloads? else 2drop false then ;
: lf-mcompare-prefixes ( a b -- a' b' ) lf-name-prefix@ swap lf-name-prefix@ swap ;
\ One component decides when both names are anonymous (ok) or the
\ components differ (unknown); otherwise both prefixes come next.
: lf-mcompare-component ( a b -- a' b' false | outcome true )
  2dup or 0= if 2drop outcome-ok true exit then
  2dup lf-mcompare-components?
  if lf-mcompare-prefixes false else 2drop outcome-unknown true then ;
: lf-mcompare-names ( a b walk -- outcome )
  >r begin r@ walk-spend? 0= if 2drop r> drop outcome-exhausted exit then
    lf-mcompare-component until r> drop ;

\ Levels, in order and without normalization. Both graphs passed the
\ level-scope audit, so children come earlier, every tag is known and the
\ work stack (one pending pair per node on a path) cannot overflow. A level
\ walk runs on the term walk's fuel and continues with what it leaves.
: lf-mcompare-level-dispatch ( a b walk tag -- outcome )
  dup lf-level-binary-tag? if drop lf-mcompare-children exit then
  case lf-level-tag-zero of drop 2drop outcome-ok endof
    lf-level-tag-param of lf-mcompare-same-first endof
    lf-level-tag-succ of lf-mcompare-first endof walk-bad-tag endcase ;
: lf-mcompare-level-visit ( walk -- outcome )
  lf-levels ['] lf-mcompare-level-dispatch lf-mcompare-visit-pair ;
: lf-mcompare-site ( -- site ) c" mixed-compare lf-mixed-compare" ;
: lf-mcompare-level-run ( a b -- outcome )
  ['] lf-mcompare-level-visit lf-mcompare-level-walker walk-run-pair
  lf-mcompare-level-walker lf-mcompare-site lf-diag-walk ;
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
: lf-mcompare-continue? ( x y outcome -- x y true | outcome false )
  dup ok? if drop true else nip nip false then ;
: lf-mcompare-heads ( slot slot walk -- slot slot true | outcome false )
  >r 2dup lf-mcompare-arity? 0= if 2drop r> drop outcome-unknown false exit then
  2dup lf-mcompare-name-ids r> lf-mcompare-names lf-mcompare-continue? ;
\ The level arrays of two references of equal arity, and their level
\ indices at one position.
: lf-mcompare-arrays ( slot slot -- addr addr count )
  lf-cref-pairs >r swap lf-cref-pairs drop swap r> ;
: lf-mcompare-arg ( addr addr i -- level level )
  tuck lf-cref-pair@ drop >r lf-cref-pair@ drop r> ;
: lf-mcompare-args ( slot slot -- outcome )
  lf-mcompare-arrays 0 ?do 2dup i lf-mcompare-arg lf-mcompare-level
    dup ok? 0= if nip nip unloop exit then drop loop 2drop outcome-ok ;
: lf-mcompare-constant ( a b walk -- outcome )
  >r lf-mcompare-crefs r> lf-mcompare-heads if lf-mcompare-args then ;

\ Terms. Both graphs passed the full audit, so only binary nodes, bound
\ variables, live free variables, symbolic Sorts and constants occur,
\ children come earlier and the work stack cannot overflow. Two free
\ variables are equal when their numbers are (one node per entry of the
\ local context). Each visit costs one unit of fuel.
: lf-mcompare-sort ( a b walk -- outcome ) drop lf-mcompare-firsts lf-mcompare-level ;
: lf-mcompare-dispatch ( a b walk tag -- outcome )
  dup lf-term-binary-tag? if drop lf-mcompare-children exit then
  case lf-tag-constant of lf-mcompare-constant endof
    lf-tag-bvar of lf-mcompare-same-first endof
    lf-tag-fvar of lf-mcompare-same-first endof
    lf-tag-symbolic-sort of lf-mcompare-sort endof walk-bad-tag endcase ;
: lf-mcompare-visit ( walk -- outcome )
  lf-terms ['] lf-mcompare-dispatch lf-mcompare-visit-pair ;
: lf-mcompare-run ( left right -- outcome )
  ['] lf-mcompare-visit lf-mcompare-walker walk-run-pair
  lf-mcompare-walker lf-mcompare-site lf-diag-walk ;

\ Audit both roots completely, left first, with the walk's fuel; a failed
\ audit leaves no fuel. lf-cterm-check fails only as invalid, exhausted or
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
