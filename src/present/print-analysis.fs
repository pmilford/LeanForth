\ The questions Lean's delaborator asks before it prints a binder or an
\ application, answered on the term store: are two binder domains the same
\ term (for grouping {A B : Prop}), is a term a proposition (for ∀ against
\ →), and which arguments of an application are explicit (hidden implicit
\ arguments). Untrusted presentation code; every answer only chooses a
\ spelling. Requires print-levels.fs. No state of its own: a comparison
\ is a visit of the print's frames (print-job.fs), counting its binder
\ depth in their context cell; it runs as a loop of its own from inside
\ the step that asks for it (lf-pp-run), and asks for no other
\ comparison, so that nests once on the host's stacks whatever the depth.

require ./print-levels.fs

\ A node's tag when it is a valid term; a term with a given tag.
: lf-pp-tag ( term -- tag true | false ) lf-term-read if 2drop true else false then ;
: lf-pp-is? ( term tag -- flag ) swap lf-pp-tag if = else drop false then ;
\ Unchecked: k bodies down a chain, k functions down a spine. A negative
\ k (only after a forbidden reset from a sink) counts as none.
: lf-pp-bodies ( node k -- node' ) 0 max 0 ?do lf-term-second@ loop ;
: lf-pp-fns ( node k -- node' ) 0 ?do lf-term-first@ loop ;
\ Comparisons answer inside the printer with ok for equal and rejected for
\ different; rejected here is an answer, never a verdict, and
\ lf-pp-decided turns it into a false flag beside ok. Any other outcome is
\ a failure that ends the print.
: lf-pp-equal ( flag -- outcome ) if outcome-ok else outcome-rejected then ;
: lf-pp-decided ( outcome -- flag outcome )
  dup ok? if true swap exit then lf-pp-hit? >r drop false r> ;

\ Structural equality of levels (Lean's Level ==). Both operands of a max
\ or imax compare, the pair waiting while the first ones do.
defer lf-pp-lsame-step ( l1 l2 frames -- ... frames next )
: lf-pp-lsame-call ( l1 l2 frames cont -- ... frames next )
  ['] lf-pp-lsame-step lf-pp-call ;
: lf-pp-lfirsts ( l1 l2 -- f1 f2 ) lf-level-first@ swap lf-level-first@ swap ;
: lf-pp-lseconds ( l1 l2 -- s1 s2 ) lf-level-second@ swap lf-level-second@ swap ;
: lf-pp-lsame-second ( outcome frames -- ... frames next )
  >r r@ lf-pp-restore2 rot ok-then2?
  if lf-pp-lseconds r> ['] frame-return lf-pp-lsame-call else r> 0 then ;
: lf-pp-lsame-both ( l1 l2 frames -- ... frames next )
  >r 2dup r@ lf-pp-save2 lf-pp-lfirsts r> ['] lf-pp-lsame-second lf-pp-lsame-call ;
: lf-pp-lsame-zero ( l1 l2 frames -- outcome frames 0 ) >r 2drop outcome-ok r> 0 ;
: lf-pp-lsame-param ( l1 l2 frames -- outcome frames 0 )
  >r lf-pp-lfirsts = lf-pp-equal r> 0 ;
: lf-pp-lsame-succ ( l1 l2 frames -- ... frames next )
  >r lf-pp-lfirsts r> ['] frame-return lf-pp-lsame-call ;
\ The step for a level tag: a CASE with one short arm per tag (kept
\ together so the tags read as a table); an unknown tag is invalid.
: lf-pp-lsame-by ( tag -- xt )
  case lf-level-tag-zero of ['] lf-pp-lsame-zero endof
    lf-level-tag-param of ['] lf-pp-lsame-param endof
    lf-level-tag-succ of ['] lf-pp-lsame-succ endof
    lf-level-tag-max of ['] lf-pp-lsame-both endof
    lf-level-tag-imax of ['] lf-pp-lsame-both endof
    ['] lf-pp-invalid-step swap endcase ;
: lf-pp-lsame ( l1 l2 frames -- ... frames next )
  >r 2dup lf-level-pair-valid? 0= if 2drop outcome-invalid r> 0 exit then
  over lf-level-tag@ over lf-level-tag@ <> if 2drop outcome-rejected r> 0 exit then
  over lf-level-tag@ lf-pp-lsame-by r> swap execute ;
' lf-pp-lsame is lf-pp-lsame-step

\ Constants: name and universe arguments of a constant node.
: lf-pp-cref ( term -- index identity ) lf-term-first@ dup lf-cref-current ;
: lf-pp-const-name ( term -- name true | false )
  lf-pp-cref lf-cref-read if 2drop true else false then ;
: lf-pp-const-levels ( term -- addr count true | false ) lf-pp-cref lf-cref-levels ;
: lf-pp-level-at ( addr i -- level ) lf-cref-pair@ drop ;
\ The pairs of levels from i up to n, addr1's first, a part of a visit:
\ each pair compares after the one before it, the addresses, n and the
\ next index waiting meanwhile.
defer lf-pp-lsame-rest ( addr1 addr2 n i frames -- ... frames next )
: lf-pp-lsame-back ( outcome frames -- ... frames next )
  4 lf-pp-failed? if 0 exit then
  >r r@ lf-pp-restore2 r@ lf-pp-restore2 r> lf-pp-lsame-rest ;
: lf-pp-lsame-pair ( addr1 addr2 i -- l1 l2 ) tuck lf-pp-level-at >r lf-pp-level-at r> ;
: lf-pp-lsame-from ( addr1 addr2 n i frames -- ... frames next )
  >r 2dup > 0= if 2drop 2drop outcome-ok r> 0 exit then
  2dup 1+ r@ lf-pp-save2 nip -rot 2dup r@ lf-pp-save2 rot lf-pp-lsame-pair
  r> ['] lf-pp-lsame-back lf-pp-lsame-call ;
' lf-pp-lsame-from is lf-pp-lsame-rest
: lf-pp-lsame-list ( addr1 addr2 n frames cont -- ... frames next )
  over frame-save 0 swap lf-pp-lsame-rest ;
: lf-pp-names-same ( a b -- outcome )
  lf-pp-const-name 0= if drop-invalid exit then
  swap lf-pp-const-name 0= if drop-invalid exit then = lf-pp-equal ;
: lf-pp-levels-same ( a b frames -- ... frames next )
  >r lf-pp-const-levels 0= if drop-invalid r> 0 exit then
  rot lf-pp-const-levels 0= if 2drop outcome-invalid r> 0 exit then
  rot over <> if 2drop drop outcome-rejected r> 0 exit then
  r> ['] frame-return lf-pp-lsame-list ;
: lf-pp-const-same ( a b frames -- ... frames next )
  >r 2dup lf-pp-names-same ok-then2? if r> lf-pp-levels-same else r> 0 then ;

\ Structural equality of b with a lifted over one binder: the test of
\ Lean's shouldGroupWithNext, which compares the next binder's domain with
\ this one's. Binder names and kinds inside are ignored, as Lean's Expr ==
\ ignores them. The binder depth inside a and b is the frames' context
\ cell; variable i of a at depth d matches i in b when i < d and i + 1
\ otherwise. Both children compare, the pair waiting while the first ones
\ do; a binder's second ones one binder deeper (frame-up restores it).
defer lf-pp-same-step ( a b frames -- ... frames next )
: lf-pp-tag-known? ( tag -- flag ) lf-tag-sort lf-tag-constant between? ;
: lf-pp-same-call ( a b frames cont -- ... frames next ) ['] lf-pp-same-step lf-pp-call ;
: lf-pp-cmp-depth ( -- addr ) lf-pp-frames frame-context ;
: lf-pp-var-same? ( i j -- flag ) over lf-pp-cmp-depth @ < if = else swap 1+ = then ;
: lf-pp-firsts ( a b -- a1 b1 ) lf-term-first@ swap lf-term-first@ swap ;
: lf-pp-seconds ( a b -- a2 b2 ) lf-term-second@ swap lf-term-second@ swap ;
: lf-pp-same-second ( outcome frames -- ... frames next )
  >r r@ lf-pp-restore2 rot ok-then2?
  if lf-pp-seconds r> ['] frame-return lf-pp-same-call else r> 0 then ;
\ (frame-up works on any results below the frames: it touches only them.)
: lf-pp-same-body ( outcome frames -- ... frames next )
  >r r@ lf-pp-restore2 rot ok-then2? 0= if r> 0 exit then
  lf-pp-seconds 1 r@ frame-context+! r> ['] frame-up lf-pp-same-call ;
: lf-pp-same-pair ( a b frames cont -- ... frames next )
  2>r 2dup 2r@ drop lf-pp-save2 lf-pp-firsts 2r> lf-pp-same-call ;
: lf-pp-same-app ( a b frames -- ... frames next ) ['] lf-pp-same-second lf-pp-same-pair ;
: lf-pp-same-binder ( a b frames -- ... frames next )
  ['] lf-pp-same-body lf-pp-same-pair ;
: lf-pp-same-sort ( a b frames -- outcome frames 0 ) >r lf-pp-firsts = lf-pp-equal r> 0 ;
: lf-pp-same-bvar ( a b frames -- outcome frames 0 )
  >r lf-pp-firsts lf-pp-var-same? lf-pp-equal r> 0 ;
: lf-pp-same-levels ( a b frames -- ... frames next )
  >r lf-pp-firsts r> ['] frame-return lf-pp-lsame-call ;
\ The step for a term tag: a CASE with one short arm per tag (kept
\ together so the tags read as a table); λ and Π, the remaining known
\ tags, compare alike.
: lf-pp-same-by ( tag -- xt )
  case lf-tag-sort of ['] lf-pp-same-sort endof
    lf-tag-bvar of ['] lf-pp-same-bvar endof
    lf-tag-symbolic-sort of ['] lf-pp-same-levels endof
    lf-tag-constant of ['] lf-pp-const-same endof
    lf-tag-app of ['] lf-pp-same-app endof
    ['] lf-pp-same-binder swap endcase ;
: lf-pp-same ( a b frames -- ... frames next )
  >r 2dup lf-term-pair-valid? 0= if 2drop outcome-invalid r> 0 exit then
  over lf-term-tag@ over lf-term-tag@ <> if 2drop outcome-rejected r> 0 exit then
  over lf-term-tag@ dup lf-pp-tag-known? 0= if drop 2drop outcome-invalid r> 0 exit then
  lf-pp-same-by r> swap execute ;
' lf-pp-same is lf-pp-same-step
: lf-pp-same-domain? ( a b -- flag outcome )
  0 lf-pp-cmp-depth ! ['] lf-pp-same-step lf-pp-run lf-pp-decided ;

\ Lean's isPropQuick, the test the delaborator uses to print a Pi as ∀:
\ after the Pi binders, the body is a variable, or a variable applied to n
\ arguments, whose type is n arrows ending in a Sort whose level is always
\ zero. A constant or any other head counts as not a proposition: Lean
\ would then infer the type, which this printer cannot (see the user
\ guide; lf-print-statement says so for a theorem's statement).
: lf-pp-var-type ( i -- type true | false )
  dup 0 lf-pp-depth within if lf-pp-entry lf-pbind-domain @ true else drop false then ;
: lf-pp-chain-step ( node k tag -- node' k' true | node k false )
  >r over r> lf-pp-is? 0= if false exit then swap lf-term-second@ swap 1+ true ;
: lf-pp-chain ( node tag -- end k outcome )
  0 swap begin lf-pp-spend 0= if drop outcome-exhausted exit then
    >r r@ lf-pp-chain-step r> swap 0= until drop outcome-ok ;
: lf-pp-spine-step ( node n -- node' n' true | node n false )
  over lf-tag-app lf-pp-is? if swap lf-term-first@ swap 1+ true else false then ;
: lf-pp-spine ( term -- head n outcome )
  0 begin lf-pp-spend 0=
  if outcome-exhausted exit then lf-pp-spine-step 0= until outcome-ok ;
\ The type of variable i at the end of k Pi binders starting at chain.
: lf-pp-chain-var ( chain k i -- type true | false )
  2dup > if - 1- lf-pp-bodies lf-term-first@ true else swap - nip lf-pp-var-type then ;
: lf-pp-arrows ( type n -- type' true | false )
  0 ?do dup lf-tag-pi lf-pp-is? 0=
  if drop false unloop exit then lf-term-second@ loop true ;
: lf-pp-prop-sort? ( type -- flag outcome )
  dup lf-pp-tag 0= if drop false outcome-ok exit then
  case lf-tag-sort of lf-term-first@ 0= outcome-ok endof
    lf-tag-symbolic-sort of lf-term-first@ lf-pp-always-zero? endof
    >r drop false outcome-ok r> endcase ;
: lf-pp-arrow-prop? ( type n -- flag outcome )
  lf-pp-arrows if lf-pp-prop-sort? else false outcome-ok then ;
: lf-pp-head-type ( chain k head -- type true | false )
  dup lf-tag-bvar lf-pp-is? if lf-term-first@ lf-pp-chain-var else drop 2drop false then ;
: lf-pp-end-prop? ( chain k end -- flag outcome )
  lf-pp-spine dup ok? 0= if >r 2drop 2drop false r> exit then drop
  >r lf-pp-head-type if r> lf-pp-arrow-prop? else r> drop false outcome-ok then ;
: lf-pp-prop? ( term -- flag outcome )
  dup lf-tag-pi lf-pp-chain dup ok? 0= if >r 2drop drop false r> exit then drop
  swap lf-pp-end-prop? ;

\ Parameter kinds of an application's head (Lean's getParamKinds, without
\ unfolding): the binder kinds along its type, which is the binder's
\ domain for a variable and the declared type (lf-pres-declare) for a
\ constant; a fun's own binders. A head of unknown type has none (0 0).
: lf-pp-kind ( node -- kind ) lf-pres-binder@ if nip else lf-binder-default then ;
: lf-pp-const-type ( head -- type true | false )
  lf-pp-const-name if lf-pres-type@ else false then ;
: lf-pp-known ( type true | false -- chain tag ) if lf-tag-pi else 0 0 then ;
\ A CASE with one arm per kind of head (six lines, read as a table).
: lf-pp-params ( head -- chain tag )
  dup lf-pp-tag 0= if drop 0 0 exit then
  case lf-tag-bvar of lf-term-first@ lf-pp-var-type lf-pp-known endof
    lf-tag-constant of lf-pp-const-type lf-pp-known endof
    lf-tag-lam of lf-tag-lam endof
    >r drop 0 0 r> endcase ;
\ Binders of the chain, at most limit of them.
: lf-pp-avail ( chain tag limit -- n )
  dup >r 0 ?do 2dup lf-pp-is? 0= if 2drop i unloop r> drop exit then
    swap lf-term-second@ swap loop 2drop r> ;
: lf-pp-kind-at ( chain i -- kind ) lf-pp-bodies lf-pp-kind ;

\ Lean's useAppExplicit: show every argument when the head's parameters
\ are unknown or too few, or when the parameter after the last argument is
\ implicit or instance implicit; otherwise show only explicit arguments.
\ Unchecked: app's spine was read by lf-pp-spine.
: lf-pp-head ( app -- head n ) 0 begin over lf-term-tag@ lf-tag-app = while swap
  lf-term-first@ swap 1+ repeat ;
: lf-pp-loud? ( kind -- flag ) dup lf-binder-implicit = swap lf-binder-instance = or ;
: lf-pp-explicit? ( head n -- flag )
  >r lf-pp-params over swap r@ 1+ lf-pp-avail
  dup r@ < if 2drop r> drop true exit then
  r@ > if r> lf-pp-kind-at lf-pp-loud? else r> 2drop false then ;
: lf-pp-visible? ( app i -- flag )
  swap lf-pp-head 2dup lf-pp-explicit? if 2drop drop true exit then
  drop lf-pp-params drop swap lf-pp-kind-at lf-binder-default = ;
: lf-pp-arg-at ( app i -- arg ) over lf-pp-head nip 1- swap - lf-pp-fns lf-term-second@ ;
: lf-pp-shown# ( app -- count )
  0 over lf-pp-head nip 0 ?do over i lf-pp-visible? if 1+ then loop nip ;
: lf-pp-last ( app -- i )
  -1 over lf-pp-head nip 0 ?do over i lf-pp-visible? if drop i then loop nip ;
\ Lean's needsExplicit: @ goes before a constant or variable head shown
\ with all its arguments, except a constant without universe arguments
\ whose parameters are unknown.
: lf-pp-atom-head? ( head -- flag )
  dup lf-tag-constant lf-pp-is? swap lf-tag-bvar lf-pp-is? or ;
: lf-pp-unknown? ( head -- flag ) lf-pp-params 1 lf-pp-avail 0= ;
: lf-pp-bare-const? ( head -- flag )
  dup lf-tag-constant lf-pp-is?
  if lf-pp-const-levels if nip 0= else false then else drop false then ;
: lf-pp-lcnf? ( head n -- flag ) 0> over lf-pp-unknown? and swap lf-pp-bare-const? and ;
: lf-pp-at? ( head n -- flag )
  2dup lf-pp-explicit? >r over lf-pp-atom-head? r> and
  if lf-pp-lcnf? 0= else 2drop false then ;
