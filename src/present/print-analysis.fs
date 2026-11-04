\ The questions Lean's delaborator asks before it prints a binder or an
\ application, answered on the term store: are two binder domains the same
\ term (for grouping {A B : Prop}), is a term a proposition (for ∀ against
\ →), and which arguments of an application are explicit (hidden implicit
\ arguments). Untrusted presentation code; every answer only chooses a
\ spelling. Requires print-levels.fs. No state of its own: comparisons
\ count their binder depth in the print's frames record.

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

\ Structural equality of levels (Lean's Level ==).
defer lf-pp-lsame-visit ( l1 l2 -- outcome )
: lf-pp-lsame-call ( l1 l2 -- outcome ) ['] lf-pp-lsame-visit lf-pp-call ;
: lf-pp-lfirsts ( l1 l2 -- f1 f2 ) lf-level-first@ swap lf-level-first@ swap ;
: lf-pp-lseconds ( l1 l2 -- s1 s2 ) lf-level-second@ swap lf-level-second@ swap ;
: lf-pp-lsame-both ( l1 l2 -- outcome )
  2dup lf-pp-lfirsts lf-pp-lsame-call ok-then2? if lf-pp-lseconds lf-pp-lsame-call then ;
\ A CASE with one short arm per level tag (six lines, kept together so the
\ tags read as a table); an unknown tag is invalid.
: lf-pp-lsame-by ( l1 l2 tag -- outcome )
  case lf-level-tag-zero of 2drop outcome-ok endof
    lf-level-tag-param of lf-pp-lfirsts = lf-pp-equal endof
    lf-level-tag-succ of lf-pp-lfirsts lf-pp-lsame-call endof
    lf-level-tag-max of lf-pp-lsame-both endof
    lf-level-tag-imax of lf-pp-lsame-both endof
    >r 2drop outcome-invalid r> endcase ;
: lf-pp-lsame ( l1 l2 -- outcome )
  2dup lf-level-pair-valid? 0= if 2drop outcome-invalid exit then
  over lf-level-tag@ over lf-level-tag@ <> if 2drop outcome-rejected exit then
  over lf-level-tag@ lf-pp-lsame-by ;
' lf-pp-lsame is lf-pp-lsame-visit

\ Constants: name and universe arguments of a constant node.
: lf-pp-cref ( term -- index identity ) dup lf-term-first@ swap lf-term-second@ ;
: lf-pp-const-name ( term -- name true | false )
  lf-pp-cref lf-cref-read if 2drop true else false then ;
: lf-pp-const-levels ( term -- addr count true | false ) lf-pp-cref lf-cref-levels ;
: lf-pp-level-at ( addr i -- level ) lf-cref-pair@ drop ;
: lf-pp-lsame-list ( addr1 addr2 n -- outcome )
  0 ?do over i lf-pp-level-at over i lf-pp-level-at lf-pp-lsame-call
    ok-then2? 0= if unloop exit then loop 2drop outcome-ok ;
: lf-pp-names-same ( a b -- outcome )
  lf-pp-const-name 0= if drop-invalid exit then
  swap lf-pp-const-name 0= if drop-invalid exit then = lf-pp-equal ;
: lf-pp-levels-same ( a b -- outcome )
  lf-pp-const-levels 0= if drop-invalid exit then
  rot lf-pp-const-levels 0= if 2drop outcome-invalid exit then
  rot over <> if 2drop drop outcome-rejected exit then lf-pp-lsame-list ;
: lf-pp-const-same ( a b -- outcome )
  2dup lf-pp-names-same ok-then2? if lf-pp-levels-same then ;

\ Structural equality of b with a lifted over one binder: the test of
\ Lean's shouldGroupWithNext, which compares the next binder's domain with
\ this one's. Binder names and kinds inside are ignored, as Lean's Expr ==
\ ignores them. The binder depth inside a and b is the frames record's
\ context cell; variable i of a at depth d matches i in b when i < d and
\ i + 1 otherwise.
defer lf-pp-same-visit ( a b -- outcome )
: lf-pp-tag-known? ( tag -- flag ) lf-tag-sort lf-tag-constant between? ;
: lf-pp-same-call ( a b -- outcome ) ['] lf-pp-same-visit lf-pp-call ;
: lf-pp-cmp-depth ( -- addr ) lf-pjob lf-pjob-context ;
: lf-pp-var-same? ( i j -- flag ) over lf-pp-cmp-depth @ < if = else swap 1+ = then ;
: lf-pp-firsts ( a b -- a1 b1 ) lf-term-first@ swap lf-term-first@ swap ;
: lf-pp-seconds ( a b -- a2 b2 ) lf-term-second@ swap lf-term-second@ swap ;
: lf-pp-under ( a b -- outcome )
  1 lf-pp-cmp-depth +! lf-pp-same-call -1 lf-pp-cmp-depth +! ;
: lf-pp-same-app ( a b -- outcome )
  2dup lf-pp-firsts lf-pp-same-call ok-then2? if lf-pp-seconds lf-pp-same-call then ;
: lf-pp-same-binder ( a b -- outcome )
  2dup lf-pp-firsts lf-pp-same-call ok-then2? if lf-pp-seconds lf-pp-under then ;
\ A CASE with one short arm per term tag (six lines, kept together so the
\ tags read as a table); λ and Π, the remaining known tags, compare alike.
: lf-pp-same-by ( a b tag -- outcome )
  case lf-tag-sort of lf-pp-firsts = lf-pp-equal endof
    lf-tag-bvar of lf-pp-firsts lf-pp-var-same? lf-pp-equal endof
    lf-tag-symbolic-sort of lf-pp-firsts lf-pp-lsame-call endof
    lf-tag-constant of lf-pp-const-same endof
    lf-tag-app of lf-pp-same-app endof
    >r lf-pp-same-binder r> endcase ;
: lf-pp-same ( a b -- outcome )
  2dup lf-term-pair-valid? 0= if 2drop outcome-invalid exit then
  over lf-term-tag@ over lf-term-tag@ <> if 2drop outcome-rejected exit then
  over lf-term-tag@ dup lf-pp-tag-known?
  if lf-pp-same-by else drop 2drop outcome-invalid then ;
' lf-pp-same is lf-pp-same-visit
: lf-pp-same-domain? ( a b -- flag outcome ) 0 lf-pp-cmp-depth ! lf-pp-same-call
  lf-pp-decided ;

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
