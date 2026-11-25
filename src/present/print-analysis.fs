\ The questions Lean's delaborator asks before it prints a binder or an
\ application, answered on the term store: are two binder domains the same
\ term (for grouping {A B : Prop}), is a term a proposition (for ∀ against
\ →), and which arguments of an application are explicit (hidden implicit
\ arguments). Untrusted presentation code; every answer only chooses a
\ spelling. Requires print-levels.fs and lib/find.fs. No state of its
\ own: a comparison is a visit of the print's frames (print-job.fs),
\ counting its binder depth in their context cell; it runs as a loop of
\ its own from inside the step that asks for it (lf-pp-run), and asks
\ for no other comparison, so that nests once on the host's stacks
\ whatever the depth.

require ../lib/find.fs
require ../core/terms.fs
require ./print-levels.fs
require ../core/literals.fs
require ../core/string-literals.fs
require ../core/projections.fs
require ../core/name-equal.fs
require ../core/unsupported-forms.fs

\ A node's tag when it is a valid term; a term with a given tag.
: lf-pp-tag ( term -- tag true | false ) lf-term-read if 2drop true else false then ;
: lf-pp-is? ( term tag -- flag ) swap lf-pp-tag if = else drop false then ;
\ An application, or a projection, which prints as its leaf applied to
\ the projected term (core/projections.fs): Prod.1 p for Lean's p.1.
lf-tag-app lf-tag-projection 2 lf-tags constant lf-pp-app-tags
: lf-pp-app-tag? ( tag -- flag ) lf-pp-app-tags lf-tag-in? ;
: lf-pp-applied? ( term -- flag ) lf-pp-tag if lf-pp-app-tag? else false then ;
\ Unchecked: k bodies down a chain. A negative k (only after a forbidden
\ reset from a sink) counts as none.
: lf-pp-bodies ( node k -- node' ) 0 max 0 ?do lf-term-second@ loop ;
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
\ After the first parts compared equal: the second parts, that seconds
\ ( x1 x2 -- s1 s2 ) reads, compared by call ( s1 s2 frames cont -- ...
\ frames next ); the term comparison below uses it too.
: lf-pp-seconds-then ( outcome frames seconds call -- ... frames next )
  2swap >r r@ lf-pp-restore2 rot ok-then2?
  if 2swap >r execute r> r> swap ['] frame-return swap execute else nip nip r> 0 then ;
: lf-pp-lsame-second ( outcome frames -- ... frames next )
  ['] lf-pp-lseconds ['] lf-pp-lsame-call lf-pp-seconds-then ;
: lf-pp-lsame-both ( l1 l2 frames -- ... frames next )
  >r 2dup r@ lf-pp-save2 lf-pp-lfirsts r> ['] lf-pp-lsame-second lf-pp-lsame-call ;
: lf-pp-lsame-zero ( l1 l2 frames -- outcome frames 0 ) >r 2drop outcome-ok r> 0 ;
\ (lf-pp-firsts-equal compares the first fields that firsts ( x1 x2 -- f1
\ f2 ) reads; lf-pp-firsts-levels compares them as levels; both serve the
\ term comparison below too.)
: lf-pp-firsts-equal ( x1 x2 frames firsts -- outcome frames 0 )
  swap >r execute = lf-pp-equal r> 0 ;
: lf-pp-firsts-levels ( x1 x2 frames firsts -- ... frames next )
  swap >r execute r> ['] frame-return lf-pp-lsame-call ;
: lf-pp-lsame-param ( l1 l2 frames -- outcome frames 0 )
  ['] lf-pp-lfirsts lf-pp-firsts-equal ;
: lf-pp-lsame-succ ( l1 l2 frames -- ... frames next )
  ['] lf-pp-lfirsts lf-pp-firsts-levels ;
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
\ Every tag of a term but the importer's unsupported leaves.
: lf-pp-tag-known? ( tag -- flag )
  dup lf-tag-sort lf-tag-mvar between? swap lf-tag-unsupported <> and ;
: lf-pp-same-call ( a b frames cont -- ... frames next ) ['] lf-pp-same-step lf-pp-call ;
: lf-pp-cmp-depth ( -- addr ) lf-pp-frames frame-context ;
: lf-pp-var-same? ( i j -- flag ) over lf-pp-cmp-depth @ < if = else swap 1+ = then ;
: lf-pp-firsts ( a b -- a1 b1 ) lf-term-first@ swap lf-term-first@ swap ;
: lf-pp-seconds ( a b -- a2 b2 ) lf-term-second@ swap lf-term-second@ swap ;
: lf-pp-same-second ( outcome frames -- ... frames next )
  ['] lf-pp-seconds ['] lf-pp-same-call lf-pp-seconds-then ;
\ (frame-up works on any results below the frames: it touches only them.)
: lf-pp-same-body ( outcome frames -- ... frames next )
  >r r@ lf-pp-restore2 rot ok-then2? 0= if r> 0 exit then
  lf-pp-seconds 1 r@ frame-context+! r> ['] frame-up lf-pp-same-call ;
: lf-pp-same-pair ( a b frames cont -- ... frames next )
  2>r 2dup 2r@ drop lf-pp-save2 lf-pp-firsts 2r> lf-pp-same-call ;
: lf-pp-same-app ( a b frames -- ... frames next ) ['] lf-pp-same-second lf-pp-same-pair ;
: lf-pp-same-binder ( a b frames -- ... frames next )
  ['] lf-pp-same-body lf-pp-same-pair ;
: lf-pp-same-sort ( a b frames -- outcome frames 0 ) ['] lf-pp-firsts lf-pp-firsts-equal ;
: lf-pp-same-bvar ( a b frames -- outcome frames 0 )
  >r lf-pp-firsts lf-pp-var-same? lf-pp-equal r> 0 ;
: lf-pp-same-levels ( a b frames -- ... frames next )
  ['] lf-pp-firsts lf-pp-firsts-levels ;
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
\ A free variable or metavariable is the same as itself only; literals
\ and projection leaves by their contents (Lean's Literal and proj ==);
\ a let and a projection part by part, as an application (a let and a
\ have, of different tags, differ here, where Lean's == ignores nonDep).
: lf-pp-proj= ( a b -- flag )
  2dup lf-proj-name swap lf-proj-name lf-name-same?
  if lf-proj-idx swap lf-proj-idx = else 2drop false then ;
\ Two leaves of one tag (a CASE table): by contents or as nodes. The
\ step finds its frames again (print-job.fs: always the printer's own).
: lf-pp-leaf-test ( tag -- xt )
  case lf-tag-lit of ['] lf-lit-same? endof  lf-tag-str of ['] lf-str-same? endof
    lf-tag-proj of ['] lf-pp-proj= endof  ['] = swap endcase ;
: lf-pp-leaf= ( a b -- flag ) over lf-term-tag@ lf-pp-leaf-test execute ;
: lf-pp-same-leaf ( a b frames -- outcome frames 0 )
  drop lf-pp-leaf= lf-pp-equal lf-pp-frames 0 ;
lf-tag-fvar lf-tag-mvar lf-tag-lit lf-tag-str lf-tag-proj 5 lf-tags
constant lf-pp-leaf-kinds
lf-tag-projection lf-tag-let lf-tag-let-nondep 3 lf-tags constant lf-pp-pair-kinds
: lf-pp-leaf-kind? ( tag -- flag ) lf-pp-leaf-kinds lf-tag-in? ;
: lf-pp-pair-kind? ( tag -- flag ) lf-pp-pair-kinds lf-tag-in? ;
: lf-pp-same-kind ( tag -- xt )
  dup lf-pp-leaf-kind? if drop ['] lf-pp-same-leaf exit then
  dup lf-pp-pair-kind? if drop ['] lf-pp-same-app else lf-pp-same-by then ;
: lf-pp-same ( a b frames -- ... frames next )
  >r 2dup lf-term-pair-valid? 0= if 2drop outcome-invalid r> 0 exit then
  over lf-term-tag@ over lf-term-tag@ <> if 2drop outcome-rejected r> 0 exit then
  over lf-term-tag@ dup lf-pp-tag-known? 0= if drop 2drop outcome-invalid r> 0 exit then
  lf-pp-same-kind r> swap execute ;
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
  over lf-pp-applied? if swap lf-term-first@ swap 1+ true else false then ;
: lf-pp-spine ( term -- head n outcome ) ['] lf-pp-spine-step lf-pp-fuelled ;
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
\ A free variable's type is its local declaration's (Lean's isPropQuick
\ reads it too); one that is not live has none.
: lf-pp-fvar-type ( fvar -- type true | false )
  dup lf-fvar-live? if lf-fvar-type true else drop false then ;
: lf-pp-bvar-type ( chain k head -- type true | false )
  dup lf-tag-bvar lf-pp-is? if lf-term-first@ lf-pp-chain-var else drop 2drop false then ;
: lf-pp-head-type ( chain k head -- type true | false )
  dup lf-tag-fvar lf-pp-is? if nip nip lf-pp-fvar-type else lf-pp-bvar-type then ;
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
\ A CASE with one arm per kind of head (six lines, read as a table); a
\ free variable's type is its local declaration's.
: lf-pp-tag-params ( head -- chain tag )
  dup lf-pp-tag 0= if drop 0 0 exit then
  case lf-tag-bvar of lf-term-first@ lf-pp-var-type lf-pp-known endof
    lf-tag-constant of lf-pp-const-type lf-pp-known endof
    lf-tag-lam of lf-tag-lam endof
    >r drop 0 0 r> endcase ;
: lf-pp-params ( head -- chain tag )
  dup lf-tag-fvar lf-pp-is? if lf-pp-fvar-type lf-pp-known else lf-pp-tag-params then ;
\ Binders of the chain, at most limit of them.
: lf-pp-avail ( chain tag limit -- n )
  dup >r 0 ?do 2dup lf-pp-is? 0= if 2drop i unloop r> drop exit then
    swap lf-term-second@ swap loop 2drop r> ;
: lf-pp-kind-at ( chain i -- kind ) lf-pp-bodies lf-pp-kind ;

\ Lean's useAppExplicit: show every argument when the head's parameters
\ are unknown or too few, or when the parameter after the last argument is
\ implicit or instance implicit; otherwise show only explicit arguments.
\ Unchecked: app's spine was read by lf-pp-spine.
: lf-pp-head ( app -- head n ) 0 begin over lf-term-tag@ lf-pp-app-tag? while swap
  lf-term-first@ swap 1+ repeat ;
: lf-pp-loud? ( kind -- flag ) lf-binder-implicit lf-binder-instance one-of2? ;
: lf-pp-explicit? ( head n -- flag )
  >r lf-pp-params over swap r@ 1+ lf-pp-avail
  dup r@ < if 2drop r> drop true exit then
  r@ > if r> lf-pp-kind-at lf-pp-loud? else r> 2drop false then ;
: lf-pp-visible? ( app i -- flag )
  swap lf-pp-head 2dup lf-pp-explicit? if 2drop drop true exit then
  drop lf-pp-params drop swap lf-pp-kind-at lf-binder-default = ;
: lf-pp-arg-at ( app i -- arg ) over lf-pp-head nip swap lf-term-arg ;
\ How many arguments are shown; the last one shown, else -1.
: lf-pp-arg-shown? ( app i -- app flag ) over swap lf-pp-visible? ;
: lf-pp-shown# ( app -- count ) dup lf-pp-head nip ['] lf-pp-arg-shown? count-index ;
: lf-pp-last ( app -- i )
  -1 swap dup lf-pp-head nip ['] lf-pp-arg-shown? find-last-index if nip then ;
\ Lean's needsExplicit: @ goes before a constant or variable head shown
\ with all its arguments, except a constant without universe arguments
\ whose parameters are unknown.
: lf-pp-atom-head? ( head -- flag )
  dup lf-tag-constant lf-pp-is? over lf-tag-bvar lf-pp-is? or
  swap lf-tag-fvar lf-pp-is? or ;
: lf-pp-unknown? ( head -- flag ) lf-pp-params 1 lf-pp-avail 0= ;
: lf-pp-bare-const? ( head -- flag )
  dup lf-tag-constant lf-pp-is?
  if lf-pp-const-levels if nip 0= else false then else drop false then ;
: lf-pp-lcnf? ( head n -- flag ) 0> over lf-pp-unknown? and swap lf-pp-bare-const? and ;
: lf-pp-at? ( head n -- flag )
  2dup lf-pp-explicit? >r over lf-pp-atom-head? r> and
  if lf-pp-lcnf? 0= else 2drop false then ;
