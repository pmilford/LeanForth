\ Weak head normal form as Lean's kernel computes it (ADR 0014 Q4, Q5,
\ Q8; plan task 4.2.2c): ports of whnf_core (type_checker.cpp 468-551),
\ whnf (706-743), is_delta (555-563) and unfold_definition (565-602) at
\ the referee commit eb6cafb7 (ADR 0014, Reproduction). [kernel] code:
\ experimental, not through the review gate, not independently audited.
\
\ whnf_core reduces without unfolding (Lean's order). Sorts, Pis,
\ lambdas, constants, bound variables and free variables that are no let
\ variables are normal (473-488); a let variable is its value, reduced
\ (zeta, whnf_fvar 409-417; none occur before plan task 4.2.3). An
\ application's head is reduced first (514): a lambda head takes as many
\ arguments as it has leading lambdas, all at once (Lean's instantiate,
\ mixed-open.fs), the others are applied again and the result is reduced
\ (beta, 515-524); a head that did not change and is no lambda goes to
\ the iota hook below (reduce_recursor, 393-407, 525-536); any other head
\ is applied to the arguments again and the result reduced (537-539).
\ whnf repeats whnf_core and one delta step while the head unfolds
\ (729-742): is_delta holds for a definition or a theorem that the check's
\ snapshot holds as usable, given as many universe arguments as it has
\ parameters (ADR 0014 G5: theorems unfold; opaque declarations, axioms,
\ inductive types, constructors and recursors never); its value with
\ those arguments for its parameters (instantiate_value_lparams,
\ instantiate.cpp 256-264: the stored value itself when there are none)
\ is applied to the arguments again. Bound variables, Sorts, Pis and free
\ variables that are no let variables are returned at once (708-722).
\
\ Where LeanForth does not decide yet, the answer is unknown, never a
\ guess (ADR 0014 Q8; owner rule: a temporary gap, named here):
\ - K7: before a delta step, where Lean's reduce_nat (672-703) would look
\   -- Nat.succ with one argument, or one of its fourteen binary Nat
\   operations with two, matched by name and without universe arguments --
\   unknown, diagnostic 82 (plan task 5.2.3, literals);
\ - iota: the default hook answers unknown for a recursor at the head,
\   diagnostic 81 (plan task 5.2.1b, which brings recursor reduction);
\ - outside a check of the checked environment (lf-mixed-infer, the
\   probe and lf-mixed-convert's tables, whose constants are the
\   signature index's), a constant at the head of whnf may have a value:
\   unknown (K1, diagnostic 64); such constants are never recursors;
\ - in a check, a constant whose lookup is undecided or unsupported (K5)
\   gives the lookup's outcome.
\ Not yet as Lean (no verdict depends on them): the caches m_whnf_core,
\ m_whnf and m_unfold, and the unfold counts of kernel diagnostics (plan
\ tasks 4.2.7, 4.3.1); projections, literals and let terms are
\ unsupported forms (U2) that never reach these passes; the derivation
\ log records nothing new here (plan task 4.2.2e).
\
\ Passes. Every visit is a chain of steps on a frames record that the
\ caller gives (lib/frame.fs), so the passes have no depth limit (plan
\ task 6.2.0): lf-whnf-call and lf-whnf-core-call ask for the visit of a
\ node ( node frames cont -- ... frames next ), cont getting ( node'
\ outcome frames ); lf-whnf-on and lf-whnf-core-on run one visit to its
\ end from a word ( node frames -- node' outcome ), as a loop of its own
\ on the cells in use, so a step of another pass on the same record may
\ use them (mixed-infer.fs does). Every visit, and every further
\ reduction step inside one, costs one unit of the frames' fuel; the
\ substitutions they run (mixed-open.fs, mixed-level-substitute.fs) are
\ paid from it too. Out of fuel is exhausted, a stack or store the heap
\ cannot grow full; neither is ever a result. Inputs are audited terms
\ whose free variables are live (as every term inference and conversion
\ give). Lean's kernel reduces closed terms only, but ADR 0011's analysis
\ and check-block.fs compare terms read under binders they did not open:
\ a beta argument with a loose bound variable is lifted as Lean's
\ instantiate lifts it (lf-whnf-beta); cheap_beta_reduce takes closed
\ terms only (inference's). Results are new scratch nodes or input nodes,
\ never discarded here.
\
\ The iota hook (for plan task 5.2.1b; its stack effect is stable):
\   defer lf-whnf-iota ( app frames -- ... frames next )
\ Lean's reduce_recursor (393-407). whnf_core opens a visit of app, an
\ application whose head whnf_core left unchanged and which is no lambda
\ (525-526), whose first step is lf-whnf-iota. It is a step of the pass
\ on frames and must end the visit with ( reduct outcome frames 0 ):
\   reduct ok   the rule's right side (526-533): whnf_core reduces it;
\   -1 ok       no rule applies: whnf_core gives app (535);
\   -1 outcome  any other outcome ends whnf_core with it: unknown where a
\               route is not ported, exhausted, full or invalid.
\ Inside, the hook may ask for child visits on the same frames, each
\ continuing with a step of its own: lf-whnf-call (Lean's whnf, which
\ reduce_recursor puts the major premise in: tc 400, where the kernel
\ always has cheap_rec false) and lf-whnf-core-call; it keeps values
\ across them with frame-save and frame-restore (at most frame-spare
\ cells at once). lf-whnf-env? says whether the checked environment can
\ be asked (lf-env-lookup and its slots). The default, lf-whnf-iota-
\ default, answers unknown (diagnostic 81) for a constant head that names
\ a recursor -- a usable slot of that kind, or Lean's generated recursor
\ of an accepted type (lf-env-genrec-of) -- in a check, and no rule
\ otherwise. Quotients (Quot.lift, Quot.ind) are unsupported declarations
\ (U1), so Lean's quot_reduce_rec never applies to a checked term.
\
\ For plan task 5.2.1b, the words to call: lf-whnf-iota (set it with
\ IS), lf-whnf-call and lf-whnf-core-call from inside it, lf-whnf-on and
\ lf-whnf-core-on from a word (check-block's telescope, in place of its
\ beta-only stand-in), lf-whnf-env?, and lf-whnf-iota-default to fall
\ back on.
\
\ State: two growable arrays, members of the checker context
\ (lib/context.fs): an application's arguments, last first, as Lean's
\ get_app_rev_args gives them, and a copy of a constant's universe
\ arguments; each is filled and used within one step, never across a
\ child visit. One paired walk record, lf-whnf-scan, for
\ has_loose_bvars. Shared and read-only: the table of Lean's binary Nat
\ operations (K7), and the hook, deferred only so that plan task 5.2.1b
\ can set it, once, while loading.

require ../lib/lib.fs
require ../lib/slab.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/local-context.fs
require ../core/names.fs
require ../core/terms.fs
require ./environment.fs
require ./env-signature.fs
require ./mixed-head.fs
require ./mixed-instantiate.fs
require ./mixed-level-substitute.fs
require ./mixed-open.fs
require ./mixed-rebuild.fs

1 cells context-slab: lf-whnf-args     \ an application's arguments, last first
2 cells context-slab: lf-whnf-pairs    \ a constant's universe arguments, copied

: lf-whnf-site ( -- site ) c" whnf lf-whnf" ;
: lf-whnf-note ( n1 n2 code -- ) lf-whnf-site swap lf-diag-note ;

\ Whether this context checks a declaration of the current environment
\ (a check's snapshot, not a view), so that constants can be looked up.
\ Records nothing.
: lf-whnf-env? ( -- flag )
  lf-env-ours if lf-env-length lf-env-limit > else false then ;

\ ---------------------------------------------------------------------------
\ Spines. An application's head and arguments (Lean's get_app_rev_args):
\ the arguments are collected last first into lf-whnf-args, valid until
\ the next collection. mk_rev_app applies arguments k-1 .. 0 of the
\ array to f, the first collected outermost; a full store is full.
: lf-whnf-head ( node -- head ) lf-mhead-spine drop ;
\ A node with its identity, 0 when it is not live (a pass refuses it).
: lf-whnf-handle ( node -- node identity ) dup lf-term-identity 0= if 0 then ;
: lf-whnf-arg ( i -- addr ) lf-whnf-args slab-at ;
: lf-whnf-collect ( node n -- )
  0 ?do dup lf-term-second@ i lf-whnf-arg ! lf-term-first@ loop drop ;
: lf-whnf-args! ( node n -- outcome )
  dup lf-whnf-args slab-hold dup ok?
  if drop lf-whnf-collect outcome-ok else nip nip then ;
\ Collect node's arguments: their number and ok, or the failure.
: lf-whnf-spine-args ( node -- n outcome ) dup lf-mhead-spine nip tuck lf-whnf-args! ;
: lf-whnf-apply ( f k -- node outcome )
  begin dup while
    1- tuck lf-whnf-arg @ lf-term-app 0= if drop lf-rebuild-full exit then swap
  repeat drop outcome-ok ;

\ Tags. A lambda; a free variable that is a live let variable (zeta).
: lf-whnf-lam? ( node -- flag ) lf-term-tag@ lf-tag-lam = ;
: lf-whnf-fvar? ( node -- flag ) lf-term-tag@ lf-tag-fvar = ;
: lf-whnf-let? ( node -- flag ) dup lf-fvar-live? if lf-fvar-let? else drop false then ;
: lf-whnf-const? ( node -- flag ) lf-term-tag@ lf-tag-constant = ;
\ A head whnf_core need not visit: anything but a free variable, or a
\ live free variable that is no let variable.
: lf-whnf-plain-head? ( head -- flag )
  dup lf-whnf-fvar? if dup lf-fvar-live? swap lf-whnf-let? 0= and else drop true then ;

\ ---------------------------------------------------------------------------
\ has_loose_bvars: whether node, read with no binder around it, has a
\ bound variable beyond its own binders. Lean reads a cached flag; here a
\ walk of its own visits node (ADR 0014 Q12), paid from the frames' fuel,
\ and stops at the first such variable (as unknown, the walk's only
\ unknown).
lf-walk-room context-walk2: lf-whnf-scan
: lf-whnf-scan-bvar ( first second walk -- outcome )
  nip walk-context @ < if outcome-ok else outcome-unknown then ;
: lf-whnf-scan-binary ( first second walk tag -- outcome )
  over walk-context @ swap lf-tag-app <> - swap walk-children-at ;
: lf-whnf-scan-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if lf-whnf-scan-binary exit then
  lf-tag-bvar = if lf-whnf-scan-bvar else drop 2drop outcome-ok then ;
: lf-whnf-scan-visit ( walk -- outcome ) lf-terms ['] lf-whnf-scan-dispatch walk-visit ;
: lf-whnf-scanned ( outcome -- flag outcome )
  dup outcome-unknown = if drop true outcome-ok exit then
  dup ok? 0= if lf-whnf-scan lf-whnf-site lf-diag-walk then false swap ;
: lf-whnf-loose? ( node frames -- flag outcome )
  >r r@ frame-fuel @ lf-whnf-scan walk-budget drop
  0 ['] lf-whnf-scan-visit lf-whnf-scan walk-run-pair lf-whnf-scanned
  lf-whnf-scan walk-fuel @ r> frame-fuel ! ;

\ ---------------------------------------------------------------------------
\ Beta (515-524): of f's leading lambdas, as many as there are arguments
\ (m, at least one), and the body under them; that body with arguments
\ 1 .. m put for its bound variables at once -- Lean's instantiate with
\ the array's cells n-m .. n-1, the m-th argument for bound variable 0 --
\ on the frames' fuel; then the arguments m+1 .. n applied again.
: lf-whnf-strip ( f n -- body m )
  >r lf-term-second@ 1
  begin over lf-whnf-lam? over r@ < and while 1+ swap lf-term-second@ swap repeat
  r> drop ;
: lf-whnf-lend ( frames -- ) frame-fuel @ lf-open-fuel ! ;
: lf-whnf-repay ( frames -- ) lf-open-fuel @ swap frame-fuel ! ;
: lf-whnf-put ( body m k frames -- node outcome )
  >r lf-whnf-arg swap r@ lf-whnf-lend lf-instantiate r> lf-whnf-repay ;
: lf-whnf-beta-all ( f n frames -- node outcome )
  >r tuck lf-whnf-strip rot over - -rot 2 pick r> lf-whnf-put
  ok-then? if swap lf-whnf-apply else nip no-result then ;
\ Arguments with loose bound variables. Lean's kernel reduces closed terms
\ only, but conversion here also compares terms read under binders it
\ did not open (ADR 0011's rejection analysis, check-block.fs). Lean's
\ instantiate lifts each argument it puts under a binder
\ (instantiate.cpp 26, lift_loose_bvars); mixed-open.fs does not, as its
\ terms are closed. So when an argument taken has a loose bound
\ variable, the head lambda takes one argument, by mixed-instantiate.fs,
\ which lifts, and the result is reduced again: the same weak head
\ normal form, one contraction at a time.
: lf-whnf-arg-open? ( frames i -- frames flag outcome )
  lf-whnf-arg @ over lf-whnf-loose? ;
: lf-whnf-open-args? ( k m frames -- flag outcome )
  -rot over + swap ?do i lf-whnf-arg-open? ok-then? 0= if nip false swap unloop exit then
    if drop true outcome-ok unloop exit then
  loop drop false outcome-ok ;
: lf-whnf-instantiated ( result id status -- result outcome )
  dup ok? if nip else nip nip no-result then ;
: lf-whnf-put1 ( body arg frames -- node outcome )
  >r >r lf-whnf-handle r> lf-whnf-handle r@ frame-fuel @ lf-mixed-instantiate
  lf-minst-fuel @ r> frame-fuel ! lf-whnf-instantiated ;
: lf-whnf-beta-one ( f n frames -- node outcome )
  >r tuck 1- lf-whnf-arg @ swap lf-term-second@ swap r> lf-whnf-put1
  ok-then? if swap 1- lf-whnf-apply else nip no-result then ;
: lf-whnf-beta ( f n frames -- node outcome )
  >r 2dup lf-whnf-strip nip over swap - over over - r@ lf-whnf-open-args?
  ok-then? 0= if nip nip r> drop no-result exit then
  if r> lf-whnf-beta-one else r> lf-whnf-beta-all then ;

\ ---------------------------------------------------------------------------
\ Finding a constant in the check's snapshot, as is_delta and the iota
\ hook ask Lean's environment (env().find): a constant the check declares
\ itself (an inductive block's own types and constructors,
\ env-signature.fs) is found first and has no value; otherwise the
\ environment's lookup gives (d ok) for a usable slot, (-1 ok) for
\ Lean's generated recursor that no slot holds (lf-env-genrec-of then
\ names the type's slot), or its failure (K5 unknown or unsupported,
\ invalid). (-2 ok) says Lean's environment has no such constant: one
\ the check declares itself, or none at all (N1, here no failure: the
\ diagnostic the lookup recorded is put back as it was).
-2 constant lf-whnf-absent
: lf-whnf-cref ( const -- slot ) lf-term-first@ lf-cref-slot ;
: lf-whnf-find ( name -- d outcome )
  >r lf-diag@ r> lf-env-lookup-pass dup outcome-rejected =
  if 2drop lf-diag! lf-whnf-absent outcome-ok else 2>r 2drop 2drop 2r> then ;
: lf-whnf-lookup ( const -- d outcome )
  lf-whnf-cref lf-crec-name @ dup lf-envsig-local
  if 2drop lf-whnf-absent outcome-ok else lf-whnf-find then ;
\ A found slot's input declaration.
: lf-whnf-decl ( d -- decl outcome )
  lf-env-usable ok-then? if lf-slot-decl outcome-ok else no-result then ;

\ is_delta (555-563): a definition or theorem (has_value, declaration.h
\ 466-468) with as many universe parameters as the constant has
\ arguments. (decl ok) when the constant unfolds, (-1 ok) when it does
\ not, or the failure. Outside a check, unknown (K1, see the header).
: lf-whnf-valued? ( decl count -- flag )
  over lf-idecl-arity @ = swap lf-idecl-kind @
  dup lf-kind-definition = swap lf-kind-theorem = or and ;
: lf-whnf-k1 ( const -- -1 outcome )
  0 lf-diag-needs-unfolding lf-whnf-note -1 outcome-unknown ;
: lf-whnf-slot-delta ( const d -- decl outcome )
  dup 0< if 2drop -1 outcome-ok exit then
  lf-whnf-decl ok-then? 0= if nip no-result exit then
  swap lf-whnf-cref lf-crec-arity @ over swap lf-whnf-valued?
  if outcome-ok else drop -1 outcome-ok then ;
: lf-whnf-delta-of ( const -- decl outcome )
  lf-whnf-env? 0= if lf-whnf-k1 exit then
  dup lf-whnf-lookup ok-then? if lf-whnf-slot-delta else nip no-result then ;

\ instantiate_value_lparams: the declaration's value itself when the
\ constant has no universe arguments (no copy, as Lean), else the value
\ with the constant's arguments, copied first (lf-mixed-level-substitute
\ needs its input outside every store), for the declaration's parameters,
\ on the frames' fuel.
: lf-whnf-copy ( addr count -- pairs count )
  tuck 2* cells 0 lf-whnf-pairs slab-at swap move 0 lf-whnf-pairs slab-at swap ;
: lf-whnf-pairs! ( addr count -- pairs count outcome )
  dup lf-whnf-pairs slab-hold dup ok?
  if drop lf-whnf-copy outcome-ok else >r 2drop 0 0 r> then ;
: lf-whnf-substituted ( index id 0 | status -- index outcome )
  dup ok? if 2drop outcome-ok else no-result then ;
: lf-whnf-substitute ( value decl pairs count frames -- value' outcome )
  >r 2>r swap lf-whnf-handle rot lf-idecl-params@ drop 2r>
  r@ frame-fuel @ lf-mixed-level-substitute lf-whnf-substituted
  lf-mls-fuel @ r> frame-fuel ! ;
: lf-whnf-value ( decl const frames -- value outcome )
  >r lf-whnf-cref lf-cref-pairs
  dup 0= if 2drop lf-idecl-value @ r> drop outcome-ok exit then
  lf-whnf-pairs! ok-then? 0= if nip nip r> drop no-result exit then
  rot dup lf-idecl-value @ swap 2swap r> lf-whnf-substitute ;

\ unfold_definition (589-602) of node, whose head is a constant: (node'
\ ok) unfolded, (-1 ok) when the head does not unfold, or the failure.
: lf-whnf-reapply ( value node -- node' outcome )
  lf-whnf-spine-args ok-then? if lf-whnf-apply else nip no-result then ;
: lf-whnf-unfold-head ( node frames const decl -- node' outcome )
  swap rot lf-whnf-value ok-then? if swap lf-whnf-reapply else nip no-result then ;
: lf-whnf-unfold ( node frames -- node' outcome )
  over lf-whnf-head dup lf-whnf-const? 0= if drop 2drop -1 outcome-ok exit then
  dup lf-whnf-delta-of ok-then? 0= if nip nip nip no-result exit then
  dup 0< if 2drop 2drop -1 outcome-ok else lf-whnf-unfold-head then ;

\ ---------------------------------------------------------------------------
\ K7 (ADR 0014 Q8): where reduce_nat (672-703) would look at node -- a
\ constant without universe arguments named Nat.succ with one argument,
\ or one of the fourteen binary operations with two -- unknown,
\ diagnostic 82 with the head; else ok. Names are compared by their
\ components (Lean's name equality), from the last.
\ A table of texts: each entry its length in a cell and its characters,
\ aligned; a length of 0 ends it. Shared and read-only.
: lf-whnf-text, ( c-addr u -- ) dup , here swap dup allot move align ;
: lf-whnf-text ( entry -- c-addr u ) dup cell+ swap @ ;
create lf-whnf-nat-binary
  s" add" lf-whnf-text,  s" sub" lf-whnf-text,  s" mul" lf-whnf-text,
  s" pow" lf-whnf-text,  s" gcd" lf-whnf-text,  s" mod" lf-whnf-text,
  s" div" lf-whnf-text,  s" beq" lf-whnf-text,  s" ble" lf-whnf-text,
  s" land" lf-whnf-text,  s" lor" lf-whnf-text,  s" xor" lf-whnf-text,
  s" shiftLeft" lf-whnf-text,  s" shiftRight" lf-whnf-text,  0 ,
\ Whether name is a string component of these bytes after the prefix.
: lf-whnf-part? ( name c-addr u -- flag )
  rot dup lf-name-tag@ lf-name-tag-str =
  if lf-name-text compare 0= else drop 2drop false then ;
: lf-whnf-anon? ( name -- flag ) lf-name-tag@ lf-name-tag-anon = ;
: lf-whnf-nat? ( name -- flag )
  lf-name-prefix@ dup s" Nat" lf-whnf-part?
  if lf-name-prefix@ lf-whnf-anon? else drop false then ;
: lf-whnf-binary? ( name -- flag )
  lf-whnf-nat-binary begin dup @ while
    2dup lf-whnf-text lf-whnf-part? if 2drop true exit then lf-whnf-text + aligned
  repeat 2drop false ;
: lf-whnf-matched? ( name n -- flag )
  over lf-whnf-nat? 0= if 2drop false exit then
  case 1 of s" succ" lf-whnf-part? endof  2 of lf-whnf-binary? endof
    nip false swap endcase ;
: lf-whnf-k7? ( node -- flag )
  lf-mhead-spine over lf-whnf-const? 0= if 2drop false exit then
  swap lf-whnf-cref dup lf-crec-arity @ if 2drop false exit then
  lf-crec-name @ swap lf-whnf-matched? ;
: lf-whnf-k7 ( node -- outcome )
  dup lf-whnf-k7? if lf-whnf-head 0 lf-diag-name-matched lf-whnf-note outcome-unknown
  else drop outcome-ok then ;

\ ---------------------------------------------------------------------------
\ The iota hook and its default (see the header).
defer lf-whnf-iota ( app frames -- ... frames next )
: lf-whnf-recursor? ( d -- flag outcome )
  dup -1 = if drop true outcome-ok exit then dup 0< if drop false outcome-ok exit then
  lf-whnf-decl ok-then?
  if lf-idecl-kind @ lf-kind-recursor = outcome-ok else false swap then ;
: lf-whnf-pending ( const -- -1 outcome )
  0 lf-diag-iota-pending lf-whnf-note -1 outcome-unknown ;
: lf-whnf-iota-const ( const -- reduct outcome )
  dup lf-whnf-lookup ok-then? 0= if nip no-result exit then
  lf-whnf-recursor? ok-then? 0= if nip no-result exit then
  if lf-whnf-pending else drop -1 outcome-ok then ;
: lf-whnf-iota-head ( head -- reduct outcome )
  dup lf-whnf-const? lf-whnf-env? and if lf-whnf-iota-const else drop -1 outcome-ok then ;
: lf-whnf-iota-default ( app frames -- reduct outcome frames 0 )
  >r lf-whnf-head lf-whnf-iota-head r> 0 ;
' lf-whnf-iota-default is lf-whnf-iota

\ ---------------------------------------------------------------------------
\ Opening visits. A visit opens when the frames admit it (fuel, then
\ room, lib/frame.fs); a refused one continues at once with -1 and the
\ outcome, recorded as a diagnostic.
: lf-whnf-refused ( x frames cont outcome -- -1 outcome frames cont )
  >r over r@ swap lf-whnf-site lf-diag-frames drop r> frame-refuse ;
: lf-whnf-open ( x frames cont xt -- ... frames next )
  >r over frame-admit dup ok? if drop r> frame-open else r> drop lf-whnf-refused then ;
\ A step that ends its visit with a failure: no result.
: lf-whnf-failed ( outcome frames -- -1 outcome frames 0 ) >r no-result r> 0 ;
: lf-whnf-keep ( node frames -- node outcome frames 0 ) outcome-ok swap 0 ;
: lf-whnf-ended ( node outcome frames -- node outcome frames 0 ) 0 ;

\ whnf_core's visit. Going on with a new node within the same visit (a
\ tail call in Lean: 523, 533, 538, 543) costs one unit of fuel.
defer lf-wc-visit ( node frames -- ... frames next )
: lf-wc-again ( node frames -- node frames next | -1 outcome frames 0 )
  dup frame-fuel @ 0> if -1 over frame-fuel +! ['] lf-wc-visit exit then
  dup lf-whnf-site lf-diag-frames-fuel nip outcome-exhausted swap lf-whnf-failed ;
: lf-wc-then ( node outcome frames -- ... frames next )
  over ok? if nip lf-wc-again else >r nip no-result r> 0 then ;
: lf-wc-call ( node frames cont -- ... frames next ) ['] lf-wc-visit lf-whnf-open ;

\ The head f of node's spine, whnf_core'd: a lambda contracts (beta); f
\ the head itself goes to the iota hook, node saved across its visit; any
\ other f is applied to the arguments again. Each case goes on with the
\ result.
: lf-wc-beta ( node f frames -- ... frames next )
  >r swap lf-whnf-spine-args ok-then? 0= if nip r> lf-whnf-failed exit then
  r@ lf-whnf-beta r> lf-wc-then ;
: lf-wc-rebuild ( node f frames -- ... frames next )
  >r swap lf-whnf-spine-args ok-then? 0= if nip r> lf-whnf-failed exit then
  lf-whnf-apply r> lf-wc-then ;
: lf-wc-iota-back ( reduct outcome frames -- ... frames next )
  >r r@ frame-restore -rot ok-then? 0= if nip r> lf-whnf-failed exit then
  dup 0< if drop outcome-ok r> 0 else nip r> lf-wc-again then ;
: lf-whnf-iota-step ( app frames -- ... frames next ) lf-whnf-iota ;
: lf-wc-iota ( node f frames -- ... frames next )
  nip 2dup frame-save ['] lf-wc-iota-back ['] lf-whnf-iota-step lf-whnf-open ;
: lf-wc-head ( node f frames -- ... frames next )
  over lf-whnf-lam? if lf-wc-beta exit then
  >r 2dup swap lf-whnf-head = r> swap if lf-wc-iota else lf-wc-rebuild then ;
\ An application: its head is visited first only when it is a let
\ variable (or no live variable), node saved across that visit.
: lf-wc-headed ( f outcome frames -- ... frames next )
  >r r@ frame-restore -rot ok-then? if r> lf-wc-head else nip r> lf-whnf-failed then ;
: lf-wc-app ( node frames -- ... frames next )
  over lf-whnf-head dup lf-whnf-plain-head? if swap lf-wc-head exit then
  -rot tuck frame-save ['] lf-wc-headed lf-wc-call ;
\ A free variable: a let variable's value goes on (zeta), any other live
\ one is normal; one the local context does not name is invalid.
: lf-wc-fvar ( node frames -- ... frames next )
  over lf-fvar-live? 0= if nip outcome-invalid swap lf-whnf-failed exit then
  over lf-fvar-let? if swap lf-fvar-value swap lf-wc-again else lf-whnf-keep then ;
: lf-whnf-normal? ( tag -- flag )
  dup lf-tag-lam = over lf-tag-pi = or over lf-tag-constant = or
  over lf-tag-bvar = or swap lf-tag-symbolic-sort = or ;
: lf-wc-leaf ( node frames tag -- ... frames next )
  lf-whnf-normal? if lf-whnf-keep else nip outcome-invalid swap lf-whnf-failed then ;
: lf-wc-tagged ( node frames tag -- ... frames next )
  dup lf-tag-app = if drop lf-wc-app exit then
  dup lf-tag-fvar = if drop lf-wc-fvar exit then lf-wc-leaf ;
:noname ( node frames -- ... frames next )
  over lf-term-valid? 0= if nip outcome-invalid swap lf-whnf-failed exit then
  over lf-term-tag@ lf-wc-tagged ; is lf-wc-visit

\ whnf's visit: the easy cases at once (708-722); otherwise whnf_core,
\ then K7, then one delta step, which goes on with whnf_core of the
\ unfolded term within the same visit; the first result that does not
\ unfold is the answer.
defer lf-whnf-cored ( t1 outcome frames -- ... frames next )
: lf-whnf-next ( t1 frames t' outcome -- ... frames next )
  dup ok? 0= if >r drop nip r> swap lf-whnf-failed exit then drop
  dup 0< if drop outcome-ok swap 0 exit then
  rot drop swap ['] lf-whnf-cored lf-wc-call ;
:noname ( t1 outcome frames -- ... frames next )
  over ok? 0= if 0 exit then nip
  over lf-whnf-k7 dup ok? 0= if rot drop swap lf-whnf-failed exit then drop
  2dup lf-whnf-unfold lf-whnf-next ; is lf-whnf-cored
: lf-whnf-easy? ( node -- flag )
  dup lf-term-tag@ dup lf-tag-bvar = over lf-tag-pi = or swap lf-tag-symbolic-sort = or
  if drop true exit then
  dup lf-whnf-fvar? if lf-whnf-let? 0= else drop false then ;
: lf-whnf-visit ( node frames -- ... frames next )
  over lf-term-valid? 0= if nip outcome-invalid swap lf-whnf-failed exit then
  over lf-whnf-easy? if lf-whnf-keep exit then
  ['] lf-whnf-cored lf-wc-call ;

\ ---------------------------------------------------------------------------
\ cheap_beta_reduce (instantiate.cpp 211-230), which infer_lambda applies
\ to the type of a lambda chain's body (type_checker.cpp 140): for e = f
\ a1 .. an with f a lambda, f's leading lambdas, at most n, are stripped
\ (i of them) to body; body applied to a(i+1) .. an when body has no
\ loose bound variable; when body is bound variable k, a(i-k) applied to
\ them; else e unchanged. A plain function of e, no reduction step: it
\ visits nothing but body's loose bound variables (lf-whnf-loose?);
\ e must be closed.
: lf-whnf-stripped ( fn n -- body i )
  0 begin 2 pick lf-whnf-lam? over 3 pick < and
  while 1+ rot lf-term-second@ -rot repeat nip ;
\ For body bound variable k: argument i-k, cell n-i+k of the array.
: lf-whnf-named ( body n i -- arg n i )
  >r tuck r@ - swap lf-term-first@ + lf-whnf-arg @ swap r> ;
: lf-whnf-cheap-pick ( body n i e frames -- e' outcome )
  >r 3 pick r> lf-whnf-loose? ok-then? 0= if >r 2drop 2drop r> no-result exit then
  0= if drop - lf-whnf-apply exit then
  3 pick lf-term-tag@ lf-tag-bvar <> if >r 2drop drop r> outcome-ok exit then
  drop lf-whnf-named - lf-whnf-apply ;
: lf-whnf-beta-head? ( e -- flag )
  dup lf-term-tag@ lf-tag-app = if lf-whnf-head lf-whnf-lam? else drop false then ;
: lf-cheap-beta ( e frames -- e' outcome )
  over lf-whnf-beta-head? 0= if drop outcome-ok exit then
  >r dup lf-whnf-spine-args ok-then? 0= if nip r> drop no-result exit then
  over lf-whnf-head over lf-whnf-stripped 2swap -rot r> lf-whnf-cheap-pick ;

\ ---------------------------------------------------------------------------
\ The public words (see the header).
: lf-whnf-core-call ( node frames cont -- ... frames next ) lf-wc-call ;
: lf-whnf-call ( node frames cont -- ... frames next ) ['] lf-whnf-visit lf-whnf-open ;
: lf-whnf-core-on ( node frames -- node' outcome )
  ['] lf-whnf-core-call frame-through drop ;
: lf-whnf-on ( node frames -- node' outcome ) ['] lf-whnf-call frame-through drop ;
