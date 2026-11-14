\ Weak head normal form as Lean's kernel computes it (ADR 0014 Q4, Q5,
\ Q8; plan task 4.2.2c): ports of whnf_core (type_checker.cpp 468-551),
\ whnf (706-743), is_delta (555-563) and unfold_definition (565-602) at
\ the referee commit eb6cafb7 (ADR 0014, Reproduction). [kernel] code:
\ not through the review gate (AGENTS.md).
\
\ whnf_core reduces without unfolding (Lean's order). Sorts, Pis,
\ lambdas, constants, bound variables and free variables that are no let
\ variables are normal (473-488); a let variable is its value, reduced
\ (whnf_fvar 409-417), and a let term (core/let-terms.fs) its body with
\ its value put for the bound variable, reduced (zeta, 542-544; plan task
\ 4.2.3). An application's head (a let term ends a spine, as in Lean's
\ get_app_fn) is reduced first (514): a lambda head takes as many
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
\ Lean's caches m_whnf_core, m_whnf and m_unfold, and the node data Lean
\ reads instead of the has_loose_bvars and has_fvar walks, are
\ kernel/caches.fs's, through the hooks lf-wc-entry, lf-whnf-entry,
\ lf-whnf-valued and lf-whnf-known (plan task 4.2.7); without it every
\ pass runs as here. Not yet as Lean (no verdict depends on them): the
\ unfold counts of kernel diagnostics (plan task 4.3.1); metadata is an unsupported
\ form (U2) that never reaches these passes; a literal, natural-number or
\ string, is normal (Lean's Lit, 476 and 710); the derivation log records
\ nothing new here (plan task 4.2.2e). A projection (core/projections.fs), a
\ node of its own over a projection leaf and its term, alone or at the
\ head of a spine, goes to the iota hook, which reduces it (iota.fs,
\ reduce_proj); a leaf alone is never a term (defeq.fs takes Lean's
\ Expr.proj whole, never its leaf): malformed, invalid.
\ cheap_proj (468, 444-454; plan task 5.2.2): is_def_eq_core asks
\ whnf_core with it (lf-whnf-cheap-call; type_checker.cpp 983-1014 and
\ 1155-1156): a projection's term is then put in whnf_core, still cheap,
\ instead of whnf (lf-whnf-proj-call, which the iota hook uses). It is
\ the mode of the innermost whnf_core visit (lf-whnf-cheap): a whnf
\ visit, which runs whnf_core without it (731) -- as reduce_recursor's
\ whnf of a major premise does (400) -- and each public whnf_core visit
\ set their own mode where it differs, and push the step that puts the
\ other back when they end (one cell of their own); whnf_core's own
\ steps inherit it. Lean reads m_whnf_core in both modes but keeps no
\ entry from a cheap visit (547): kernel/caches.fs asks lf-whnf-cheap?.
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
\ give). Lean's kernel reduces closed terms only. check-block.fs now opens
\ each binder it walks into on the inference job's scope (as Lean's
\ mk_local_decl_for), so its terms are read under the scope; the recursor
\ builder (inductive-recursor.fs) and ADR 0011's analysis still read terms
\ under binders no scope holds, and iota.fs's structure eta (R3) refuses
\ those (unknown). A beta argument with a loose bound variable is lifted as Lean's
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
\ otherwise. iota.fs's hook tries Lean's quot_reduce_rec (quot.fs) first,
\ as reduce_recursor does.
\
\ For plan task 5.2.1b, the words to call: lf-whnf-iota (set it with
\ IS), lf-whnf-call, lf-whnf-core-call and lf-whnf-proj-call from inside
\ it, lf-whnf-on and lf-whnf-core-on from a word (check-block's
\ telescope, in place of its beta-only stand-in), lf-whnf-env?, and
\ lf-whnf-iota-default to fall back on. defeq.fs adds lf-whnf-cheap-call.
\
\ State: two growable arrays, members of the checker context
\ (lib/context.fs): an application's arguments, last first, as Lean's
\ get_app_rev_args gives them, and a copy of a constant's universe
\ arguments; each is filled and used within one step, never across a
\ child visit. One paired walk record, lf-whnf-scan, for
\ has_loose_bvars. One context record, lf-whnf-state: the cheap_proj mode
\ (lf-whnf-cheap, above; lf-whnf-reset clears it after a THROW) and the
\ count of open terms typed under the scope (lf-whnf-scope-use, below;
\ only its changes are read). Shared and read-only:
\ the table of Lean's binary Nat operations (K7), and the hook, deferred
\ only so that plan task 5.2.1b can set it, once, while loading.

require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/bytes.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/let-terms.fs
require ../core/local-context.fs
require ../core/names.fs
require ../core/projections.fs
require ../core/terms.fs
require ./environment.fs
require ./env-signature.fs
require ./mixed-head.fs
require ./reduce-nat.fs
require ./mixed-instantiate.fs
require ./mixed-level-substitute.fs
require ./mixed-open.fs
require ./mixed-rebuild.fs

1 cells context-slab: lf-whnf-args     \ an application's arguments, last first
2 cells context-slab: lf-whnf-pairs    \ a constant's universe arguments, copied
begin-structure /lf-whnfrec
  field: lf-whnfrec-cheap    \ true: whnf_core runs with cheap_proj
  field: lf-whnfrec-scoped   \ open terms typed under the scope so far
end-structure
/lf-whnfrec context-record: lf-whnf-state
: lf-whnf-cheap ( -- addr ) lf-whnf-state lf-whnfrec-cheap ;
\ The iota hook counts each term with loose bound variables it types
\ under the inference job's scope (iota.fs: K and structure eta on a
\ scoped major premise): a result reached so depends on the scope, which
\ an open key does not name, so kernel/caches.fs keeps none for it.
: lf-whnf-scope-uses ( -- n ) lf-whnf-state lf-whnfrec-scoped @ ;
: lf-whnf-scope-use ( -- ) 1 lf-whnf-state lf-whnfrec-scoped +! ;

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
\ f applied to the last k arguments of app's spine, f itself for k = 0
\ (app then not read): the iota and quotient reductions' extra arguments.
: lf-whnf-apply-last ( f app k -- node outcome )
  dup 0= if 2drop outcome-ok exit then
  swap lf-whnf-spine-args ok-then? 0= if nip nip no-result exit then drop lf-whnf-apply ;

\ Tags. A lambda; a free variable that is a live let variable (zeta).
: lf-whnf-lam? ( node -- flag ) lf-term-tag@ lf-tag-lam = ;
: lf-whnf-fvar? ( node -- flag ) lf-term-tag@ lf-tag-fvar = ;
: lf-whnf-let? ( node -- flag ) dup lf-fvar-live? if lf-fvar-let? else drop false then ;
: lf-whnf-const? ( node -- flag ) lf-term-tag@ lf-tag-constant = ;
\ A head whnf_core need not visit: anything but a let term or a free
\ variable, or a live free variable that is no let variable.
: lf-whnf-plain-head? ( head -- flag )
  dup lf-let? if drop false exit then
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
  over walk-context @ swap lf-term-binder-tag? - swap walk-children-at ;
\ A step of a loose-variable scan (here and mixed-infer.fs's): a binary
\ node's children pushed, one binder deeper under a lambda or Pi; a bound
\ variable given to xt ( first second walk -- outcome ); any other leaf
\ passed.
: lf-whnf-scan-step ( first second walk tag xt -- outcome )
  >r dup lf-term-binary-tag? if r> drop lf-whnf-scan-binary exit then
  lf-tag-bvar = if r> execute else r> 2drop 2drop outcome-ok then ;
: lf-whnf-scan-dispatch ( first second walk tag -- outcome )
  ['] lf-whnf-scan-bvar lf-whnf-scan-step ;
: lf-whnf-scan-visit ( walk -- outcome ) ['] lf-whnf-scan-dispatch lf-term-visit ;
: lf-whnf-scanned ( outcome -- flag outcome )
  dup outcome-unknown = if drop true outcome-ok exit then
  dup ok? 0= if lf-whnf-scan lf-whnf-site lf-diag-walk then false swap ;
\ The answer Lean reads from a node's cached data (expr.h:
\ has_loose_bvars, has_fvar), as the term store keeps it in the node's
\ data word (core/terms.fs, ADR 0016 C1; plan task 6.5.5): a loose bound
\ variable for both walks, a free variable for has_fvar's. The walk is
\ then not run and costs nothing, as Lean's flag; the walks read no
\ entry of a free variable, so a dead one counts as the word counts it.
\ A node without data asks the hook (the caches' memo, kernel/caches.fs;
\ by default never known), and only then is walked.
defer lf-whnf-known ( node visit -- flag true | false )
:noname ( node visit -- false ) 2drop false ; is lf-whnf-known
: lf-whnf-open-word? ( data visit -- flag )
  ['] lf-whnf-scan-visit = if lf-data-loose 0<> exit then
  dup lf-data-loose 0<> swap lf-data-fvar? or ;
: lf-whnf-word ( node visit -- flag true | false )
  swap lf-term-data@ if swap lf-whnf-open-word? true else drop false then ;
: lf-whnf-scan-run ( node frames visit -- flag outcome )
  2 pick over lf-whnf-word if >r 2drop drop r> outcome-ok exit then
  2 pick over lf-whnf-known if >r 2drop drop r> outcome-ok exit then
  swap >r r@ frame-fuel @ lf-whnf-scan walk-budget drop
  0 swap lf-whnf-scan walk-run-pair lf-whnf-scanned
  lf-whnf-scan walk-fuel @ r> frame-fuel ! ;
: lf-whnf-loose? ( node frames -- flag outcome ) ['] lf-whnf-scan-visit lf-whnf-scan-run ;
\ has_fvar, as is_def_eq_core and lazy delta test it (1060, 1142): the
\ same walk, which also stops at a free variable. A loose bound variable
\ counts as one: it stands for a binder a caller did not open (ADR 0011's
\ analysis, check-block.fs), which Lean's kernel would have opened to a
\ free variable.
: lf-whnf-free-dispatch ( first second walk tag -- outcome )
  dup lf-tag-fvar = if drop 2drop drop outcome-unknown exit then lf-whnf-scan-dispatch ;
: lf-whnf-free-visit ( walk -- outcome ) ['] lf-whnf-free-dispatch lf-term-visit ;
: lf-whnf-free? ( node frames -- flag outcome ) ['] lf-whnf-free-visit lf-whnf-scan-run ;

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
: lf-whnf-arg-at? ( frames k j -- frames k flag outcome )
  over + swap >r lf-whnf-arg-open? r> -rot ;
: lf-whnf-open-args? ( k m frames -- flag outcome )
  -rot ['] lf-whnf-arg-at? ok-any? 2swap 2drop ;
: lf-whnf-instantiated ( result id status -- result outcome )
  dup ok? if nip else nip nip no-result then ;
: lf-whnf-put1 ( body arg frames -- node outcome )
  >r >r lf-term-handle r> lf-term-handle r@ frame-fuel @ lf-mixed-instantiate
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
\ The answer "none" of is_delta, unfold_definition and the iota hook, in
\ the place of a declaration or a node (review rvU4, style point 2).
-1 constant lf-whnf-none
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
  dup 0< if 2drop lf-whnf-none outcome-ok exit then
  lf-whnf-decl ok-then? 0= if nip no-result exit then
  swap lf-whnf-cref lf-crec-arity @ over swap lf-whnf-valued?
  if outcome-ok else drop lf-whnf-none outcome-ok then ;
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
  >r 2>r swap lf-term-handle rot lf-idecl-params@ drop 2r>
  r@ frame-fuel @ lf-mixed-level-substitute lf-whnf-substituted
  lf-mls-fuel @ r> frame-fuel ! ;
: lf-whnf-value ( decl const frames -- value outcome )
  >r lf-whnf-cref lf-cref-pairs
  dup 0= if 2drop lf-idecl-value @ r> drop outcome-ok exit then
  lf-whnf-pairs! ok-then? 0= if nip nip r> drop no-result exit then
  rot dup lf-idecl-value @ swap 2swap r> lf-whnf-substitute ;
\ The hook of Lean's m_unfold cache (kernel/caches.fs sets it): the value
\ of decl for const, as lf-whnf-value gives it.
defer lf-whnf-valued ( decl const frames -- value outcome )
' lf-whnf-value is lf-whnf-valued

\ unfold_definition (589-602) of node, whose head is a constant: (node'
\ ok) unfolded, (-1 ok) when the head does not unfold, or the failure.
: lf-whnf-reapply ( value node -- node' outcome )
  lf-whnf-spine-args ok-then? if lf-whnf-apply else nip no-result then ;
: lf-whnf-unfold-head ( node frames const decl -- node' outcome )
  swap rot lf-whnf-valued ok-then? if swap lf-whnf-reapply else nip no-result then ;
: lf-whnf-unfold ( node frames -- node' outcome )
  over lf-whnf-head dup lf-whnf-const? 0= if drop 2drop lf-whnf-none outcome-ok exit then
  dup lf-whnf-delta-of ok-then? 0= if nip nip nip no-result exit then
  dup lf-whnf-none = if 2drop 2drop lf-whnf-none outcome-ok else lf-whnf-unfold-head then ;

\ ---------------------------------------------------------------------------
\ K7 (ADR 0014 Q8). Lean's reduce_nat (672-703) looks at node when its
\ head is a constant without universe arguments named Nat.succ with one
\ argument, or one of the fourteen binary operations with two
\ (lf-whnf-k7?), and computes a literal when the whnf of each argument is
\ a literal or the constant Nat.zero (is_nat_lit_ext, 607; the first
\ argument first, the second only then), whether or not node has a free
\ variable (Lean tests none here). Since plan task 5.2.3 it computes as
\ Lean does (reduce-nat.fs:
\ the literal, or Bool.true or Bool.false for Nat.beq and Nat.ble, with
\ Lean's refusals); otherwise reduce_nat gives nothing and Lean goes on,
\ as LeanForth does (a Nat.succ of a variable, say, which iota then takes
\ as a constructor).
\ The arguments are put in whnf by a visit of their own (lf-whnf-nat-call,
\ below). Names are compared by their components (Lean's name equality),
\ from the last.
\ A table of texts: each entry its length in a cell and its characters,
\ aligned; a length of 0 ends it. Shared and read-only.
create lf-whnf-nat-binary
  s" add" cell-counted,  s" sub" cell-counted,  s" mul" cell-counted,
  s" pow" cell-counted,  s" gcd" cell-counted,  s" mod" cell-counted,
  s" div" cell-counted,  s" beq" cell-counted,  s" ble" cell-counted,
  s" land" cell-counted,  s" lor" cell-counted,  s" xor" cell-counted,
  s" shiftLeft" cell-counted,  s" shiftRight" cell-counted,  0 ,
\ Whether name is Nat.x for an anonymous root (names.fs's lf-name-top?).
: lf-whnf-nat? ( name -- flag ) lf-name-prefix@ s" Nat" lf-name-top? ;
\ The index of name's operation in the table, or -1.
: lf-whnf-binary ( name -- i )
  0 lf-whnf-nat-binary begin dup @ while
    2 pick over cell-count lf-name-str-is? if drop nip exit then
    swap 1+ swap cell-count + aligned
  repeat 2drop drop -1 ;
: lf-whnf-binary? ( name -- flag ) lf-whnf-binary 0< 0= ;
: lf-whnf-op ( node -- i ) lf-whnf-head lf-whnf-cref lf-crec-name @ lf-whnf-binary ;
: lf-whnf-matched? ( name n -- flag )
  over lf-whnf-nat? 0= if 2drop false exit then
  case 1 of s" succ" lf-name-str-is? endof  2 of lf-whnf-binary? endof
    nip false swap endcase ;
: lf-whnf-k7? ( node -- flag )
  lf-mhead-spine over lf-whnf-const? 0= if 2drop false exit then
  swap lf-whnf-cref dup lf-crec-arity @ if 2drop false exit then
  lf-crec-name @ swap lf-whnf-matched? ;
: lf-whnf-zero? ( node -- flag )
  dup lf-whnf-const? 0= if drop false exit then
  lf-whnf-cref dup lf-crec-arity @ if drop false exit then
  lf-crec-name @ dup s" zero" lf-name-str-is? if lf-whnf-nat? else drop false then ;

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
  if lf-whnf-pending else drop lf-whnf-none outcome-ok then ;
: lf-whnf-iota-head ( head -- reduct outcome )
  dup lf-whnf-const? lf-whnf-env? and if lf-whnf-iota-const else drop lf-whnf-none outcome-ok then ;
: lf-whnf-iota-default ( app frames -- reduct outcome frames 0 )
  >r lf-whnf-head lf-whnf-iota-head r> 0 ;
' lf-whnf-iota-default is lf-whnf-iota

\ ---------------------------------------------------------------------------
\ Opening visits. A visit opens when the frames admit it (fuel, then
\ room, lib/frame.fs); a refused one continues at once with -1 and the
\ outcome, recorded as a diagnostic.
: lf-whnf-refused ( x frames cont outcome -- -1 outcome frames cont )
  >r over r@ swap lf-whnf-site lf-diag-frames drop r> frame-refuse ;
: lf-whnf-open ( x frames cont xt -- ... frames next ) ['] lf-whnf-refused frame-open-or ;
\ A step that ends its visit with a failure: no result.
: lf-whnf-failed ( outcome frames -- -1 outcome frames 0 ) >r no-result r> 0 ;
: lf-whnf-keep ( node frames -- node outcome frames 0 ) outcome-ok swap 0 ;

\ The cheap_proj mode (see the header). A visit's first step sets the
\ visit's mode; where that changes it, the step that puts the old one
\ back is pushed, to run when the visit ends.
: lf-whnf-cheap? ( -- flag ) lf-whnf-cheap @ ;
: lf-whnf-reset ( -- ) false lf-whnf-cheap ! ;
: lf-whnf-to-cheap ( x outcome frames -- x outcome frames 0 ) true lf-whnf-cheap ! 0 ;
: lf-whnf-to-full ( x outcome frames -- x outcome frames 0 ) lf-whnf-reset 0 ;
: lf-whnf-mode ( frames flag -- frames )
  dup lf-whnf-cheap? = if drop exit then dup lf-whnf-cheap !
  if ['] lf-whnf-to-full else ['] lf-whnf-to-cheap then over frame-save ;

\ whnf_core's visit. Going on with a new node within the same visit (a
\ tail call in Lean: 523, 533, 538, 543) costs one unit of fuel.
defer lf-wc-visit ( node frames -- ... frames next )
\ The first step of a whnf_core visit, and of each step that goes on with
\ a new node within one (Lean's recursive whnf_core calls): lf-wc-visit,
\ or the m_whnf_core cache's step around it (kernel/caches.fs sets it).
defer lf-wc-entry ( node frames -- ... frames next )
' lf-wc-visit is lf-wc-entry
: lf-wc-again ( node frames -- node frames next | -1 outcome frames 0 )
  dup frame-fuel @ 0> if -1 over frame-fuel +! ['] lf-wc-entry exit then
  dup lf-whnf-site lf-diag-frames-fuel nip outcome-exhausted swap lf-whnf-failed ;
: lf-wc-then ( node outcome frames -- ... frames next )
  over ok? if nip lf-wc-again else >r nip no-result r> 0 then ;
: lf-wc-call ( node frames cont -- ... frames next ) ['] lf-wc-entry lf-whnf-open ;

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
  dup lf-whnf-none = if drop outcome-ok r> 0 else nip r> lf-wc-again then ;
: lf-whnf-iota-step ( app frames -- ... frames next ) lf-whnf-iota ;
: lf-wc-iota ( node f frames -- ... frames next )
  nip 2dup frame-save ['] lf-wc-iota-back ['] lf-whnf-iota-step lf-whnf-open ;
: lf-wc-head ( node f frames -- ... frames next )
  over lf-whnf-lam? if lf-wc-beta exit then
  >r 2dup swap lf-whnf-head = r> swap if lf-wc-iota else lf-wc-rebuild then ;
\ An application: its head is visited first only when it is a let term
\ or a let variable (or no live variable), as Lean's whnf_core reduces
\ the head first (514), node saved across that visit.
: lf-wc-invalid ( node frames -- -1 outcome frames 0 )
  nip outcome-invalid swap lf-whnf-failed ;
: lf-wc-headed ( f outcome frames -- ... frames next )
  >r r@ frame-restore -rot ok-then? if r> lf-wc-head else nip r> lf-whnf-failed then ;
: lf-wc-app ( node frames -- ... frames next )
  over lf-whnf-head dup lf-whnf-plain-head? if swap lf-wc-head exit then
  -rot tuck frame-save ['] lf-wc-headed lf-wc-call ;
\ A projection alone (reduce_proj, 504-510) goes to the iota hook as a
\ spine of no arguments whose head is itself, as one applied does.
: lf-wc-proj ( node frames -- ... frames next ) >r dup r> lf-wc-iota ;
\ Zeta (542-544): a let term (core/let-terms.fs) is its body with its
\ value put for the bound variable, Lean's instantiate on the frames'
\ fuel (a value with a loose bound variable is lifted, as beta lifts an
\ argument: lf-whnf-put1), reduced again within the same visit; one whose
\ second argument is no lambda is malformed.
: lf-whnf-zeta-closed ( body v frames -- node outcome )
  >r 1 lf-whnf-args slab-hold dup ok? 0= if nip nip no-result r> drop exit then drop
  0 lf-whnf-arg ! 1 0 r> lf-whnf-put ;
: lf-whnf-zeta ( body v frames -- node outcome )
  2dup lf-whnf-loose? ok-then? 0= if >r drop 2drop r> no-result exit then
  if lf-whnf-put1 else lf-whnf-zeta-closed then ;
: lf-wc-zeta ( node frames -- ... frames next )
  over lf-let-well? 0= if lf-wc-invalid exit then
  >r dup lf-let-body swap lf-let-value r@ lf-whnf-zeta r> lf-wc-then ;
\ A free variable: a let variable's value goes on (zeta), any other live
\ one is normal; one the local context does not name is invalid.
: lf-wc-fvar ( node frames -- ... frames next )
  over lf-fvar-live? 0= if nip outcome-invalid swap lf-whnf-failed exit then
  over lf-fvar-let? if swap lf-fvar-value swap lf-wc-again else lf-whnf-keep then ;
: lf-whnf-normal? ( tag -- flag )
  dup lf-tag-lam = over lf-tag-pi = or over lf-tag-constant = or
  over lf-tag-bvar = or over lf-literal-tag? or swap lf-tag-symbolic-sort = or ;
\ Any other leaf, a projection leaf alone among them (see the header),
\ is malformed.
: lf-wc-leaf ( node frames tag -- ... frames next )
  lf-whnf-normal? if lf-whnf-keep else nip outcome-invalid swap lf-whnf-failed then ;
: lf-wc-tagged ( node frames tag -- ... frames next )
  case lf-tag-app of lf-wc-app endof  lf-tag-fvar of lf-wc-fvar endof
    lf-tag-let of lf-wc-zeta endof  lf-tag-let-nondep of lf-wc-zeta endof
    lf-tag-projection of lf-wc-proj endof  lf-wc-leaf 0 endcase ;
:noname ( node frames -- ... frames next )
  over lf-term-valid? 0= if nip outcome-invalid swap lf-whnf-failed exit then
  over lf-term-tag@ lf-wc-tagged ; is lf-wc-visit

\ whnf's visit: the easy cases at once (708-722); otherwise whnf_core,
\ then reduce_nat (K7, above), then one delta step, which goes on with
\ whnf_core of the unfolded term within the same visit; the first result
\ that does not unfold is the answer.
defer lf-nat-visit ( node frames -- ... frames next )
: lf-whnf-nat-call ( node frames cont -- ... frames next ) ['] lf-nat-visit lf-whnf-open ;
defer lf-whnf-cored ( t1 outcome frames -- ... frames next )
: lf-whnf-next ( t1 frames t' outcome -- ... frames next )
  dup ok? 0= if >r drop nip r> swap lf-whnf-failed exit then drop
  dup lf-whnf-none = if drop outcome-ok swap 0 exit then
  rot drop swap ['] lf-whnf-cored lf-wc-call ;
: lf-whnf-delta-step ( t1 frames -- ... frames next ) 2dup lf-whnf-unfold lf-whnf-next ;
\ reduce_nat's answer on t1, saved across its visit: the literal (or
\ Bool constant) it computes, whnf's answer, or none, then delta.
: lf-whnf-nat-back ( r outcome frames -- ... frames next )
  >r r@ frame-restore -rot ok-then? 0= if nip r> lf-whnf-failed exit then
  dup lf-whnf-none = if drop r> lf-whnf-delta-step else nip outcome-ok r> 0 then ;
\ reduce_nat is tried on t1 when its head and arity match (lf-whnf-k7?),
\ whether or not t1 has a free variable: Lean's reduce_nat (672-703) has
\ no such test, nor has whnf's call of it (732). Only lazy delta (1060)
\ and is_def_eq_core's Bool.true step (1142) test has_fvar (defeq.fs).
:noname ( t1 outcome frames -- ... frames next )
  over ok? 0= if 0 exit then nip
  over lf-whnf-k7? if 2dup frame-save ['] lf-whnf-nat-back lf-whnf-nat-call exit then
  lf-whnf-delta-step ; is lf-whnf-cored
: lf-whnf-easy? ( node -- flag )
  dup lf-term-tag@ dup lf-tag-bvar = over lf-tag-pi = or over lf-literal-tag? or
  swap lf-tag-symbolic-sort = or if drop true exit then
  dup lf-whnf-fvar? if lf-whnf-let? 0= else drop false then ;
\ Its whnf_core runs without cheap_proj (731).
: lf-whnf-visit ( node frames -- ... frames next )
  over lf-term-valid? 0= if nip outcome-invalid swap lf-whnf-failed exit then
  over lf-whnf-easy? if lf-whnf-keep exit then
  false lf-whnf-mode ['] lf-whnf-cored lf-wc-call ;
\ The first step of a whnf visit: lf-whnf-visit, or the m_whnf cache's
\ step around it (kernel/caches.fs sets it).
defer lf-whnf-entry ( node frames -- ... frames next )
' lf-whnf-visit is lf-whnf-entry

\ reduce_nat on node, for which lf-whnf-k7? holds: its first argument's
\ whnf, then a binary operation's second one's, must be a literal or
\ Nat.zero (is_nat_lit_ext; reduce_bin_nat_op 612-619 puts the second in
\ whnf only when the first is one); then reduce-nat.fs computes. The
\ visit keeps node (and the first literal across the second visit) and
\ ends with ( r outcome frames 0 ): the result, lf-whnf-none, or a
\ failure.
: lf-nat-end ( r outcome frames -- r outcome frames 0 ) 1 over frame-drop 0 ;
: lf-nat-end2 ( r outcome frames -- r outcome frames 0 ) 2 over frame-drop 0 ;
: lf-nat-ext ( w -- lit outcome )
  dup lf-lit-leaf? if outcome-ok exit then
  lf-whnf-zero? if 0 lf-reduce-nat-literal else lf-whnf-none outcome-ok then ;
: lf-nat-literal ( w outcome -- lit outcome ) ok-then? if lf-nat-ext else no-result then ;
: lf-nat-second ( w outcome frames -- ... frames next )
  >r lf-nat-literal ok-then? 0= if no-result r> lf-nat-end2 exit then
  dup lf-whnf-none = if outcome-ok r> lf-nat-end2 exit then
  0 r@ frame-pick swap 1 r@ frame-pick lf-whnf-op lf-reduce-nat-binary r> lf-nat-end2 ;
: lf-nat-first ( w outcome frames -- ... frames next )
  >r lf-nat-literal ok-then? 0= if no-result r> lf-nat-end exit then
  dup lf-whnf-none = if outcome-ok r> lf-nat-end exit then
  0 r@ frame-pick lf-mhead-spine nip 1 = if lf-reduce-nat-succ r> lf-nat-end exit then
  r@ frame-save 1 r@ frame-pick lf-term-second@
  r> ['] lf-nat-second ['] lf-whnf-entry lf-whnf-open ;
:noname ( node frames -- ... frames next )
  2dup frame-save >r dup lf-mhead-spine nip 1 =
  if lf-term-second@ else lf-term-first@ lf-term-second@ then
  r> ['] lf-nat-first ['] lf-whnf-entry lf-whnf-open ; is lf-nat-visit

\ ---------------------------------------------------------------------------
\ cheap_beta_reduce (instantiate.cpp 211-230), which infer_lambda applies
\ to the type of a lambda chain's body (type_checker.cpp 140): for e = f
\ a1 .. an with f a lambda, f's leading lambdas, at most n, are stripped
\ (i of them) to body; body applied to a(i+1) .. an when body has no
\ loose bound variable; when body is bound variable k, a(i-k) applied to
\ them; else e unchanged. A plain function of e, no reduction step: it
\ visits nothing but body's loose bound variables (lf-whnf-loose?);
\ e must be closed: a body bound variable beyond the stripped lambdas
\ (an open e) is invalid (review rvU4 L2).
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
  3 pick lf-term-first@ 2 pick < 0= if 2drop 2drop -1 outcome-invalid exit then
  drop lf-whnf-named - lf-whnf-apply ;
: lf-whnf-beta-head? ( e -- flag )
  dup lf-term-tag@ lf-tag-app = if lf-whnf-head lf-whnf-lam? else drop false then ;
: lf-cheap-beta ( e frames -- e' outcome )
  over lf-whnf-beta-head? 0= if drop outcome-ok exit then
  >r dup lf-whnf-spine-args ok-then? 0= if nip r> drop no-result exit then
  over lf-whnf-head over lf-whnf-stripped 2swap -rot r> lf-whnf-cheap-pick ;

\ ---------------------------------------------------------------------------
\ The public words (see the header): whnf_core without cheap_proj, and
\ with it (is_def_eq_core's, defeq.fs), whnf, and reduce_proj's visit of
\ a projection's term (450-453): whnf_core in a cheap whnf_core's mode,
\ else whnf.
: lf-wc-full-entry ( node frames -- ... frames next ) false lf-whnf-mode lf-wc-entry ;
: lf-wc-cheap-entry ( node frames -- ... frames next ) true lf-whnf-mode lf-wc-entry ;
: lf-whnf-core-call ( node frames cont -- ... frames next )
  ['] lf-wc-full-entry lf-whnf-open ;
: lf-whnf-cheap-call ( node frames cont -- ... frames next )
  ['] lf-wc-cheap-entry lf-whnf-open ;
: lf-whnf-call ( node frames cont -- ... frames next ) ['] lf-whnf-entry lf-whnf-open ;
: lf-whnf-proj-call ( node frames cont -- ... frames next )
  lf-whnf-cheap? if lf-wc-call else lf-whnf-call then ;
: lf-whnf-core-on ( node frames -- node' outcome )
  ['] lf-whnf-core-call frame-through drop ;
: lf-whnf-on ( node frames -- node' outcome ) ['] lf-whnf-call frame-through drop ;
