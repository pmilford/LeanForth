\ Iota reduction as Lean's kernel computes it (plan task 5.2.1b; ADR
\ 0015 rule R1): a port of inductive_reduce_rec (inductive.h 77-116,
\ with get_rec_rule_for and is_constructor_app, inductive.cpp 53-60 and
\ 114-122), which reduce_recursor (type_checker.cpp 393-407) calls from
\ whnf_core, behind whnf.fs's hook lf-whnf-iota (set here, while
\ loading). [kernel] code: experimental, not through the review gate, not
\ independently audited.
\
\ For an application whose head names a recursor that a usable slot holds
\ (its record B3 found equal to Lean's: numbers, k, rules), and that has
\ its major premise (argument numParams + numMotives + numMinors +
\ numIndices), the major premise is put in Lean's whnf (whnf.fs, a child
\ visit on the same frames). When that is an application of a
\ constructor Lean's environment holds, the recursor's rule for that
\ constructor, its universe parameters replaced by the application's
\ universe arguments, is applied to the application's parameters, motives
\ and minor premises, then to the constructor's last nfields arguments
\ (its fields), then to the arguments after the major premise; whnf_core
\ goes on with that. No rule applies (whnf_core keeps the application)
\ when the head is no recursor, the major premise is missing, the
\ recursor has no rule for the constructor, the constructor has fewer
\ arguments than the rule's fields, or the universe arguments are not as
\ many as the recursor's parameters -- each as in Lean.
\ For k set, Lean's to_cnstr_when_K (R2, plan task 5.2.1c; section
\ below) first puts the nullary constructor in the major premise's place
\ when the types agree. Not ported, so unknown (diagnostic 81, as
\ whnf.fs's default): a major premise that is no constructor application
\ when K could not run (outside environment mode, a major premise with
\ loose bound variables, an inference, whnf or comparison that is
\ unknown) or when its type may be a non-recursive structure that R3
\ cannot expand; and Lean's generated recursor that no slot holds (ADR
\ 0015 decision 12). A literal major premise (L2; plan task
\ 5.2.3) becomes a constructor first, as nat_lit_to_constructor makes
\ it: 0 as Nat.zero, n + 1 as Nat.succ n (reduce-nat.fs); a string
\ literal becomes String.ofList of its characters, put in whnf
\ (string_lit_to_constructor, kernel/string-literals.fs), and so does a
\ string literal projected (reduce_proj_core). Before any of
\ this, as reduce_recursor (393-398), quot_reduce_rec (quot.fs: Quot.lift
\ and Quot.ind on Quot.mk, plan task 5.2.4).
\ State: none of its own; the work arrays and the frames are whnf.fs's,
\ each array filled and used within one step; K lends a comparison
\ defeq.fs's typer cell, restored when the comparison returns.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/input.fs
require ../core/name-equal.fs
require ../core/names.fs
require ../core/projections.fs
require ../core/terms.fs
require ./defeq.fs
require ./environment.fs
require ./inductive-block.fs
require ./infer-proj.fs
require ./mixed-head.fs
require ./mixed-infer.fs
require ./reduce-nat.fs
require ./string-literals.fs
require ./whnf.fs
require ./quot.fs

\ ---------------------------------------------------------------------------
\ The recursor's record (core/input.fs): its numbers, k and rules.
: lf-iota-field ( decl k -- n ) swap lf-idecl-data swap lf-more-field ;
\ Its parameters, motives and minor premises: the arguments its rules take
\ first.
: lf-iota-prefix ( decl -- n )
  dup lf-irc-params lf-iota-field over lf-irc-motives lf-iota-field +
  swap lf-irc-minors lf-iota-field + ;
: lf-iota-major-idx ( decl -- i ) dup lf-iota-prefix swap lf-irc-indices lf-iota-field + ;
: lf-iota-k? ( decl -- flag ) lf-irc-k lf-iota-field 0<> ;
\ Its rule for the constructor named name, or 0 (get_rec_rule_for).
: lf-iota-rule ( decl name -- rule|0 )
  swap lf-idecl-data lf-irc-rules@ 0 ?do
    2dup i lf-irc-rule lf-irule-ctor lf-name-same? if i lf-irc-rule nip unloop exit then
  loop 2drop 0 ;

\ Spines: an application's arguments, its first k peeled off the end.
: lf-iota-n ( app -- n ) lf-mhead-spine nip ;
: lf-iota-peel ( node k -- node' ) 0 ?do lf-term-first@ loop ;
\ Argument i of app, which has n arguments.
: lf-iota-arg ( app n i -- arg ) - 1- lf-iota-peel lf-term-second@ ;
\ The major premise e of app, whose recursor's record is decl.
: lf-iota-major ( app decl -- e ) lf-iota-major-idx >r dup lf-iota-n r> lf-iota-arg ;
: lf-iota-head-name ( node -- name ) lf-whnf-head lf-whnf-cref lf-crec-name @ ;

\ The recursor app's head names: its record (decl ok); (-1 ok) when no
\ rule can apply (no constant, no recursor, or a constant Lean's
\ environment does not hold); unknown for Lean's generated recursor; or
\ the lookup's failure.
: lf-iota-of-slot ( const d -- decl outcome )
  dup -1 = if drop lf-whnf-pending exit then
  dup 0< if 2drop -1 outcome-ok exit then
  nip lf-whnf-decl ok-then? 0= if no-result exit then
  dup lf-idecl-kind @ lf-kind-recursor = if outcome-ok else drop -1 outcome-ok then ;
: lf-iota-recursor ( app -- decl outcome )
  lf-whnf-head dup lf-whnf-const? lf-whnf-env? and 0= if drop -1 outcome-ok exit then
  dup lf-whnf-lookup ok-then? 0= if nip no-result exit then lf-iota-of-slot ;

\ Whether node is a constructor application (is_constructor_app): its
\ head a constant that a usable slot holds as a constructor, whose
\ declaration is given (0 for none).
: lf-iota-ctor ( node -- decl|0 outcome )
  lf-whnf-head dup lf-whnf-const? 0= if drop 0 outcome-ok exit then
  lf-whnf-lookup ok-then? 0= if 0 swap exit then
  dup 0< if drop 0 outcome-ok exit then
  lf-whnf-decl ok-then? 0= if 0 swap exit then
  dup lf-idecl-kind @ lf-kind-constructor = 0= if drop 0 then outcome-ok ;
: lf-iota-ctor? ( node -- flag outcome )
  lf-iota-ctor ok-then? if 0<> outcome-ok else false swap then ;

\ A major premise that is no constructor application. Its type's name is
\ the head of the recursor type's binder major_idx (get_major_induct,
\ declaration.cpp 145-153), or 0. Whether it is a non-recursive structure
\ (is_non_rec_structure, inductive.cpp 28-33) its slot's shape says, the
\ numIndices and is_rec LeanForth computed, never the file's
\ (environment.fs lf-env-structure; review rvCONV B2).
: lf-iota-pi? ( node -- flag ) lf-term-tag@ lf-tag-pi = ;
: lf-iota-induct ( decl -- name|0 )
  dup lf-idecl-type @ swap lf-iota-major-idx 0 ?do
    dup lf-iota-pi? 0= if drop 0 unloop exit then lf-term-second@
  loop
  dup lf-iota-pi? 0= if drop 0 exit then
  lf-term-first@ lf-whnf-head dup lf-whnf-const? 0= if drop 0 exit then
  lf-whnf-cref lf-crec-name @ ;
: lf-iota-not-ported ( app -- -1 outcome ) lf-whnf-head lf-whnf-pending ;

\ Structure eta in iota (R3; plan task 5.2.2; to_cnstr_when_structure,
\ inductive.h 63-75, expand_eta_struct, inductive.cpp 99-112): a closed
\ major premise of a non-recursive structure, whose type -- inferred
\ aside, as Lean's infer_type, then put in whnf -- applies that structure
\ and is no proposition, becomes the structure's constructor at the
\ type's universe arguments, applied to the type's first numParams
\ arguments and to the projections e.0 .. e.(n-1) (core/projections.fs);
\ a proposition's stays as it is (BL-8), as does one whose type is
\ another. The inference runs inside an inference job in environment
\ mode only; elsewhere, for a term with loose bound variables (read
\ under binders the check did not open), and wherever that inference
\ fails, unknown. Aside, inference compares nothing (Lean's infer_type
\ here is infer_only), so it runs inside a comparison too: is_prop of
\ Prod Bool Bool, met in one (iota.prod-eta).
: lf-iota-typed ( node -- Ty outcome )
  lf-minfer-walk ok-then? if lf-minfer-whnf-job else no-result then ;
: lf-iota-type-of ( node -- Ty outcome ) ['] lf-iota-typed lf-iproj-aside ;
: lf-iota-closed? ( node -- flag )
  lf-minfer-frames lf-whnf-loose? ok? if 0= else drop false then ;
: lf-iota-of-struct? ( sdecl Ty -- flag )
  lf-whnf-head dup lf-whnf-const? 0= if 2drop false exit then
  lf-whnf-cref lf-crec-name @ swap lf-idecl-name @ lf-name-same? ;
\ The constructor named name at Ty's head's universe arguments, a new
\ constant node (its pairs copied first, as a reference needs).
: lf-iota-ctor-const ( name Ty -- node outcome )
  lf-whnf-head lf-whnf-cref lf-cref-pairs lf-whnf-pairs!
  ok-then? 0= if nip nip no-result exit then
  >r >r lf-name-generation @ r> r> lf-cref-new 0= if -1 outcome-full exit then
  lf-cterm-new if drop outcome-ok else -1 outcome-full then ;
: lf-iota-params ( node Ty p -- node' outcome )
  0 ?do dup dup lf-iota-n i lf-iota-arg rot swap lf-term-app
    0= if drop -1 outcome-full unloop exit then swap
  loop drop outcome-ok ;
: lf-iota-fields-of ( node major name nf -- node' outcome )
  0 ?do
    2dup i lf-proj-of ok-then? 0= if >r 2drop drop r> no-result unloop exit then
    >r rot r> lf-term-app 0= if 2drop -1 outcome-full unloop exit then -rot
  loop 2drop outcome-ok ;
: lf-iota-expand ( Ty major sdecl -- node outcome )
  dup lf-idecl-name @ >r lf-iproj-ctor ok-then? 0= if r> drop nip nip no-result exit then
  dup lf-idecl-name @ 3 pick lf-iota-ctor-const ok-then?
  0= if r> drop >r 2drop drop r> no-result exit then
  over lf-idecl-data lf-ict-params lf-more-field 4 pick 2dup lf-iota-n >
  if r> drop 2drop 2drop 2drop -1 outcome-unknown exit then
  swap lf-iota-params ok-then? 0= if r> drop >r 2drop drop r> no-result exit then
  swap lf-idecl-data lf-ict-fields lf-more-field rot swap r> swap lf-iota-fields-of
  rot drop ;
: lf-iota-eta ( app major sdecl -- major' true | reduct outcome false )
  lf-minfer-env? 0= if 2drop lf-iota-not-ported false exit then
  over lf-iota-closed? 0= if 2drop lf-iota-not-ported false exit then
  over lf-iota-type-of ok-then? 0= if drop 2drop lf-iota-not-ported false exit then
  2dup lf-iota-of-struct? 0= if 2drop 2drop -1 outcome-ok false exit then
  dup lf-iproj-prop? ok-then? 0= if drop 2drop drop lf-iota-not-ported false exit then
  if 2drop 2drop -1 outcome-ok false exit then
  -rot lf-iota-expand ok-then? 0= if nip no-result false exit then nip true ;

\ A major premise that is no constructor application (inductive.h 90-99):
\ K undecided (pending, below), unknown; a non-recursive structure, R3
\ above; any other type, no rule (-1 ok).
: lf-iota-no-ctor ( app decl m pending -- app decl m' true | reduct outcome false )
  if 2drop lf-iota-not-ported false exit then
  over lf-iota-induct ?dup 0= if 2drop lf-iota-not-ported false exit then
  lf-whnf-find ok-then? 0= if >r 2drop drop r> no-result false exit then
  dup 0< if drop 2drop lf-iota-not-ported false exit then
  lf-env-structure ok-then? 0= if >r 2drop drop r> no-result false exit then
  ?dup 0= if 2drop drop -1 outcome-ok false exit then
  >r 2 pick swap r> lf-iota-eta 0= if >r >r 2drop r> r> false exit then true ;

\ The rule applies when the constructor has its fields and the recursor
\ as many universe arguments as parameters (inductive.h 104-105).
: lf-iota-levels? ( app decl -- flag )
  swap lf-whnf-head lf-whnf-cref lf-crec-arity @ swap lf-idecl-arity @ = ;
: lf-iota-applies? ( app decl major rule -- flag )
  lf-irule-nfields swap lf-iota-n > 0= >r lf-iota-levels? r> and ;

\ The rule's right side at the application's universe arguments
\ (instantiate_lparams: the stored root itself when there are none), then
\ applied to the application's first p arguments, to the major premise's
\ last nfields arguments, and to the k arguments after the major premise
\ (inductive.h 106-115).
: lf-iota-rhs ( rhs decl const frames -- rhs' outcome )
  >r lf-whnf-cref lf-cref-pairs
  dup 0= if 2drop drop r> drop outcome-ok exit then
  lf-whnf-pairs! ok-then? 0= if nip nip nip r> drop no-result exit then
  r> lf-whnf-substitute ;
: lf-iota-head-args ( rhs app n p -- node outcome )
  - lf-iota-peel lf-whnf-spine-args ok-then? 0= if nip no-result exit then lf-whnf-apply ;
: lf-iota-fields ( rhs major nfields -- node outcome )
  swap lf-whnf-spine-args ok-then? 0= if nip nip no-result exit then drop lf-whnf-apply ;
: lf-iota-extra ( rhs app k -- node outcome )
  dup 0= if 2drop outcome-ok exit then
  swap lf-whnf-spine-args ok-then? 0= if nip nip no-result exit then drop lf-whnf-apply ;
: lf-iota-start ( app decl rule frames -- app decl rhs outcome )
  >r lf-irule-rhs over 3 pick lf-whnf-head r> lf-iota-rhs
  ok-then? 0= if no-result exit then
  2 pick dup lf-iota-n 3 pick lf-iota-prefix lf-iota-head-args ;
: lf-iota-finish ( app decl major rule rhs -- reduct outcome )
  -rot lf-irule-nfields lf-iota-fields ok-then? 0= if nip nip no-result exit then
  -rot over lf-iota-n swap lf-iota-major-idx - 1- lf-iota-extra ;
: lf-iota-apply ( app decl major rule frames -- reduct outcome )
  >r 2over 2 pick r> lf-iota-start ok-then? 0=
  if >r 2drop 2drop 2drop r> no-result exit then
  nip nip lf-iota-finish ;

\ After the major premise's whnf (inductive.h 92-115); pending: K
\ undecided.
: lf-iota-reduce ( app decl major pending frames -- reduct outcome )
  >r over lf-iota-ctor? ok-then? 0= if >r 2drop 2drop r> no-result r> drop exit then
  if drop else lf-iota-no-ctor 0= if r> drop exit then then
  2dup lf-iota-head-name lf-iota-rule ?dup 0=
  if 2drop drop -1 outcome-ok r> drop exit then
  2over 2over lf-iota-applies? 0= if 2drop 2drop -1 outcome-ok r> drop exit then
  r> lf-iota-apply ;

\ The hook's step (whnf.fs): the major premise's whnf is a child visit,
\ the recursor's record, the application and pending (K undecided)
\ saved across it.
\ A literal major premise as its constructor (L2).
: lf-iota-lit ( major -- major' outcome )
  dup lf-lit-leaf? if lf-reduce-nat-constructor else outcome-ok then ;
: lf-iota-saved ( frames -- app decl pending )
  dup frame-restore >r dup frame-restore >r frame-restore r> swap r> ;
\ A string literal major premise (L2, inductive.h 96-97): its constructor
\ form in whnf (kernel/string-literals.fs, a child visit) takes its place,
\ and the rule for its head applies or none does; Lean's structure eta
\ (R3) is not tried on it.
: lf-iota-string-major ( app decl major pending frames -- reduct outcome )
  >r over lf-iota-ctor? ok-then? 0= if >r 2drop 2drop r> no-result r> drop exit then
  if r> lf-iota-reduce exit then
  r> drop nip nip if lf-iota-not-ported else drop -1 outcome-ok then ;
: lf-iota-stringed ( major outcome frames -- ... frames next )
  >r ok-then? 0= if 3 r@ frame-drop r> lf-whnf-failed exit then
  r@ lf-iota-saved >r rot r> r@ lf-iota-string-major r> 0 ;
: lf-iota-majored ( major outcome frames -- ... frames next )
  >r ok-then? 0= if 3 r@ frame-drop r> lf-whnf-failed exit then
  dup lf-str-leaf? if r> ['] lf-iota-stringed lf-str-whnf-call exit then
  lf-iota-lit ok-then? 0= if 3 r@ frame-drop r> lf-whnf-failed exit then
  r@ lf-iota-saved >r rot r> r@ lf-iota-reduce r> 0 ;
: lf-iota-whnf ( e pending frames -- ... frames next )
  tuck frame-save ['] lf-iota-majored lf-whnf-call ;
: lf-iota-none ( app frames decl -- -1 ok frames 0 ) drop nip -1 outcome-ok rot 0 ;

\ ---------------------------------------------------------------------------
\ K-like reduction (R2; plan task 5.2.1c): to_cnstr_when_K (inductive.h
\ 31-49), which inductive_reduce_rec runs for a recursor with k set on
\ the major premise e as the application gives it, before its whnf
\ (89-91). e's type, inferred aside (Lean's infer, infer-only: the
\ typer mixed-infer.fs lends comparisons, on the frames' fuel), put in
\ whnf (a child visit), must apply a constant named as the recursor's
\ major inductive type (get_major_induct); mk_nullary_cnstr
\ (inductive.cpp 80-97) then makes that type's first constructor at the
\ type's universe arguments, applied to its first numParams arguments;
\ when the constructor's type, inferred aside, is_def_eq e's type
\ (defeq.fs, a child visit, lent the typer as inference lends it), the
\ constructor takes e's place. Otherwise e stays ("kept": another head, a
\ type without constructors, a no). Either way the major premise is then
\ put in whnf and reduced as above, as in Lean.
\ K cannot run as Lean (undecided, e stays): outside environment mode,
\ for an e with loose bound variables (read under binders the check did
\ not open), where the inference, a whnf or the comparison is unknown, a
\ lookup cannot follow Lean, or e's type has fewer than numParams
\ arguments (Lean would shrink its buffer past the end; never for a
\ well-typed e). A major premise whose whnf is then a constructor
\ application still reduces -- the rule of a k recursor takes no field,
\ so the reduct is the one K's constructor would give -- and any other
\ is unknown (diagnostic 81). Exhausted, full and invalid end the visit.
\ The comparison runs in environment mode with a typer, so it never
\ doubts (defeq.fs): its no is Lean's.
: lf-iota-k-kept ( e frames -- ... frames next ) false swap lf-iota-whnf ;
: lf-iota-k-undecided ( e frames -- ... frames next ) true swap lf-iota-whnf ;
\ A failure: unknown leaves K undecided; any other ends the visit, the
\ saved record and application dropped.
: lf-iota-k-fail ( e outcome frames -- -1 outcome frames 0 )
  rot drop 2 over frame-drop lf-whnf-failed ;
: lf-iota-k-failed ( e outcome frames -- ... frames next )
  over outcome-unknown = if nip lf-iota-k-undecided else lf-iota-k-fail then ;
\ After the child visits: e, saved last, back.
: lf-iota-k-off ( outcome frames -- ... frames next )
  dup frame-restore -rot lf-iota-k-failed ;
: lf-iota-k-keep ( frames -- ... frames next ) dup frame-restore swap lf-iota-k-kept ;

\ Whether K can run on e: environment mode, e closed.
: lf-iota-k-ready? ( e frames -- flag outcome )
  lf-minfer-env? 0= if 2drop false outcome-ok exit then
  lf-whnf-loose? ok-then? if 0= outcome-ok else false swap then ;
\ The major inductive type's name when Ty's head is a constant of that
\ name, else 0 (kept); unknown for a recursor type without that binder.
: lf-iota-k-induct ( Ty decl -- name|0 outcome )
  lf-iota-induct ?dup 0= if drop 0 outcome-unknown exit then
  swap lf-whnf-head dup lf-whnf-const? 0= if 2drop 0 outcome-ok exit then
  lf-whnf-cref lf-crec-name @ over lf-name-same? 0= if drop 0 then outcome-ok ;
\ get_first_cnstr (inductive.cpp 80-86): the first constructor's name of
\ the type named name, 0 for no inductive type or none.
: lf-iota-first-ctor ( name -- ctor|0 outcome )
  lf-whnf-find ok-then? 0= if 0 swap exit then
  dup 0< if drop 0 outcome-unknown exit then
  lf-whnf-decl ok-then? 0= if 0 swap exit then
  dup lf-idecl-kind @ lf-kind-inductive <> if drop 0 outcome-ok exit then
  lf-idecl-data lf-ity-ctors@ if @ else drop 0 then outcome-ok ;
\ mk_nullary_cnstr (88-97): ctor at Ty's universe arguments applied to
\ Ty's first p arguments.
: lf-iota-k-make ( ctor Ty p -- N outcome )
  over lf-iota-n over < if 2drop drop -1 outcome-unknown exit then
  >r tuck lf-iota-ctor-const ok-then? 0= if nip r> drop no-result exit then
  swap r> lf-iota-params ;
\ The nullary constructor for Ty, -1 when K keeps e.
: lf-iota-k-null ( Ty decl -- N|-1 outcome )
  2dup lf-iota-k-induct ok-then? 0= if nip nip -1 swap exit then
  ?dup 0= if 2drop -1 outcome-ok exit then
  lf-iota-first-ctor ok-then? 0= if nip nip -1 swap exit then
  ?dup 0= if 2drop -1 outcome-ok exit then
  swap lf-irc-params lf-iota-field >r swap r> lf-iota-k-make ;

\ The steps. e is saved above the record and the application while its
\ type is put in whnf (Ty), N and the comparison's typer above it while
\ Ty and N's type are compared.
: lf-iota-k-compared ( flag outcome frames -- ... frames next )
  >r r@ frame-restore lf-dq-typer ! r@ frame-restore r@ frame-restore 2swap
  ok-then? 0= if rot drop r> lf-iota-k-failed exit then
  if drop else nip then false r> lf-iota-whnf ;
: lf-iota-k-compare ( Ty N NT frames -- ... frames next )
  >r swap r@ frame-save lf-dq-typer @ r@ frame-save
  lf-dq-typer @ 0= if ['] lf-minfer-typer lf-dq-typer ! then
  r> ['] lf-iota-k-compared lf-defeq-call ;
: lf-iota-k-typed ( Ty outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-iota-k-off exit then
  dup 2 r@ frame-pick lf-iota-k-null ok-then? 0= if nip r> lf-iota-k-off exit then
  dup 0< if 2drop r> lf-iota-k-keep exit then
  dup r@ lf-minfer-typed ok-then? 0= if nip nip r> lf-iota-k-off exit then
  r> lf-iota-k-compare ;
: lf-iota-k ( e frames -- ... frames next )
  2dup lf-iota-k-ready? ok-then? 0= if swap lf-iota-k-fail exit then
  0= if lf-iota-k-undecided exit then
  2dup lf-minfer-typed ok-then? 0= if swap lf-iota-k-failed exit then
  rot 2 pick frame-save swap ['] lf-iota-k-typed lf-whnf-call ;
: lf-iota-go ( e k frames -- ... frames next )
  swap if lf-iota-k else false swap lf-iota-whnf then ;

\ ---------------------------------------------------------------------------
\ Projection reduction (plan task 5.2.2, ADR 0015 J1; reduce_proj
\ 444-454, reduce_proj_core 420-441, from whnf_core 504-510): a spine
\ whose head is a projection (core/projections.fs; alone, a spine of no
\ arguments) has the projection's term e put in Lean's whnf; a
\ constructor application of its leaf's structure with more than
\ numParams + i arguments gives argument numParams + i, the field,
\ applied to the spine's arguments, and whnf_core goes on with that;
\ anything else leaves the spine as it is.
\ In a whnf_core visit with cheap_proj (whnf.fs), e is put in whnf_core,
\ still cheap, instead of whnf (lf-whnf-proj-call, 450-453).
: lf-iota-field-of ( c k -- field|-1 )
  over lf-iota-n 2dup < if swap lf-iota-arg else 2drop drop -1 then ;
: lf-iota-projected-to ( leaf c decl -- field|-1 )
  dup lf-idecl-data lf-ict-induct lf-more-field 3 pick lf-proj-name lf-name-same?
  0= if 2drop drop -1 exit then
  lf-idecl-data lf-ict-params lf-more-field rot lf-proj-idx + lf-iota-field-of ;
\ reduce_proj_core (423-440) of c, no string literal: its field of leaf
\ when c is an application of a constructor of leaf's structure with
\ more than numParams + i arguments, else -1; or a lookup's failure.
: lf-iota-proj-field ( c leaf -- field|-1 outcome )
  over lf-iota-ctor ok-then? 0= if nip nip no-result exit then
  ?dup 0= if 2drop -1 outcome-ok exit then
  >r swap r> lf-iota-projected-to outcome-ok ;
: lf-iota-proj-made ( c outcome frames -- ... frames next )
  >r r@ frame-restore -rot ok-then? 0= if nip r> lf-whnf-failed exit then
  over lf-whnf-head lf-proj-leaf lf-iota-proj-field ok-then?
  0= if nip r> lf-whnf-failed exit then
  dup 0< if 2drop -1 outcome-ok r> 0 exit then
  swap dup lf-iota-n lf-iota-extra r> 0 ;
\ A string literal c first becomes its constructor form in whnf
\ (reduce_proj_core 421-422; kernel/string-literals.fs, a child visit).
: lf-iota-proj-string? ( c outcome -- flag ) ok? if lf-str-leaf? else drop false then ;
: lf-iota-proj-back ( c outcome frames -- ... frames next )
  2 pick 2 pick lf-iota-proj-string?
  if nip ['] lf-iota-proj-made lf-str-whnf-call else lf-iota-proj-made then ;
: lf-iota-proj ( app frames -- ... frames next )
  over over frame-save swap lf-whnf-head lf-proj-struct swap
  ['] lf-iota-proj-back lf-whnf-proj-call ;

\ reduce_proj_core for defeq.fs's step 8 (lazy_delta_proj_reduction,
\ 1089-1098; lf-dq-reduce-proj), the first step of a visit of its own:
\ c's field of leaf, or -1, with c as it is -- a string literal first put
\ in its constructor form in whnf (421-422), a child visit, leaf kept.
: lf-iota-core-back ( c outcome frames -- field|-1 outcome frames 0 )
  >r r@ frame-restore -rot ok-then? if swap lf-iota-proj-field else nip no-result then
  r> 0 ;
: lf-iota-core ( c leaf frames -- ... frames next )
  2 pick lf-str-leaf? if tuck frame-save ['] lf-iota-core-back lf-str-whnf-call exit then
  >r lf-iota-proj-field r> 0 ;
' lf-iota-core is lf-dq-reduce-proj

\ reduce_recursor (type_checker.cpp 393-407): quot_reduce_rec first
\ (quot.fs), then inductive_reduce_rec.
: lf-iota ( app frames -- ... frames next )
  over lf-whnf-head lf-proj? if lf-iota-proj exit then
  over lf-quot-rule ok-then? 0= if rot drop swap lf-whnf-failed exit then
  dup 0< 0= if swap lf-quot-reduce exit then drop
  over lf-iota-recursor ok-then? 0= if rot drop swap lf-whnf-failed exit then
  dup 0< if lf-iota-none exit then
  2 pick lf-iota-n over lf-iota-major-idx > 0= if lf-iota-none exit then
  dup 2 pick frame-save 2 pick 2 pick frame-save
  rot swap tuck lf-iota-major swap lf-iota-k? rot lf-iota-go ;
' lf-iota is lf-whnf-iota
