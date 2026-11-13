\ Nested inductive blocks (plan task 5.2.5b; ADR 0015, "Implementation
\ (plan task 5.2.5b)"), as Lean 4.35.0's kernel checks them
\ (inductive.cpp, commit eb6cafb7). A block is nested when a
\ constructor's type has, after its parameters, an application I Ds is
\ of an inductive type I of the environment whose parametric arguments Ds
\ mention a type of the block (Tree | node : List Tree -> Tree;
\ Lean.Syntax with Array Syntax). Lean checks such a block as a mutual
\ one with copies of I's types and then restores the occurrences
\ (add_inductive, 1248-1349). Two passes here, both run by
\ check-block.fs:
\   the translation (elim_nested_inductive_fn, 985-1180; step 4, after
\     T1): each constructor's type, and each auxiliary type's as it is
\     made (a queue, 1156-1176), is rewritten top-down after its
\     parameters (replace, 1133-1136): an application I Ds is that is a
\     nested occurrence (Lean's is_nested_inductive_app, 1023-1055: I an
\     inductive type of the environment, its numParams first arguments Ds
\     mentioning a type of the block, any made so far included, and then
\     no local variable in them, else nestedLocalVariable, N2) becomes
\     Iaux As is, As the parameters, its arguments is kept as they are.
\     The first time I Ds is met (compared by Lean's == with the
\     parameters abstracted, 1081-1091), every type J of I's block becomes
\     an auxiliary type _nested.J_k (mk_unique_name, 1001-1007: k from 1,
\     the first name no declaration before the block has): J's type at
\     I's universe levels, its first numParams(I) binders instantiated
\     with Ds (instantiate_pi_params, 1057-1063: a binder that is no Pi is
\     ill-formed, N3), under the constructor's own parameter binders; and
\     J's constructors likewise, their names' prefix J replaced by the
\     auxiliary name (1098-1127). Steps 5 to 12 then check the translated
\     block as a mutual one: inductive-block.fs reads its types and
\     constructors from lf-ind-aux-decls and lf-ind-ctor-decls;
\   the restoration (restore_nested 927-975, 1257-1314; step 12, after
\     the recursors are built): in every recursor type and rule, an
\     auxiliary type applied to at least the parameters becomes I Ds
\     (with the term's own outer binders as the parameters) applied to the
\     rest of its arguments, an auxiliary constructor becomes J.c at I's
\     levels applied to Ds and the rest; fewer arguments than parameters
\     is N3; the arguments of a replaced application are kept as they
\     are, as Lean's replace leaves them. The auxiliary types' recursors
\     are T.rec_1, T.rec_2, ... after the block's first type
\     (mk_aux_rec_name_map, 1191-1217): they get those names before the
\     recursors are built, which makes the terms the renaming makes. Their
\     rules name the constructors J.c (restore_constructor_name, 916-925),
\     kept per constructor for B3.
\ A constructor's own type restored is its input type (the translation
\ keeps its parameter binders and replaces each occurrence by one that
\ restores to it), so B3 compares constructors as before. Lean's typing
\ of the occurrences (1319-1324) is check-block.fs's; its re-check of
\ the restored terms (1333-1347) is defensive, as G4 is (ADR 0015
\ decision 7), and B3 compares them with the file's instead.
\ Every pass runs on frame steps (lib/frame.fs, mixed-rebuild.fs) on the
\ block's fuel; every table grows in the heap; a name the store cannot
\ hold is full. The three passes are Lean's replace calls, whose cache
\ keeps each shared (node, offset) pair's result (replace_fn.cpp 26-40):
\ each keeps its results in a replace memo (replace-memo.fs), so it grows
\ with those pairs, never with the paths (review MO). [kernel] code:
\ not through the review gate (AGENTS.md).
\ State: one record, lf-nest-state (the occurrence being replaced or
\ restored, the type J being copied, the lowering's amount,
\ mk_unique_name's next index), two slabs, lf-nest-doms (the
\ constructor's parameter domains) and lf-nest-text (a name component
\ being made), and three pass records (fields lf-npass-*: frames and
\ replace memo), lf-nest-xlate-pass (the translation), lf-nest-lower-pass
\ (an occurrence's parameters lowered to the block's) and
\ lf-nest-restore-pass (the restoration), all members of the checker
\ context; the block's own records are inductive-block.fs's, its term
\ builders inductive-recursor.fs's.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/name-equal.fs
require ../core/names.fs
require ../core/terms.fs
require ./environment.fs
require ./inductive-block.fs
require ./inductive-recursor.fs
require ./mixed-compare.fs
require ./mixed-instantiate.fs
require ./mixed-level-substitute.fs
require ./mixed-rebuild.fs
require ./replace-memo.fs

begin-structure /lf-nest
  field: lf-nest-node        \ the application being replaced or restored
  field: lf-nest-n           \ its arguments
  field: lf-nest-depth       \ binders around it (below the parameters when translating)
  field: lf-nest-k           \ I's numParams
  field: lf-nest-slot        \ I's slot
  field: lf-nest-key         \ I Ds at the parameters' depth
  field: lf-nest-j-decl      \ the type J being copied: its declaration
  field: lf-nest-aux-at      \ its auxiliary type
  field: lf-nest-amount      \ the lowering's amount
  field: lf-nest-next        \ mk_unique_name's next index
end-structure
/lf-nest context-record: lf-nest-state
1 cells context-slab: lf-nest-doms
1 context-slab: lf-nest-text
\ A pass's record: its frames first, so that a step finds the pass's
\ replace memo at the address of the frames it is given.
begin-structure /lf-npass
  /frames +field lf-npass-frames   \ fuel, nesting, the offset as context
  /lf-rmemo +field lf-npass-memo   \ results per (node, offset), one call's
end-structure
0 lf-npass-frames 0<> [if] .( inductive-nested.fs: frames come first) cr abort [then]
/lf-npass context-record: lf-nest-xlate-pass
/lf-npass context-record: lf-nest-lower-pass
/lf-npass context-record: lf-nest-restore-pass
: lf-nest-frames ( -- frames ) lf-nest-xlate-pass lf-npass-frames ;
: lf-nest-lower-frames ( -- frames ) lf-nest-lower-pass lf-npass-frames ;
: lf-nest-restore-frames ( -- frames ) lf-nest-restore-pass lf-npass-frames ;
\ The frames' stacks and the memos' tables, freed with the context (the
\ visitors are set once in every context, after their definitions).
:noname ( -- )
  lf-nest-xlate-pass lf-nest-lower-pass lf-nest-restore-pass 3 0 do
    dup lf-npass-frames frame-free lf-npass-memo lf-rmemo-release
  loop ; context-teardown

: lf-nest-site ( -- site ) c" inductive-nested lf-nest-translate" ;
: lf-nest-p ( -- p ) lf-ind-nparams ;
: lf-nest-node@ ( -- node ) lf-nest-state lf-nest-node @ ;
: lf-nest-n@ ( -- n ) lf-nest-state lf-nest-n @ ;
: lf-nest-depth@ ( -- c ) lf-nest-state lf-nest-depth @ ;
: lf-nest-k@ ( -- k ) lf-nest-state lf-nest-k @ ;
: lf-nest-key@ ( -- node ) lf-nest-state lf-nest-key @ ;
: lf-nest-a@ ( -- a ) lf-nest-state lf-nest-aux-at @ ;
: lf-nest-j@ ( -- decl ) lf-nest-state lf-nest-j-decl @ ;
: lf-nest-head ( -- head ) lf-nest-node@ lf-ind-spine drop ;
\ Take the application node at depth c: it, c and its arguments.
: lf-nest-take ( node c -- )
  lf-nest-state lf-nest-depth ! dup lf-nest-state lf-nest-node !
  lf-ind-spine nip lf-nest-state lf-nest-n ! ;
\ N3, Lean's "ill-formed declaration" and "failed to restore" (x: the
\ node or name met).
: lf-nest-shape ( x -- -1 outcome )
  0 lf-nest-site lf-diag-nested-shape lf-diag-note outcome-rejected no-result ;
\ A node made by inductive-recursor.fs's builders (whose failure sticks
\ until lf-rcr-begin): (node ok), or (-1 failure).
: lf-nest-built ( node -- node outcome ) lf-rcr-status@ dup ok? 0= if nip no-result then ;
\ A constant name at the level pairs given.
: lf-nest-const ( name pairs n -- node )
  >r >r lf-name-generation @ r> r> lf-cref-new lf-rcr-referenced ;

\ ---------------------------------------------------------------------------
\ Passes on frame steps: a frames record's fuel lent from the block's and
\ given back; a pass on root from context 0: (root' ok) or (-1 failure),
\ every node it made discarded on failure (mixed-rebuild.fs).
: lf-nest-lend ( frames -- ) frame-fuel @ lf-ind-fuel ! ;
: lf-nest-back ( frames -- ) lf-ind-fuel @ swap frame-fuel ! ;
\ Lean's replace cache (replace_fn.cpp 26-40, m_cache): a pass keeps the
\ result of each application, binder and replaced node at the offset of
\ its visit for the rest of its call, in its record's replace memo
\ (replace-memo.fs), and gives it back when it meets the node there
\ again, for the visit's one unit of fuel. A call begins with an empty
\ memo (a call that threw may have left entries, stale for the next) and
\ takes its entries out when it ends. The memo costs no fuel.
: lf-nest-memo ( frames -- memo ) lf-npass-memo ;
: lf-nest-memo-begin ( frames -- )
  lf-nest-memo dup lf-rmemo-count if dup lf-rmemo-empty then 0 swap lf-rmemo-begin ;
: lf-nest-memo-end ( outcome frames -- outcome ) over swap lf-nest-memo lf-rmemo-end ;
: lf-nest-recall? ( node frames -- result true | false )
  tuck frame-context @ rot lf-nest-memo lf-rmemo@ ;
: lf-nest-remember ( result node frames -- )
  tuck frame-context @ rot lf-nest-memo lf-rmemo! ;
\ A visit's result kept for its node when it is one (ok).
: lf-nest-kept ( result outcome node frames -- result outcome )
  2over ok? nip if >r >r over r> r> lf-nest-remember else 2drop then ;
: lf-nest-run ( root frames -- root' outcome )
  lf-ind-fuel @ over frame-budget 0= if 2drop -1 outcome-invalid exit then
  dup lf-nest-memo-begin dup >r 0 swap lf-rebuild-run r@ frame-fuel @ lf-ind-fuel !
  r@ lf-nest-memo-end r> lf-nest-site lf-diag-frames nip ;
\ A binary node rebuilt as mixed-rebuild.fs's passes rebuild it, its
\ result kept: the last step reads the node, which the visit saved below
\ its first child's result.
: lf-nest-rebuilt ( r2 outcome frames -- result outcome frames 0 )
  1 over frame-pick >r ['] lf-rebuild-build lf-rebuild-joined drop
  r> swap dup >r lf-nest-kept r> 0 ;
: lf-nest-second ( r1 outcome frames -- second frames next | -1 outcome frames 0 )
  ['] lf-nest-rebuilt lf-rebuild-next ;
: lf-nest-binary ( node frames -- first frames next | -1 outcome frames 0 )
  2dup lf-rebuild-stuck? if nip >r lf-rebuild-deep r> 0 exit then
  ['] lf-nest-second lf-rebuild-first ;
\ A node met before at this offset in this call: its result again; else
\ visited by xt ( node frames -- ... frames next ).
: lf-nest-again ( node frames xt -- ... frames next )
  >r 2dup lf-nest-recall? if r> drop lf-replace-recall else r> execute then ;
\ A visit that keeps its node, and one that visits an application's
\ children (any other node kept).
: lf-nest-keep ( node frames -- node outcome frames 0 )
  ['] lf-rebuild-keep lf-rebuild-return ;
: lf-nest-descend ( node frames -- ... frames next )
  over lf-tag-app lf-ind-tag? if lf-nest-binary else lf-nest-keep then ;
\ The answer "not replaced" of a replacing step: visit the node's
\ children.
-1 constant lf-nest-none
: lf-nest-none? ( result outcome -- flag ) ok? swap lf-nest-none = and ;
\ A replacing visit: try ( node c -- result outcome ) on the node at the
\ visit's context, on the block's fuel; not replaced, its children.
: lf-nest-try ( node frames try -- result outcome )
  >r dup >r lf-nest-lend r@ frame-context @ r> r> swap >r execute r> lf-nest-back ;
: lf-nest-replaced ( node frames try -- ... frames next )
  >r 2dup r> lf-nest-try 2dup lf-nest-none?
  if 2drop lf-nest-descend else 2swap dup >r lf-nest-kept r> 0 then ;
\ A leaf no store holds is refused, any other kept.
: lf-nest-leaf ( node frames tag -- ... frames next )
  lf-rebuild-no-tag = if lf-rebuild-refuse else lf-nest-keep then ;
\ A node no try is asked of: a binder's children visited, a leaf kept.
: lf-nest-other ( node frames tag -- ... frames next )
  dup lf-term-binary-tag? 0= if lf-nest-leaf exit then
  drop ['] lf-nest-binary lf-nest-again ;

\ ---------------------------------------------------------------------------
\ Lowering the parametric arguments of an occurrence under c binders
\ below the parameters to the parameters' depth (Lean's replace_params,
\ 1013-1016, on terms that have them as free variables): a variable
\ bound inside is kept, one of the c binders is a local variable (Lean's
\ has_loose_bvars, 1036: rejected by the caller), any other moves down
\ by c.
: lf-nest-amount@ ( -- c ) lf-nest-state lf-nest-amount @ ;
: lf-nest-loose ( node frames -- -1 outcome ) 2drop outcome-rejected no-result ;
: lf-nest-down ( node frames -- result outcome )
  drop lf-term-first@ lf-nest-amount@ - lf-term-bvar lf-rebuild-allocated ;
: lf-nest-lower-bvar ( node frames -- result outcome )
  over lf-term-first@ over frame-context @ - dup 0< if drop lf-rebuild-keep exit then
  lf-nest-amount@ < if lf-nest-loose else lf-nest-down then ;
: lf-nest-lower-leaf ( node frames tag -- result outcome )
  case lf-tag-bvar of lf-nest-lower-bvar endof
    lf-rebuild-no-tag of lf-rebuild-bad endof  >r lf-rebuild-keep r> endcase ;
: lf-nest-lower-visit ( node frames -- ... frames next )
  over lf-term-valid? lf-rebuild-tag dup lf-term-binary-tag?
  if drop ['] lf-nest-binary lf-nest-again else over >r lf-nest-lower-leaf r> 0 then ;
:noname ( -- ) ['] lf-nest-lower-visit lf-nest-lower-frames frame-init ; context-setup
: lf-nest-lower ( node c -- node' outcome )
  ?dup 0= if outcome-ok exit then
  lf-nest-state lf-nest-amount ! lf-nest-lower-frames lf-nest-run ;

\ ---------------------------------------------------------------------------
\ Names. A name's components; its ancestor t prefixes up; a component
\ put on base; name's last t components put on base (Lean's operator+
\ and replace_prefix, name.cpp 302-318, 363-375).
: lf-nest-length ( name -- n )
  0 begin over while 1+ swap lf-name-prefix@ swap repeat nip ;
: lf-nest-up ( name t -- name' ) 0 ?do lf-name-prefix@ loop ;
: lf-nest-part ( base part -- name true | false )
  dup lf-name-tag@ lf-name-tag-str =
  if lf-name-text lf-name-str else lf-name-payload lf-name-num then ;
: lf-nest-graft ( name t base -- name' true | false )
  over 0 ?do
    2 pick 2 pick i - 1- lf-nest-up lf-nest-part 0= if 2drop false unloop exit then
  loop nip nip true ;
\ How many prefixes up name is ancestor, or -1.
: lf-nest-distance ( name ancestor -- t|-1 )
  0 begin 2 pick 2 pick lf-name-same? 0= while
    rot dup 0= if 2drop drop -1 exit then lf-name-prefix@ -rot 1+
  repeat nip nip ;
\ Lean's replace_prefix: name with its prefix prefix replaced by new;
\ name itself when prefix is none of its prefixes.
: lf-nest-replace-prefix ( name prefix new -- name' true | false )
  >r over swap lf-nest-distance dup 0< if drop r> drop true exit then r> lf-nest-graft ;
\ Lean's appendIndexAfter (append_after(idx), name.cpp 340-342): a last
\ string component s becomes s_idx, a last number gets a component _idx.
: lf-nest-digits ( n -- c-addr u ) base @ >r decimal 0 <# #s [char] _ hold #> r> base ! ;
: lf-nest-text-at ( -- addr ) 0 lf-nest-text slab-at ;
: lf-nest-joined ( c-addr u c-addr2 u2 -- c-addr' u' true | false )
  2over nip over + dup lf-nest-text slab-hold ok? 0= if drop 2drop 2drop false exit then
  >r 2swap tuck lf-nest-text-at swap move lf-nest-text-at + swap move
  lf-nest-text-at r> true ;
: lf-nest-str-indexed ( c-addr u name -- name' true | false )
  dup lf-name-prefix@ >r lf-name-text 2swap lf-nest-joined
  if r> -rot lf-name-str else r> drop false then ;
: lf-nest-indexed ( name idx -- name' true | false )
  lf-nest-digits rot dup lf-name-tag@ lf-name-tag-str =
  if lf-nest-str-indexed else -rot lf-name-str then ;
\ mk_unique_name: base_k, k the next index from 1 (counted on for each
\ name tried) for which no declaration before the block has that name:
\ any slot, the test environment.fs records as a query an import replays
\ (lf-slot-any; review rvSN3 m5).
: lf-nest-taken? ( name -- flag ) ['] lf-slot-any lf-env-limit lf-env-first 0< 0= ;
: lf-nest-unique ( base -- name true | false )
  begin dup lf-nest-state lf-nest-next @ lf-nest-indexed 0= if drop false exit then
    1 lf-nest-state lf-nest-next +! dup lf-nest-taken? while drop
  repeat nip true ;
\ _nested + J, made unique: an auxiliary type's name.
: lf-nest-aux-name ( J -- name true | false )
  0 s" _nested" lf-name-str 0= if drop false exit then
  >r dup lf-nest-length r> lf-nest-graft 0= if false exit then lf-nest-unique ;

\ ---------------------------------------------------------------------------
\ Making an auxiliary type J_k for the occurrence I Ds: a declaration of
\ the environment named name, of kind (Lean's m_env.get, which throws for
\ none: N3), its slot usable, else the lookup's failure (K5, too early).
: lf-nest-decl ( name kind -- decl outcome )
  >r dup lf-env-limit lf-env-find dup outcome-rejected =
  if 2drop r> drop lf-nest-shape exit then
  ok-then? 0= if nip r> drop no-result exit then nip
  lf-input-decl dup lf-idecl-kind @ r> = if outcome-ok else lf-nest-shape then ;
\ Its type at I's universe levels (instantiate_lparams, 1106): the
\ occurrence's head's levels for the declaration's own parameters; N3
\ when their numbers differ.
: lf-nest-levels ( -- pairs n ) lf-nest-head lf-term-first@ lf-cref-slot lf-cref-pairs ;
: lf-nest-subst ( root formals pairs n -- root' outcome )
  >r >r >r lf-rcr-handle r> r> r> lf-ind-fuel @ lf-mixed-level-substitute
  lf-mls-fuel @ lf-ind-fuel ! dup ok? if 2drop outcome-ok else no-result then ;
: lf-nest-at-levels ( decl -- root outcome )
  dup lf-idecl-type @ swap lf-idecl-params@ lf-nest-levels
  rot over <> if 2drop drop lf-nest-shape exit then
  dup 0= if 2drop drop outcome-ok exit then lf-nest-subst ;
\ instantiate_pi_params (1057-1063): its first numParams(I) binders, each
\ a Pi (else N3), instantiated with Ds, D0 first.
: lf-nest-key-arg ( i -- D ) lf-nest-key@ lf-nest-k@ rot lf-ind-arg ;
: lf-nest-inst ( root D -- root' outcome )
  >r lf-term-second@ lf-rcr-handle r> lf-rcr-handle lf-ind-fuel @
  lf-mixed-instantiate lf-minst-fuel @ lf-ind-fuel ! nip ;
: lf-nest-pi-params ( root -- root' outcome )
  lf-nest-k@ 0 ?do
    dup lf-tag-pi lf-ind-tag? 0= if lf-nest-shape unloop exit then
    i lf-nest-key-arg lf-nest-inst dup ok? 0= if unloop exit then drop
  loop outcome-ok ;
\ Under the constructor's own parameter binders (lctx.mk_pi(As, ...)).
: lf-nest-dom ( i -- addr ) cells lf-nest-doms slab-base + ;
: lf-nest-wrap ( body -- root outcome )
  lf-nest-p 0 ?do lf-nest-p 1- i - lf-nest-dom @ swap lf-rcr-pi loop lf-nest-built ;
: lf-nest-instance ( decl -- root outcome )
  lf-nest-at-levels ok-then? 0= if no-result exit then
  lf-nest-pi-params ok-then? 0= if no-result exit then lf-nest-wrap ;
\ The occurrence J Ds an auxiliary type stands for: J at I's levels
\ applied to the lowered Ds.
: lf-nest-key-of ( J -- key outcome )
  lf-nest-levels lf-nest-const lf-nest-k@ 0 ?do i lf-nest-key-arg lf-rcr-app loop
  lf-nest-built ;
\ A new record: an auxiliary type's, a constructor's (their fields zero,
\ the declaration the first type's, a constructor's of kind constructor).
: lf-nest-template ( decl -- ) lf-ind-type swap /lf-idecl move ;
: lf-nest-grow-type ( -- a outcome )
  lf-ind-types@ dup 1+ lf-ind-type-cells slab-hold ok-then? 0= if no-result exit then
  dup lf-ind-in-types@ - 1+ lf-ind-aux-decls slab-hold ok-then? 0= if no-result exit then
  dup lf-ind-ty /lf-ty erase dup lf-ind-aux-decl lf-nest-template outcome-ok ;
: lf-nest-ctor-decl ( j -- decl ) lf-ind-ctor-decls slab-at ;
: lf-nest-grow-ctor ( -- j outcome )
  lf-ind-ctors@ dup 1+ lf-ind-ctor-cells slab-hold ok-then? 0= if no-result exit then
  dup 1+ lf-ind-ctor-decls slab-hold ok-then? 0= if no-result exit then
  dup lf-ind-ctor-cells slab-at /lf-ind-ctor erase dup lf-nest-ctor-decl lf-nest-template
  lf-kind-constructor over lf-nest-ctor-decl lf-idecl-kind !
  1 lf-ind-state lf-ind-ctors +! outcome-ok ;
\ A constructor c of J: _nested.J_k.c, its type made as J's.
: lf-nest-ctor-name ( c -- name true | false )
  lf-nest-j@ lf-idecl-name @ lf-nest-a@ lf-ind-tname lf-nest-replace-prefix ;
: lf-nest-make-ctor ( c -- outcome )
  dup lf-kind-constructor lf-nest-decl ok-then? 0= if nip exit then
  lf-nest-instance ok-then? 0= if nip exit then
  swap lf-nest-ctor-name 0= if drop outcome-full exit then
  lf-nest-grow-ctor ok-then? 0= if nip nip exit then
  lf-nest-ctor-decl tuck lf-idecl-name ! lf-idecl-type ! outcome-ok ;
\ The type J_k: its name, type and key, then its constructors.
: lf-nest-type-named ( -- outcome )
  lf-nest-j@ lf-idecl-name @ lf-nest-aux-name 0= if outcome-full exit then
  lf-nest-a@ lf-ind-aux-decl lf-idecl-name ! outcome-ok ;
: lf-nest-type-typed ( -- outcome )
  lf-nest-j@ lf-nest-instance ok-then? 0= if exit then
  lf-nest-a@ lf-ind-aux-decl lf-idecl-type ! outcome-ok ;
: lf-nest-type-keyed ( -- outcome )
  lf-nest-j@ lf-idecl-name @ lf-nest-key-of ok-then? 0= if exit then
  lf-nest-a@ lf-ind-ty lf-ty-key ! outcome-ok ;
: lf-nest-j-ctors ( -- items n ) lf-nest-j@ lf-idecl-data lf-ity-ctors@ ;
: lf-nest-type-ctors ( -- outcome )
  lf-ind-ctors@ lf-nest-a@ lf-ind-ty lf-ty-ctor !
  lf-nest-j-ctors nip lf-nest-a@ lf-ind-ty lf-ty-ctors ! 1 lf-ind-state lf-ind-types +!
  lf-nest-j-ctors 0 ?do
    dup i cells + @ lf-nest-make-ctor dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
: lf-nest-make-type ( J -- outcome )
  lf-kind-inductive lf-nest-decl ok-then? 0= if exit then lf-nest-state lf-nest-j-decl !
  lf-nest-grow-type ok-then? 0= if exit then lf-nest-state lf-nest-aux-at !
  outcome-ok ['] lf-nest-type-named ok-and ['] lf-nest-type-typed ok-and
  ['] lf-nest-type-keyed ok-and ['] lf-nest-type-ctors ok-and ;
\ Every type of I's block, in its all list's order: (a ok), a I's own.
: lf-nest-all ( -- items n )
  lf-nest-state lf-nest-slot @ lf-input-decl lf-idecl-data lf-ity-all@ ;
: lf-nest-own ( -- i )
  lf-nest-head lf-ind-const-name lf-nest-all 0 ?do
    2dup i cells + @ lf-name-same? if 2drop i unloop exit then
  loop 2drop -1 ;
: lf-nest-new ( -- a outcome )
  lf-nest-own dup 0< if drop -1 outcome-invalid exit then lf-ind-types@ +
  lf-nest-all 0 ?do
    dup i cells + @ lf-nest-make-type dup ok?
    0= if nip nip unloop no-result exit then drop
  loop drop outcome-ok ;

\ ---------------------------------------------------------------------------
\ The translation. An auxiliary type whose key is the occurrence's (Lean's
\ ==, 1087: mixed-compare.fs lf-mixed-equal, each shared pair once,
\ binder names and annotations not stored): a, or -1. A difference is an
\ answer, not a failure: the diagnostic stays as it was.
: lf-nest-same? ( a -- flag outcome )
  lf-ind-ty lf-ty-key @ lf-rcr-handle lf-nest-key@ lf-rcr-handle lf-ind-fuel @
  lf-mixed-equal lf-mcompare-fuel @ lf-ind-fuel ! ;
: lf-nest-known ( -- a outcome )
  lf-ind-types@ lf-ind-in-types@ ?do
    i lf-nest-same? ok-then? 0= if -1 swap unloop exit then
    if i outcome-ok unloop exit then
  loop -1 outcome-ok ;
\ The replacement Iaux As is: the auxiliary type at the block's levels,
\ applied to the parameters #(c+p-1) .. #c and to the occurrence's
\ arguments after I's parameters.
: lf-nest-is ( f -- node )
  lf-nest-n@ lf-nest-k@ ?do lf-nest-node@ lf-nest-n@ i lf-ind-arg lf-rcr-app loop ;
: lf-nest-aux-app ( a -- result outcome )
  lf-ind-tname lf-rcr-const lf-nest-depth@ lf-nest-p + 1- lf-nest-p lf-rcr-apply-vars
  lf-nest-is lf-nest-built ;
: lf-nest-replace ( -- result outcome )
  lf-nest-known ok-then? 0= if no-result exit then
  dup 0< if drop lf-nest-new ok-then? 0= if no-result exit then then lf-nest-aux-app ;
\ Whether one of the first k of the n arguments of node's spine mentions
\ a type of the block (on the block's fuel).
: lf-nest-mentions? ( node n k -- flag outcome )
  0 ?do
    2dup i lf-ind-arg lf-ind-occurrences ok-then?
    0= if nip nip false swap unloop exit then
    if 2drop true outcome-ok unloop exit then
  loop 2drop false outcome-ok ;
\ An occurrence's I: a type Lean's environment holds (lf-env-find),
\ inductive; its slot, or -1 for none (no inductive slot of that name
\ before the block: Lean's find fails or finds no inductive type; none
\ usable: Lean's environment does not hold it); K5 or invalid when Lean
\ may hold it.
: lf-nest-inductive ( name -- d outcome )
  dup lf-ind-earlier 0< if drop -1 outcome-ok exit then
  lf-env-limit lf-env-find dup outcome-rejected = if 2drop -1 outcome-ok exit then
  ok-then? 0= if no-result exit then
  dup lf-input-decl lf-idecl-kind @ lf-kind-inductive <> if drop -1 then outcome-ok ;
\ I's numParams k, at most the occurrence's arguments, k > 0.
: lf-nest-k! ( d -- flag )
  dup lf-nest-state lf-nest-slot ! lf-input-decl lf-idecl-data lf-ity-params lf-more-field
  dup lf-nest-state lf-nest-k ! dup 0> swap lf-nest-n@ > 0= and ;
\ The key: I Ds lowered to the parameters' depth; a local variable is N2.
: lf-nest-partial ( -- node )
  lf-nest-node@ lf-nest-n@ lf-nest-k@ - 0 ?do lf-term-first@ loop ;
: lf-nest-local ( -- outcome )
  lf-nest-node@ lf-nest-depth@ lf-nest-site lf-diag-nested-local lf-diag-note
  outcome-rejected ;
: lf-nest-keyed ( -- outcome )
  lf-nest-partial lf-nest-depth@ lf-nest-lower dup outcome-rejected =
  if 2drop lf-nest-local exit then
  ok-then? 0= if exit then lf-nest-state lf-nest-key ! outcome-ok ;
\ The test, in Lean's order: a constant head; some argument mentioning
\ the block (else no first k can); I; k; the first k mentioning it; Ds
\ without local variables. (result ok) replaced; (-1 ok) none.
: lf-nest-candidate? ( -- flag outcome )
  lf-nest-head lf-tag-constant lf-ind-tag? 0= if false outcome-ok exit then
  lf-nest-node@ lf-nest-n@ dup lf-nest-mentions? ;
: lf-nest-is-type? ( -- flag outcome )
  lf-nest-head lf-ind-const-name lf-nest-inductive ok-then? 0= if false swap exit then
  dup 0< if drop false outcome-ok exit then
  lf-nest-k! 0= if false outcome-ok exit then
  lf-nest-node@ lf-nest-n@ lf-nest-k@ lf-nest-mentions? ;
: lf-nest-occurrence ( node c -- result outcome )
  lf-nest-take lf-nest-candidate? ok-then? 0= if no-result exit then
  0= if lf-nest-none outcome-ok exit then
  lf-nest-is-type? ok-then? 0= if no-result exit then
  0= if lf-nest-none outcome-ok exit then
  lf-nest-keyed dup ok? 0= if no-result exit then drop lf-nest-replace ;
\ The visit: an application replaced or its children visited; a binder's
\ children; any other leaf kept. A binary node met before at this offset
\ gives its result again.
: lf-nest-occurring ( node frames -- ... frames next )
  ['] lf-nest-occurrence lf-nest-replaced ;
: lf-nest-visit ( node frames -- ... frames next )
  over lf-term-valid? lf-rebuild-tag
  dup lf-tag-app = if drop ['] lf-nest-occurring lf-nest-again exit then
  lf-nest-other ;
:noname ( -- ) ['] lf-nest-visit lf-nest-frames frame-init ; context-setup
\ Constructor j's type: its first p binders' domains recorded (it has
\ them: T1, or made so), its body translated, the binders put back.
: lf-nest-strip ( root -- body outcome )
  lf-nest-p lf-nest-doms slab-hold ok-then? 0= if no-result exit then
  lf-nest-p 0 ?do
    dup lf-tag-pi lf-ind-tag? 0= if drop -1 outcome-invalid unloop exit then
    dup lf-term-first@ i lf-nest-dom ! lf-term-second@
  loop outcome-ok ;
: lf-nest-type-cell ( j -- addr ) lf-nest-ctor-decl lf-idecl-type ;
: lf-nest-ctor ( j -- outcome )
  dup lf-nest-type-cell @ lf-nest-strip ok-then? 0= if nip exit then
  lf-nest-frames lf-nest-run ok-then? 0= if nip exit then
  lf-nest-wrap ok-then? 0= if nip exit then swap lf-nest-type-cell ! outcome-ok ;
\ The queue: each type's constructors in turn, the auxiliary types made
\ meanwhile included.
: lf-nest-type ( q -- outcome )
  dup lf-ind-ty lf-ty-ctors @ over lf-ind-ty lf-ty-ctor @ tuck + swap ?do
    i lf-nest-ctor dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
: lf-nest-queue ( -- outcome )
  0 begin dup lf-ind-types@ < while
    dup lf-nest-type dup ok? 0= if nip exit then drop 1+
  repeat drop outcome-ok ;
\ Before: every input constructor's declaration copied, read in place of
\ the input's from now on; the builders' levels the block's. After: the
\ auxiliary types counted; none (the audit's test found more than
\ Lean's), the input read again, else Lean's is_rec and is_reflexive on
\ the translated block.
: lf-nest-copy ( j -- )
  dup lf-ind-in-types@ + lf-ind-member swap lf-nest-ctor-decl /lf-idecl move ;
: lf-nest-begin ( -- outcome )
  lf-ind-in-ctors@ lf-ind-ctor-decls slab-hold dup ok? 0= if exit then drop
  lf-ind-in-ctors@ 0 ?do i lf-nest-copy loop true lf-ind-state lf-ind-xlated !
  1 lf-nest-state lf-nest-next ! 0 lf-rcr-begin lf-rcr-levels lf-rcr-status@ ;
: lf-nest-end ( outcome -- outcome )
  lf-ind-types@ lf-ind-in-types@ - lf-ind-state lf-ind-aux ! dup ok? 0= if exit then
  lf-ind-aux@ if drop lf-ind-flags-again exit then false lf-ind-state lf-ind-xlated ! ;
\ Translate the block when the audit found it may be nested: ok (its
\ auxiliary types lf-ind-aux@, 0 when not nested), rejected (N2, N3), K5
\ (unknown, unsupported) or invalid for an I Lean may hold, full,
\ exhausted.
: lf-nest-translate ( -- outcome )
  lf-ind-maybe? 0= if outcome-ok exit then
  lf-nest-begin ['] lf-nest-queue ok-and lf-nest-end ;

\ ---------------------------------------------------------------------------
\ The restoration. Which auxiliary type a constant names (a, or -1);
\ which auxiliary constructor (j, or -1).
: lf-nest-aux-type ( head -- a ) lf-ind-which dup lf-ind-in-types@ < if drop -1 then ;
: lf-nest-aux-ctor ( head -- j )
  dup lf-tag-constant lf-ind-tag? 0= if drop -1 exit then lf-ind-const-name
  lf-ind-ctors@ lf-ind-in-ctors@ ?do
    dup i lf-ind-ctor lf-idecl-name @ lf-name-same? if drop i unloop exit then
  loop drop -1 ;
\ Type a's key under the node's binders (c from the root, p of them the
\ parameters).
: lf-nest-key-at ( a -- node )
  lf-ind-ty lf-ty-key @ 0 lf-nest-depth@ lf-nest-p - lf-rcr-shift ;
\ f applied to the node's arguments after the parameters.
: lf-nest-rest ( f -- node )
  lf-nest-n@ lf-nest-p ?do lf-nest-node@ lf-nest-n@ i lf-ind-arg lf-rcr-app loop ;
\ f applied to the arguments of key K.
: lf-nest-key-args ( f K -- node )
  dup lf-ind-spine nip 0 ?do tuck dup lf-ind-spine nip i lf-ind-arg lf-rcr-app swap loop
  drop ;
\ Constructor j's restored name at the levels of K's head.
: lf-nest-ctor-head ( j K -- head )
  lf-ind-spine drop lf-term-first@ lf-cref-slot lf-cref-pairs rot
  lf-ind-ctor-cells slab-at lf-ictor-name @ -rot lf-nest-const ;
\ Fewer arguments than parameters is N3; a node above the parameters is
\ invalid (no generated term has one).
: lf-nest-short ( -- outcome|0 )
  lf-nest-depth@ lf-nest-p < if outcome-invalid exit then
  lf-nest-n@ lf-nest-p < if lf-nest-node@ lf-nest-shape nip exit then 0 ;
: lf-nest-type-back ( a -- result outcome )
  lf-nest-short ?dup if nip no-result exit then
  lf-nest-key-at lf-nest-rest lf-nest-built ;
: lf-nest-ctor-back ( j -- result outcome )
  lf-nest-short ?dup if nip no-result exit then
  dup lf-ind-owner lf-nest-key-at lf-nest-built ok-then? 0= if nip no-result exit then
  tuck lf-nest-ctor-head swap lf-nest-key-args lf-nest-rest lf-nest-built ;
: lf-nest-restore-node ( node c -- result outcome )
  lf-nest-take lf-nest-head lf-nest-aux-type dup 0< 0= if lf-nest-type-back exit then drop
  lf-nest-head lf-nest-aux-ctor dup 0< 0= if lf-nest-ctor-back exit then
  drop lf-nest-none outcome-ok ;
: lf-nest-restoring ( node frames -- ... frames next )
  ['] lf-nest-restore-node lf-nest-replaced ;
: lf-nest-restore-visit ( node frames -- ... frames next )
  over lf-term-valid? lf-rebuild-tag dup lf-tag-app = over lf-tag-constant = or
  if drop ['] lf-nest-restoring lf-nest-again exit then
  lf-nest-other ;
:noname ( -- ) ['] lf-nest-restore-visit lf-nest-restore-frames frame-init ; context-setup
\ Every constructor's name for B3: an auxiliary one's restored
\ (restore_constructor_name: its prefix, its type's name, replaced by
\ the name of its key's head), any other its own.
: lf-nest-key-name ( a -- name )
  lf-ind-ty lf-ty-key @ lf-ind-spine drop lf-ind-const-name ;
: lf-nest-restored ( j -- name true | false )
  dup lf-ind-ctor lf-idecl-name @ swap dup lf-ind-in-ctors@ < if drop true exit then
  lf-ind-owner dup lf-ind-tname swap lf-nest-key-name lf-nest-replace-prefix ;
: lf-nest-names ( -- outcome )
  lf-ind-ctors@ 0 ?do
    i lf-nest-restored 0= if outcome-full unloop exit then
    i lf-ind-ctor-cells slab-at lf-ictor-name !
  loop outcome-ok ;
\ Each recursor type and rule restored in place.
: lf-nest-restore ( root -- root' outcome ) lf-nest-restore-frames lf-nest-run ;
: lf-nest-rec-back ( d -- outcome )
  dup lf-ind-ty lf-ty-rec-type @ lf-nest-restore ok-then? 0= if nip exit then
  swap lf-ind-ty lf-ty-rec-type ! outcome-ok ;
: lf-nest-rule-back ( j -- outcome )
  dup lf-ind-rule @ lf-nest-restore ok-then? 0= if nip exit then
  swap lf-ind-rule ! outcome-ok ;
: lf-nest-each ( xt n -- outcome )
  0 ?do i over execute dup ok? 0= if nip unloop exit then drop loop drop outcome-ok ;
: lf-nest-recs-back ( -- outcome ) ['] lf-nest-rec-back lf-ind-types@ lf-nest-each ;
: lf-nest-rules-back ( -- outcome ) ['] lf-nest-rule-back lf-ind-ctors@ lf-nest-each ;
\ After the recursors are built (step 12): restore them; ok at once for
\ a block that is not nested.
: lf-nest-restore-all ( -- outcome )
  lf-ind-aux@ 0= if outcome-ok exit then
  lf-nest-names ['] lf-nest-recs-back ok-and ['] lf-nest-rules-back ok-and ;
\ Before they are built: each auxiliary type's recursor named T.rec_i,
\ i from 1 in the types' order, T the block's first type
\ (mk_aux_rec_name_map; its T.rec named at step 6); full when a name
\ cannot be made.
: lf-nest-rec-name ( a -- outcome )
  0 lf-ind-ty lf-ty-rec-name @ over lf-ind-in-types@ - 1+ lf-nest-indexed
  0= if drop outcome-full exit then swap lf-ind-ty lf-ty-rec-name ! outcome-ok ;
: lf-nest-rec-names ( -- outcome )
  lf-ind-types@ lf-ind-in-types@ ?do
    i lf-nest-rec-name dup ok? 0= if unloop exit then drop
  loop outcome-ok ;
