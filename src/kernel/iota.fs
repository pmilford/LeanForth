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
\ Not ported, so unknown (diagnostic 81, as whnf.fs's default): a
\ major premise that is no constructor application when the recursor has
\ k set (Lean's to_cnstr_when_K may still find the constructor, by
\ inference and comparison) or when its type may be a non-recursive
\ structure (Lean's to_cnstr_when_structure eta-expands it with
\ projections, U2); and Lean's generated recursor that no slot holds (ADR
\ 0015 decision 12). For k set, a major premise whose whnf is the
\ constructor gets the same rule Lean's to_cnstr_when_K gives (the one
\ constructor, no fields). Literal majors (L2) never occur: literals are
\ unsupported (U2; plan task 5.2.3), and whnf.fs answers unknown where
\ Lean's reduce_nat could make one (K7). Quotients are unsupported (U1).
\ State: none of its own; the work arrays and the frames are whnf.fs's,
\ each array filled and used within one step.

require ../lib/lib.fs
require ../core/input.fs
require ../core/name-equal.fs
require ../core/names.fs
require ../core/terms.fs
require ./environment.fs
require ./inductive-block.fs
require ./mixed-head.fs
require ./whnf.fs

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
\ head a constant that a usable slot holds as a constructor.
: lf-iota-ctor? ( node -- flag outcome )
  lf-whnf-head dup lf-whnf-const? 0= if drop false outcome-ok exit then
  lf-whnf-lookup ok-then? 0= if false swap exit then
  dup 0< if drop false outcome-ok exit then
  lf-whnf-decl ok-then? 0= if false swap exit then
  lf-idecl-kind @ lf-kind-constructor = outcome-ok ;

\ A major premise that is no constructor application. Its type's name is
\ the head of the recursor type's binder major_idx (get_major_induct,
\ declaration.cpp 145-153), or 0. That type is certainly no non-recursive
\ structure (is_non_rec_structure, inductive.cpp 28-33) when its slot's
\ exported fields say so -- not one constructor, or indices, or recursive
\ -- and B4 found the indices and isRec it compares Lean's; a constant
\ that is no inductive type is none either.
: lf-iota-pi? ( node -- flag ) lf-term-tag@ lf-tag-pi = ;
: lf-iota-induct ( decl -- name|0 )
  dup lf-idecl-type @ swap lf-iota-major-idx 0 ?do
    dup lf-iota-pi? 0= if drop 0 unloop exit then lf-term-second@
  loop
  dup lf-iota-pi? 0= if drop 0 exit then
  lf-term-first@ lf-whnf-head dup lf-whnf-const? 0= if drop 0 exit then
  lf-whnf-cref lf-crec-name @ ;
: lf-iota-shape? ( decl -- flag )
  dup lf-idecl-kind @ lf-kind-inductive <> if drop true exit then
  lf-idecl-data dup lf-ity-ctors@ nip 1 <> over lf-ity-indices lf-more-field 0<> or
  swap lf-ity-flags lf-more-field lf-ity-rec-bit and 0<> or ;
: lf-iota-plain? ( d -- flag )
  dup lf-env-warnings ok? 0= if 2drop false exit then
  lf-warn-indices lf-warn-rec or and if drop false exit then
  lf-whnf-decl ok? if lf-iota-shape? else drop false then ;
: lf-iota-not-ported ( app -- -1 outcome ) lf-whnf-head lf-whnf-pending ;
: lf-iota-no-ctor ( app decl -- reduct outcome )
  dup lf-iota-k? if drop lf-iota-not-ported exit then
  lf-iota-induct ?dup 0= if lf-iota-not-ported exit then
  lf-whnf-find ok-then? 0= if nip no-result exit then
  dup 0< if drop lf-iota-not-ported exit then
  lf-iota-plain? if drop -1 outcome-ok else lf-iota-not-ported then ;

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

\ After the major premise's whnf (inductive.h 92-115).
: lf-iota-reduce ( app decl major frames -- reduct outcome )
  >r dup lf-iota-ctor? ok-then? 0= if >r 2drop drop r> no-result r> drop exit then
  0= if drop lf-iota-no-ctor r> drop exit then
  2dup lf-iota-head-name lf-iota-rule ?dup 0=
  if 2drop drop -1 outcome-ok r> drop exit then
  2over 2over lf-iota-applies? 0= if 2drop 2drop -1 outcome-ok r> drop exit then
  r> lf-iota-apply ;

\ The hook's step (whnf.fs): the major premise's whnf is a child visit,
\ the recursor's record and the application saved across it.
: lf-iota-majored ( major outcome frames -- ... frames next )
  >r r@ frame-restore r@ frame-restore 2swap
  ok-then? 0= if nip nip r> lf-whnf-failed exit then
  r@ lf-iota-reduce r> 0 ;
: lf-iota-none ( app frames decl -- -1 ok frames 0 ) drop nip -1 outcome-ok rot 0 ;
: lf-iota ( app frames -- ... frames next )
  over lf-iota-recursor ok-then? 0= if rot drop swap lf-whnf-failed exit then
  dup 0< if lf-iota-none exit then
  2 pick lf-iota-n over lf-iota-major-idx > 0= if lf-iota-none exit then
  dup 2 pick frame-save 2 pick 2 pick frame-save
  lf-iota-major-idx >r swap dup lf-iota-n r> lf-iota-arg swap
  ['] lf-iota-majored lf-whnf-call ;
' lf-iota is lf-whnf-iota
