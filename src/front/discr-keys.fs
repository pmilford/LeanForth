\ Discrimination-tree keys (plan FE1e2; docs/design/FE1E_APPLICATIONS.md
\ §3.2 and §4; S1_INTERFACE.md §2, §4, §9): ports of Lean 4.35.0's
\ DiscrTree.mkPath and getUnifyKeyArgs (Lean/Meta/DiscrTree/Main.lean,
\ lines 200-421) with reduceDT, toNatLit?, isOffset and ignoreArg. Keys
\ go into front/elab-keys.fs's store, where the elaboration data keeps
\ the instances' keys, so a key made here compares with a data key by
\ elab-key=; a constant's key names the declaration of the data's stage
\ (elab-decl-of), a query's free variable has its own tag.
\ - lf-dt-path ( type -- k n outcome ): mkPath (Main.lean:329), at
\   reducible transparency: the n keys of type from key k, in Lean's
\   order (a key, then the terms it has: a constant's arguments, first to
\   last, a projection's arguments then its structure, an arrow's domain).
\   Each argument ignoreArg drops is a star: an instance-implicit one, an
\   implicit or strict-implicit one that is no type (isType: whnfD of its
\   type is a Sort; a literal never is), a proof.
\ - lf-dt-key ( e root? list -- k list' outcome ): getUnifyKeyArgs
\   (Main.lean:350, isMatch false), at the configured transparency (the
\   caller's withReducible): e's key at k, e's arguments put on the todo
\   list (a key's first argument comes first off the list). With
\   isDefEqStuckEx (lf-defeq-stuck) a constant application holding a
\   metavariable answers lf-meta-stuck when the constant is reducible, a
\   matcher with a metavariable in a discriminant, or a recursor
\   (Main.lean:359-397); a metavariable is a star; else a read-only or
\   synthetic-opaque one is other.
\ - lf-dt-nat-lit ( e -- u flag outcome ): toNatLit? (Main.lean:111).
\ - Todo lists, persistent: lf-dt-nil (-1), lf-dt-cons ( term list --
\   list' outcome ), lf-dt-first ( list -- term ), lf-dt-rest ( list --
\   list' ); lf-dt-star, an entry that is Lean's tmpStar. A list is a
\   chain of (rest, term) cells in the slab dk-cells, shared by every list
\   that extends it, forgotten from a mark (lf-dt-release): lib/runs.fs's
\   runs append at the end and keep no marks, lib/cons.fs hash-conses
\   records; neither is a cons list.
\ - lf-dt-mark ( -- keys texts cells ) and lf-dt-release ( keys texts
\   cells -- ): forget every key, text and list cell made since the mark
\   (a failed lf-dt-path leaves its keys until then); lf-dt-scoped ( i*x
\   xt -- j*x ) runs xt between the two (its results must not be keys).
\ - lf-dt-const? ( head -- const true | false ): a constant head;
\   lf-dt-const-decl ( const -- d true | false ): its declaration in the
\   data's stage (elab-decl-of).
\ reduceDT (Main.lean:200-244) is whnfCore, unfoldDefinition? and strict
\ eta, repeated. unfoldDefinition? acts on a definition the transparency
\ unfolds, which needs smart unfolding's facts (S1 appendix D, plan S2):
\ there the answer is unsupported, never a guess. Also unsupported: a
\ literal beyond one cell and a string literal (S5), and where the Meta
\ words the keys read (whnf, inferType, getFunInfoNArgs) are.
\ Outcomes: ok; lf-meta-stuck as above (Meta layer only); unsupported;
\ exhausted when meta-config.fs's budget runs out (one step a key);
\ invalid for a constant the data's stage lacks or a term that is not
\ live; full when a store or the heap has no room. Untrusted.
\ State: the record dk (the key being made) and the slabs dk-cells
\ (todo list cells), dk-args (a spine's arguments, the last first) and
\ dk-kinds (the head's binder kinds), in the checker context (ADR 0009).
\ Not reentrant: the Meta words it calls make no keys. Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../core/terms.fs
require ../core/literals.fs
require ../core/string-literals.fs
require ../core/projections.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../present/binder-table.fs
require ./meta-config.fs
require ./meta-spine.fs
require ./meta-env.fs
require ./term-eqv.fs
require ./mvars.fs
require ./whnf.fs
require ./infer.fs
require ./fun-info.fs
require ./elab-keys.fs
require ./elab-data.fs

-1 constant lf-dt-nil
-2 constant lf-dt-star
begin-structure /tcell   \ a todo list's cell
  field: tc-rest   \ the list after this cell
  field: tc-term   \ its term
end-structure
begin-structure /dk
  field: dk-root   \ true: the root term (no toNatLit? or offset test)
  field: dk-path   \ true: mkPath's pushArgs, false: getUnifyKeyArgs
  field: dk-list   \ the todo list the arguments go on
  field: dk-term   \ the term reduced
  field: dk-h      \ its head (getAppFn)
  field: dk-n      \ its number of arguments
end-structure
/dk context-record: dk
/tcell context-slab: dk-cells
1 cells context-slab: dk-args
1 cells context-slab: dk-kinds

\ ---- Todo lists.
: dk-at ( list -- addr ) dk-cells slab-at ;
: lf-dt-first ( list -- term ) dk-at tc-term @ ;
: lf-dt-rest ( list -- list' ) dk-at tc-rest @ ;
: lf-dt-cons ( term list -- list' outcome )
  1 dk-cells slab-claim ok-then? 0= if nip nip no-result exit then
  tuck dk-at tuck tc-rest ! rot swap tc-term ! outcome-ok ;
: lf-dt-mark ( -- keys texts cells ) elab-keys-mark dk-cells slab-count ;
: lf-dt-release ( keys texts cells -- ) dk-cells slab-cut elab-keys-drop ;
: lf-dt-scoped ( i*x xt -- j*x ) lf-dt-mark 2>r >r execute r> 2r> lf-dt-release ;

\ ---- Names and shapes (Lean's constant names, by text).
: dk-head ( -- head ) dk dk-h @ ;
: dk-e ( -- e ) dk dk-term @ ;
: dk-name ( const -- name ) lf-term-first@ lf-cref-slot lf-cref-name@ drop ;
: lf-dt-const-decl ( const -- d true | false ) dk-name elab-decl-of ;
: lf-dt-const? ( head -- const true | false )
  dup lf-term-const? if true else drop false then ;
: dk-last ( e -- a ) lf-term-second@ ;
: dk-arg ( e i -- a ) over lf-meta-args# lf-meta-nth-arg ;

\ ---- toNatLit? (Main.lean:111-146): a literal, Nat.zero, Nat.succ x and
\ OfNat.ofNat _ x _ of a numeral x; its value, flag false for none.
: dk-lit-small ( leaf -- u outcome )
  dup lf-lit-small? if lf-lit-cell outcome-ok else drop -1 outcome-unsupported then ;
: dk-ofnat? ( e -- flag ) 3 s" OfNat.ofNat" lf-meta-app-of? ;
: dk-zero? ( e -- flag ) 0 s" Nat.zero" lf-meta-app-of? ;
: dk-end? ( e -- flag ) dup lf-lit-leaf? swap dk-zero? or ;
\ One step down a numeral: ( acc e -- acc' e' more? ).
: dk-nat-step ( acc e -- acc' e' more? )
  dup lf-meta-succ? if dk-last swap 1+ swap true exit then
  dup dk-ofnat? if 1 dk-arg true exit then false ;
: dk-numeral? ( e -- flag )
  begin dup dk-end? if drop true exit then 0 swap dk-nat-step rot drop while repeat
  drop false ;
: dk-sum ( acc u -- n outcome ) over + tuck u> if drop -1 outcome-unsupported else
  outcome-ok then ;
: dk-nat-end ( acc e -- u outcome )
  dup dk-zero? if drop outcome-ok exit then
  dk-lit-small ok-then? if dk-sum else nip no-result then ;
: dk-nat-value ( e -- u outcome )
  0 swap begin dup dk-end? 0= while dk-nat-step drop repeat dk-nat-end ;
: lf-dt-nat-lit ( e -- u flag outcome )
  dup dk-numeral? 0= if drop 0 false outcome-ok exit then
  dk-nat-value ok-then? if true outcome-ok else -1 false rot then ;

\ ---- Making keys.
: dk-new ( tag -- k outcome ) lf-meta-spend? if elab-key-new else drop -1
  outcome-exhausted then ;
: dk-digits ( u -- c-addr n ) base @ >r decimal 0 <# #s #> r> base ! ;
: dk-text ( c-addr n k -- outcome )
  dup elab-key-text-start >r dup elab-text-room ok-then? 0= if nip nip r> drop exit then
  swap move r> elab-key-text-end outcome-ok ;
: dk-lit-key ( u -- k outcome )
  elab-key-lit dk-new ok-then? 0= if nip no-result exit then
  tuck >r dk-digits r> dk-text ;
: dk-declared ( name -- d outcome ) elab-decl-of if outcome-ok else -1 outcome-invalid
  then ;
: dk-ref-key ( d n tag -- k outcome )
  dk-new ok-then? 0= if nip nip no-result exit then
  tuck elab-key-arity! tuck elab-key-ref! outcome-ok ;
: dk-const-key ( const n -- k outcome )
  swap dk-name dk-declared ok-then? if swap elab-key-const dk-ref-key else nip
  no-result then ;
: dk-fvar-key ( fvar n -- k outcome ) elab-key-fvar dk-ref-key ;
: dk-idx! ( leaf k -- k ) tuck swap lf-proj-idx swap elab-key-idx! ;
: dk-proj-key ( leaf n -- k outcome )
  over lf-proj-name dk-declared ok-then? 0= if nip nip no-result exit then
  swap elab-key-proj dk-ref-key ok-then? if dk-idx! outcome-ok else nip no-result then ;

\ ---- Putting terms on the list: the spine's arguments, the last first,
\ so that the first comes off first.
: dk-push ( term -- outcome )
  dk dk-list @ lf-dt-cons ok-then? if dk dk-list ! outcome-ok then ;
: dk-arg@ ( j -- a ) dk-args slab-at @ ;
: dk-push-at ( j -- outcome ) dk-arg@ dk-push ;
: dk-push-all ( -- outcome ) dk-args slab-count ['] dk-push-at ok-each ;

\ ---- ignoreArg (Main.lean:77-92), with getFunInfoNArgs' binder kinds.
: dk-kind-copy ( i -- outcome ) lf-meta-param drop dk-kinds slab-push ;
: dk-kinds-copy ( m -- outcome ) dk-kinds slab-clear ['] dk-kind-copy ok-each ;
: dk-kinds-make ( head n -- outcome ) lf-meta-fun-info ok-then? if dk-kinds-copy then ;
: dk-kind ( i -- kind|-1 ) dup dk-kinds slab-count < if dk-kinds slab-at @ else drop -1
  then ;
: dk-sort? ( e -- flag ) lf-term-tag@ dup lf-tag-sort = swap lf-tag-symbolic-sort = or ;
\ isType: the type's whnf at default transparency (whnfD) is a Sort.
: dk-type? ( a -- flag outcome )
  lf-infer ok-then? 0= if false swap exit then
  lf-meta-whnf-d ok-then? if dk-sort? outcome-ok else false swap then ;
: dk-proof? ( a -- flag outcome ) lf-infer ok-then? if lf-meta-is-prop else false swap
  then ;
: dk-implicit? ( kind -- flag ) dup lf-binder-implicit = swap lf-binder-strict = or ;
: dk-not-type? ( a -- flag outcome ) dk-type? swap 0= swap ;
\ A literal's type is Nat or String (inferType): no proof and no type,
\ so ignored exactly under an implicit or strict-implicit binder.
: dk-literal? ( a -- flag ) lf-term-tag@ lf-literal-tag? ;
: dk-ignore? ( a kind -- flag outcome )
  dup lf-binder-instance = if 2drop true outcome-ok exit then
  over dk-literal? if nip dk-implicit? outcome-ok exit then
  dk-implicit? if dk-not-type? else dk-proof? then ;
\ Argument j of the slab is parameter n-1-j.
: dk-param ( j -- kind ) dk dk-n @ swap - 1- dk-kind ;
: dk-indexed ( j -- term outcome )
  dup dk-arg@ swap dk-param over swap dk-ignore? ok-then? 0= if nip no-result exit then
  if drop lf-dt-star then outcome-ok ;
: dk-push-arg ( j -- outcome ) dk-indexed ok-then? if dk-push then ;
: dk-push-indexed ( -- outcome ) dk-args slab-count ['] dk-push-arg ok-each ;
: dk-push-args ( head -- outcome )
  dk dk-path @ 0= if drop dk-push-all exit then
  dk dk-n @ dk-kinds-make dup ok? if drop dk-push-indexed then ;

\ ---- reduceDT: whnfCore, unfoldDefinition? (unsupported where it would
\ act), strict eta, until none acts.
: dk-const-head ( e -- const true | false ) lf-meta-head lf-dt-const? ;
: dk-unfolds? ( e -- flag outcome )
  dk-const-head 0= if false outcome-ok exit then
  dk-name lf-defeq-mode lf-menv-unfoldable ok-then? if nip outcome-ok else nip false
  swap then ;
: dk-unfold-check ( e -- outcome )   \ a definition it would unfold: unsupported
  dk-unfolds? ok-true? if outcome-unsupported else nip then ;
: dk-eta ( e -- e' flag outcome )
  dup lf-term-lam? if lf-meta-eta-expanded else false outcome-ok then ;
: dk-reduce-step ( e -- e' again? outcome )
  lf-whnf-core ok-then? 0= if -1 false rot exit then
  dup dk-unfold-check ok-then? if dk-eta else -1 false rot then ;
: dk-reduce ( e -- e' outcome )
  begin dk-reduce-step ok-then? 0= if nip no-result exit then 0= until outcome-ok ;

\ ---- isOffset (Main.lean:156-170), mkPath's nested constants only; a
\ numeral last argument is tested first, which gives Lean's answer with
\ fewer whnf calls.
: dk-nat-type? ( e -- flag outcome )
  lf-meta-whnf ok-then? if s" Nat" lf-meta-const-named? outcome-ok else false swap then ;
: dk-numeral-last? ( e -- flag ) dk-last dk-numeral? ;
: dk-typed-offset ( e i -- flag outcome )
  over dk-numeral-last? if dk-arg dk-nat-type? else 2drop false outcome-ok then ;
: dk-offset? ( e -- flag outcome )
  dup 2 s" Nat.add" lf-meta-app-of? if dk-numeral-last? outcome-ok exit then
  dup 4 s" Add.add" lf-meta-app-of? if 0 dk-typed-offset exit then
  dup 6 s" HAdd.hAdd" lf-meta-app-of? if 1 dk-typed-offset exit then
  lf-meta-succ? outcome-ok ;

\ ---- The keys of each head.
: dk-star ( -- k outcome ) elab-key-star dk-new ;
: dk-other ( -- k outcome ) elab-key-other dk-new ;
: dk-nested? ( -- flag ) dk dk-root @ 0= ;
: dk-args-key ( k outcome -- k outcome ) dup ok? if drop dk-head dk-push-args then ;
: dk-fvar ( -- k outcome ) dk-head dk dk-n @ dk-fvar-key dk-args-key ;
: dk-lit ( leaf -- k outcome )
  dup lf-tag-str lf-term-tag? if drop -1 outcome-unsupported exit then
  dk-lit-small ok-then? if dk-lit-key else no-result then ;
\ A projection (Main.lean:290-299): its structure goes on before the
\ arguments; under mkPath a class's structure is no_index, a star.
: dk-class-struct? ( leaf -- flag )
  lf-proj-name elab-decl-of if elab-class-of dup if nip then else false then ;
: dk-struct ( proj -- term )
  dup lf-proj-struct swap lf-proj-leaf dk-class-struct? dk dk-path @ and
  if drop lf-dt-star then ;
: dk-proj ( -- k outcome )
  dk-head dup dk-struct dk-push dup ok? 0= if nip no-result exit then drop
  lf-proj-leaf dk dk-n @ dk-proj-key dk-args-key ;
\ A metavariable: a star, or other when read-only or synthetic opaque
\ (getUnifyKeyArgs: always a star under isDefEqStuckEx).
: dk-stuck-ex? ( -- flag ) lf-defeq-stuck lf-meta-flag? dk dk-path @ 0= and ;
: dk-mvar ( -- k outcome )
  dk-stuck-ex? dk-head lf-mvar-assignable? or if dk-star else dk-other then ;
: dk-arrow ( -- k outcome )
  dk-head lf-term-first@ dk-push dup ok? 0= if no-result exit then
  drop elab-key-arrow dk-new ;

\ A constant: mkPath's nested numerals and offsets, getUnifyKeyArgs'
\ stuck tests, then the key and its arguments.
: dk-decl ( -- d outcome ) dk-head lf-meta-const-decl if outcome-ok else -1
  outcome-invalid then ;
: dk-reducible? ( d -- flag outcome )
  lf-menv-status ok-then? if elab-reducible = outcome-ok else false swap then ;
: dk-mvar-in? ( from to -- flag ) swap false -rot ?do dk-e i dk-arg lf-meta-mvar-free?
  0= or loop ;
: dk-match-span ( m -- from to ) elab-matcher@ rot drop swap 1+ tuck + ;
: dk-match-arity ( m -- n ) dup elab-matcher-alts nip swap elab-matcher@ rot drop + 1+ + ;
: dk-matcher ( d -- m true | false )
  lf-menv-name elab-decl-of if elab-matcher-of else false then ;
: dk-matcher-stuck? ( d -- flag )
  dk-matcher 0= if false exit then
  dup dk-match-arity dk dk-n @ > if drop false else dk-match-span dk-mvar-in? then ;
: dk-rec? ( d -- flag ) lf-menv-kind lf-kind-recursor = ;
: dk-stuck-const? ( d -- flag outcome )
  dup dk-reducible? ok-then? 0= if nip false swap exit then
  if drop true outcome-ok exit then
  dup dk-matcher-stuck? if drop true else dk-rec? then outcome-ok ;
: dk-unify-stuck ( -- outcome )
  dk-stuck-ex? dk-e lf-meta-mvar-free? 0= and 0= if outcome-ok exit then
  dk-decl ok-then? 0= if exit then
  dk-stuck-const? ok-then? if if lf-meta-stuck else outcome-ok then then ;
: dk-const-plain ( -- k outcome ) dk-head dk dk-n @ dk-const-key dk-args-key ;
: dk-path-nested ( -- k flag outcome )
  dk-e lf-dt-nat-lit ok-then? 0= if nip -1 false rot exit then
  if dk-lit-key true swap exit then drop
  dk-e dk-offset? ok-then? 0= if -1 false rot exit then
  if dk-star true swap else -1 false outcome-ok then ;
: dk-const-path ( -- k outcome )
  dk-nested? if dk-path-nested ok-then? 0= if nip no-result exit then
    if outcome-ok exit then drop then
  dk-const-plain ;
: dk-const ( -- k outcome )
  dk dk-path @ if dk-const-path exit then
  dk-unify-stuck dup ok? if drop dk-const-plain else no-result then ;

: dk-other-head ( head tag -- k outcome )
  case lf-tag-fvar of drop dk-fvar endof   lf-tag-mvar of drop dk-mvar endof
    lf-tag-pi of drop dk-arrow endof   >r drop dk-other r> endcase ;
: dk-dispatch ( -- k outcome )
  dk-head dup lf-term-tag@ case
    lf-tag-constant of drop dk-const endof   lf-tag-projection of drop dk-proj endof
    lf-tag-lit of dk-lit endof   lf-tag-str of dk-lit endof   dup >r dk-other-head r>
    endcase ;
\ getUnifyKeyArgs' nested numeral (Main.lean:353-355), before the head.
: dk-unify-lit ( -- k flag outcome )
  dk dk-path @ dk-nested? 0= or if -1 false outcome-ok exit then
  dk-e lf-dt-nat-lit ok-then? 0= if nip -1 false rot exit then
  if dk-lit-key true swap else drop -1 false outcome-ok then ;
: dk-keyed ( -- k outcome )
  dk-unify-lit ok-then? 0= if nip no-result exit then if outcome-ok exit then drop
  dk-dispatch ;
: dk-spined ( e -- outcome )
  dup dk dk-term ! dk-args lf-meta-spine ok-then? 0= if exit then
  dk dk-h ! dk-args slab-count dk dk-n ! outcome-ok ;
: dk-reduced ( e -- k outcome )
  dk-reduce ok-then? 0= if no-result exit then
  dk-spined dup ok? if drop dk-keyed else no-result then ;
: dk-start ( e root? list path? -- e ) dk dk-path ! dk dk-list ! dk dk-root ! ;
: dk-key ( e root? list path? -- k list' outcome )
  dk-start dup lf-dt-star = if drop dk-star else dk-reduced then dk dk-list @ swap ;
: lf-dt-key ( e root? list -- k list' outcome ) false dk-key ;

\ ---- mkPath: pushArgs from the root until the list is empty, at
\ reducible transparency.
: dk-path-step ( list root? -- list' outcome )
  >r dup lf-dt-first swap lf-dt-rest r> swap true dk-key rot drop ;
: dk-path-loop ( type -- outcome )
  lf-dt-nil lf-dt-cons ok-then? 0= if exit then true
  begin over lf-dt-nil <> while dk-path-step ok-then? 0= if exit then false repeat
  2drop outcome-ok ;
: dk-path-count ( k0 outcome -- k n outcome ) elab-keys# rot tuck - rot ;
: dk-path-run ( type -- k n outcome )   \ the list cells it made forgotten
  elab-keys# swap dk-cells slab-count >r dk-path-loop r> dk-cells slab-cut dk-path-count ;
: lf-dt-path ( type -- k n outcome ) ['] dk-path-run lf-tr-reducible lf-meta-at ;

base !   \ the BASE this file was loaded with
