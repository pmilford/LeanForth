\ The front end's view of the environment (plan FE1c; ADR 0021 D6, D10):
\ what Lean 4.35.0's Meta layer asks of its environment before it
\ unfolds a constant (Lean/Meta/GetUnfoldableConst.lean, canUnfoldDefault
\ and getUnfoldableConst?; Lean/ReducibilityAttrs.lean), over the
\ declarations of the context's input (core/input.fs: a library export
\ staged and fed, import/feed.fs) and the elaboration data read against
\ the same stage (front/elab-data.fs). Untrusted and fail-closed: a
\ question whose answer needs a fact LeanForth does not have answers
\ unsupported, never a guess; nothing here reaches the kernel.
\
\ Where each fact comes from:
\ - The export (the input): a declaration by name (the newest of that
\   name, as the environment's chain), its kind, universe parameters,
\   type, value and reducibility hint.
\ - The elaboration data (FE1d): its reducibility status, Lean's
\   ReducibilityStatus; a declaration no record names is semireducible,
\   Lean's default. Without data read against the stage named, or with a
\   stage named that is not the one this context's input was fed from
\   (its names' numbers are another's), a question that needs the status
\   answers unsupported. An input declaration the named stage does not
\   hold answers invalid (unreachable today: the feed makes the input
\   from the stage's declarations).
\ - Format 2 of the elaboration data (FE1e1; S1 appendix D): matcher
\   information (getMatcherInfo?), projection function information
\   (getProjectionFnInfo?) and the auxiliary-recursor tag (isAuxRecursor:
\   casesOn, recOn, brecOn, below, ...); a definition no record names is
\   none of them. Lean asks these only of definitions: its constructions
\   make matchers, projections and auxiliary recursors as definitions. So
\   any other kind answers false (certain), a definition the data's
\   answer, or unsupported without data read against the stage; Eq.ndrec,
\   Eq.ndrec_symm and Eq.ndrecOn, which isAuxRecursor names itself, are
\   auxiliary recursors. Whether a definition has a smart-unfolding
\   `_sunfold` definition (Lean's find? (mkSmartUnfoldingNameFor f),
\   WHNF.lean:854) is format 3's sunfold record of it (plan S2 merge A:
\   the export leaves the `_sunfold` definitions out, and the data has a
\   record for every one of the export's modules, so none means none),
\   unsupported without data; a text definition has none (LeanForth
\   elaborates no structural recursion, which alone makes them).
\
\ Transparency modes (meta-config.fs, numbered as Lean's TransparencyMode
\ constructors): lf-tr-all, lf-tr-default, lf-tr-reducible,
\ lf-tr-instances, lf-tr-none, lf-tr-implicit. canUnfoldDefault: none
\ unfolds nothing, all everything,
\ default all but an irreducible declaration; reducible a reducible one;
\ instances also an instance-reducible one; implicit also an
\ implicit-reducible one.
\
\ Two modes (S1 §1). The fed mode (lf-menv-stage!; tests and plan
\ 8.2.1g) reads the context's input as above. The run mode
\ (lf-menv-library!, bound by cli/check-lf.fs once the library and its
\ elaboration data are read, and by lfc-library-open) is Lean's
\ getConstInfo while a text runs: the library from the importer stage that
\ holds it, decoded on demand (front/lib-decode.fs), and the text's own
\ declarations, each added at its hand-over (lf-menv-add, handover.fs) as
\ Lean's addDecl makes a declaration visible to the next. A handle is the
\ stage's declaration number (the elaboration data's too), or the stage's
\ count plus i for the text's i-th; a text declaration is found before the
\ library's of the same name, newest first. A text declaration is
\ semireducible, none of format 2's kinds, its hint opaque (lazy delta, S2,
\ will need heights), and has no inductive data. lf-menv-reset (cli's
\ lfc-empty, lfc-library-close) leaves the run mode and forgets the text's
\ declarations and every decoded one; a text list made before the term
\ store was last reset is forgotten too.
\
\ Words: lf-menv-stage! ( stage -- ) the fed mode: the stage the
\ elaboration data was read against, sealed and fed to this context (0:
\ none); lf-menv-library! ( stage -- ) the run mode over the library's
\ stage (0: no library), its declarations those the stage holds now;
\ lf-menv-reset ( -- ); lf-menv-add ( decl -- outcome ) a text
\ declaration (author's lf-fdecl record) made visible, full when there is
\ no room (nothing kept), invalid for a kind that is none of
\ lf-decl-theorem .. lf-decl-stub; lf-menv-find ( name -- d outcome ) the
\ declaration of a name, invalid when none has it (Lean: unknown
\ constant), full or unsupported when a library declaration cannot be
\ decoded (d -1 whenever the outcome is not ok); lf-menv-name,
\ lf-menv-kind, lf-menv-type, lf-menv-params ( d -- addr n ),
\ lf-menv-value ( d -- term true | false ), lf-menv-hint ( d -- hint
\ height ), lf-menv-data ( d -- addr|0 ) its inductive data (core/input.fs's
\ layout), unchecked: d from lf-menv-find; lf-menv-kinds ( d -- addr n )
\ the kinds (0-3, Lean's BinderInfo) of its type's leading Pi binders (S1
\ §4): a library declaration's from the tier's binder tags (in the fed
\ mode, of the stage named, else none), or Lean's own where the data read
\ against that stage has a binder_kinds record of it (format 3.2, plan
\ FE1c-bk), a text declaration's as its binder
\ words wrote them, recorded by lf-menv-add; never read from a shared term
\ node; the answer holds until the next call, and fewer kinds than binders
\ (none known, no room) leave the rest unknown to the caller;
\ lf-menv-kinds-in ( d k -- addr n ) the same for the leading binders of
\ the domain of its type's binder k (S2 §4; none for a text declaration);
\ lf-menv-status ( d -- status outcome ) an elab-* status;
\ lf-menv-can-unfold ( d mode -- flag outcome ) canUnfoldDefault, and
\ canUnfoldAtMatcher under meta-config.fs's lf-meta-at-matcher (S2 merge
\ B: also a @[match_pattern] definition, lf-menv-match-pattern? ( d --
\ flag outcome ) from the data's tag, and 21 names Lean lists);
\ lf-menv-unfoldable ( name mode -- d flag outcome ) getUnfoldableConst?:
\ flag true when the name is a definition that mode unfolds (a theorem
\ or any other kind: false); lf-menv-matcher?, lf-menv-proj-fn?,
\ lf-menv-aux-recursor?, lf-menv-smart? ( d -- flag outcome ) as above;
\ lf-menv-proj-class? ( d -- flag outcome ) whether d is a class's
\ projection function (Lean's isProjInst: getProjectionFnInfo?'s
\ fromClass), from format 2's projection records as lf-menv-proj-fn?;
\ lf-menv-reducible? ( d -- flag outcome ) Lean's isReducible (status
\ reducible); lf-menv-hint-known? ( d -- flag ) whether lf-menv-hint is
\ Lean's: false for a text declaration, whose height is not recorded;
\ lf-menv-kind@ ( d k -- kind true | false ) the kind of its type's
\ binder k (from 0) as lf-menv-kinds gives it, false where that gives
\ none; lf-menv-data-decl ( name -- d' true | false ) the elaboration
\ data's declaration (elab-data.fs's numbers, of the stage it was read
\ against) of a name of this context: fed, the stage's of the same name;
\ run, a library declaration's own number (a text declaration, or no
\ data read against the library, has none); lf-menv-of-data ( d' -- d
\ outcome ) the converse, as lf-menv-find (fed: the input's newest of
\ that name; run: d', decoded);
\ lf-menv-nat-succ? ( name -- flag ) whether a name is Nat.succ,
\ lf-menv-nat-name? ( name -- flag ) whether it is in Nat's namespace,
\ lf-menv-wf-rec? ( name -- flag ) whether it is Acc.rec or
\ WellFounded.rec (reduceRec's isWFRec), lf-menv-dite? ( name -- flag )
\ whether it is dite (unfoldNestedDIte).
\ Outcomes: ok; invalid for a declaration number beyond the input, a
\ mode beyond the six, a name that is not valid or that no declaration
\ has, or a declaration the stage does not hold; unsupported as above.
\ Constants for the Meta layer: lf-meta-const-at ( name gen addr n -- term
\ outcome ) a name's constant at the n levels at addr, one cell each;
\ lf-meta-const-with ( d xt -- term outcome ) declaration d's constant at
\ a level xt ( -- level outcome ) makes for each universe parameter, in
\ order (mvars.fs's lf-meta-const-fresh, Lean's
\ mkConstWithFreshMVarLevels, passes lf-level-mvar-new); full when a
\ store has no room, invalid for a level that names none, else the xt's
\ outcome (-1 then).
\ State: one context record, menv (the fed stage, the mode, the text
\ list's stamp), and the slabs me-texts, me-tparams, me-tkinds,
\ me-kinds and me-pairs. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/texts.fs
require ../core/names.fs
require ../core/levels.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/input.fs
require ../core/statement-match.fs
require ../import/stage.fs
require ./elab-data.fs
require ./meta-config.fs
require ./lib-decode.fs
require ../present/print-forth.fs

begin-structure /menv
  field: menv-stage   \ fed mode: the stage the elaboration data was read against, or 0
  field: menv-run     \ true in the run mode
  field: menv-gen     \ the term store's generation the text list is for
end-structure
/menv context-record: menv
begin-structure /mtx  \ a text declaration
  field: mtx-name
  field: mtx-kind
  field: mtx-type
  field: mtx-value    \ a term, or -1
  field: mtx-params   \ its first universe parameter in me-tparams
  field: mtx-params#
  field: mtx-kinds    \ its first binder kind in me-tkinds
  field: mtx-kinds#
end-structure
/mtx context-slab: me-texts
1 cells context-slab: me-tparams
1 cells context-slab: me-tkinds
1 cells context-slab: me-kinds      \ lf-menv-kinds' answer
2 cells context-slab: me-pairs      \ a constant's levels, made for it
: lf-menv-stage! ( stage -- ) menv menv-stage ! ;
: me-stage ( -- stage ) menv menv-stage @ ;
: me-run? ( -- flag ) menv menv-run @ ;

\ ---- The text list, stamped with the term store's generation.
: me-gen ( -- n ) lf-term-generation @ ;
: me-texts-clear ( -- )
  me-texts slab-clear me-tparams slab-clear me-tkinds slab-clear me-gen menv menv-gen ! ;
: me-texts-current ( -- ) me-gen menv menv-gen @ <> if me-texts-clear then ;
: lf-menv-reset ( -- )
  false menv menv-run ! 0 lf-menv-stage! me-texts-clear lf-libdec-reset ;
: lf-menv-library! ( stage -- ) lf-menv-reset lf-libdec-stage! true menv menv-run ! ;

\ ---- Handles: the way a handle is read (0 fed, 1 library, 2 text) and a
\ table of the three words that read it.
: me-lib# ( -- n ) lf-libdec-count ;
: me-count ( -- n ) me-run? if me-lib# me-texts slab-count + else lf-input-count then ;
: me-way ( d -- d k ) me-run? 0= if 0 exit then dup me-lib# u< if 1 else 2 then ;
: me-table ( fed-xt lib-xt text-xt "name" -- ) create rot , swap , , ;
: me-ask ( d table -- i*x ) swap me-way rot swap cells + @ execute ;
: me-rec ( d -- r ) lf-libdec-decl drop ;
: me-text ( d -- mtx ) me-lib# - me-texts slab-at ;

\ ---- Declarations: found by name, the text's newest first in the run
\ mode (a library declaration decoded as it is found).
: me-decl? ( d -- flag ) 0 me-count within ;
: me-found ( d -- d outcome ) dup 0< if outcome-invalid else outcome-ok then ;
: me-text-named ( name -- d true | false )
  me-texts slab-count begin dup while
    1- 2dup me-texts slab-at mtx-name @ = if nip me-lib# + true exit then
  repeat 2drop false ;
\ A library declaration decoded: its name was found, so a decoder's
\ invalid for one of the library's (malformed tier data) is unsupported,
\ never "no such constant" (review N3 of 2026-11-18; meta-spine.fs); one
\ past the library's count (a stage grown while bound) stays unknown.
: me-lib-d? ( d -- flag ) lf-libdec-count u< ;
: me-undecoded ( d outcome -- d outcome' )
  dup outcome-invalid = if over me-lib-d? if drop outcome-unsupported then then ;
: me-decoded ( d -- d outcome )
  dup lf-libdec-decl nip me-undecoded ok-or-none ;
: me-run-find ( name -- d outcome )
  me-texts-current dup me-text-named if nip outcome-ok exit then
  lf-libdec-find ok-then? if me-decoded else no-result then ;
: lf-menv-find ( name -- d outcome )
  dup lf-name-valid? 0= if drop -1 outcome-invalid exit then
  me-run? if me-run-find else lf-input-newest me-found then ;
: me-fed-kind ( d -- kind ) lf-input-decl lf-idecl-kind @ ;
: me-fed-type ( d -- term ) lf-input-decl lf-idecl-type @ ;
: me-fed-value ( d -- term ) lf-input-decl lf-idecl-value @ ;
: me-fed-hint ( d -- hint height ) lf-input-decl dup lf-idecl-hint @ swap lf-idecl-height
  @ ;
: me-fed-data ( d -- addr|0 ) lf-input-decl lf-idecl-data ;
: me-lib-name ( d -- name ) me-rec lf-libdec-dname ;
: me-lib-kind ( d -- kind ) me-rec lf-libdec-kind ;
: me-lib-type ( d -- term ) me-rec lf-libdec-type ;
: me-lib-value ( d -- term ) me-rec lf-libdec-value ;
: me-lib-hint ( d -- hint height ) me-rec lf-libdec-hint ;
: me-lib-params ( d -- addr n ) me-rec lf-libdec-params ;
: me-lib-data ( d -- addr|0 ) me-rec lf-libdec-data ;
: me-text-name ( d -- name ) me-text mtx-name @ ;
: me-text-kind ( d -- kind ) me-text mtx-kind @ ;
: me-text-type ( d -- term ) me-text mtx-type @ ;
: me-text-value ( d -- term ) me-text mtx-value @ ;
: me-text-hint ( d -- hint height ) drop lf-hint-opaque 0 ;
: me-text-params ( d -- addr n )
  me-text dup mtx-params @ me-tparams slab-at swap mtx-params# @ ;
: me-text-data ( d -- 0 ) drop 0 ;
' lf-input-name ' me-lib-name ' me-text-name me-table me-names
' me-fed-kind ' me-lib-kind ' me-text-kind me-table me-decl-kinds
' me-fed-type ' me-lib-type ' me-text-type me-table me-types
' me-fed-value ' me-lib-value ' me-text-value me-table me-values
' me-fed-hint ' me-lib-hint ' me-text-hint me-table me-hints
' lf-input-params ' me-lib-params ' me-text-params me-table me-params
' me-fed-data ' me-lib-data ' me-text-data me-table me-datas
: lf-menv-name ( d -- name ) me-names me-ask ;
: lf-menv-kind ( d -- kind ) me-decl-kinds me-ask ;
: lf-menv-type ( d -- term ) me-types me-ask ;
: lf-menv-params ( d -- addr n ) me-params me-ask ;
: lf-menv-value ( d -- term true | false ) me-values me-ask dup 0< if drop false else true
  then ;
: lf-menv-hint ( d -- hint height ) me-hints me-ask ;
: lf-menv-data ( d -- addr|0 ) me-datas me-ask ;
: me-defn? ( d -- flag ) lf-menv-kind lf-kind-definition = ;

\ ---- Constants: a name at levels, the (level, identity) pairs
\ constant-references.fs takes pushed on me-pairs and read at once. Each
\ call cuts me-pairs back to its count on entry (me-scope), so a level
\ xt that makes a constant of its own leaves the outer pairs as they were.
: me-pair+ ( level -- outcome )
  dup lf-level-identity 0= if drop outcome-invalid exit then swap me-pairs slab-2push ;
: me-level-at ( addr k -- addr outcome ) over swap cells + @ me-pair+ ;
: me-level-by ( xt k -- xt outcome ) drop dup execute ok-then? if me-pair+ then ;
: me-newest ( n -- addr n ) me-pairs slab-count over - me-pairs slab-at swap ;
: me-made ( name gen n -- term outcome )   \ at me-pairs' newest n levels
  me-newest lf-cref-new
  if lf-cterm-new if drop outcome-ok exit then then -1 outcome-full ;
: me-finish ( name gen n outcome -- term outcome )
  ok-then? if me-made else nip nip no-result then ;
: me-scope ( i*x xt -- term outcome )
  me-pairs slab-count >r execute r> me-pairs slab-cut ;
: me-at ( name gen addr n -- term outcome )   \ n < 0: no levels, as ok-each runs none
  0 max tuck ['] me-level-at ok-each nip me-finish ;
: lf-meta-const-at ( name gen addr n -- term outcome ) ['] me-at me-scope ;
: me-named ( d -- name gen n )
  dup lf-menv-name swap lf-menv-params nip lf-name-generation @ swap ;
: me-with ( d xt -- term outcome )
  over lf-menv-params nip ['] me-level-by ok-each nip
  ok-then? if me-named me-made else no-result then ;
: lf-meta-const-with ( d xt -- term outcome ) ['] me-with me-scope ;

\ ---- Reducibility status: the elaboration data's record of the stage's
\ declaration of the same name (the feed keeps the stage's name numbers).
\ Only the stage this context's names come from (the feed attached its
\ tier) and the data was read against: another's numbers are not ours.
: me-fed? ( stage -- flag ) stage-tier lf-name-view lf-nview-input @ = ;
: me-data? ( -- flag )
  me-stage dup 0= if exit then dup me-fed? swap elab-read-against? and ;
: me-staged ( d -- d' true | false ) lf-input-name me-stage stage-find ;
: me-status ( d -- status outcome )
  me-data? 0= if drop -1 outcome-unsupported exit then
  me-staged if elab-status outcome-ok else -1 outcome-invalid then ;
: me-run-data? ( -- flag ) lf-libdec-stage dup if elab-read-against? then ;
: me-lib-status ( d -- status outcome )
  me-run-data? if elab-status outcome-ok else drop -1 outcome-unsupported then ;
: me-text-status ( d -- status outcome ) drop elab-semireducible outcome-ok ;
' me-status ' me-lib-status ' me-text-status me-table me-statuses
: lf-menv-status ( d -- status outcome )
  dup me-decl? if me-statuses me-ask else drop -1 outcome-invalid then ;


\ ---- Facts of a definition from the data (format 3): the stage's
\ declaration of the same name asked with xt ( d -- x true | false );
\ unsupported without data, false for any other kind; Eq.ndrec,
\ Eq.ndrec_symm and Eq.ndrecOn are auxiliary recursors by name.
: me-data-fact ( d xt -- flag outcome )
  swap me-staged 0= if drop false outcome-invalid exit then
  swap execute dup if nip then outcome-ok ;
: me-known-fact ( d xt -- flag outcome )
  me-data? if me-data-fact else 2drop false outcome-unsupported then ;
: me-lib-fact ( d xt -- flag outcome )
  me-run-data? if execute dup if nip then outcome-ok else 2drop false outcome-unsupported
    then ;
: me-fact ( d xt -- flag outcome )
  me-run? 0= if me-known-fact exit then
  over me-lib# u< if me-lib-fact else 2drop false outcome-ok then ;
: me-defn-fact ( d xt -- flag outcome )
  over me-decl? 0= if 2drop false outcome-invalid exit then
  over me-defn? if me-fact else 2drop false outcome-ok then ;
: me-aux-tag ( d -- 0 true | false )
  elab-tag-aux-recursor elab-tagged? dup if 0 swap then ;
: lf-menv-matcher? ( d -- flag outcome ) ['] elab-matcher-of me-defn-fact ;
: lf-menv-proj-fn? ( d -- flag outcome ) ['] elab-projection-of me-defn-fact ;
: lf-menv-smart? ( d -- flag outcome ) ['] elab-sunfold-of me-defn-fact ;
: me-text-decl? ( d -- flag ) me-run? if me-lib# u< 0= else drop false then ;
: me-class-proj ( d -- 0 true | false )
  elab-projection-of if elab-projection-class? dup if 0 swap then else false then ;
: lf-menv-proj-class? ( d -- flag outcome ) ['] me-class-proj me-defn-fact ;
: lf-menv-reducible? ( d -- flag outcome )
  lf-menv-status ok-then? if elab-reducible = outcome-ok else false swap then ;
: lf-menv-hint-known? ( d -- flag ) me-text-decl? 0= ;
: me-text? ( name -- flag ) lf-name-tag@ lf-name-tag-str = ;
: me-str? ( name c-addr u -- flag )
  rot dup me-text? if lf-name-text compare 0= else drop 2drop false then ;
: me-top? ( name c-addr u -- flag )
  rot dup lf-name-prefix@ 0= if -rot me-str? else drop 2drop false then ;
: me-eq? ( prefix -- flag ) s" Eq" me-top? ;
\ Names as tables of texts (lib/texts.fs; s2-finish L1, review F10).
texts-begin texts+ ndrec ndrec_symm ndrecOn
texts-end constant me-ndrec-texts
: me-ndrec-text? ( name -- flag ) ['] me-str? me-ndrec-texts texts-find 0<> ;
: me-ndrec? ( d -- flag )
  lf-menv-name dup me-ndrec-text? if lf-name-prefix@ me-eq? else drop false then ;
: lf-menv-aux-recursor? ( d -- flag outcome )
  dup me-decl? if dup me-ndrec? if drop true outcome-ok exit then then
  ['] me-aux-tag me-defn-fact ;
\ isAuxDef (WHNF.lean:79-81): isAuxRecursor alone; a noConfusion is not
\ one (pinned Lean: whnfCore leaves Nat.noConfusion's application).
: lf-menv-aux-def? ( d -- flag outcome ) lf-menv-aux-recursor? ;
\ canUnfoldAtMatcher's own names (GetUnfoldableConst.lean:44-57).
texts-begin texts+ OfNat.ofNat NatCast.natCast Zero.zero One.one decEq Nat.decEq
  texts+ Char.ofNat Char.ofNatAux String.decEq List.hasDecEq Fin.ofNat HMod.hMod
  texts+ Mod.mod
texts-end constant me-matcher-texts
texts-begin texts+ UInt8 UInt16 UInt32 UInt64
texts-end constant me-uint-texts
texts-begin texts+ ofNat decEq
texts-end constant me-uint-op-texts
: me-dotted-in? ( name table -- flag ) ['] lf-name-dotted? swap texts-find 0<> ;
: me-uint-op? ( name -- flag )
  dup ['] me-str? me-uint-op-texts texts-find
  if lf-name-prefix@ me-uint-texts me-dotted-in? else drop false then ;
: me-matcher-name? ( name -- flag )
  dup me-matcher-texts me-dotted-in? if drop true else me-uint-op? then ;
\ Lean's hasMatchPatternAttribute: the data's match_pattern tag.
: me-pattern-tag ( d' -- 0 true | false )
  elab-tag-match-pattern elab-tagged? dup if 0 swap then ;
: lf-menv-match-pattern? ( d -- flag outcome ) ['] me-pattern-tag me-defn-fact ;
\ ---- canUnfoldDefault: per mode, the statuses it unfolds (bit k for
\ status k: semireducible, reducible, irreducible, implicit-reducible,
\ instance-reducible); all and none need no status.
: me-bit ( status -- mask ) 1 swap lshift ;
: me-every ( -- mask ) elab-instance-reducible 1+ me-bit 1- ;
: me-default ( -- mask ) me-every elab-irreducible me-bit invert and ;
: me-reducible ( -- mask ) elab-reducible me-bit ;
: me-instances ( -- mask ) me-reducible elab-instance-reducible me-bit or ;
: me-implicit ( -- mask ) me-instances elab-implicit-reducible me-bit or ;
: me-mask ( mode -- mask )
  case lf-tr-all of me-every endof lf-tr-default of me-default endof
    lf-tr-reducible of me-reducible endof lf-tr-instances of me-instances endof
    lf-tr-implicit of me-implicit endof 0 swap endcase ;
: me-status-free? ( mode -- flag ) dup lf-tr-all = swap lf-tr-none = or ;
: me-unfolds? ( status mode -- flag ) me-mask swap rshift 1 and 0<> ;
: me-by-status ( d mode -- flag outcome )
  swap lf-menv-status ok-then? if swap me-unfolds? outcome-ok else nip false swap then ;
: me-bad? ( d mode -- flag ) lf-tr-modes u< swap me-decl? and 0= ;
: me-can-default ( d mode -- flag outcome )
  dup me-status-free? if nip me-mask 0<> outcome-ok else me-by-status then ;
\ canUnfoldAtMatcher (GetUnfoldableConst.lean:37), under meta-config.fs's
\ lf-meta-at-matcher: what canUnfoldDefault does not unfold, a
\ @[match_pattern] definition or one of Lean's names above does.
: me-matcher-extra ( d -- flag outcome )
  dup lf-menv-name me-matcher-name? if drop true outcome-ok exit then
  lf-menv-match-pattern? ;
\ Done: canUnfoldDefault's yes, or no predicate at matchers.
: me-more? ( flag -- flag' ) lf-meta-at-matcher lf-meta-flag? 0= or ;
: me-can-more ( d flag outcome -- flag outcome )
  ok-then? 0= if nip false swap exit then
  dup me-more? if nip outcome-ok else drop me-matcher-extra then ;
: lf-menv-can-unfold ( d mode -- flag outcome )
  2dup me-bad? if 2drop false outcome-invalid exit then
  over swap me-can-default me-can-more ;

\ ---- getUnfoldableConst?: a definition the mode unfolds; a theorem or
\ any other kind never.
: me-unfoldable ( d mode -- d flag outcome )
  over me-defn? if over swap lf-menv-can-unfold else drop false outcome-ok then ;
: lf-menv-unfoldable ( name mode -- d flag outcome )
  dup lf-tr-modes u< 0= if 2drop -1 false outcome-invalid exit then
  swap lf-menv-find ok-then? if swap me-unfoldable else nip -1 false rot then ;
\ ---- Binder kinds (S1 §4), into me-kinds. A library declaration's are
\ the export's tags, but where the elaboration data has a binder_kinds
\ record (format 3.2, plan FE1c-bk), Lean's own: lean4export writes one
\ node for types equal up to binder kinds, so the export may hold another
\ declaration's.
: me-kinds-out ( -- addr n ) 0 me-kinds slab-at me-kinds slab-count ;
: me-kinds-move ( addr n -- )
  me-kinds slab-clear dup me-kinds slab-claim ok-then? 0= if drop 2drop exit then
  drop swap 0 me-kinds slab-at rot cells move ;
: me-data-kinds ( d' -- ) elab-binder-kinds-of if elab-binder-kinds me-kinds-move then ;
: me-data-domain ( k d' -- )
  elab-binder-kinds-of if swap elab-binder-domain me-kinds-move else drop then ;
\ The fed mode's record of the staged declaration d', when there is data.
: me-fed-data-kinds ( d' -- ) me-data? if me-data-kinds else drop then ;
: me-fed-kinds ( d -- )
  me-stage 0= if drop me-kinds slab-clear exit then
  me-staged 0= if me-kinds slab-clear exit then
  dup me-stage staged-type@ me-stage stage-tier me-kinds lf-tier-kinds drop
  me-fed-data-kinds ;
: me-lib-kinds ( d -- )
  dup me-kinds lf-libdec-kinds drop me-run-data? if me-data-kinds else drop then ;
: me-kinds-copy ( first n -- ) swap me-tkinds slab-at swap me-kinds-move ;
: me-kinds-span ( mtx -- first n ) dup mtx-kinds @ swap mtx-kinds# @ ;
: me-text-kinds ( d -- ) me-text me-kinds-span me-kinds-copy ;
' me-fed-kinds ' me-lib-kinds ' me-text-kinds me-table me-binders
: lf-menv-kinds ( d -- addr n ) me-binders me-ask me-kinds-out ;
\ The kinds of the leading binders of the domain of d's binder k (S2 §4:
\ an eliminator's alternatives' fields), as lf-menv-kinds; a text
\ declaration's are not recorded (none).
: me-fed-tier ( -- tier ) me-stage stage-tier ;
: me-tier-kinds-in ( k e -- )
  me-fed-tier rot expr-domain
  if me-fed-tier me-kinds lf-tier-kinds drop else me-kinds slab-clear then ;
: me-fed-data-domain ( k d' -- ) me-data? if me-data-domain else 2drop then ;
: me-fed-kinds-in ( k d -- )
  me-stage 0= if 2drop me-kinds slab-clear exit then
  me-staged 0= if drop me-kinds slab-clear exit then
  2dup me-stage staged-type@ me-tier-kinds-in me-fed-data-domain ;
: me-lib-kinds-in ( k d -- )
  2dup swap lf-libdec-domain if me-kinds lf-tier-kinds drop else me-kinds slab-clear then
  me-run-data? if me-data-domain else 2drop then ;
: me-text-kinds-in ( k d -- ) 2drop me-kinds slab-clear ;
' me-fed-kinds-in ' me-lib-kinds-in ' me-text-kinds-in me-table me-binders-in
: lf-menv-kinds-in ( d k -- addr n ) swap me-binders-in me-ask me-kinds-out ;
: me-cell@ ( addr n k -- x true | false )
  tuck swap index? if cells + @ true else 2drop false then ;
: lf-menv-kind@ ( d k -- kind true | false ) swap lf-menv-kinds rot me-cell@ ;

\ ---- The elaboration data's declarations and this context's: fed, by
\ the name the input shares with the stage; run, a library declaration
\ is the stage's own (with the data read against it), a text one has
\ none.
: me-lib-decl? ( d -- flag ) me-lib# u< me-run-data? and ;
: me-run-data-decl ( name -- d true | false )
  lf-menv-find ok? if dup me-lib-decl? if true exit then then drop false ;
: lf-menv-data-decl ( name -- d' true | false )
  me-run? if me-run-data-decl else elab-decl-of then ;
: lf-menv-of-data ( d' -- d outcome )
  me-run? if me-decoded else elab-decl-name lf-menv-find then ;
\ The elaboration data's declaration of d's name; false when it has none.
: lf-menv-elab ( d -- d' true | false ) lf-menv-name lf-menv-data-decl ;
\ A definition's sunfold record (Lean's find? of f._sunfold) and its
\ rec_arg (getStructuralRecArgPos?, S2 merge B); false when none.
: lf-menv-sunfold ( d -- s true | false )
  lf-menv-elab if elab-sunfold-of else false then ;
: lf-menv-rec-arg ( d -- k true | false )
  lf-menv-sunfold if elab-sunfold-rec-arg else false then ;
\ getMatcherInfo? (S2 merge B), from format 2's matcher record: the
\ arguments before a matcher's alternatives (its parameters, motive and
\ discriminants) and its alternatives; false when the data has none.
: me-prefix ( m -- n ) elab-matcher@ + 1+ nip ;
: me-alts ( m -- n ) elab-matcher-alts nip ;
: lf-menv-matcher ( d -- m true | false )
  lf-menv-elab if elab-matcher-of else false then ;
: lf-menv-matcher-sizes ( d -- prefix alts true | false )
  lf-menv-matcher 0= if false exit then dup me-prefix swap me-alts true ;

\ ---- A text declaration made visible (lf-menv-add): its name, kind,
\ type, value, universe parameters and the kinds of its type's leading Pi
\ binders as the binder words wrote them (a text's run shares no node:
\ author/runner.fs turns sharing off; the first binder with no entry ends
\ them). A record that cannot be completed is given back.
create me-text-kinds-of   \ per lf-decl-* kind (present/print-forth.fs); 0: none
  lf-kind-theorem , lf-kind-definition , lf-kind-axiom , 0 ,
: me-kind-known? ( decl -- flag ) lf-fdecl-kind @ lf-decl-theorem lf-decl-stub between? ;
: me-kind-of ( decl -- kind ) lf-fdecl-kind @ cells me-text-kinds-of + @ ;
: me-fill ( mtx decl -- )
  2dup lf-fdecl-name @ swap mtx-name ! 2dup me-kind-of swap mtx-kind !
  2dup lf-fdecl-type @ swap mtx-type ! lf-fdecl-value @ swap mtx-value ! ;
: me-params! ( mtx decl -- outcome )
  dup lf-fdecl-universes @ >r lf-fdecl-universe swap
  me-tparams slab-count over mtx-params ! r@ swap mtx-params# !
  r@ me-tparams slab-claim ok-then? 0= if nip r> drop exit then
  me-tparams slab-at r> cells move outcome-ok ;
: me-pi? ( term -- flag ) dup 0< if drop false else lf-term-tag@ lf-tag-pi = then ;
: me-kind@ ( term -- kind true | false ) lf-pres-binder@ if nip true else false then ;
: me-kind+ ( pi -- pushed? outcome )
  me-kind@ if me-tkinds slab-push true swap else false outcome-ok then ;
: me-kinds-of-type ( type -- n outcome )
  0 swap begin dup me-pi? while
    dup me-kind+ ok-then? 0= if nip exit then 0= if drop outcome-ok exit then
    swap 1+ swap lf-term-second@
  repeat drop outcome-ok ;
: me-kinds! ( mtx -- outcome )
  me-tkinds slab-count over mtx-kinds ! dup mtx-type @ me-kinds-of-type >r swap mtx-kinds#
    ! r> ;
: me-text-made ( decl mtx -- outcome )
  2dup swap me-fill tuck swap me-params! ok-then? if me-kinds! then ;
: me-add ( decl -- outcome )
  me-texts-current 1 me-texts slab-claim ok-then? 0= if nip exit then
  me-texts slab-at dup /mtx erase me-text-made dup ok? 0= if me-texts slab-drop then
    ;
: lf-menv-add ( decl -- outcome ) dup me-kind-known? if me-add else drop-invalid then ;

\ Whether a name is Nat.succ (whnf's reduceNat? and Nat offsets know it
\ by name).
: lf-menv-nat-succ? ( name -- flag )
  dup s" succ" me-str? if lf-name-prefix@ s" Nat" me-top? else drop false then ;
\ Whether a name is in Nat's namespace, Nat.x (whnf's reduceNat?).
: lf-menv-nat-name? ( name -- flag )
  lf-name-prefix@ dup if s" Nat" me-top? else drop false then ;
\ Whether a name is Acc.rec or WellFounded.rec (reduceRec's isWFRec).
: me-wf? ( prefix -- flag ) dup s" Acc" me-top? swap s" WellFounded" me-top? or ;
: lf-menv-wf-rec? ( name -- flag )
  dup s" rec" me-str? if lf-name-prefix@ me-wf? else drop false then ;
\ Whether a name is dite (reduceMatcher?'s unfoldNestedDIte).
: lf-menv-dite? ( name -- flag ) s" dite" me-top? ;

base !   \ the BASE this file was loaded with
