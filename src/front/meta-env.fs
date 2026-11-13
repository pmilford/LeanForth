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
\   `_sunfold` definition is not available yet (the export leaves those
\   out and no exporter writes format 2's sunfold records; plan S2): a
\   definition answers unsupported.
\
\ Transparency modes (meta-config.fs, numbered as Lean's TransparencyMode
\ constructors): lf-tr-all, lf-tr-default, lf-tr-reducible,
\ lf-tr-instances, lf-tr-none, lf-tr-implicit. canUnfoldDefault: none unfolds nothing, all everything,
\ default all but an irreducible declaration; reducible a reducible one;
\ instances also an instance-reducible one; implicit also an
\ implicit-reducible one.
\
\ Words: lf-menv-stage! ( stage -- ) the stage the elaboration data was
\ read against, sealed and fed to this context (0: none);
\ lf-menv-find ( name -- d outcome ) the input declaration of a name,
\ invalid when none has it (Lean: unknown constant); lf-menv-name, lf-menv-kind,
\ lf-menv-type, lf-menv-params, lf-menv-value ( d -- term true | false ),
\ lf-menv-hint ( d -- hint height ), unchecked: d below lf-input-count;
\ lf-menv-status ( d -- status outcome ) an elab-* status;
\ lf-menv-can-unfold ( d mode -- flag outcome ) canUnfoldDefault;
\ lf-menv-unfoldable ( name mode -- d flag outcome ) getUnfoldableConst?:
\ flag true when the name is a definition that mode unfolds (a theorem
\ or any other kind: false); lf-menv-matcher?, lf-menv-proj-fn?,
\ lf-menv-aux-recursor?, lf-menv-smart? ( d -- flag outcome ) as above;
\ lf-menv-nat-succ? ( name -- flag ) whether a name is Nat.succ,
\ lf-menv-nat-name? ( name -- flag ) whether it is in Nat's namespace.
\ Outcomes: ok; invalid for a declaration number beyond the input, a
\ mode beyond the six, a name that is not valid or that no declaration
\ has, or a declaration the stage does not hold; unsupported as above.
\ State: one context record, menv (the stage). Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/names.fs
require ../core/input.fs
require ../import/stage.fs
require ./elab-data.fs
require ./meta-config.fs

begin-structure /menv
  field: menv-stage   \ the stage the elaboration data was read against, or 0
end-structure
/menv context-record: menv
: lf-menv-stage! ( stage -- ) menv menv-stage ! ;
: me-stage ( -- stage ) menv menv-stage @ ;

\ ---- Declarations of the input.
: me-decl? ( d -- flag ) 0 lf-input-count within ;
: me-found ( d -- d outcome ) dup 0< if outcome-invalid else outcome-ok then ;
: lf-menv-find ( name -- d outcome )
  dup lf-name-valid? if lf-input-newest me-found else drop -1 outcome-invalid then ;
: lf-menv-name ( d -- name ) lf-input-name ;
: lf-menv-kind ( d -- kind ) lf-input-decl lf-idecl-kind @ ;
: lf-menv-type ( d -- term ) lf-input-decl lf-idecl-type @ ;
: lf-menv-params ( d -- addr n ) lf-input-params ;
: lf-menv-value ( d -- term true | false )
  lf-input-decl lf-idecl-value @ dup 0< if drop false else true then ;
: lf-menv-hint ( d -- hint height )
  lf-input-decl dup lf-idecl-hint @ swap lf-idecl-height @ ;
: me-defn? ( d -- flag ) lf-menv-kind lf-kind-definition = ;

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
: lf-menv-status ( d -- status outcome )
  dup me-decl? if me-status else drop -1 outcome-invalid then ;

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
: lf-menv-can-unfold ( d mode -- flag outcome )
  2dup me-bad? if 2drop false outcome-invalid exit then
  dup me-status-free? if nip me-mask 0<> outcome-ok else me-by-status then ;

\ ---- getUnfoldableConst?: a definition the mode unfolds; a theorem or
\ any other kind never.
: me-unfoldable ( d mode -- d flag outcome )
  over me-defn? if over swap lf-menv-can-unfold else drop false outcome-ok then ;
: lf-menv-unfoldable ( name mode -- d flag outcome )
  dup lf-tr-modes u< 0= if 2drop -1 false outcome-invalid exit then
  swap lf-menv-find ok-then? if swap me-unfoldable else nip -1 false rot then ;

\ ---- Facts of a definition from format 2: the stage's declaration of
\ the same name asked with xt ( d -- x true | false ); unsupported
\ without data, false for any other kind; Eq.ndrec, Eq.ndrec_symm and
\ Eq.ndrecOn are auxiliary recursors by name. Smart unfolding: unsupported
\ for a definition (no data has it yet).
: me-data-fact ( d xt -- flag outcome )
  swap me-staged if swap execute dup if nip then outcome-ok else drop false outcome-invalid then ;
: me-known-fact ( d xt -- flag outcome )
  me-data? if me-data-fact else 2drop false outcome-unsupported then ;
: me-defn-fact ( d xt -- flag outcome )
  over me-decl? 0= if 2drop false outcome-invalid exit then
  over me-defn? if me-known-fact else 2drop false outcome-ok then ;
: me-aux-tag ( d -- 0 true | false ) elab-tag-aux-recursor elab-tagged? dup if 0 swap then ;
: lf-menv-matcher? ( d -- flag outcome ) ['] elab-matcher-of me-defn-fact ;
: lf-menv-proj-fn? ( d -- flag outcome ) ['] elab-projection-of me-defn-fact ;
: lf-menv-smart? ( d -- flag outcome )
  dup me-decl? 0= if drop false outcome-invalid exit then
  me-defn? if false outcome-unsupported else false outcome-ok then ;
: me-text? ( name -- flag ) lf-name-tag@ lf-name-tag-str = ;
: me-str? ( name c-addr u -- flag )
  rot dup me-text? if lf-name-text compare 0= else drop 2drop false then ;
: me-top? ( name c-addr u -- flag )
  rot dup lf-name-prefix@ 0= if -rot me-str? else drop 2drop false then ;
: me-eq? ( prefix -- flag ) s" Eq" me-top? ;
: me-ndrec-text? ( name -- flag )
  dup s" ndrec" me-str? over s" ndrec_symm" me-str? or swap s" ndrecOn" me-str? or ;
: me-ndrec? ( d -- flag )
  lf-input-name dup me-ndrec-text? if lf-name-prefix@ me-eq? else drop false then ;
: lf-menv-aux-recursor? ( d -- flag outcome )
  dup me-decl? if dup me-ndrec? if drop true outcome-ok exit then then
  ['] me-aux-tag me-defn-fact ;
\ Whether a name is Nat.succ (whnf's reduceNat? and Nat offsets know it
\ by name).
: lf-menv-nat-succ? ( name -- flag )
  dup s" succ" me-str? if lf-name-prefix@ s" Nat" me-top? else drop false then ;
\ Whether a name is in Nat's namespace, Nat.x (whnf's reduceNat?).
: lf-menv-nat-name? ( name -- flag ) lf-name-prefix@ dup if s" Nat" me-top? else drop false then ;

base !   \ the BASE this file was loaded with
