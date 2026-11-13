\ LeanForth text checked by the kernel (plan tasks 8.2.1c and 8.2.1d;
\ ADR 0017 Amendment 1, A1, A3, A4 and A6, and its Amendment 2): the
\ loading step of `leanforth check [--env EXPORT] FILE.lf`, in place of
\ cli/check-run.fs's ck-load. The file runs through the LeanForth words in
\ this Gforth (author/runner.fs, sealed: only LeanForth's word lists are
\ visible, ADR 0017 Amendment 1, A5); the declarations it made are written
\ as export records (author/export.fs) into the importer stage
\ (import/stage.fs, stage-produce), behind the library's when --env names
\ one (stage-extend); the stage is sealed and fed to the checker, and the
\ run goes on as an export's does: ck-check checks every declaration in
\ file order, the library's first, and the command line prints the
\ verdicts from the published slots (cli/leanforth.fs). So a text is
\ checked exactly as an export holding the same declarations would be,
\ with the same labels, axioms and exit codes. The whole file is the
\ unit, as ADR 0017 Amendment 1, A3 "now" says: a text that stops with an
\ error is not checked at all (lfc-failed?; the command line prints the
\ error at its line and column), and no declaration is checked before the
\ file ends (one at a time at each `end NAME` waits for plan 8.2.1g).
\
\ With --env EXPORT the library export is read first (its manifest checked
\ unless --no-manifest), and the text names its constants as Lean does
\ (author/library.fs): lfc-find is the finder, which looks a full name up
\ in the stage's names and declarations before sealing. Import stubs are
\ refused in every checked run (error 48). The stores the words fill are
\ given room for any hand-written text while they run (lfc-rooms, the
\ largest a store may hold), and their settings back afterwards.
\
\ Words: lfc-env! ( c-addr u -- ) names the library export, 0 0 none;
\ ck-lf-load ( c-addr u checked? -- outcome ), after ck-start: the text
\ c-addr u staged and fed, checked? for the library's manifest; the
\ outcome is kept as ck-load's is (ck-read-outcome), the phase that failed
\ too (ck-staging, ck-feeding); lfc-failed? ( -- flag ) whether the text
\ itself stopped (then lf-author-error. tells where and why);
\ lfc-refused? ( -- flag ) whether it ran but its records did not reach
\ the stage whole (the writer or the stage refused one; review L4);
\ lfc-fresh ( -- ) clears both, before a text's run (ck-lf-load does,
\ and the command line before anything else of a text's run);
\ lfc-library-open ( c-addr u checked? -- outcome ) and lfc-library-close
\ ( -- ), a library for the words outside check (see below);
\ lfc-elab-file! ( c-addr u -- ) names the library's elaboration data
\ (--elab-data, plan row FE1d; 0 0 none), read and checked after the
\ library and before the text runs (front/elab-data.fs), and
\ lfc-elab-failed? ( -- flag ) says whether it was refused (then
\ elab-error tells where and why, and the text did not run).
\ Untrusted, like the stage and the words: neither can make a declaration
\ accepted; only check-declaration and the publisher decide.
\ State: one context record, lfc (the library's name, whether the text
\ failed or its records were refused, the settings kept while the words
\ run, the elaboration data's name and whether it was refused).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/input.fs
require ../author/runner.fs
require ../front/reader.fs
require ../front/tactic-basic.fs
require ../import/stage.fs
require ../front/elab-data.fs
require ../front/meta-env.fs
require ../front/mvars.fs
require ./check-run.fs

begin-structure /lfc
  2 cells +field lfc-env         \ the library export's file name, or 0 0
  field: lfc-failed              \ true: the text stopped with an error
  field: lfc-refused             \ true: its records did not reach the stage whole
  field: lfc-sharing             \ the term store's sharing before the run
  field: lfc-names               \ the name store's capacity setting before it
  2 cells +field lfc-elab-file   \ the elaboration data's file name, or 0 0
  field: lfc-elab-failed         \ true: the elaboration data was refused
end-structure
/lfc context-record: lfc

: lfc-env! ( c-addr u -- ) lfc lfc-env 2! ;
\ A library: an export (--env) or a snapshot's tier (--snapshot, ck-importing?).
: lfc-library? ( -- flag ) lfc lfc-env @ 0<> ck-importing? or ;
: lfc-failed? ( -- flag ) lfc lfc-failed @ ;
: lfc-refused? ( -- flag ) lfc lfc-refused @ ;
\ No flag set: at the start of each text's run (review N3).
: lfc-fresh ( -- )
  false lfc lfc-failed ! false lfc lfc-refused ! false lfc lfc-elab-failed ! ;

\ ---- The stores' room while the words run: the name store's setting and
\ those of check-run.fs's table (ck-rooms: terms, levels, references and
\ the input, which the words do not use; the feed comes later), raised to
\ the most a store may hold (they grow only as records are made), then
\ given back; the first refusal is the outcome.
: lfc-rooms ( -- outcome )
  ck-rooms lf-name-capacity lfc lfc-names ! feed-most lf-name-capacity! ck-first ;
: lfc-rooms-back ( -- outcome ) ck-restore lfc lfc-names @ lf-name-capacity! ck-first ;

\ ---- The library's names (author/library.fs): a name of the run's name
\ store looked up in the stage's tier part by part, prefix first, without
\ adding any (-1: no such name; as deep as the name has parts), then its
\ one declaration.
: lfc-tier ( -- tier ) ck-stage stage-tier ;
: lfc-numeric? ( id -- flag ) lf-name-tag@ lf-name-tag-num = ;
: lfc-part ( prefix id -- n )
  dup lfc-numeric? if lf-name-payload lfc-tier name-seek-num drop exit then
  lf-name-text lfc-tier name-seek-str drop ;
: lfc-name ( id -- n )
  dup 0= if exit then dup lf-name-prefix@ recurse dup 0< if nip exit then swap lfc-part ;
\ The one declaration of tier name n (none for a name several have).
: lfc-decl ( n -- d true | false )
  dup 0< if drop false exit then
  dup ck-stage stage-by-name slab-count u< 0= if drop false exit then
  ck-stage resolution if +1>number else false then ;
: lfc-universes ( d -- n )
  ck-stage staged-params@ dup none? if drop 0 exit then
  ck-stage stage-tuples tuple-length ;
\ A definition's height when its hints are regular, else 0.
: lfc-regular? ( d -- flag )
  dup ck-stage staged-kind@ kind-def =
  swap ck-stage staged-hints@ lf-hint-regular = and ;
: lfc-height ( d -- h ) dup lfc-regular? if ck-stage staged-hint@ else drop 0 then ;
: lfc-find ( name -- universes height true | false )
  lfc-name lfc-decl 0= if false exit then dup lfc-universes swap lfc-height true ;

\ ---- What the natural reader asks of a library constant (front/reader.fs,
\ lfn-library-arity): how many explicit binders its type's telescope has,
\ or -1 when the telescope ends in something that Lean's whnf may unfold
\ to more (an application of a definition or of a lambda, which whnf
\ beta-reduces, a let, a projection or metadata), and whether it is a
\ definition itself (so a type headed by it may unfold).
: lfc-tag ( e -- tag ) lfc-tier expr-tag@ ;
: lfc-def? ( d -- flag ) ck-stage staged-kind@ kind-def = ;
: lfc-pi? ( e -- flag ) lfc-tag tag-pi tag-let within ;
: lfc-explicit ( n e -- n' ) lfc-tag tag-pi = if 1+ then ;
: lfc-telescope ( e -- n e' )
  0 swap begin dup lfc-pi? while tuck lfc-explicit swap lfc-tier expr-b@ repeat ;
: lfc-head ( e -- e' ) begin dup lfc-tag tag-app = while lfc-tier expr-a@ repeat ;
: lfc-const-unfolds? ( e -- flag ) lfc-tier expr-a@ lfc-decl if lfc-def? else false then ;
: lfc-redex-tag? ( tag -- flag )
  dup tag-lam tag-pi within over let-tag? or over tag-let-body = or
  over tag-proj = or swap tag-mdata = or ;
: lfc-unfolds? ( e -- flag )
  lfc-head dup lfc-tag dup tag-const =
  if drop lfc-const-unfolds? else nip lfc-redex-tag? then ;
: lfc-arity ( name -- arity unfolds? true | false )
  lfc-name lfc-decl 0= if false exit then
  dup lfc-def? swap ck-stage staged-type@ lfc-telescope lfc-unfolds? if drop -1 then
  swap true ;
' lfc-arity is lfn-library-arity

\ ---- The stage: the library export read (not sealed yet), or empty.
12 constant lfc-log2
: lfc-read ( checked? -- outcome )
  lfc lfc-env 2@ rot if ck-stage stage-read else ck-stage stage-read-unchecked then ;
: lfc-library-read ( checked? -- outcome )
  lfc lfc-env 2@ ck-size ck-slots ck-log2 ck-stage stage-init
  ok-then? 0= if exit then
  ck-any-version? ck-stage stage-any-version! lfc-read ;
\ A snapshot's tier is in the stage already, read and not sealed
\ (ck-snapshot-import): its declarations are the library's.
: lfc-stage-start ( checked? -- outcome )
  ck-importing? if drop outcome-ok exit then
  lfc-library? if lfc-library-read exit then drop lfc-log2 ck-stage stage-init ;

\ ---- The elaboration data (--elab-data; plan row FE1d): read against
\ the library's names, before they are sealed, and its export's SHA-256:
\ a snapshot's export's, the manifest check's digest, or, for a library
\ read without its manifest, the file hashed here (cli/check-run.fs); a
\ library that cannot be hashed refuses the data (elab-unhashed, error 26).
\ Not with a layered snapshot (refused by the command line): the hash is
\ the base's, the names the layers' too.
: lfc-elab-file! ( c-addr u -- ) lfc lfc-elab-file 2! ;
: lfc-elab-failed? ( -- flag ) lfc lfc-elab-failed @ ;
: lfc-manifest-sha ( -- addr ) ck-stage stage-manifest manifest-digest ;
: lfc-export-sha ( -- addr outcome )
  ck-importing? if ck-snap snap-export-sha outcome-ok exit then
  ck-state ck-checked-read @ if lfc-manifest-sha outcome-ok exit then
  lfc lfc-env 2@ ck-sha-file ck-digest swap ;
: lfc-elab-read ( -- outcome )
  lfc lfc-elab-file 2@ ck-stage lfc-export-sha
  ok-then? if elab-read else nip nip nip elab-unhashed then ;
: lfc-elab-step ( -- outcome )
  lfc lfc-elab-file @ 0= if outcome-ok exit then
  lfc-elab-read dup ok? 0= lfc lfc-elab-failed ! ;
: lfc-library-ready ( checked? -- outcome )
  lfc-stage-start dup ok? if drop lfc-elab-step then ;

\ ---- The text: run by the words, a checked run with the library's finder.
: lfc-finder ( -- xt|0 ) lfc-library? if ['] lfc-find else 0 then ;
: lfc-settings! ( -- )
  lfc-finder lf-author-library! true lf-author-checked! ck-stage lf-menv-library! ;
: lfc-settings-off ( -- ) 0 lf-author-library! false lf-author-checked! ;
\ A text that declares nothing of its own has nothing to check (error 49).
: lfc-own? ( -- flag ) false lf-author-count 0 ?do i lfa-library? 0= or loop ;
: lfc-nothing ( -- outcome )
  0 0 0 lfa-e-nothing lfa-record lfa-e-nothing lf-author-outcome ;
: lfc-something ( outcome -- outcome )
  dup ok? lfc-own? 0= and if drop lfc-nothing then ;
: lfc-run ( c-addr u -- outcome )
  lfc-settings! lf-author-begin lf-author-file lfc-settings-off lfc-something
  dup ok? 0= lfc lfc-failed ! ;
\ Its declarations into the stage, after the library's (stage-extend):
\ records of LeanForth's own exporter, so of another exporter than the
\ pinned one, which the stage takes only when asked.
: lfc-line ( c-addr u -- outcome ) ck-stage stage-line ;
\ A natural text's declarations come from the front end's hand-over
\ (front/handover.fs): when any did (author/form.fs, lfa-front-made?),
\ also in a text that turned to the kernel form after them, only what the
\ declarations reach is written, so a metavariable or node the elaborator
\ left unused blocks nothing (author/export.fs). A text with none, a
\ kernel-form text, is written whole, as before (review fe1f L3).
: lfc-reached? ( -- flag ) lfa-front-made? ;
: lfc-write ( -- outcome )
  ['] lfc-line lfc-reached? if lf-author-export-reached else lf-author-export then ;
: lfc-extended ( -- outcome ) lfc-library? if ck-stage stage-extend else outcome-ok then ;
: lfc-produce ( -- outcome )
  lfc-extended dup ok? 0= if exit then drop
  true ck-stage stage-any-version! ['] lfc-write ck-stage stage-produce
  ck-any-version? ck-stage stage-any-version! ;
\ The text and its records; the stores the words filled are emptied (the
\ records are in the stage now) and given back their settings and sharing.
: lfc-sharing! ( -- ) lf-term-sharing? lfc lfc-sharing ! ;
: lfc-sharing-back ( -- ) lfc lfc-sharing @ lf-term-sharing! ;
: lfc-empty ( -- )
  lf-term-reset lf-level-reset lf-cref-reset lf-name-reset lfa-declarations-reset
  lf-menv-reset lf-mctx-reset ;
: lfc-records ( -- outcome ) lfc-produce dup ok? 0= lfc lfc-refused ! ;
: lfc-made ( c-addr u -- outcome ) lfc-run dup ok? if drop lfc-records then ;
\ The making xt ( c-addr u -- outcome ) runs under CATCH, so that the
\ stores are emptied and given back their room and sharing whatever
\ happens; a THROW then passes on (review N5; the stage has rolled back).
: lfc-caught ( c-addr u xt -- outcome code )
  catch dup if nip nip outcome-invalid swap then ;
: lfc-back ( outcome -- outcome ) lfc-empty lfc-rooms-back ck-first lfc-sharing-back ;
: lfc-making ( c-addr u xt -- outcome )
  lfc-sharing! lfc-rooms ok-then2? if lfc-caught else nip 0 then
  swap lfc-back swap throw ;
: lfc-text ( c-addr u -- outcome ) ['] lfc-made lfc-making ;

\ ---- A library for a run outside check (a Forth session, the authoring
\ tests): lfc-library-open reads the export c-addr u, its manifest checked
\ when checked? is true, into the stage, not sealed, and lets the words
\ name its constants (lfc-find, in this context) and the Meta layer read
\ its declarations (front/meta-env.fs's run mode; any elaboration data
\ read before is dropped: it was read against the stage freed);
\ lfc-library-close frees the stage and the words name none again. A
\ text's run binds the run mode to the stage (lfc-settings!) and
\ lfc-empty leaves it, emptying the metavariable context too (S1 §1).
: lfc-library-open ( c-addr u checked? -- outcome )
  >r lfc-env! elab-reset ck-stage stage-free r> lfc-library-read
  dup ok? if ['] lfc-find lf-author-library! ck-stage lf-menv-library! then ;
: lfc-library-close ( -- )
  lf-menv-reset elab-reset 0 lf-author-library! ck-stage stage-free 0 0 lfc-env! ;

\ ---- Loading, as ck-load (cli/check-run.fs): the staging phase is the
\ library's reading, the text's run and its records, and the seal.
: lfc-staging ( c-addr u checked? -- outcome )
  lfc-fresh lfc-library-ready ok-then? if lfc-text else nip then
  dup ok? if drop ck-stage stage-seal then ;
: lfc-stage-phase ( c-addr u checked? -- outcome )
  ck-phase-begin lfc-staging ck-staging ck-phase-end ck-staging ck-fail ;
: ck-lf-load ( c-addr u checked? -- outcome )
  ck-export! lfc-stage-phase dup ok? if drop ck-stage-facts ck-feed-phase then
  dup ok? if ck-input-facts then dup ck-state ck-loaded ! ;

base !   \ the BASE this file was loaded with
