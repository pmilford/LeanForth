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
\ lfc-library# ( -- n ) the library's declarations, the input's first n;
\ lfc-library-open ( c-addr u checked? -- outcome ) and lfc-library-close
\ ( -- ), a library for the words outside check (see below).
\ Untrusted, like the stage and the words: neither can make a declaration
\ accepted; only check-declaration and the publisher decide.
\ State: one context record, lfc (the library's name, whether the text
\ failed, the library's size, the settings kept while the words run).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../author/runner.fs
require ../import/stage.fs
require ./check-run.fs

begin-structure /lfc
  2 cells +field lfc-env         \ the library export's file name, or 0 0
  field: lfc-failed              \ true: the text stopped with an error
  field: lfc-library             \ declarations the library export holds
  field: lfc-sharing             \ the term store's sharing before the run
  field: lfc-names               \ the stores' capacity settings before the run
  field: lfc-terms
  field: lfc-levels
  field: lfc-crefs
end-structure
/lfc context-record: lfc

: lfc-env! ( c-addr u -- ) lfc lfc-env 2! ;
\ A library: an export (--env) or a snapshot's tier (--snapshot, ck-importing?).
: lfc-library? ( -- flag ) lfc lfc-env @ 0<> ck-importing? or ;
: lfc-failed? ( -- flag ) lfc lfc-failed @ ;
: lfc-library# ( -- n ) lfc lfc-library @ ;

\ ---- The stores' room while the words run: the name, term, level and
\ reference stores' settings raised to the most a store may hold (they
\ grow only as records are made), then given back; the first refusal is
\ the outcome.
: lfc-kept ( -- ) lf-name-capacity lfc lfc-names ! lf-term-capacity lfc lfc-terms !
  lf-level-capacity lfc lfc-levels ! lf-cref-capacity lfc lfc-crefs ! ;
: lfc-rooms ( -- outcome )
  lfc-kept feed-most lf-name-capacity! feed-most lf-term-capacity! ck-first
  feed-most lf-level-capacity! ck-first feed-most lf-cref-capacity! ck-first ;
: lfc-rooms-back ( -- outcome )
  lfc lfc-names @ lf-name-capacity! lfc lfc-terms @ lf-term-capacity! ck-first
  lfc lfc-levels @ lf-level-capacity! ck-first
  lfc lfc-crefs @ lf-cref-capacity! ck-first ;

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
\ A definition's height when its hints are regular (code 2), else 0.
: lfc-regular? ( d -- flag )
  dup ck-stage staged-kind@ kind-def = swap ck-stage staged-hints@ 2 = and ;
: lfc-height ( d -- h ) dup lfc-regular? if ck-stage staged-hint@ else drop 0 then ;
: lfc-find ( name -- universes height true | false )
  lfc-name lfc-decl 0= if false exit then dup lfc-universes swap lfc-height true ;

\ ---- The stage: the library export read (not sealed yet), or empty.
12 constant lfc-log2
: lfc-read ( checked? -- outcome )
  lfc lfc-env 2@ rot if ck-stage stage-read else ck-stage stage-read-unchecked then ;
: lfc-library-read ( checked? -- outcome )
  lfc lfc-env 2@ ck-size ck-slots ck-log2 ck-stage stage-init
  ok-then? 0= if exit then
  ck-any-version? ck-stage stage-any-version! lfc-read
  ck-stage stage-decls lfc lfc-library ! ;
\ A snapshot's tier is in the stage already, read and not sealed
\ (ck-snapshot-import): its declarations are the library's.
: lfc-snapshot-start ( checked? -- outcome )
  drop ck-stage stage-decls lfc lfc-library ! outcome-ok ;
: lfc-stage-start ( checked? -- outcome )
  0 lfc lfc-library ! ck-importing? if lfc-snapshot-start exit then
  lfc-library? if lfc-library-read exit then drop lfc-log2 ck-stage stage-init ;

\ ---- The text: run by the words, a checked run with the library's finder.
: lfc-finder ( -- xt|0 ) lfc-library? if ['] lfc-find else 0 then ;
: lfc-settings! ( -- ) lfc-finder lf-author-library! true lf-author-checked! ;
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
: lfc-write ( -- outcome ) ['] lfc-line lf-author-export ;
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
  lf-term-reset lf-level-reset lf-cref-reset lf-name-reset lfa-declarations-reset ;
: lfc-made ( c-addr u -- outcome ) lfc-run dup ok? if drop lfc-produce then ;
: lfc-text ( c-addr u -- outcome )
  lfc-sharing! lfc-rooms ok-then? if lfc-made else nip then
  lfc-empty lfc-rooms-back ck-first lfc-sharing-back ;

\ ---- A library for a run outside check (a Forth session, the authoring
\ tests): lfc-library-open reads the export c-addr u, its manifest checked
\ when checked? is true, into the stage, not sealed, and lets the words
\ name its constants (lfc-find, in this context); lfc-library-close frees
\ the stage and the words name none again.
: lfc-library-open ( c-addr u checked? -- outcome )
  >r lfc-env! ck-stage stage-free r> lfc-library-read
  dup ok? if ['] lfc-find lf-author-library! then ;
: lfc-library-close ( -- ) 0 lf-author-library! ck-stage stage-free 0 0 lfc-env! ;

\ ---- Loading, as ck-load (cli/check-run.fs): the staging phase is the
\ library's reading, the text's run and its records, and the seal.
: lfc-staging ( c-addr u checked? -- outcome )
  false lfc lfc-failed ! lfc-stage-start ok-then? if lfc-text else nip then
  dup ok? if drop ck-stage stage-seal then ;
: lfc-stage-phase ( c-addr u checked? -- outcome )
  ck-phase-begin lfc-staging ck-staging ck-phase-end ck-staging ck-fail ;
: ck-lf-load ( c-addr u checked? -- outcome )
  ck-export! lfc-stage-phase dup ok? if drop ck-stage-facts ck-feed-phase then
  dup ok? if ck-input-facts then dup ck-state ck-loaded ! ;

base !   \ the BASE this file was loaded with
