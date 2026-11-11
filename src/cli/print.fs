\ Proof outlines from a Lean export (plan tasks 2.4.4 and 3.4.1; ADR 0013
\ L7): the words behind `leanforth print` (cli/leanforth.fs) and make print
\ (tests/support/print-outline.fs). The export is staged and fed to the
\ checker as `check` does (cli/check-run.fs: import/stage.fs, import/
\ feed.fs; any size), with two hooks on the feed, which read what the feed
\ drops and put it into the presentation side table
\ (present/binder-table.fs), which the checker never reads: every binder's
\ name and kind (pr-binder-hook), and the line of the export each
\ declaration came from (pr-decl-hook, the stage keeps it). The declared
\ type of a constant is found in the input itself (lf-pres-type@), so the
\ side table's small table of declarations is not used. The export is read
\ once, so the names come from the very bytes checked.
\ Then each declaration is checked in turn, through the checked
\ environment's serial step (lf-env-step) with the derivation log at
\ level terms and every limit at its capacity, and its outline
\ (present/proof-outline.fs) printed right after its check, while its log
\ is still in the context.
\
\ Untrusted presentation code: nothing here decides or changes a verdict;
\ the verdict printed is the published slot's (lf-env-outcome), with its
\ label and axioms, and the log is the checker's; the outline printer
\ itself refuses a log that does not agree with that verdict, a
\ declaration not accepted, and a log truncated or kept without formulas.
\ The printer's scratch between checks advances the stores' identity
\ serials, so a diagnostic whose numbers are identities or serials (codes
\ 8, 21, 25, 27) can differ from check's for a later declaration; no
\ verdict depends on them.
\ State: one record in the checker context, print-state (the number of
\ declarations whose line is kept), and a growable array of the context,
\ pr-lines: the line of each input declaration in the file. No fixed
\ buffer: a name is compared with the text given component by component,
\ whatever its length and depth.

require ../lib/lib.fs
require ../core/input.fs
require ../core/derivation-log.fs
require ../kernel/environment.fs
require ../kernel/env-publish.fs
require ../kernel/check-declaration.fs
require ../present/binder-table.fs
require ../present/print-names.fs
require ../present/proof-outline.fs
require ./check-run.fs

begin-structure /pr
  field: pr-decls                       \ input declarations whose line is kept
end-structure
/pr context-record: print-state
1 cells context-slab: pr-lines          \ each input declaration's line, by index

\ The feed's hooks. A binder's name and kind go to the side table (a
\ refusal only leaves a name out); the line of declaration d goes to each
\ input declaration it made (a block's members one by one, its header none).
: pr-binder-hook ( term name kind -- ) lf-pres-binder! drop ;
: pr-line! ( line i -- ) pr-lines slab-at ! ;
: pr-lines-room? ( n -- flag ) pr-lines slab-hold ok? ;
: pr-decl-hook ( d before after -- )
  dup pr-lines-room? 0= if drop 2drop exit then
  dup print-state pr-decls ! rot ck-stage staged-line@ -rot swap
  ?do dup i pr-line! loop drop ;
: pr-reset ( -- ) 0 print-state pr-decls ! lf-pres-reset ;
\ Stage and feed the export c-addr u (cli/check-run.fs's ck-load, after
\ ck-start), its manifest checked when checked? is true, the hooks on:
\ the outcome of the stage or the feed.
\ The side table keeps a binder's name per node, so the term store's
\ hash-consing (core/terms.fs, compact-store plan step S3), which would
\ make two binders that differ only in their names one node, is off.
: pr-load ( c-addr u checked? -- outcome )
  false lf-term-sharing! pr-reset ['] pr-binder-hook ['] pr-decl-hook ck-hooks! ck-load ;

\ Whether the text c-addr u spells the name id: components joined by dots,
\ numeric ones in decimal (as the printer spells a name), compared from the
\ last component back, so nothing is copied and no length is limited.
: pr-part-text ( id -- c-addr u )
  dup lf-name-tag@ lf-name-tag-str = if lf-name-text else lf-name-payload lf-pp-digits then ;
\ The text ends with the part pa pu: the text without it, or false.
: pr-ends? ( c u pa pu -- c u' flag )
  2 pick over u< if 2drop false exit then
  2swap 2 pick - 2dup + 3 pick 5 pick 5 pick compare 0=
  >r 2>r 2drop 2r> r> ;
: pr-dot? ( c u -- c u' flag ) dup 0= if false exit then 1- 2dup + 1 s" ." compare 0= ;
: pr-named? ( c-addr u id -- flag )
  begin dup while
    dup >r pr-part-text pr-ends? 0= if r> drop 2drop false exit then
    r> lf-name-prefix@ dup if >r pr-dot? 0= if r> drop 2drop false exit then r> then
  repeat drop nip 0= ;
\ The first declaration named c-addr u: (i true), or false.
: pr-find ( c-addr u -- i true | false )
  lf-input-count 0 ?do 2dup i lf-input-name pr-named? if 2drop i true unloop exit then loop
  2drop false ;

\ Checking declaration i (lf-env-step): whether the run must stop, as
\ check's does: a fault, or a THROW in the check (the context spent).
: pr-step ( i -- fault? )
  ['] lf-check-declaration swap lf-env-step nip lf-env-spent? or ;
\ Whether declaration i is still to check: not already published by the
\ check of its inductive block's first member (as the environment's own
\ run skips it, lf-env-next), whose log and outline cover the block.
: pr-due? ( i -- flag ) lf-env-published? 0= ;
\ Its verdict, read in a view of the environment: the outcome and, when
\ accepted, the axiom set (-1 otherwise); invalid when no view can be had.
: pr-verdict ( i -- outcome axioms )
  lf-env-view ok? 0= if drop outcome-invalid -1 exit then
  dup lf-env-outcome swap lf-env-axioms ok? 0= if drop -1 then ;
: pr-line ( i -- line )
  dup print-state pr-decls @ < if pr-lines slab-at @ else drop 0 then ;
\ Print the outline of declaration i of the export c-addr u (detail:
\ every step of its log), right after its check; its outcome.
: pr-print ( c-addr u i detail -- outcome )
  >r dup >r pr-line lf-outline-source r> pr-verdict over r> swap >r lf-outline r> ;
\ The log every later check writes: level terms, every limit at its
\ capacity, which a complete outline needs (set outside jobs).
: pr-log-on ( -- ) lf-log-terms lf-log-set lf-log-capacities lf-log-limits ;

\ The statement forms of --statement: names joined by commas, as the mask
\ lf-forms! takes (present/statement-forms.fs); false for a name that is
\ none of them or for an empty list.
: pr-form-bit ( c-addr u -- bit )
  2dup s" lean" compare 0= if 2drop lf-form-lean exit then
  2dup s" mathematics" compare 0= if 2drop lf-form-mathematics exit then
  2dup s" leanforth" compare 0= if 2drop lf-form-leanforth exit then
  s" all" compare 0= if lf-forms-all else 0 then ;
\ The first name of a comma-separated list: the rest, then the name.
: pr-item ( c-addr u -- rest-addr rest-u item-addr item-u )
  2dup s" ," search 0= if 2drop 2dup + 0 2swap exit then
  2swap drop 2 pick over - >r >r 1 /string r> r> ;
: pr-ends-comma? ( c-addr u -- flag ) dup 0= if 2drop false exit then
  2dup dup 1- /string s" ," compare 0= nip nip ;
: pr-forms ( c-addr u -- mask true | false )
  2dup pr-ends-comma? if 2drop false exit then
  0 >r begin dup while pr-item pr-form-bit dup 0= if drop 2drop r> drop false exit then
    r> or >r repeat 2drop r> ?dup if true else false then ;
