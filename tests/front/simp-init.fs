\ The LeanForth side of make reference-simp-init (simp group 4, pass 3;
\ tests/front/check_simp_init.py, which writes the texts): Init's export
\ read once into a stage with its manifest, then its format-4.1
\ elaboration data, then each LeanForth text of a list run in turn by
\ the authoring words, as the tactics' unit tests run theirs
\ (tests/support/tactic-text.fs). Each run is one line, "ok FILE", or
\ "error FILE " and the author's error (lf-author-error.) followed by
\ "<bt>" and the return stack at the run's first throw of an unsupported
\ outcome that no deeper one followed, as Gforth prints a backtrace (its
\ THROW is deferred: wrapped here while the texts run), and "</bt>", so
\ that the harness can name the word that refused. Gforth 1.0 only: a
\ test tool, never part of the checker. Nothing here accepts a theorem:
\ check_simp_init.py hands the texts that ran to bin/leanforth check
\ against Init's snapshot, whose kernel decides.
\ Usage:
\   gforth tests/front/simp-init.fs -e 's" EXPORT" s" DATA" s" LIST" simp-init-run bye'
require ../../src/load/checker.fs
require ../../src/load/front.fs
require ../../src/cli/check-lf.fs
decimal

: si-must ( outcome -- ) ok? 0= abort" simp-init.fs: a loading step failed" ;
: si-open ( export-a export-u data-a data-u -- )
  16000000 lf-term-capacity! drop  1000000 lf-cref-capacity! drop
  2swap true lfc-library-open si-must
  lfc-elab-file! lfc-elab-read si-must lfc-rooms si-must ;

\ ---- The first unsupported throw's return stack (a deeper one replaces
\ it: a THROW passed on by a CATCH is no deeper than the first), else
\ that of a tactic's own refusal (lf-tac-unported: the author's error 99).
action-of throw constant si-throw0
lf-meta-throw-base outcome-unsupported - constant si-code
variable si-rp   variable si-bts
: si-deeper? ( -- flag ) si-rp @ 0= rp@ si-rp @ u<= or ;
: si-tactic? ( code -- flag )
  lf-author-throw = lf-author-code lfa-e-tac-form = and si-rp @ 0= and ;
: si-first? ( code -- flag ) dup si-code = if drop si-deeper? else si-tactic? then ;
: si-save ( -- ) rp@ si-rp ! store-backtrace stored-backtrace $@ si-bts $! ;
: si-throw ( code -- code ) dup si-first? if si-save then si-throw0 execute ;
: si-bt. ( -- ) ."  <bt>" si-rp @ if si-bts $@ over + print-backtrace then ."  </bt>" ;

\ ---- One text.
: si-error. ( c-addr u -- ) ." error " type space lf-author-error. si-bt. ;
: si-ran ( c-addr u -- )
  lf-author-code if si-error. else ." ok " type then cr ;
: si-text ( c-addr u -- )
  0 si-rp ! 2dup lf-author-begin ['] lf-author-file catch
  ?dup if ." thrown " . 2drop type cr exit then drop si-ran ;

\ ---- The list: one file name a line.
create si-line 1024 allot
: si-next ( fid -- c-addr u true | false )
  si-line 1024 rot read-line throw if si-line swap true else drop false then ;
: si-texts ( fid -- ) begin dup si-next while si-text repeat close-file throw ;
: simp-init-run ( export-a export-u data-a data-u list-a list-u -- )
  2>r si-open 2r> r/o open-file throw
  ['] si-throw is throw si-texts si-throw0 is throw ;
