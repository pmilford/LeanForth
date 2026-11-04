\ Correctness mode by a mode shift (ADR 0019 §9 (b2), the owner's primary
\ design): the program's words are Forth's own. DUP is FORTH-WORDLIST's
\ DUP; beside its interpretation and compilation semantics it has
\ *verification semantics* (verify-semantics.fs), which a third
\ interpreter state performs. Hosts without recognizers have no hook into
\ their own interpreter, so that state is the short loop below,
\ Forth-2012's text interpreter with a third branch: take the next name
\ with PARSE-NAME; find it with SEARCH-WORDLIST, the file's own words
\ first, then FORTH-WORDLIST; if found, perform its verification
\ semantics; otherwise it must be a plain decimal, read here. The loop
\ runs inside each line as Forth's input source (the runner evaluates
\ "pv-verify-line LINE" with only pv-verify-line visible), so PARSE-NAME,
\ PARSE and >IN are Forth's own and :, ( and CONSTANT parse as Forth's do.
\
\ A host word is known by its identity: the execution token that
\ SEARCH-WORDLIST gives now must be the one the table kept for that name
\ when it was made, so a standard word redefined before the run is refused
\ ("a standard word redefined before the run"), which the separate
\ vocabulary cannot notice. The name is part of the identity because
\ Gforth 0.7.3 gives every compile-only word (IF, THEN, ; ...) one shared
\ token. A reserved word (outside IR 0.1) is known by its name alone. A
\ host word with no verification semantics, LeanForth's own included, is
\ refused as unknown; no host word ever runs, and the host converts no
\ number, so no recognizer of Gforth 1.0 acts.
\
\ Run mode is the same file in plain Forth: `include FILE`.
\
\ Public words (and lf-verify-to, lf-verify-reason, lf-verify-where and
\ lf-verify-message of verify-report.fs and verify-runner.fs):
\   lf-verify-file ( c-addr u -- outcome )   the file at path c-addr u
\   lf-verify-text ( c-addr u c-addr2 u2 -- outcome )  lines of text,
\                                            named c-addr2 u2 in the header
\ Example: s" src/program/clamp.fs" lf-verify-file  writes clamp's IR 0.1
\ (tests/program/ir/clamp.ir) and gives outcome-ok.
\
\ Untrusted, like the rest of correctness mode; it runs source text, so it
\ belongs in the authoring program, never in the checker's process. State:
\ none of its own beyond the entry word list, made while it loads.

require ./verify-runner.fs

\ A token found in FORTH-WORDLIST (xt), or not (0), that has a table
\ entry: performed if it is the word the table knows.
: pv-shift-entry ( entry xt|0 -- )
  over pv-entry-kind @ pv-kind-reserved = if 2drop pv-why-not-ir pv-fail then
  over pv-entry-host @ <> if drop pv-why-replaced pv-fail then pv-perform ;
\ A token with no entry: a host word refuses; anything else must be a
\ plain decimal.
: pv-unknown ( -- ) pv-why-unknown pv-fail ;
: pv-shift-other ( c-addr u xt|0 -- )
  if 2drop pv-unknown then pv-literal? 0= if pv-unknown then pv-lit ;
: pv-shift-named ( c-addr u -- )
  2dup pv-host >r 2dup pv-entry-of
  if nip nip r> pv-shift-entry else r> pv-shift-other then ;
\ One token in verification state.
: pv-shift-token ( c-addr u -- )
  2dup pv-token! 2dup pv-file-word if nip nip pv-call else pv-shift-named then ;

wordlist constant pv-shift-entry-words
get-current pv-shift-entry-words set-current
\ The verification state, for the rest of the input source.
: pv-verify-line ( -- ) begin parse-name dup while pv-shift-token repeat 2drop ;
set-current

: pv-shift-prefix ( -- c-addr u ) s" pv-verify-line " ;
: pv-shift-order ( -- ) pv-shift-entry-words 1 set-order ;
: pv-shift-line ( -- ) pv-evaluated evaluate ;
' pv-shift-prefix ' pv-shift-order ' pv-shift-line ' pv-interrupted pv-design: pv-shift

: lf-verify-file ( c-addr u -- outcome ) pv-shift pv-file-run ;
: lf-verify-text ( c-addr u c-addr2 u2 -- outcome ) pv-shift pv-text-run ;
