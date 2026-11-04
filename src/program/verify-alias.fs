\ Correctness mode by a separate vocabulary (ADR 0019 §1-§3, "the alias"),
\ kept working beside the mode shift (verify.fs), which the owner chose as
\ primary: both share every action (verify-semantics.fs) and must give
\ the same IR and the same diagnostics (tests/program/verify_check.py).
\ LeanForth's own words with Forth's names (dup, if, : ...), one for each
\ entry of the verification table, live in the word list pv-alias-words;
\ while a line runs, Forth's own text interpreter (EVALUATE) finds them
\ with only that list and the file's own words in the search order, and
\ each performs its entry's verification semantics. Nothing else is
\ visible, so no host word can run.
\
\ Forth's interpreter also reads numbers, and on Gforth 1.0 its
\ recognizers read more forms ("x", ->x, `dup, 1e ...). So every word of
\ this vocabulary and of the file, when it runs, first checks the text
\ between the previous one and itself (the gap): it must hold only plain
\ decimals, each written as lit n as it is checked, and the data stack
\ must have grown by exactly one cell per decimal, with the value its text
\ gives, and the floating-point stack not at all; the cells are then
\ taken off. The rest of each line is checked the same way. When Forth
\ throws (-13 for an unknown token, others from recognizers), the first
\ token after the checked text that is no plain decimal is refused as
\ unknown. A word finds its own token by reading back from >IN
\ (lfa-invoked, src/author/source.fs), as the authoring words do.
\
\ What it cannot see: a host whose standard word was redefined before the
\ run (the mode shift refuses it), since its words are found by name.
\
\ Public words: lf-alias-file ( c-addr u -- outcome ) and lf-alias-text
\ ( c-addr u c-addr2 u2 -- outcome ), as lf-verify-file and
\ lf-verify-text. Untrusted. State: one context record, pv-alias-gap; the
\ word list, made while this file loads.

require ../author/source.fs
require ./verify-runner.fs

\ The gap: where the line has been read up to, and the values of its
\ decimals. A line of fewer than 128 characters has at most 64 tokens.
64 constant pv-gap-max
begin-structure /pv-gap
  field: pv-gap-synced           \ characters of the line read so far
  field: pv-gap-count            \ decimals in the gap being checked
  pv-gap-max cells +field pv-gap-values
end-structure
/pv-gap context-record: pv-alias-gap

: pv-synced ( -- addr ) pv-alias-gap pv-gap-synced ;
: pv-gap# ( -- addr ) pv-alias-gap pv-gap-count ;
: pv-gap-value ( i -- addr ) cells pv-alias-gap pv-gap-values + ;
: pv-gap-push ( n -- )
  pv-gap# @ pv-gap-max < 0= abort" pv: gap full" pv-gap# @ pv-gap-value ! 1 pv-gap# +! ;

\ The text of the line from offset from to offset to.
: pv-span ( from to -- c-addr u ) over - >r pv-text drop swap chars + r> ;
\ Each token of a gap is a plain decimal, written as lit n, or refused.
: pv-gap-token ( c-addr u -- )
  2dup pv-token! pv-literal? 0= if pv-why-unknown pv-fail then dup pv-gap-push pv-lit ;
: pv-gap-scan ( c-addr u -- )
  begin lfa-next-token dup while pv-gap-token repeat 2drop 2drop ;
\ The cells Forth's interpreter pushed: one per decimal, the last on top.
: pv-host-value ( x i -- ) pv-gap-value @ <> if pv-why-host-literal pv-fail then ;
: pv-taken ( i*x -- )
  depth pv-floor @ - pv-gap# @ <> if pv-why-host-literal pv-fail then
  pv-gap# @ 0 ?do pv-gap# @ 1- i - pv-host-value loop
  pv-floats? 0= if pv-why-host-literal pv-fail then ;
: pv-gap ( from to -- ) 0 pv-gap# ! pv-span pv-gap-scan pv-taken ;

\ Run first by every word of the vocabulary and of the file: its gap,
\ then its own token becomes the current one. A word run any other way
\ than by the runner's EVALUATE of the line refuses.
: pv-ours? ( -- flag ) source pv-evaluated rot = >r = r> and ;
: pv-read-in ( -- ) >in @ pv-text nip min pv-synced ! ;
: pv-offset ( c-addr -- offset ) pv-text drop - ;
: pv-sync ( -- )
  pv-ours? 0= if pv-why-interrupted pv-fail-here then
  lfa-invoked 2dup 2>r drop pv-offset pv-synced @ swap pv-gap 2r> pv-token! pv-read-in ;
\ A word of the vocabulary, and a word of the file, when the interpreter
\ runs it; the line counts as read up to >IN afterwards, past any text
\ the word parsed.
: pv-alias-perform ( entry -- ) >r pv-sync r> pv-perform pv-read-in ;
: pv-alias-call ( index -- ) >r pv-sync r> pv-call pv-read-in ;
' pv-alias-call is pv-word-runs

\ The vocabulary: one word for each entry of the table, named as the
\ entry, made while this file loads with the entry's name handed to
\ CREATE through EVALUATE.
wordlist constant pv-alias-words
: pv-alias-make ( entry "name" -- ) create , does> @ pv-alias-perform ;
create pv-alias-text 32 chars allot
: pv-alias-name ( entry -- c-addr u )
  s" pv-alias-make " tuck pv-alias-text swap chars move >r pv-entry-text
  tuck pv-alias-text r@ chars + swap chars move r> + pv-alias-text swap ;
: pv-alias ( i -- ) pv-entry dup pv-alias-name evaluate ;
get-current pv-alias-words set-current
:noname ( -- ) pv-names store-count @ 0 ?do i pv-alias loop ; execute
set-current

\ The design: the file's words searched after the vocabulary, so that no
\ file word can shadow one of it; the rest of each line checked after it.
: pv-alias-prefix ( -- c-addr u ) s" " ;
: pv-alias-order ( -- ) pv-words @ pv-alias-words 2 set-order ;
: pv-rest-of-line ( -- from to ) pv-synced @ pv-text nip ;
: pv-alias-line ( -- ) 0 pv-synced ! pv-evaluated evaluate pv-rest-of-line pv-gap ;
\ After a THROW of the host's: the gap up to the first token that is no
\ plain decimal, refused as unknown; were there none, the exception.
: pv-alias-caught ( code -- )
  pv-floats-clear 0 pv-gap# ! pv-rest-of-line pv-span pv-gap-scan pv-interrupted ;
' pv-alias-prefix ' pv-alias-order ' pv-alias-line ' pv-alias-caught
pv-design: pv-alias-design

: lf-alias-file ( c-addr u -- outcome ) pv-alias-design pv-file-run ;
: lf-alias-text ( c-addr u c-addr2 u2 -- outcome ) pv-alias-design pv-text-run ;
