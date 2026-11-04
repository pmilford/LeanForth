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
\ between the previous one and itself (the gap): it must hold only the
\ numbers verify-semantics.fs reads (decimals, Forth-2012's # $ % prefixes
\ and 'c'), each written as lit n as it is checked, and the data stack
\ must have grown by exactly one cell per number, with the value its text
\ gives, and the floating-point stack not at all; the cells are then
\ taken off. The rest of each line is checked the same way. When Forth
\ throws (-13 for an unknown token, others from recognizers), the first
\ token after the checked text that is no such number is refused as
\ unknown. A word finds its own token by reading back from >IN
\ (lfa-invoked, src/author/source.fs), as the authoring words do. A word
\ of the file is found by Forth's interpreter itself, so its newest
\ version, as in the mode shift.
\
\ What it cannot see: a host whose standard word was redefined before the
\ run (the mode shift refuses it), since its words are found by name. On
\ a host with cells narrower than 33 bits, which reads 4294967295 as -1,
\ it refuses such a literal where the mode shift writes it (unmodeled
\ there).
\
\ Public words: lf-alias-file ( c-addr u -- outcome ) and lf-alias-text
\ ( c-addr u c-addr2 u2 -- outcome ), as lf-verify-file and
\ lf-verify-text. Untrusted. State: one context record, pv-alias-gap; the
\ word list, made while this file loads.

require ../author/source.fs
require ./verify-runner.fs

\ The gap: where the line has been read up to, and the values of its
\ numbers, each a double (verify-semantics.fs). A line of fewer than 128
\ characters has at most 64 tokens.
64 constant pv-gap-max
begin-structure /pv-gap
  field: pv-gap-synced           \ characters of the line read so far
  field: pv-gap-count            \ numbers in the gap being checked
  pv-gap-max 2* cells +field pv-gap-values
end-structure
/pv-gap context-record: pv-alias-gap

: pv-synced ( -- addr ) pv-alias-gap pv-gap-synced ;
: pv-gap# ( -- addr ) pv-alias-gap pv-gap-count ;
: pv-gap-value ( i -- addr ) 2* cells pv-alias-gap pv-gap-values + ;
: pv-gap-push ( d -- )
  pv-gap# @ pv-gap-max < 0= abort" pv: gap full" pv-gap# @ pv-gap-value 2! 1 pv-gap# +! ;

\ The text of the line from offset from to offset to.
: pv-span ( from to -- c-addr u ) over - >r pv-text drop swap chars + r> ;
\ Each token of a gap is a number, written as lit n, or refused.
: pv-host-literal? ( flag -- ) pv-why-host-literal pv-?fail ;
: pv-gap-token ( c-addr u -- )
  2dup pv-token! pv-literal? 0= pv-why-unknown pv-?fail 2dup pv-gap-push pv-lit ;
: pv-gap-scan ( c-addr u -- )
  begin lfa-next-token dup while pv-gap-token repeat 2drop 2drop ;
\ The cells Forth's interpreter pushed: one per number, the last on top,
\ each holding the number's value (a 32-bit host, which reads $FFFFFFFF
\ as -1, is refused here).
: pv-host-value ( x i -- ) >r s>d r> pv-gap-value 2@ d= 0= pv-host-literal? ;
: pv-taken ( i*x -- )
  depth pv-floor @ - pv-gap# @ <> pv-host-literal?
  pv-gap# @ 0 ?do pv-gap# @ 1- i - pv-host-value loop pv-floats? 0= pv-host-literal? ;
: pv-gap ( from to -- ) 0 pv-gap# ! pv-span pv-gap-scan pv-taken ;

\ Run first by every word of the vocabulary and of the file: its gap,
\ then its own token becomes the current one. A word run any other way
\ than by the runner's EVALUATE of the line refuses.
: pv-ours? ( -- flag ) source pv-evaluated rot = >r = r> and ;
: pv-read-in ( -- ) >in @ pv-text nip min pv-synced ! ;
: pv-sync ( -- )
  pv-ours? 0= pv-why-interrupted pv-?fail-here
  lfa-invoked 2dup 2>r drop pv-chars-in pv-synced @ swap pv-gap 2r> pv-token! pv-read-in ;
\ A word of the vocabulary, and a word of the file, when the interpreter
\ runs it; the line counts as read up to >IN afterwards, past any text
\ the word parsed.
: pv-alias-perform ( entry -- ) >r pv-sync r> pv-perform pv-read-in ;
: pv-alias-call ( index -- ) >r pv-sync r> pv-call pv-read-in ;

\ The vocabulary: one word for each entry of the table, named as the
\ entry, made while this file loads with the entry's name handed to
\ CREATE through EVALUATE ("pv-alias-make NAME").
wordlist constant pv-alias-words
: pv-alias-make ( entry "name" -- ) create , does> @ pv-alias-perform ;
s" pv-alias-make " nip pv-entry-chars + constant pv-alias-chars
create pv-alias-text pv-alias-chars chars allot
\ Append c-addr u to the text, which holds n characters.
: pv-alias-append ( c-addr u n -- n' )
  >r tuck pv-alias-text r@ chars + swap chars move r> + ;
: pv-alias-name ( entry -- c-addr u )
  s" pv-alias-make " 0 pv-alias-append >r pv-entry-text r> pv-alias-append
  pv-alias-text swap ;
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
\ A host word an action reads (TYPE after S"): found by name, as every
\ word of this vocabulary is.
: pv-alias-host ( c-addr u entry -- ) drop 2drop ;
pv-design: pv-alias-design
' pv-alias-prefix pv-alias-design pv-design-prefix !
' pv-alias-order pv-alias-design pv-design-order !
' pv-alias-line pv-alias-design pv-design-line !
' pv-alias-caught pv-alias-design pv-design-caught !
' pv-alias-call pv-alias-design pv-design-call !
' pv-alias-host pv-alias-design pv-design-host !

: lf-alias-file ( c-addr u -- outcome ) pv-alias-design pv-file-run ;
: lf-alias-text ( c-addr u c-addr2 u2 -- outcome ) pv-alias-design pv-text-run ;
