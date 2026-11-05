\ Unit tests of src/lib/text-rule.fs, visible text, on its own (no
\ checker loaded): the header's examples; the ends of the banned and
\ not-seen ranges; texts that look blank; malformed UTF-8, which fails
\ closed; and the private helpers on bytes that are not UTF-8, which stop
\ at the end of the text. Every code point is compared with the schema's
\ patterns by tests/core/test_run_records.py.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/text-rule.fs
lf-lib-private order+

\ The header's examples.
: plain ( -- c-addr u ) s" composition" ;
: overridden ( -- c-addr u ) s\" a\xe2\x80\xaeb" ;
: filler ( -- c-addr u ) s\" \xe3\x85\xa4" ;
: accented ( -- c-addr u ) s\" a\xcc\x81" ;
T{ plain tr-shown? overridden tr-rule? filler tr-shown? accented tr-shown?
  -> true false false true }T
T{ 0 0 tr-rule? 0 0 tr-shown? -> true false }T

\ One character: the rule, and shown.
create one-char 4 allot
: rule? ( code -- flag ) one-char utf8-put one-char swap tr-rule? ;
: shown? ( code -- flag ) one-char utf8-put one-char swap tr-shown? ;
T{ $0 rule? $1f rule? $20 rule? $7e rule? $7f rule? $9f rule? -> 0 0 -1 -1 0 0 }T
T{ $a0 rule? $ad rule? $600 rule? $61c rule? $200b rule? $2028 rule? -> -1 0 0 0 0 0 }T
T{ $202e rule? $202f rule? $feff rule? $fffa rule? $110bd rule? -> 0 -1 0 0 0 }T
T{ $e0001 rule? $e0080 rule? -> 0 -1 }T
T{ $20 shown? $3000 shown? $3164 shown? $2800 shown? $ffa0 shown? -> 0 0 0 0 0 }T
T{ $115f shown? $300 shown? $36f shown? $370 shown? $fe0f shown? -> 0 0 0 -1 0 }T
T{ $e0100 shown? $e1000 shown? $41 shown? $3b1 shown? $1f600 shown? -> 0 -1 -1 -1 -1 }T
\ Private use and unassigned code points count as seen.
T{ $e000 shown? $ffff shown? $10ffff shown? -> -1 -1 -1 }T

\ Malformed UTF-8 fails closed in both words.
: overlong ( -- c-addr u ) s\" \xc0\xaf" ;
: surrogate ( -- c-addr u ) s\" \xed\xa0\x80" ;
: too-high ( -- c-addr u ) s\" \xf4\x90\x80\x80" ;
: cut-short ( -- c-addr u ) s\" a\xe2\x80" ;
: lone-tail ( -- c-addr u ) s\" \x80a" ;
T{ overlong tr-rule? surrogate tr-rule? too-high tr-rule? cut-short tr-rule? -> 0 0 0 0 }T
T{ lone-tail tr-rule? lone-tail tr-shown? cut-short tr-shown? -> 0 0 0 }T

\ The helpers on bytes that are not UTF-8: tr-next takes all that is left
\ as the code -1, which is banned and not seen; tr-some? ends at the text's
\ end. tr-next decodes a valid character (bytes.fs's utf8-decode).
T{ lone-tail tr-next rot drop -> 0 -1 }T
T{ -1 tr-banned? -1 tr-seen? -> true false }T
T{ lone-tail ' tr-seen? tr-some? lone-tail ' tr-banned? tr-some? -> false true }T
T{ accented 1 /string tr-next nip nip overridden 1 /string tr-next nip nip -> $301 $202e }T

\ tr-banned?, public: a code point no text may hold, at the ends of the
\ ranges; what it bans is exactly what tr-rule? refuses in a text.
T{ $0 tr-banned? $1f tr-banned? $20 tr-banned? $85 tr-banned? $a0 tr-banned? -> -1 -1 0 -1 0 }T
T{ $200f tr-banned? $2010 tr-banned? $2028 tr-banned? $202e tr-banned? -> -1 0 -1 -1 }T
T{ $bb tr-banned? $e007f tr-banned? $e0080 tr-banned? -> 0 -1 0 }T
: agrees? ( code -- flag ) dup tr-banned? 0= swap rule? = ;
T{ $85 agrees? $2066 agrees? $41 agrees? $feff agrees? $bb agrees? -> -1 -1 -1 -1 -1 }T

cases-done
bye
