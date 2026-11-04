\ The program words' run record, reasons and output (ADR 0019): shared by
\ both designs that run a Forth source file in correctness mode, the mode
\ shift (verify.fs) and the separate vocabulary (verify-alias.fs). A run
\ writes IR 0.1 (docs/programming/PROGRAM_IR.md) one line at a time
\ through an output word ( c-addr u -- ), each line with the line and
\ column of its source token, and stops at the first refusal with one
\ diagnostic line, "OUTCOME @line:column: reason: token", and an outcome
\ (ADR 0008): unsupported for Forth outside IR 0.1, invalid for malformed
\ Forth or an unreadable file, full when a capacity is reached.
\
\ Reasons are numbered as src/program/ir-reader.fs, today's reader and
\ the program words' test oracle, numbers its diagnostics, plus four of
\ their own (27 to 30); their messages are records in the format of the
\ authoring layer's catalogue (src/author/errors.fs), each with its fixed
\ outcome. The current token is an offset into the line being run, the
\ authoring layer's idea of a position (src/author/source.fs).
\
\ Untrusted: the words translate text and prove nothing; receipts name
\ them in their trusted-reader assumption. State: one context record,
\ pv-run, reached only through the accessors below; the catalogue, the
\ indentation's blanks and the two designs' records, read-only once
\ loaded. The output word, run while a run is under way, must take its
\ two cells and leave none (else the run fails as invalid, "output word
\ failed"); a run it starts in its own context aborts (THROW -2) and
\ changes nothing.

require ../lib/lib.fs
require ../author/errors.fs

\ The THROW code with which a word stops a run after recording its
\ diagnostic; only the runner (verify-runner.fs) catches it.
-4130 constant pv-throw

\ Reasons. 1 to 21 and 26 are today's reader's, with its messages.
0 constant pv-why-none
1 constant pv-why-unknown        2 constant pv-why-not-ir
3 constant pv-why-outside        4 constant pv-why-inside
5 constant pv-why-unbalanced     6 constant pv-why-nested
7 constant pv-why-unclosed       8 constant pv-why-comment
9 constant pv-why-recursive      10 constant pv-why-redefined
11 constant pv-why-long-name     12 constant pv-why-no-value
13 constant pv-why-left-over     14 constant pv-why-capacity
15 constant pv-why-unreadable    16 constant pv-why-character
17 constant pv-why-no-name       18 constant pv-why-two-whiles
19 constant pv-why-one-value     20 constant pv-why-borrowed
21 constant pv-why-dividing      23 constant pv-why-output
25 constant pv-why-busy          26 constant pv-why-interrupted
27 constant pv-why-host-literal  28 constant pv-why-compiling
29 constant pv-why-replaced      30 constant pv-why-number-name

create pv-catalogue
  pv-why-unknown s" not a known word or 32-bit decimal" lfa-unsupported,
  pv-why-not-ir s" a Forth word outside IR 0.1" lfa-unsupported,
  pv-why-outside s" not allowed outside a definition" lfa-unsupported,
  pv-why-inside s" not allowed inside a definition" lfa-unsupported,
  pv-why-unbalanced s" unbalanced control structure" lfa-invalid,
  pv-why-nested s" a definition inside a definition" lfa-invalid,
  pv-why-unclosed s" definition not closed" lfa-invalid,
  pv-why-comment s" comment not closed on its line" lfa-unsupported,
  pv-why-recursive s" recursive call" lfa-unsupported,
  pv-why-redefined s" name already defined" lfa-unsupported,
  pv-why-long-name s" name longer than 31 characters" lfa-unsupported,
  pv-why-no-value s" constant without a value" lfa-unsupported,
  pv-why-left-over s" values left outside a definition" lfa-unsupported,
  pv-why-capacity s" reader capacity exceeded" lfa-full,
  pv-why-unreadable s" file not readable or line too long" lfa-invalid,
  pv-why-character s" a character outside printable ASCII" lfa-unsupported,
  pv-why-no-name s" a name must follow on the same line" lfa-invalid,
  pv-why-two-whiles s" a second WHILE in one loop" lfa-unsupported,
  pv-why-one-value s" not exactly one value before CONSTANT" lfa-unsupported,
  pv-why-borrowed s" takes values from outside the file" lfa-unsupported,
  pv-why-dividing s" a division outside a definition" lfa-unsupported,
  pv-why-output s" output word failed" lfa-invalid,
  pv-why-busy s" reader busy" lfa-invalid,
  pv-why-interrupted s" read stopped by an exception" lfa-invalid,
  pv-why-host-literal s" the host read a literal differently from its text" lfa-invalid,
  pv-why-compiling s" run while Forth is compiling" lfa-invalid,
  pv-why-replaced s" a standard word redefined before the run" lfa-unsupported,
  pv-why-number-name s" a name that reads as a number" lfa-unsupported,
  pv-why-none outcome-invalid s" no diagnostic" lfa-message,

\ A reason's record; any number the catalogue lacks gives the closing
\ record, "no diagnostic" with the outcome invalid, never ok.
: pv-message-of ( reason -- message )
  pv-catalogue begin dup lfa-last? 0= while 2dup lfa-message-code @ <> while
    lfa-message-next repeat then nip ;
: lf-verify-message ( reason -- c-addr u ) pv-message-of lfa-message-text ;
: pv-reason-outcome ( reason -- outcome ) pv-message-of lfa-message-outcome @ ;

\ Capacities: those of today's reader.
96 constant pv-out-chars         \ longest output line
128 constant pv-line-chars       \ source lines must be shorter than this
32 constant pv-prefix-chars      \ room before the line for a design's entry word
128 constant pv-path-chars       \ a longer path is cut (it cannot fit its header line)
20 constant pv-indent-chars      \ the deepest indentation (verify-semantics.fs checks it)

\ A design: how it runs a line, made once while its file loads and read
\ only afterwards. The mode shift (verify.fs) and the separate vocabulary
\ (verify-alias.fs) are the two; pv-design: makes an empty one, whose
\ fields the design's file fills.
begin-structure /pv-design
  field: pv-design-prefix        \ ( -- c-addr u ) text before each line
  field: pv-design-order         \ ( -- ) set the run's search order
  field: pv-design-line          \ ( -- ) run the line in the source buffer
  field: pv-design-caught        \ ( code -- ) after a THROW that is no diagnostic
  field: pv-design-call          \ ( index -- ) a word of the file, run by Forth's interpreter
end-structure
: pv-design: ( "name" -- ) create here /pv-design dup allot erase ;

begin-structure /pv-run
  field: pv-run-emit             \ the output word ( c-addr u -- )
  field: pv-run-busy             \ true while a run is under way in this context
  \ The run: pv-reset erases everything from here on.
  field: pv-run-design           \ the design running it
  field: pv-run-outcome          \ ok until the first diagnostic
  field: pv-run-reason           \ why it stopped, or pv-why-none
  field: pv-run-line             \ the line being run, from 1; 0 before the first
  field: pv-run-where            \ where it stopped: line and column, as lfa-pos
  field: pv-run-token            \ the current token: offset in the line, -1 for none
  field: pv-run-token#           \ and its length
  field: pv-run-text             \ the line being run: address
  field: pv-run-text#            \ and length
  field: pv-run-prefix#          \ characters before the line in pv-run-source
  field: pv-run-out#
  pv-out-chars chars aligned +field pv-run-out
  pv-prefix-chars pv-line-chars + chars aligned +field pv-run-source  \ evaluated
  field: pv-run-path#
  pv-path-chars chars aligned +field pv-run-path
end-structure
/pv-run context-record: pv-run

\ Accessors: the only words that name pv-run.
: pv-busy ( -- addr ) pv-run pv-run-busy ;
: pv-emit-xt ( -- addr ) pv-run pv-run-emit ;
: pv-design ( -- addr ) pv-run pv-run-design ;
: pv-design@ ( -- design ) pv-design @ ;
\ A word of the file when Forth's interpreter runs it: the design says.
: pv-word-runs ( index -- ) pv-design@ pv-design-call @ execute ;
: pv-outcome ( -- addr ) pv-run pv-run-outcome ;
: pv-reason ( -- addr ) pv-run pv-run-reason ;
: pv-line# ( -- addr ) pv-run pv-run-line ;
: pv-where ( -- addr ) pv-run pv-run-where ;
: pv-token ( -- addr ) pv-run pv-run-token ;
: pv-token# ( -- addr ) pv-run pv-run-token# ;
: pv-text ( -- c-addr u ) pv-run dup pv-run-text @ swap pv-run-text# @ ;
: pv-text! ( c-addr u -- ) pv-run tuck pv-run-text# ! pv-run-text ! ;
: pv-prefix# ( -- addr ) pv-run pv-run-prefix# ;
: pv-out# ( -- addr ) pv-run pv-run-out# ;
: pv-out ( -- c-addr ) pv-run pv-run-out ;
: pv-source ( -- c-addr ) pv-run pv-run-source ;
: pv-path ( -- c-addr u ) pv-run dup pv-run-path swap pv-run-path# @ ;
\ A copy of the path, so that it may be in a transient buffer; a longer
\ one is cut, and cannot fit its header line either.
: pv-path! ( c-addr u -- )
  pv-path-chars min dup pv-run pv-run-path# ! pv-run pv-run-path swap chars move ;
\ The run: the record after its output word and busy flag.
: pv-the-run ( -- addr u ) pv-run pv-run-design /pv-run 0 pv-run-design - ;

\ A new context types each line; lf-verify-to chooses another output word.
: pv-type-line ( c-addr u -- ) type cr ;
: pv-setup ( -- ) ['] pv-type-line pv-emit-xt ! ;
' pv-setup context-setup
: lf-verify-to ( xt -- ) pv-emit-xt ! ;

\ The current token, as an offset in characters into the line being run;
\ none (-1) for a diagnostic without one, whose column is then 0.
: pv-no-token ( -- ) -1 pv-token ! 0 pv-token# ! ;
: pv-chars-in ( c-addr -- offset ) pv-text drop - 1 chars / ;
: pv-token! ( c-addr u -- ) pv-token# ! pv-chars-in pv-token ! ;
: pv-offset! ( offset -- ) pv-token ! 0 pv-token# ! ;
: pv-column ( -- column ) pv-token @ 1+ 0 max ;
: pv-here ( -- line column ) pv-line# @ pv-column ;
: pv-token-text ( -- c-addr u )
  pv-token @ 0< if s" " exit then pv-text drop pv-token @ chars + pv-token# @ ;

\ The output line under construction, sent through the output word. An
\ output word that throws, or that leaves the stack at another depth,
\ fails the run as invalid ("output word failed"), the exception caught.
: pv-room ( -- u ) pv-out-chars pv-out# @ - ;
: pv-copy ( c-addr u -- ) pv-out pv-out# @ chars + swap dup pv-out# +! chars move ;
: pv-clipped ( c-addr u -- ) pv-room min pv-copy ;
: pv-output-failed ( -- )
  outcome-invalid pv-outcome ! pv-why-output pv-reason ! pv-throw throw ;
: pv-call-out ( c-addr u -- code ) pv-emit-xt @ catch dup if nip nip then ;
: pv-emit ( c-addr u -- )
  depth >r pv-call-out depth r> 1- <> or if pv-output-failed then ;
: pv-send ( -- ) pv-out pv-out# @ 0 pv-out# ! pv-emit ;

\ Numbers are written in decimal whatever BASE is.
: pv-decimal ( n -- c-addr u ) base @ >r decimal dup abs 0 <# #s rot sign #> r> base ! ;

\ The diagnostic: the first refusal is recorded with where it happened
\ and written as one line, its pieces clipped to the line; later ones are
\ ignored. pv-fail stops the run there, quoting the current token;
\ pv-fail-here the same without the token.
: pv-at ( line column -- )
  s"  @" pv-clipped swap pv-decimal pv-clipped s" :" pv-clipped pv-decimal pv-clipped ;
: pv-quote ( c-addr u -- ) dup if s" : " pv-clipped pv-clipped else 2drop then ;
: pv-diagnostic ( c-addr u -- )
  0 pv-out# ! pv-outcome @ outcome-text pv-clipped pv-where @ lfa-pos> pv-at
  s" : " pv-clipped pv-reason @ lf-verify-message pv-clipped pv-quote pv-send ;
: pv-record ( reason -- )
  dup pv-reason-outcome pv-outcome ! pv-reason ! pv-here lfa-pos pv-where ! ;
: pv-report ( c-addr u reason -- )
  pv-outcome @ ok? if pv-record pv-diagnostic else drop 2drop then ;
: pv-stop ( -- ) pv-throw throw ;
: pv-fail ( reason -- ) >r pv-token-text r> pv-report pv-stop ;
: pv-fail-here ( reason -- ) >r s" " r> pv-report pv-stop ;
\ The same when the flag is true.
: pv-?fail ( flag reason -- ) swap if pv-fail then drop ;
: pv-?fail-here ( flag reason -- ) swap if pv-fail-here then drop ;

\ Pieces of an IR line. Text that would not fit stops the run as full.
: pv-append ( c-addr u -- ) dup pv-room > pv-why-capacity pv-?fail pv-copy ;
: pv-number ( n -- ) pv-decimal pv-append ;
: pv-location ( line column -- )
  s"  @" pv-append swap pv-number s" :" pv-append pv-number ;
: pv-done ( -- ) pv-here pv-location pv-send ;
: pv-done-at ( pos -- ) lfa-pos> pv-location pv-send ;
\ Two spaces per level: level 1 for a definition's top instructions.
create pv-blanks pv-indent-chars chars allot  pv-blanks pv-indent-chars blank
: pv-indent ( level -- ) 2* pv-blanks swap pv-append ;
