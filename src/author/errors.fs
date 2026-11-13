\ Authoring errors (ADR 0017 §10): a stable code, the position and text of
\ the token being acted on, and sometimes a second position the message
\ refers to (where a binder was opened, where a constant was written).
\ docs/programming/LEANFORTH_WORDS.md is the catalogue; tests pin the
\ codes, never the wording. A LeanForth word that finds a mistake calls
\ lfa-fail, which records the error and THROWs lf-author-throw; only the
\ runner (runner.fs) catches it, as the authoring program's top level
\ (ADR 0018), and turns it into an outcome. Untrusted authoring code: an
\ error stops the authoring run; it never reaches the checker.
\ State: one context record, lfa-error; the catalogue is a shared,
\ read-only table.

require ../lib/lib.fs
require ./source.fs

\ The THROW code of an authoring error, in the range ADR 0018 reserves for
\ LeanForth (proposed there as -4129).
-4129 constant lf-author-throw

\ Codes. Each has an outcome (ADR 0008): invalid for a mistake in the
\ text, unsupported for a form the term store cannot hold yet, full for a
\ store or table that ran out of room.
1 constant lfa-e-unknown         \ no word, variable, universe or constant has the name
2 constant lfa-e-no-name         \ a name must follow on the same line
3 constant lfa-e-missing         \ a value is missing above the binder or declaration
4 constant lfa-e-outside         \ terms belong inside a declaration
5 constant lfa-e-not-term        \ a universe level where a term is needed
6 constant lfa-e-not-level       \ a term where a universe level is needed
7 constant lfa-e-universe-term   \ a universe parameter where a term is needed
8 constant lfa-e-not-universe    \ a variable where a universe parameter is needed
9 constant lfa-e-not-constant    \ ^ after something that is not a constant
10 constant lfa-e-many-levels    \ more than 8 universe arguments
11 constant lfa-e-arity          \ wrong number of universe arguments
12 constant lfa-e-body           \ a binder's body is not exactly one term
13 constant lfa-e-no-binder      \ fun or forall with no binder of this term open
14 constant lfa-e-nested         \ a declaration inside a declaration
15 constant lfa-e-not-empty      \ values on the stack before a declaration
16 constant lfa-e-universe-late  \ universe after a binder or a term
17 constant lfa-e-define-here    \ := where it is not expected
18 constant lfa-e-statement      \ the statement is not exactly one term
19 constant lfa-e-no-define      \ := is missing
20 constant lfa-e-proof          \ the proof is not exactly one term
21 constant lfa-e-open-binder    \ a binder of the proof is still open
22 constant lfa-e-end-name       \ end names another declaration or namespace
23 constant lfa-e-no-namespace   \ end names no open namespace
24 constant lfa-e-namespace-here \ namespace or open inside a declaration
25 constant lfa-e-namespaces     \ too many namespaces open
26 constant lfa-e-unknown-space  \ open names no known namespace
27 constant lfa-e-ambiguous      \ a short name found in two places
28 constant lfa-e-declared       \ a constant or universe declared twice
29 constant lfa-e-label-twice    \ a label used twice in one declaration
30 constant lfa-e-bad-name       \ not a name: number-like, an empty part, a leading zero
31 constant lfa-e-var-index      \ var# outside the binders
32 constant lfa-e-count          \ a count (a number) is needed
33 constant lfa-e-unfinished     \ the text ends inside a declaration
34 constant lfa-e-not-value      \ a cell that is no live, unused LeanForth value
35 constant lfa-e-not-word       \ a number-like token that is no plain decimal
36 constant lfa-e-interpreter    \ a name word not run by the text interpreter
37 constant lfa-e-note-end       \ a note without its closing " on the line
38 constant lfa-e-unknown-constant \ root: names no constant
39 constant lfa-e-line           \ a line longer than the runner's buffer
40 constant lfa-e-file           \ the file cannot be opened or read
41 constant lfa-e-forth          \ another Forth exception
42 constant lfa-e-comment-end    \ a ( comment without its closing ) on the line
43 constant lfa-e-protected-here \ protected not right before a declaration word
44 constant lfa-e-protected-root \ a protected declaration outside every namespace
45 constant lfa-e-compiling      \ a run started, or a line ended, while Forth compiles
46 constant lfa-e-character      \ a character no line may hold
47 constant lfa-e-search-order   \ the caller's search order is too long to save
48 constant lfa-e-stub-checked   \ import-stub in a checked run
49 constant lfa-e-nothing        \ a checked text that declares nothing
50 constant lfa-e-literal        \ unsupported: natural-number literals
51 constant lfa-e-sketch
  \ unsupported: let, have, projections, strings, by, import
52 constant lfa-e-hole           \ unsupported: holes are for the elaborator
53 constant lfa-e-root-name      \ unsupported: _root_ in a declaration's name
54 constant lfa-e-export         \ unsupported: export and its aliases
55 constant lfa-e-library-short  \ unsupported: a short name of a library constant
56 constant lfa-e-leaf           \ a projection leaf anywhere but before $
57 constant lfa-e-form-here      \ kernel-form inside a declaration
58 constant lfa-e-natural-only   \ a word of natural LeanForth in kernel-form text
59 constant lfa-e-tick           \ ' not followed by a name
60 constant lfa-e-terms-full     \ the term store is full
61 constant lfa-e-levels-full    \ the level store or a level is too large
62 constant lfa-e-names-full     \ the name store is full, or a name too long
63 constant lfa-e-references-full \ the constant-reference store is full
64 constant lfa-e-values-full    \ too many values in one declaration
65 constant lfa-e-binders-full   \ too many binders open
66 constant lfa-e-entries-full   \ too many names, namespaces or declarations
67 constant lfa-e-notes-full     \ too many labels and notes
68 constant lfa-e-syntax-full    \ the syntax store is full
69 constant lfa-e-by-here        \ by not right after :=
70 constant lfa-e-natural-later  \ unsupported: the word's natural form (plan FE2)
71 constant lfa-e-elaborate      \ unsupported: elaborating natural text (plan FE1e-f)
72 constant lfa-e-tactic         \ unsupported: tactics (plan FE1g)
73 constant lfa-e-arity-unknown  \ unsupported: arguments that depend on unfolding (FE1c)
74 constant lfa-e-incomplete     \ a hole is left in the elaborated declaration (FE1f)
75 constant lfa-e-unused-universe \ a universe parameter nothing uses (FE1f)
76 constant lfa-e-malformed      \ the elaborator's terms are malformed (FE1f)
77 constant lfa-e-instantiate    \ unsupported: an instantiation step (FE1c)

\ The catalogue: one message record per code, in order, each followed by
\ its text and aligned; a record with code 0 closes it.
begin-structure /lfa-message
  field: lfa-message-code
  field: lfa-message-outcome
  field: lfa-message-length
  0 +field lfa-message-chars
end-structure
: lfa-message, ( code outcome c-addr u -- )
  2swap swap , , dup , here swap dup chars allot move align ;
: lfa-message-text ( message -- c-addr u )
  dup lfa-message-chars swap lfa-message-length @ ;
: lfa-message-next ( message -- message' ) lfa-message-text chars + aligned ;
: lfa-invalid, ( code c-addr u -- ) outcome-invalid -rot lfa-message, ;
: lfa-unsupported, ( code c-addr u -- ) outcome-unsupported -rot lfa-message, ;
: lfa-full, ( code c-addr u -- ) outcome-full -rot lfa-message, ;
create lfa-catalogue
  lfa-e-unknown
  s" unknown name: no syntax word, bound variable, universe parameter or constant has it"
  lfa-invalid,
  lfa-e-no-name s" a name must follow on the same line" lfa-invalid,
  lfa-e-missing
  s" missing value: this word would use the stack below its binder or declaration"
  lfa-invalid,
  lfa-e-outside s" terms belong inside a declaration" lfa-invalid,
  lfa-e-not-term s" a term is needed here, not a universe level" lfa-invalid,
  lfa-e-not-level s" a universe level is needed here, not a term" lfa-invalid,
  lfa-e-universe-term
  s" a universe parameter is not a term (write root: NAME for a constant)" lfa-invalid,
  lfa-e-not-universe s" a universe parameter is needed here, not a variable" lfa-invalid,
  lfa-e-not-constant s" universe arguments attach only to a constant" lfa-invalid,
  lfa-e-many-levels s" too many universe arguments (at most 8)" lfa-invalid,
  lfa-e-arity
  s" wrong number of universe arguments for the constant (write each with ^)" lfa-invalid,
  lfa-e-body s" the body of the binder must be exactly one term" lfa-invalid,
  lfa-e-no-binder s" no binder of this term is open here" lfa-invalid,
  lfa-e-nested s" declarations do not nest" lfa-invalid,
  lfa-e-not-empty s" a declaration starts with an empty stack" lfa-invalid,
  lfa-e-universe-late s" universe comes right after the declaration's name" lfa-invalid,
  lfa-e-define-here s" := is not expected here" lfa-invalid,
  lfa-e-statement s" the statement before := must be exactly one term" lfa-invalid,
  lfa-e-no-define s" := is missing" lfa-invalid,
  lfa-e-proof s" the proof after := must be exactly one term" lfa-invalid,
  lfa-e-open-binder s" a binder of the proof is still open" lfa-invalid,
  lfa-e-end-name s" end names another declaration or namespace" lfa-invalid,
  lfa-e-no-namespace s" end names no open namespace" lfa-invalid,
  lfa-e-namespace-here s" namespace and open belong outside declarations" lfa-invalid,
  lfa-e-namespaces s" too many namespaces open" lfa-full,
  lfa-e-unknown-space s" unknown namespace" lfa-invalid,
  lfa-e-ambiguous s" ambiguous name: write the full name" lfa-invalid,
  lfa-e-declared s" already declared" lfa-invalid,
  lfa-e-label-twice s" label used twice in this declaration" lfa-invalid,
  lfa-e-bad-name s" not a name: an empty part, a part like a number, or a leading zero"
  lfa-invalid,
  lfa-e-var-index s" var# index outside the binders" lfa-invalid,
  lfa-e-count s" a count (a number) is needed here" lfa-invalid,
  lfa-e-unfinished s" the text ends inside a declaration or with values left" lfa-invalid,
  lfa-e-not-value s" not a live LeanForth value: each value is used once" lfa-invalid,
  lfa-e-not-word
  s" not a LeanForth word or number: numbers are plain decimals of at most 9 digits"
  lfa-invalid,
  lfa-e-interpreter s" a LeanForth word must be run by the text interpreter" lfa-invalid,
  lfa-e-note-end s\" a note must end with \" on the same line" lfa-invalid,
  lfa-e-unknown-constant s" unknown constant" lfa-invalid,
  lfa-e-line s" line too long" lfa-full,
  lfa-e-file s" the file cannot be opened or read" lfa-invalid,
  lfa-e-forth s" a Forth exception, with its THROW code" lfa-invalid,
  lfa-e-comment-end s" a ( comment must end with ) on the same line" lfa-invalid,
  lfa-e-protected-here
  s" protected comes right before theorem, def, axiom or import-stub" lfa-invalid,
  lfa-e-protected-root s" protected declarations must be in a namespace" lfa-invalid,
  lfa-e-compiling
  s" LeanForth text runs only while Forth interprets, never while it compiles"
  lfa-invalid,
  lfa-e-character
  s" a character no line may hold (a control or format character, or no UTF-8)"
  lfa-invalid,
  lfa-e-search-order
  s" out of room: the search order holds more wordlists than a run can save" lfa-full,
  lfa-e-stub-checked
  s" import-stub is never checked: name the library with --env and use its constant"
  lfa-invalid,
  lfa-e-nothing s" nothing to check: the text declares no theorem, definition or axiom"
  lfa-invalid,
  lfa-e-literal
  s" not supported yet: natural-number literals need literal nodes (ADR 0017 section 14)"
  lfa-unsupported,
  lfa-e-sketch
  s" not supported yet: designed in ADR 0017 but not built yet"
  lfa-unsupported,
  lfa-e-hole s" not supported yet: holes are filled by the elaborator (plan task 8.3.1)"
  lfa-unsupported,
  lfa-e-root-name s" not supported yet: _root_ in a declaration's name" lfa-unsupported,
  lfa-e-export s" not supported yet: export and the aliases it makes" lfa-unsupported,
  lfa-e-library-short
  s" not supported yet: a library constant by a short name; write the full name"
  lfa-unsupported,
  lfa-e-leaf s" a projection leaf is no term: apply it with $ to the term it projects"
  lfa-invalid,
  lfa-e-form-here s" kernel-form belongs outside declarations" lfa-invalid,
  lfa-e-natural-only
  s" a word of natural LeanForth: the text is in the kernel form (kernel-form)"
  lfa-invalid,
  lfa-e-tick s" ' takes the name right after it on the same line" lfa-invalid,
  lfa-e-terms-full s" out of room: the term store is full" lfa-full,
  lfa-e-levels-full s" out of room: the level store is full or the level too large"
    lfa-full,
  lfa-e-names-full s" out of room: the name store is full or the name too long" lfa-full,
  lfa-e-references-full s" out of room: the constant-reference store is full" lfa-full,
  lfa-e-values-full s" out of room: too many values in one declaration" lfa-full,
  lfa-e-binders-full s" out of room: too many binders open" lfa-full,
  lfa-e-entries-full s" out of room: too many names, namespaces or declarations" lfa-full,
  lfa-e-notes-full s" out of room: too many labels and notes" lfa-full,
  lfa-e-syntax-full s" out of room: the syntax store is full" lfa-full,
  lfa-e-by-here s" by comes right after := and before the proof" lfa-invalid,
  lfa-e-natural-later
  s" not supported yet in natural LeanForth (plan FE2); write kernel-form first"
  lfa-unsupported,
  lfa-e-elaborate
  s" not supported yet: elaborating natural LeanForth (plan FE1e-f)" lfa-unsupported,
  lfa-e-tactic s" not supported yet: tactics (plan FE1g)" lfa-unsupported,
  lfa-e-arity-unknown
  s" not supported yet: how many arguments the name takes depends on unfolding its type"
  lfa-unsupported,
  lfa-e-incomplete
  s" elaboration incomplete: a hole (metavariable) is left in the declaration"
  lfa-invalid,
  lfa-e-unused-universe
  s" unused universe parameter: the statement (or a definition's value) must use it"
  lfa-invalid,
  lfa-e-malformed
  s" malformed elaboration: a term that is no node, or a value unfit for the declaration"
  lfa-invalid,
  lfa-e-instantiate
  s" not supported yet: this step of instantiating metavariables (plan FE1c)"
  lfa-unsupported,
  0 outcome-invalid s" " lfa-message,

\ The catalogue record of a code; an unknown code gives the closing record.
: lfa-last? ( message -- flag ) lfa-message-code @ 0= ;
: lfa-message-of ( code -- message )
  lfa-catalogue begin dup lfa-last? 0= while 2dup lfa-message-code @ <> while
    lfa-message-next repeat then nip ;
: lf-author-message ( code -- c-addr u ) lfa-message-of lfa-message-text ;
: lf-author-outcome ( code -- outcome ) lfa-message-of lfa-message-outcome @ ;

\ The error record: the first error of a run.
64 constant lfa-token-keep
begin-structure /lfa-err
  field: lfa-err-code        \ 0 while no error is recorded
  field: lfa-err-at          \ position of the token
  field: lfa-err-see         \ a second position, or -1
  field: lfa-err-number      \ a number the code defines (a Forth THROW code), or 0
  field: lfa-err-length      \ characters of the token kept
  lfa-token-keep +field lfa-err-token
end-structure
/lfa-err context-record: lfa-error

: lfa-error-reset ( -- ) lfa-error /lfa-err erase -1 lfa-error lfa-err-see ! ;
: lf-author-code ( -- code ) lfa-error lfa-err-code @ ;
\ Record an error at position pos with token c-addr u, unless one is
\ recorded already.
: lfa-keep-token ( c-addr u -- )
  lfa-token-keep min dup lfa-error lfa-err-length ! lfa-error lfa-err-token swap move ;
: lfa-record ( c-addr u pos code -- )
  lf-author-code if 2drop 2drop exit then
  lfa-error tuck lfa-err-code ! lfa-err-at ! lfa-keep-token ;
\ A second position for the message, and a number.
: lfa-see! ( pos -- ) lfa-error lfa-err-see ! ;
: lfa-number! ( n -- ) lfa-error lfa-err-number ! ;

\ Stop the run with an error at the current token: lfa-fail; with a second
\ position: lfa-fail-see; lfa-must stops unless the flag is true.
: lfa-fail ( code -- ) >r lfa-token lfa-here r> lfa-record lf-author-throw throw ;
\ The same with a token and position of the caller's.
: lfa-fail-at ( c-addr u pos code -- ) lfa-record lf-author-throw throw ;
: lfa-fail-see ( pos code -- ) swap lfa-see! lfa-fail ;
: lfa-must ( flag code -- ) swap if drop else lfa-fail then ;

\ The error as a line of text: error CODE at line:col L:C (token `T`):
\ MESSAGE, then ; see line:col L:C when there is a second position, and
\ the number for a Forth exception.
: lfa-.n ( n -- ) base @ >r decimal 0 .r r> base ! ;
: lfa-.pos ( pos -- ) ." line:col " lfa-pos> swap lfa-.n ." :" lfa-.n ;
: lfa-.token ( -- ) ."  (token `" lfa-error lfa-err-token lfa-error lfa-err-length @ type
  ." `)" ;
: lfa-.see ( -- ) lfa-error lfa-err-see @ dup 0< if drop exit then ." ; see " lfa-.pos ;
: lfa-.number ( -- ) lf-author-code lfa-e-forth = if ."  " lfa-error lfa-err-number @
  lfa-.n then ;
: lf-author-error. ( -- )
  lf-author-code 0= if ." no error" exit then
  ." error " lf-author-code lfa-.n ."  at " lfa-error lfa-err-at @ lfa-.pos lfa-.token
  ." : " lf-author-code lf-author-message type lfa-.number lfa-.see ;
