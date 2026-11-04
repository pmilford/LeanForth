\ The runner of correctness mode (ADR 0019 §3), shared by both designs: it
\ reads a source file once, whole, as bytes (at most 65,536 of them),
\ splits it into lines at LF (one CR just before an LF dropped), refuses
\ any character other than printable ASCII, a space or a tab, and lines of
\ 128 characters or more, exactly as today's reader does, and hands each
\ line to the design's line word, which runs it through Forth's text
\ interpreter (EVALUATE) with the design's word lists alone in the search
\ order. Lines are therefore Forth's input source, one at a time: no
\ construct can reach the next line.
\
\ Around the run it saves the caller's search order, compilation word
\ list and BASE (src/lib/text-run.fs) and gives them back however the run
\ ends; BASE is ten throughout. It refuses to start while Forth compiles
\ (an immediate word calling it would otherwise compile the file into its
\ caller), and after every line requires STATE zero and the data stack as
\ deep as before. It CATCHes every THROW: a diagnostic's (pv-throw) ends
\ the run with its outcome; any other THROW goes to the design, which
\ names the token at fault, or ends the run as invalid ("read stopped by
\ an exception"). A run is the authoring program's top level (ADR 0018):
\ nothing passes on to the caller but the outcome.
\
\ A design is a record of four execution tokens: its entry text (put
\ before each line, for the mode shift's entry word), its search order,
\ its line word and its handler of other THROWs.
\
\ Untrusted. State: one context record, pv-flow, and those of
\ verify-report.fs and verify-semantics.fs. A run in progress makes its
\ context busy: starting another run in it (from the output word) aborts.

require ../lib/lib.fs
require ../lib/text-run.fs
require ./verify-report.fs
require ./verify-semantics.fs

\ A design: pv-design: takes four execution tokens and lays them down in
\ this order, the last given first.
begin-structure /pv-design
  field: pv-design-caught        \ ( code -- ) after a THROW that is no diagnostic
  field: pv-design-line          \ ( -- ) run the line in pv-source
  field: pv-design-order         \ ( -- ) set the run's search order
  field: pv-design-prefix        \ ( -- c-addr u ) text before each line
end-structure
: pv-design: ( prefix order line caught "name" -- ) create , , , , ;

65536 constant pv-file-chars     \ largest source file
begin-structure /pv-flow
  field: pv-flow-rest            \ text not run yet: address
  field: pv-flow-rest#           \ and length
  field: pv-flow-file            \ true: the run reads the file named by the path
  field: pv-flow-cut             \ true: the file is larger than pv-file-chars
  field: pv-flow-buffer          \ its heap buffer, or 0
  field: pv-flow-floor           \ data-stack depth when a line began
  field: pv-flow-floats          \ floating-point stack depth when the run began
  /run-settings +field pv-flow-settings   \ the caller's
end-structure
/pv-flow context-record: pv-flow

: pv-rest ( -- c-addr u ) pv-flow dup pv-flow-rest @ swap pv-flow-rest# @ ;
: pv-rest! ( c-addr u -- ) pv-flow tuck pv-flow-rest# ! pv-flow-rest ! ;
: pv-file? ( -- addr ) pv-flow pv-flow-file ;
: pv-cut ( -- addr ) pv-flow pv-flow-cut ;
: pv-buffer ( -- addr ) pv-flow pv-flow-buffer ;
: pv-floor ( -- addr ) pv-flow pv-flow-floor ;
: pv-settings ( -- settings ) pv-flow pv-flow-settings ;
: pv-design@ ( -- design ) pv-design @ ;

\ Floating-point numbers that a host's interpreter may push are dropped.
[defined] fdepth [if]
: pv-floats! ( -- ) fdepth pv-flow pv-flow-floats ! ;
: pv-floats-clear ( -- ) begin fdepth pv-flow pv-flow-floats @ > while fdrop repeat ;
: pv-floats? ( -- flag ) fdepth pv-flow pv-flow-floats @ = ;
[else]
: pv-floats! ( -- ) ;
: pv-floats-clear ( -- ) ;
: pv-floats? ( -- true ) true ;
[then]

\ The line in the source buffer, after the design's entry text, and what
\ the design's line word hands to EVALUATE.
: pv-prefix! ( -- )
  pv-design@ pv-design-prefix @ execute dup pv-prefix-chars > abort" pv: entry too long"
  dup pv-prefix# ! pv-source swap chars move ;
: pv-load-line ( c-addr u -- )
  pv-source pv-prefix# @ chars + swap 2dup pv-text! chars move ;
: pv-evaluated ( -- c-addr u ) pv-source pv-prefix# @ pv-text nip + ;

\ Lines. A line too long, or with a character outside plain text, is
\ refused before it runs; one that a file too large cut short, too.
: pv-split ( -- c-addr n lf? )
  pv-rest 2dup text-line-end >r >r over r@ 2swap r> 1+ over min /string pv-rest! r> ;
: pv-cut-short ( c-addr u -- c-addr u )
  dup pv-line-chars < pv-cut @ and if pv-why-capacity pv-fail-here then ;
: pv-next-line ( -- c-addr u ) pv-split if text-cr-drop else pv-cut-short then ;
: pv-long? ( u -- flag ) pv-line-chars < 0= ;
: pv-plain ( -- ) pv-text text-plain-at dup pv-text nip < if pv-offset! pv-why-character
  pv-fail-here then drop ;
: pv-line-after ( -- )
  pv-no-token state @ if pv-why-compiling pv-fail-here then
  depth pv-floor @ <> if pv-why-interrupted pv-fail-here then ;
: pv-one-line ( c-addr u -- )
  dup pv-long? if 2drop pv-why-unreadable pv-fail-here then pv-load-line pv-plain
  pv-design@ pv-design-line @ depth 1- pv-floor ! execute pv-line-after ;
: pv-lines ( -- )
  begin pv-rest nip while 1 pv-line# +! pv-no-token pv-next-line pv-one-line repeat
  pv-end-of-text ;

\ The source: a file is read whole into a heap buffer, one character
\ larger than the largest file, so that a file that fills it is known to
\ be too large; text is run where it is.
: pv-heap ( -- )
  pv-file-chars 1+ allocate if drop pv-why-capacity pv-fail-here then pv-buffer ! ;
: pv-read-file ( -- )
  pv-path pv-buffer @ pv-file-chars 1+ file-slurp
  if drop pv-why-unreadable pv-fail-here then
  dup pv-file-chars > pv-cut ! pv-file-chars min pv-buffer @ swap pv-rest! ;
: pv-source-text ( -- ) pv-file? @ if pv-heap pv-read-file then ;
: pv-free ( -- ) pv-buffer @ ?dup if free drop then 0 pv-buffer ! ;

\ The header, as today's reader writes it: a path too long for its line
\ stops the run as full, quoting it.
: pv-header ( -- )
  s" lf-ir 0.1" pv-append pv-send s" source " pv-append
  pv-path dup pv-room > if pv-why-capacity pv-report pv-stop then pv-copy pv-send ;
: pv-not-compiling ( -- ) state @ if pv-why-compiling pv-fail-here then ;
: pv-isolate ( -- ) pv-design@ pv-design-order @ execute decimal ;
: pv-work ( -- ) pv-header pv-not-compiling pv-source-text pv-isolate pv-lines ;

\ After a THROW that is no diagnostic: the design's handler, which may
\ record one; if it cannot, the run stopped by an exception.
: pv-settled? ( code -- flag ) dup 0= swap pv-throw = or ;
: pv-try ( code xt -- code' ) catch dup if nip then ;
: pv-interrupted ( code -- ) drop pv-no-token pv-why-interrupted pv-fail-here ;
: pv-design-handles ( code -- ) pv-design@ pv-design-caught @ execute ;
: pv-caught ( code -- )
  dup pv-settled? if drop exit then ['] pv-design-handles pv-try
  dup pv-settled? if drop exit then ['] pv-interrupted pv-try drop ;

\ A run. pv-prepare claims the context, erases the last run and keeps the
\ path; pv-go runs and gives the outcome. Where a run that ends ok
\ stopped: its last line, column 0.
: pv-claim ( -- ) pv-busy @ abort" lf-verify: a run is under way in this context"
  true pv-busy ! ;
: pv-path! ( c-addr u -- ) pv-path-chars min dup pv-run pv-run-path# ! pv-run pv-run-path
  swap chars move ;
: pv-prepare ( c-addr u design -- )
  pv-claim pv-the-run erase pv-design ! pv-flow /pv-flow erase pv-floats! pv-state-reset
  pv-path! pv-prefix! pv-no-token outcome-ok pv-outcome ! ;
: pv-finish ( -- )
  pv-free pv-settings run-settings-restore pv-floats-clear false pv-busy !
  pv-outcome @ ok? if pv-line# @ 0 lfa-pos pv-where ! then ;
: pv-go ( -- outcome )
  pv-settings run-settings-save ['] pv-work catch pv-caught pv-finish pv-outcome @ ;

\ Running text or a file in a design; the public words of verify.fs and
\ verify-alias.fs. Text is lines separated by LF, named c-addr2 u2 in the
\ header; it must stay unchanged during the run.
: pv-text-run ( c-addr u c-addr2 u2 design -- outcome ) pv-prepare pv-rest! pv-go ;
: pv-file-run ( c-addr u design -- outcome ) pv-prepare true pv-file? ! pv-go ;

\ For tests and callers: why the last run stopped, and where.
: lf-verify-reason ( -- reason ) pv-reason @ ;
: lf-verify-where ( -- line column ) pv-where @ lfa-pos> ;
