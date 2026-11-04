\ The runner of correctness mode (ADR 0019 §3), shared by both designs. It
\ reads a source file as bytes, a block at a time and with no limit on its
\ size, as today's reader does; splits it into lines at LF (one CR just
\ before an LF dropped); refuses any character other than printable ASCII,
\ a space or a tab, and lines of 128 characters or more, as soon as a line
\ grows that long, so a file without LF is not read to its end; and hands
\ each line to the design's line word, which runs it through Forth's text
\ interpreter (EVALUATE) with the design's word lists alone in the search
\ order. Lines are therefore Forth's input source, one at a time: no
\ construct can reach the next line. Text in memory is split the same way.
\
\ Around the run it saves the caller's search order, compilation word
\ list and BASE (src/lib/text-run.fs) and gives them back however the run
\ ends; BASE is ten throughout. It refuses to start while Forth compiles
\ (an immediate word calling it would otherwise compile the file into its
\ caller), and a search order deeper than src/lib/text-run.fs can keep
\ (full); after every line it requires STATE zero and the data stack as
\ deep as before. It CATCHes every THROW: a diagnostic's (pv-throw) ends
\ the run with its outcome; any other THROW goes to the design, which
\ names the token at fault, or ends the run as invalid ("read stopped by
\ an exception"). A run is the authoring program's top level (ADR 0018):
\ nothing passes on to the caller but the outcome, and the file is closed.
\ The lines written go to the output word at the end, the version line
\ first (verify-report.fs).
\
\ Untrusted. State: one context record, pv-flow, and those of
\ verify-report.fs and verify-semantics.fs. A run in progress makes its
\ context busy: starting another run in it (from the output word) aborts
\ (THROW -2) and changes nothing.

require ../lib/lib.fs
require ../lib/text-run.fs
require ./verify-report.fs
require ./verify-semantics.fs

512 constant pv-block-chars      \ characters read from a file at a time
10 constant pv-lf
begin-structure /pv-flow
  field: pv-flow-rest            \ text not run yet: address
  field: pv-flow-rest#           \ and length
  field: pv-flow-reading         \ true: the run reads the file named by the path
  field: pv-flow-file            \ that file once open, or 0
  field: pv-flow-at              \ the next character of the block
  field: pv-flow-got             \ characters in the block
  field: pv-flow-held            \ characters of the current line, counted past the buffer
  field: pv-flow-floor           \ data-stack depth when a line began
  field: pv-flow-floats          \ floating-point stack depth when the run began
  field: pv-flow-saved           \ true once the caller's settings are kept
  /run-settings +field pv-flow-settings   \ the caller's
  pv-block-chars chars aligned +field pv-flow-block
  pv-line-chars chars aligned +field pv-flow-line
end-structure
/pv-flow context-record: pv-flow

: pv-rest ( -- c-addr u ) pv-flow dup pv-flow-rest @ swap pv-flow-rest# @ ;
: pv-rest! ( c-addr u -- ) pv-flow tuck pv-flow-rest# ! pv-flow-rest ! ;
: pv-reading ( -- addr ) pv-flow pv-flow-reading ;
: pv-fid ( -- addr ) pv-flow pv-flow-file ;
: pv-block-at ( -- addr ) pv-flow pv-flow-at ;
: pv-got ( -- addr ) pv-flow pv-flow-got ;
: pv-held ( -- addr ) pv-flow pv-flow-held ;
: pv-floor ( -- addr ) pv-flow pv-flow-floor ;
: pv-saved ( -- addr ) pv-flow pv-flow-saved ;
: pv-settings ( -- settings ) pv-flow pv-flow-settings ;
: pv-block ( -- c-addr ) pv-flow pv-flow-block ;
: pv-held-text ( -- c-addr ) pv-flow pv-flow-line ;

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

\ Lines of text: the next line of the rest, without its LF and the CR
\ before it; false when the text has ended.
: pv-split ( -- c-addr n lf? )
  pv-rest 2dup text-line-end >r >r over r@ 2swap r> 1+ over min /string pv-rest! r> ;
: pv-text-line? ( -- c-addr u true | false )
  pv-rest nip 0= if false exit then pv-split if text-cr-drop then true ;

\ Lines of a file, read a block at a time. A read error stops the run as
\ unreadable, at the line before the one being read; a line that has
\ grown past the line buffer is too long, whatever follows, and is
\ refused at once, at its own line. A last line without LF is read too,
\ and keeps a CR at its end, which is then refused as a character.
: pv-unreadable ( -- ) pv-no-token pv-why-unreadable pv-fail-here ;
: pv-refill ( -- )
  pv-block pv-block-chars pv-fid @ read-file if drop pv-unreadable then
  pv-got ! 0 pv-block-at ! ;
: pv-unread? ( -- flag ) pv-block-at @ pv-got @ < ;
: pv-take-char ( -- char ) pv-block-at @ chars pv-block + c@ 1 pv-block-at +! ;
: pv-next-char ( -- char true | false )
  pv-unread? 0= if pv-refill then pv-unread? if pv-take-char true else false then ;
: pv-too-long ( -- ) 1 pv-line# +! pv-unreadable ;
: pv-hold ( char -- )
  pv-held @ dup pv-line-chars < if chars pv-held-text + c! else 2drop pv-too-long then
  1 pv-held +! ;
: pv-line-char ( char -- lf? ) dup pv-lf = if drop true else pv-hold false then ;
: pv-held-line ( -- c-addr u ) pv-held-text pv-held @ ;
: pv-last-line? ( -- c-addr u true | false )
  pv-held-line dup if true else 2drop false then ;
\ Characters up to an LF, held: true when an LF ended them, false when the
\ file did.
: pv-read-to-lf ( -- lf? )
  begin pv-next-char 0= if false exit then pv-line-char until true ;
: pv-file-line? ( -- c-addr u true | false )
  0 pv-held ! pv-read-to-lf if pv-held-line text-cr-drop true else pv-last-line? then ;
: pv-next-line? ( -- c-addr u true | false )
  pv-reading @ if pv-file-line? else pv-text-line? then ;

\ A line too long, or with a character outside plain text, is refused
\ before it runs. The floor is the data stack's depth while the design's
\ line word runs; after it, STATE must be zero and the stack as deep.
: pv-long? ( u -- flag ) pv-line-chars < 0= ;
: pv-odd-at ( -- offset flag ) pv-text text-plain-at dup pv-text nip < ;
: pv-plain ( -- ) pv-odd-at if pv-offset! pv-why-character pv-fail-here then drop ;
: pv-line-after ( -- )
  pv-no-token state @ pv-why-compiling pv-?fail-here
  depth pv-floor @ <> pv-why-interrupted pv-?fail-here ;
: pv-one-line ( c-addr u -- )
  dup pv-long? if 2drop pv-why-unreadable pv-fail-here then pv-load-line pv-plain
  pv-design@ pv-design-line @ depth 1- pv-floor ! execute pv-line-after ;
: pv-lines ( -- )
  begin pv-next-line? while 1 pv-line# +! pv-no-token pv-one-line repeat pv-end-of-text ;

\ The header's second line, as the IR 0.1 reader writes it (the version
\ line comes first when the lines are sent): a path too long for its line
\ stops the run as full, quoting it.
: pv-header ( -- )
  s" source " pv-append
  pv-path dup pv-room > if pv-why-capacity pv-report pv-stop then pv-copy pv-send ;
: pv-not-compiling ( -- ) state @ pv-why-compiling pv-?fail-here ;
\ The caller's settings, kept unless its search order is too deep.
: pv-save ( -- )
  pv-settings run-settings-save dup pv-saved ! 0= pv-why-capacity pv-?fail-here ;
: pv-isolate ( -- ) pv-design@ pv-design-order @ execute decimal ;
\ A file is opened as a binary file, so that no host translates its line
\ ends; one that cannot be opened is unreadable.
: pv-open-file ( -- )
  pv-reading @ if pv-path r/o bin open-file if drop pv-unreadable then pv-fid ! then ;
: pv-work ( -- ) pv-header pv-not-compiling pv-save pv-open-file pv-isolate pv-lines ;

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
: pv-claim ( -- )
  pv-busy @ abort" lf-verify: a run is under way in this context" true pv-busy ! ;
: pv-new-run ( c-addr u design -- )
  pv-the-run erase pv-design ! pv-flow /pv-flow erase pv-floats! pv-state-reset
  pv-path! pv-prefix! pv-no-token outcome-ok pv-outcome ! ;
: pv-prepare ( c-addr u design -- )
  pv-claim ['] pv-new-run catch ?dup if false pv-busy ! throw then ;
: pv-close-file ( -- ) pv-fid @ ?dup if close-file drop then 0 pv-fid ! ;
\ The lines go to the output word once the caller's settings are back and
\ the file is closed, while the run is still under way; an exception
\ there that is no diagnostic counts as the output word failing.
: pv-deliver ( -- )
  ['] pv-flush catch dup pv-settled? if drop exit then
  drop outcome-invalid pv-outcome ! pv-why-output pv-reason ! ;
: pv-finish ( -- )
  pv-close-file pv-saved @ if pv-settings run-settings-restore then pv-floats-clear
  pv-deliver pv-written-free false pv-busy !
  pv-outcome @ ok? if pv-line# @ 0 lfa-pos pv-where ! then ;
: pv-go ( -- outcome ) ['] pv-work catch pv-caught pv-finish pv-outcome @ ;

\ Running text or a file in a design; the public words of verify.fs and
\ verify-alias.fs. Text is lines separated by LF, named c-addr2 u2 in the
\ header; it must stay unchanged during the run.
: pv-text-run ( c-addr u c-addr2 u2 design -- outcome ) pv-prepare pv-rest! pv-go ;
: pv-file-run ( c-addr u design -- outcome ) pv-prepare true pv-reading ! pv-go ;

\ For tests and callers: why the last run stopped, and where.
: lf-verify-reason ( -- reason ) pv-reason @ ;
: lf-verify-where ( -- line column ) pv-where @ lfa-pos> ;
