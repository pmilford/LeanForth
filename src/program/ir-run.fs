\ Interpreter of the program IR, version 0.1 (docs/programming/PROGRAM_IR.md).
\ It loads the IR's text form, as the reader src/program/ir-reader.fs and
\ the Lean printer write it, and runs a word with the semantics of
\ ProgramIR.run in tests/reference/program-ir.lean on host cells: wrapping
\ arithmetic, separate data and return stacks, a called word with a return
\ stack of its own that it must leave empty, a constant run on empty
\ stacks, the model's explicit failures, and one unit of fuel spent by each
\ call and each loop iteration. Untrusted: it proves nothing. Tests compare
\ it with the host's own execution of the source and with Lean's
\ evaluation of the model (docs/programming/PROGRAM_IR_RUN.md).
\
\ Host assumptions: cells are two's complement and +, -, NEGATE, 1+ and 1-
\ wrap (src/lib/portability.fs). * keeps the low cell of the exact product
\ (UM* DROP). / and MOD run only where the model defines them (dividend at
\ least 0, divisor above 0, where floored and symmetric division agree) and
\ RSHIFT only for a count below the cell width; everywhere else they give
\ the model's failure unmodeled, never a host result.
\
\ Outcomes (src/lib/outcome.fs). Loading: ok; invalid for text that is not
\ the IR 0.1 text form (including a name defined twice); full when a
\ capacity below is reached. A literal beyond the host's cells loads and,
\ as in the model, runs as the failure unmodeled.
\ Running: ok when the word returns normally; exhausted when it runs out of
\ fuel; unsupported for the failure unmodeled; invalid for underflow, an
\ unbalanced return stack, an unknown word or a bad constant, and for a run
\ without a loaded program or with negative fuel; full when the stacks or
\ frames below run out of room, which the model, having no limits, never
\ does. irx-result tells which of the model's results ended the run.
\
\ State: one context record, irx-state (the loaded program, the machine's
\ stacks and the frames of a run); and the stores irx-keywords and
\ irx-prims and the dispatch tables irx-actions, irx-body-actions,
\ irx-top-actions and irx-modes, all filled while this file loads and never
\ changed afterwards. One load or run at a time in each context. A program loaded
\ in one context can be run only there.

require ../lib/lib.fs
decimal

\ What running a block gives: the model's results and failures (Result and
\ Failure in program-ir.lean), and two of this interpreter's own.
0 constant irx-going         \ internal: go on with the next instruction
1 constant irx-next          \ the block ran to its end
2 constant irx-exited        \ the block ran EXIT
3 constant irx-underflow     \ a data or return-stack item was missing
4 constant irx-unmodeled     \ an operation the model gives no meaning
5 constant irx-unbalanced    \ a word returned with return-stack items
6 constant irx-unknown-word  \ a call to a name the program does not define
7 constant irx-bad-constant  \ a constant did not leave exactly one value
8 constant irx-out-of-fuel   \ a call or loop iteration with no fuel left
9 constant irx-no-room       \ beyond the capacities below; never a model result
10 constant irx-broken       \ a marker reached: the code is corrupted

\ Capacities.
512 constant irx-code-capacity    \ instructions in a program
64 constant irx-def-capacity      \ definitions, with names only called
31 constant irx-name-limit        \ longest name
16 constant irx-open-capacity     \ IF and BEGIN open while loading
3 constant irx-token-capacity     \ tokens on a line, with its location
128 constant irx-line-chars       \ lines of a file must be shorter
128 constant irx-data-capacity    \ data-stack cells
32 constant irx-return-capacity   \ return-stack cells
64 constant irx-frame-capacity    \ blocks and calls nested in a run

\ Named text: the keywords, the primitives and the definitions start with it.
32 constant irx-text-room
begin-structure /irx-text
  field: irx-text-length
  irx-text-room chars +field irx-text-body
end-structure

: irx-text@ ( text -- c-addr u ) dup irx-text-body swap irx-text-length @ ;
: irx-text= ( c-addr u text -- flag ) irx-text@ compare 0= ;
\ The caller has checked that u fits.
: irx-text! ( c-addr u text -- ) 2dup irx-text-length ! irx-text-body swap chars move ;

\ The index of the first record of a store whose text is c-addr u.
: irx-at? ( c-addr u store i -- c-addr u store flag )
  over store-slot 2over rot irx-text= ;
: irx-find ( c-addr u store -- index true | false )
  dup store-count @ 0 ?do i irx-at? if drop 2drop i true unloop exit then loop
  drop 2drop false ;

\ Keywords of the text form; an instruction's kind is its keyword's index.
13 /irx-text 0 store: irx-keywords
: irx-keyword ( c-addr u -- )
  irx-keywords store-new-slot 0= abort" irx: keywords" drop irx-text! ;
0 constant irx-k-prim    s" prim" irx-keyword
1 constant irx-k-lit     s" lit" irx-keyword
2 constant irx-k-call    s" call" irx-keyword
3 constant irx-k-if      s" if" irx-keyword
4 constant irx-k-else    s" else" irx-keyword
5 constant irx-k-then    s" then" irx-keyword
6 constant irx-k-begin   s" begin" irx-keyword
7 constant irx-k-while   s" while" irx-keyword
8 constant irx-k-repeat  s" repeat" irx-keyword
9 constant irx-k-exit    s" exit" irx-keyword
10 constant irx-k-word   s" word" irx-keyword
11 constant irx-k-constant s" constant" irx-keyword
12 constant irx-k-end    s" end" irx-keyword
10 constant irx-op-kinds  \ the first ten are instructions

\ Primitives: the host word that does the work, the data items it takes and
\ leaves, and for >R, R> and R@ the return-stack items. Inputs leave the
\ machine's stacks for the host's data stack in stack order, data items
\ first; the outputs come back, return items from the top. A partial
\ primitive has a domain word ( x1..xn -- x1..xn flag ).
begin-structure /irx-prim
  /irx-text +field irx-prim-name  \ first, so that irx-find searches the table
  field: irx-prim-in
  field: irx-prim-out
  field: irx-prim-rin
  field: irx-prim-rout
  field: irx-prim-action
  field: irx-prim-domain        \ 0 for a primitive defined everywhere
end-structure
38 /irx-prim 0 store: irx-prims
: irx-row ( c-addr u -- prim )
  irx-prims store-new-slot 0= abort" irx: primitives" drop
  dup >r irx-prim-name irx-text! r> ;
: irx-effect! ( xt in out prim -- )
  tuck irx-prim-out ! tuck irx-prim-in ! irx-prim-action ! ;
\ One row of the table: the host word, its data items in and out, the name.
: irx-prim, ( xt in out c-addr u -- ) irx-row irx-effect! ;
: irx-last-row ( -- prim ) irx-prims store-count @ 1- irx-prims store-slot ;
: irx-returns ( rin rout -- ) irx-last-row tuck irx-prim-rout ! irx-prim-rin ! ;
: irx-partial ( xt -- ) irx-last-row irx-prim-domain ! ;

\ The cell width, counted, for RSHIFT's domain.
: irx-bits ( -- u ) 0 -1 begin dup while 1 rshift swap 1+ swap repeat drop ;
irx-bits constant irx-cell-bits

: irx-noop ( -- ) ;
: irx-times ( n1 n2 -- n3 ) um* drop ;
: irx-abs ( n -- n' ) dup 0< if negate then ;
: irx-divisible? ( n1 n2 -- n1 n2 flag ) over 0< 0= over 0> and ;
: irx-shiftable? ( x u -- x u flag ) dup 0< 0= over irx-cell-bits < and ;

\ The 38 primitives of IR 0.1, in the order of Prim in program-ir.lean.
' dup 1 2 s" dup" irx-prim,      ' drop 1 0 s" drop" irx-prim,
' swap 2 2 s" swap" irx-prim,    ' over 2 3 s" over" irx-prim,
' nip 2 1 s" nip" irx-prim,      ' tuck 2 3 s" tuck" irx-prim,
' rot 3 3 s" rot" irx-prim,      ' 2dup 2 4 s" 2dup" irx-prim,
' 2drop 2 0 s" 2drop" irx-prim,
' irx-noop 1 0 s" >r" irx-prim,  0 1 irx-returns
' irx-noop 0 1 s" r>" irx-prim,  1 0 irx-returns
' dup 0 1 s" r@" irx-prim,       1 1 irx-returns
' + 2 1 s" +" irx-prim,          ' - 2 1 s" -" irx-prim,
' irx-times 2 1 s" *" irx-prim,
' / 2 1 s" /" irx-prim,          ' irx-divisible? irx-partial
' mod 2 1 s" mod" irx-prim,      ' irx-divisible? irx-partial
' negate 1 1 s" negate" irx-prim,  ' irx-abs 1 1 s" abs" irx-prim,
' 1+ 1 1 s" 1+" irx-prim,        ' 1- 1 1 s" 1-" irx-prim,
' = 2 1 s" =" irx-prim,          ' <> 2 1 s" <>" irx-prim,
' < 2 1 s" <" irx-prim,          ' > 2 1 s" >" irx-prim,
' 0= 1 1 s" 0=" irx-prim,        ' 0<> 1 1 s" 0<>" irx-prim,
' 0< 1 1 s" 0<" irx-prim,        ' 0> 1 1 s" 0>" irx-prim,
' and 2 1 s" and" irx-prim,      ' or 2 1 s" or" irx-prim,
' xor 2 1 s" xor" irx-prim,      ' invert 1 1 s" invert" irx-prim,
' rshift 2 1 s" rshift" irx-prim,  ' irx-shiftable? irx-partial
' max 2 1 s" max" irx-prim,      ' min 2 1 s" min" irx-prim,
' true 0 1 s" true" irx-prim,    ' false 0 1 s" false" irx-prim,
irx-prims store-count @ 38 <> [if] .( irx: primitive table ) abort [then]

\ Definitions. A name that is called before it is defined, or never,
\ stays undefined; calling it is the failure unknown word.
0 constant irx-kind-undefined
1 constant irx-kind-word
2 constant irx-kind-constant
begin-structure /irx-def
  /irx-text +field irx-def-name
  field: irx-def-kind
  field: irx-def-start      \ first instruction of the body
  field: irx-def-end        \ the body ends before this index
end-structure

\ The irx-op-end of a literal that does not fit in a cell (others: -1).
1 constant irx-unfit

\ Instructions, in a store in text order: the body of IF is the
\ instructions up to its ELSE (or THEN), the ELSE part those after ELSE up
\ to THEN; likewise BEGIN's test and WHILE's body. The markers ELSE, THEN,
\ WHILE and REPEAT are never run.
begin-structure /irx-op
  field: irx-op-kind      \ a keyword index below irx-op-kinds
  \ The primitive's or definition's index, or the literal; IF and BEGIN:
  \ the index of ELSE or WHILE (or THEN), -1 while open.
  field: irx-op-arg
  field: irx-op-end       \ IF and BEGIN: index of THEN or REPEAT
  field: irx-op-line      \ the line's location, 0 0 when it has none
  field: irx-op-column
end-structure

\ A block being run: the next instruction, where the block ends, its fuel,
\ and how much of each stack belongs to its callers.
begin-structure /irx-frame
  field: irx-frame-ip
  field: irx-frame-end
  field: irx-frame-fuel
  field: irx-frame-data       \ data items below this index belong to callers
  field: irx-frame-returns    \ return items below this index belong to callers
end-structure

\ What a line of the text form may be: the version line, the source line,
\ a definition's header, or a line inside a definition.
0 constant irx-m-version
1 constant irx-m-source
2 constant irx-m-top
3 constant irx-m-body

begin-structure /irx-state
  field: irx-s-outcome     \ of the load: ok until the first problem
  field: irx-s-loaded      \ true once a load finished with ok
  field: irx-s-lines       \ lines read
  field: irx-s-mode
  field: irx-s-current     \ the definition being read, or -1
  field: irx-s-open#
  irx-open-capacity cells +field irx-s-open
  field: irx-s-indent      \ of the line being read
  field: irx-s-tokens#
  irx-token-capacity 2* cells +field irx-s-tokens
  field: irx-s-at-line     \ its location, 0 0 when it has none
  field: irx-s-at-column
  irx-line-chars 2 + chars aligned +field irx-s-text
  irx-code-capacity /irx-op store-size +field irx-s-code
  irx-def-capacity /irx-def store-size +field irx-s-defs
  field: irx-s-sp
  irx-data-capacity cells +field irx-s-data
  field: irx-s-rp
  irx-return-capacity cells +field irx-s-returns
  field: irx-s-frames#
  irx-frame-capacity /irx-frame * +field irx-s-frames
  field: irx-s-result      \ how the last run ended
  field: irx-s-last        \ the instruction it started last, or -1
end-structure
/irx-state context-record: irx-state

\ Accessors.
: irx-code ( -- store ) irx-state irx-s-code ;
: irx-defs ( -- store ) irx-state irx-s-defs ;
: irx-op ( index -- op ) irx-code store-slot ;
: irx-def ( index -- def ) irx-defs store-slot ;
: irx-here ( -- index ) irx-code store-count @ ;
: irx-mode! ( mode -- ) irx-state irx-s-mode ! ;
: irx-current ( -- addr ) irx-state irx-s-current ;
: irx-open# ( -- addr ) irx-state irx-s-open# ;
: irx-tokens# ( -- addr ) irx-state irx-s-tokens# ;
: irx-token-cell ( i -- addr ) 2* cells irx-state irx-s-tokens + ;
: irx-token ( i -- c-addr u ) irx-token-cell 2@ ;
: irx-kind@ ( index -- kind )
  dup 0< if drop irx-kind-undefined else irx-def irx-def-kind @ then ;

\ Loading stops at the first problem; later lines are skipped.
: irx-loading? ( -- flag ) irx-state irx-s-outcome @ ok? ;
: irx-stop ( outcome -- ) irx-loading? if irx-state irx-s-outcome ! else drop then ;
: irx-malformed ( -- ) outcome-invalid irx-stop ;
: irx-full ( -- ) outcome-full irx-stop ;

\ Splitting a line: its indentation, then tokens separated by one space.
: irx-space? ( c-addr u -- flag ) 1 min s"  " compare 0= ;
: irx-indent ( c-addr u -- c-addr' u' n )
  0 >r begin 2dup irx-space? while 1 /string r> 1+ >r repeat r> ;
\ The first token and the rest, which starts at the space after it.
: irx-split ( c-addr u -- rest-addr rest-u token-addr token-u )
  2dup s"  " search if 2swap 2 pick - exit then 2drop 2dup chars + 0 2swap ;
: irx-keep ( c-addr u -- )
  dup 0= irx-tokens# @ irx-token-capacity = or if 2drop irx-malformed exit then
  irx-tokens# @ irx-token-cell 2! 1 irx-tokens# +! ;

\ Numbers: decimal digits at the start of c-addr u, read exactly up to 19.
: irx-convert ( c-addr u -- ud c-addr' u' )
  0 0 2swap base @ >r decimal >number r> base ! ;
: irx-count ( c-addr u -- n c-addr' u' flag ) dup >r irx-convert rot drop dup r> < ;
: irx-colon? ( c-addr u -- c-addr' u' flag )
  2dup 1 min s" :" compare if false else 1 /string true then ;
\ A location "@line:column".
: irx-location ( c-addr u -- line column flag )
  1 /string irx-count >r irx-colon? r> and >r irx-count r> and >r nip 0= r> and ;
: irx-where! ( line column -- ) irx-state tuck irx-s-at-column ! irx-s-at-line ! ;
: irx-at-sign? ( c-addr u -- flag ) 1 min s" @" compare 0= ;
: irx-locate ( -- )
  0 0 irx-where! irx-tokens# @ 0= if exit then
  irx-tokens# @ 1- irx-token 2dup irx-at-sign? 0= if 2drop exit then
  irx-location if irx-where! -1 irx-tokens# +! else 2drop irx-malformed then ;
: irx-tokenize ( c-addr u -- )
  irx-indent irx-state irx-s-indent ! 0 irx-tokens# !
  dup if irx-split irx-keep then begin dup while 1 /string irx-split irx-keep repeat
  2drop irx-locate ;

\ A literal: an optional minus sign and digits; other text is malformed.
\ The model gives a literal outside the cell no meaning, so one that does
\ not fit a host cell loads as unfit and runs as the failure unmodeled. Up
\ to 19 digits are read exactly on every host; more never fit a cell of at
\ most 64 bits.
: irx-sign ( c-addr u -- c-addr' u' negative? )
  2dup 1 min s" -" compare 0= dup if >r 1 /string r> then ;
: irx-digits? ( c-addr u -- flag )
  dup if irx-convert nip nip nip 0= else 2drop false then ;
\ The largest magnitude that fits, unsigned: max-n 1+ is the smallest cell's.
: irx-limit ( negative? -- u ) if max-n 1+ else max-n then ;
: irx-fits? ( ud negative? -- flag ) irx-limit rot u< 0= swap 0= and ;
: irx-signed ( u negative? -- n ) if negate then ;
: irx-magnitude ( c-addr u negative? -- n fits? )
  over 19 > if drop 2drop 0 false exit then
  >r irx-convert 2drop 2dup r@ irx-fits? nip swap r> irx-signed swap ;
: irx-literal ( c-addr u -- n fits? true | false )
  irx-sign >r 2dup irx-digits? 0= if 2drop r> drop irx-malformed false exit then
  r> irx-magnitude true ;

\ Names. A definition's header names a fresh or only-called name.
: irx-new-name ( c-addr u -- index true | false )
  irx-defs store-new-slot if >r irx-def-name irx-text! r> true exit then
  2drop irx-full false ;
: irx-name ( c-addr u -- index true | false )
  dup irx-name-limit > if 2drop irx-full false exit then
  2dup irx-defs irx-find if nip nip true else irx-new-name then ;

\ Shapes: the number of tokens (besides the location) and the indentation.
: irx-shape? ( tokens indent -- flag )
  irx-state irx-s-indent @ = swap irx-tokens# @ = and ;
: irx-checked ( flag -- flag ) dup 0= if irx-malformed then ;
: irx-plain? ( tokens -- flag ) irx-open# @ 1+ 2* irx-shape? irx-checked ;
: irx-outer? ( tokens -- flag ) irx-open# @ 2* irx-shape? ;

\ Appending an instruction, with the line's location.
: irx-located ( op -- )
  >r irx-state irx-s-at-line @ r@ irx-op-line !
  irx-state irx-s-at-column @ r> irx-op-column ! ;
: irx-op! ( kind arg op -- )
  tuck irx-op-arg ! tuck irx-op-kind ! -1 over irx-op-end ! irx-located ;
: irx-add ( kind arg -- index true | false )
  irx-code store-new-slot if >r irx-op! r> true else 2drop irx-full false then ;
: irx-append ( kind arg -- ) irx-add if drop then ;
: irx-unfit! ( index -- ) irx-op irx-unfit swap irx-op-end ! ;
: irx-lit-op ( n fits? -- )
  irx-k-lit rot irx-add if swap if drop else irx-unfit! then else drop then ;

\ IF and BEGIN open while loading.
: irx-top ( -- addr ) irx-open# @ 1- cells irx-state irx-s-open + ;
: irx-top-op ( -- op ) irx-top @ irx-op ;
: irx-push-open ( index -- )
  irx-open# @ irx-open-capacity = if drop irx-full exit then 1 irx-open# +! irx-top ! ;
: irx-top-kind? ( kind -- flag )
  irx-open# @ if irx-top-op irx-op-kind @ = else drop false then ;
: irx-middle-seen? ( -- flag ) irx-top-op irx-op-arg @ -1 <> ;
\ ELSE after IF, WHILE after BEGIN, at the level of their opener.
: irx-middle? ( opener -- flag )
  irx-top-kind? if irx-middle-seen? 0= else false then 1 irx-outer? and ;
: irx-middle ( opener kind -- )
  swap irx-middle? 0= if drop irx-malformed exit then
  0 irx-add if irx-top-op irx-op-arg ! then ;
\ THEN and REPEAT close the structure; an IF without ELSE ends at THEN.
: irx-close? ( opener -- flag ) irx-top-kind? 1 irx-outer? and ;
: irx-shut ( index -- )
  irx-top-op 2dup irx-op-end ! irx-op-arg dup @ -1 = if ! else 2drop then
  -1 irx-open# +! ;
: irx-closing ( kind flag -- )
  if 0 irx-add if irx-shut then else drop irx-malformed then ;

\ Lines inside a definition ( -- ), indexed by keyword.
: irx-body-prim ( -- )
  2 irx-plain? if 1 irx-token irx-prims irx-find
    if irx-k-prim swap irx-append else irx-malformed then then ;
: irx-body-lit ( -- ) 2 irx-plain? if 1 irx-token irx-literal if irx-lit-op then then ;
: irx-body-call ( -- )
  2 irx-plain? if 1 irx-token irx-name if irx-k-call swap irx-append then then ;
: irx-opening ( kind -- )
  1 irx-plain? if -1 irx-add if irx-push-open then else drop then ;
: irx-body-if ( -- ) irx-k-if irx-opening ;
: irx-body-begin ( -- ) irx-k-begin irx-opening ;
: irx-body-else ( -- ) irx-k-if irx-k-else irx-middle ;
: irx-body-while ( -- ) irx-k-begin irx-k-while irx-middle ;
: irx-body-then ( -- ) irx-k-then irx-k-if irx-close? irx-closing ;
: irx-body-repeat ( -- )
  irx-k-repeat irx-k-begin irx-close? if irx-middle-seen? else false then irx-closing ;
: irx-body-exit ( -- ) 1 irx-plain? if irx-k-exit 0 irx-append then ;
: irx-body-end ( -- )
  irx-open# @ 0= 1 0 irx-shape? and irx-checked 0= if exit then
  irx-here irx-current @ irx-def irx-def-end ! -1 irx-current ! irx-m-top irx-mode! ;
create irx-body-actions
  ' irx-body-prim , ' irx-body-lit , ' irx-body-call , ' irx-body-if , ' irx-body-else ,
  ' irx-body-then , ' irx-body-begin , ' irx-body-while , ' irx-body-repeat ,
  ' irx-body-exit , ' irx-malformed , ' irx-malformed , ' irx-body-end ,

\ A definition's header: "word name" or "constant name" at the left edge.
: irx-fresh ( index -- index true | false )
  dup irx-kind@ irx-kind-undefined = if true else drop irx-malformed false then ;
: irx-new-def ( -- index true | false )
  2 0 irx-shape? irx-checked 0= if false exit then
  1 irx-token irx-name if irx-fresh else false then ;
: irx-open-def ( kind index -- )
  tuck irx-def irx-def-kind ! irx-here over irx-def irx-def-start ! irx-current !
  irx-m-body irx-mode! ;
: irx-define ( kind -- ) irx-new-def if irx-open-def else drop then ;
: irx-top-word ( -- ) irx-kind-word irx-define ;
: irx-top-constant ( -- ) irx-kind-constant irx-define ;
create irx-top-actions
  ' irx-malformed , ' irx-malformed , ' irx-malformed , ' irx-malformed ,
  ' irx-malformed ,
  ' irx-malformed , ' irx-malformed , ' irx-malformed , ' irx-malformed ,
  ' irx-malformed , ' irx-top-word , ' irx-top-constant , ' irx-malformed ,

\ One line, in the current mode.
: irx-kind ( -- kind true | false )
  irx-tokens# @ if 0 irx-token irx-keywords irx-find else false then ;
: irx-act ( table -- ) irx-kind if cells + @ execute else drop irx-malformed then ;
: irx-statement ( c-addr u table -- )
  >r irx-tokenize irx-loading? if r> irx-act else r> drop then ;
: irx-version-line ( c-addr u -- )
  s" lf-ir 0.1" compare if irx-malformed else irx-m-source irx-mode! then ;
: irx-source-line ( c-addr u -- )
  dup 7 > >r 7 min s" source " compare 0= r> and irx-checked if irx-m-top irx-mode! then ;
: irx-top-line ( c-addr u -- ) irx-top-actions irx-statement ;
: irx-body-line ( c-addr u -- ) irx-body-actions irx-statement ;
create irx-modes
  ' irx-version-line , ' irx-source-line , ' irx-top-line , ' irx-body-line ,

\ Loading. irx-load-start forgets any program; lines then come one at a
\ time (irx-load-line, which suits the reader's output word) or from a
\ file (irx-load-file), and irx-load-finish gives the outcome.
: irx-load-start ( -- )
  irx-state /irx-state erase -1 irx-current !
  irx-code-capacity /irx-op 0 irx-code store-init 0= abort" irx: code store"
  irx-def-capacity /irx-def 0 irx-defs store-init 0= abort" irx: definition store" ;
: irx-load-line ( c-addr u -- )
  irx-loading? 0= if 2drop exit then 1 irx-state irx-s-lines +!
  irx-state irx-s-mode @ cells irx-modes + @ execute ;
: irx-load-finish ( -- outcome )
  irx-state irx-s-mode @ irx-m-top <> if irx-malformed then
  irx-loading? irx-state irx-s-loaded ! irx-state irx-s-outcome @ ;
\ Lines read so far: after a failed load, the line that stopped it.
: irx-load-lines ( -- n ) irx-state irx-s-lines @ ;

\ A file, line by line; a line of irx-line-chars or more is malformed.
: irx-text ( -- c-addr ) irx-state irx-s-text ;
: irx-fetch ( fileid -- u true | false )
  >r irx-text irx-line-chars r> read-line if 2drop irx-malformed false exit then
  0= if drop false else true then ;
: irx-line ( u -- )
  dup irx-line-chars < if irx-text swap irx-load-line else drop irx-malformed then ;
: irx-more? ( fileid -- flag ) irx-fetch if irx-line irx-loading? else false then ;
: irx-load-file ( c-addr u -- outcome )
  irx-load-start r/o open-file if drop irx-malformed else
    begin dup irx-more? 0= until close-file drop then irx-load-finish ;

\ The machine: data and return stacks of cells, and the frames of a run.
: irx-sp ( -- addr ) irx-state irx-s-sp ;
: irx-rp ( -- addr ) irx-state irx-s-rp ;
: irx-cell ( i -- addr ) cells irx-state irx-s-data + ;
: irx-rcell ( i -- addr ) cells irx-state irx-s-returns + ;
: irx-frames# ( -- addr ) irx-state irx-s-frames# ;
: irx-frame ( -- frame ) irx-frames# @ 1- /irx-frame * irx-state irx-s-frames + ;
: irx-ip ( -- addr ) irx-frame irx-frame-ip ;
: irx-fuel ( -- addr ) irx-frame irx-frame-fuel ;
\ Items the current block may use: those above its frame's bases.
: irx-items ( -- n ) irx-sp @ irx-frame irx-frame-data @ - ;
: irx-ritems ( -- n ) irx-rp @ irx-frame irx-frame-returns @ - ;

\ Moving n items between a machine stack and the host's data stack, in
\ stack order. The caller has checked depth and room.
: irx-take ( n -- x1..xn )
  dup negate irx-sp +! irx-sp @ swap 0 ?do dup i + irx-cell @ swap loop drop ;
: irx-give ( x1..xn n -- )
  dup irx-sp +! irx-sp @ swap 0 ?do 1- tuck irx-cell ! loop drop ;
: irx-rtake ( n -- x1..xn )
  dup negate irx-rp +! irx-rp @ swap 0 ?do dup i + irx-rcell @ swap loop drop ;
: irx-rgive ( x1..xn n -- )
  dup irx-rp +! irx-rp @ swap 0 ?do 1- tuck irx-rcell ! loop drop ;

\ A primitive: underflow when its inputs are missing, no room when its
\ outputs would not fit, unmodeled outside its domain.
: irx-short? ( prim -- flag )
  dup irx-prim-in @ irx-items > swap irx-prim-rin @ irx-ritems > or ;
: irx-rises ( prim -- data returns )
  dup irx-prim-out @ over irx-prim-in @ - swap dup irx-prim-rout @ swap irx-prim-rin @ - ;
: irx-crowded? ( prim -- flag )
  irx-rises irx-rp @ + irx-return-capacity > swap irx-sp @ + irx-data-capacity > or ;
: irx-inputs ( prim -- x1..xn r1..rk )
  dup irx-prim-in @ swap irx-prim-rin @ >r irx-take r> irx-rtake ;
: irx-in-domain? ( x... prim -- x... flag )
  irx-prim-domain @ ?dup if execute else true then ;
: irx-outputs ( y... prim -- )
  dup irx-prim-rout @ swap irx-prim-out @ >r irx-rgive r> irx-give ;
: irx-discard ( x... prim -- ) dup irx-prim-in @ swap irx-prim-rin @ + 0 ?do drop loop ;
: irx-apply ( prim -- result )
  >r r@ irx-inputs r@ irx-in-domain? 0= if r> irx-discard irx-unmodeled exit then
  r@ irx-prim-action @ execute r> irx-outputs irx-going ;
: irx-prim ( index -- result )
  irx-prims store-slot dup irx-short? if drop irx-underflow exit then
  dup irx-crowded? if drop irx-no-room exit then irx-apply ;
: irx-lit ( n -- result )
  irx-sp @ irx-data-capacity < if 1 irx-give irx-going else drop irx-no-room then ;

\ Frames. A new block starts with its parent's bases (none at the root).
: irx-bases ( -- data returns )
  irx-frames# @ if irx-frame dup irx-frame-data @ swap irx-frame-returns @ else 0 0 then ;
: irx-frame-bases! ( data returns frame -- ) tuck irx-frame-returns ! irx-frame-data ! ;
: irx-frame-block! ( start end fuel frame -- )
  tuck irx-frame-fuel ! tuck irx-frame-end ! irx-frame-ip ! ;
: irx-enter ( start end fuel -- flag )
  irx-frames# @ irx-frame-capacity = if 2drop drop false exit then
  irx-bases 1 irx-frames# +! irx-frame irx-frame-bases! irx-frame irx-frame-block! true ;
: irx-leave ( -- ) -1 irx-frames# +! ;

\ Running a block: one instruction after another, through irx-actions
\ (filled below), until the end, EXIT or a failure.
create irx-actions irx-op-kinds cells allot
: irx-done? ( -- flag ) irx-ip @ irx-frame irx-frame-end @ < 0= ;
: irx-dispatch ( op -- result )
  dup irx-op-kind @ dup 0 irx-op-kinds within if cells irx-actions + @ execute
  else 2drop irx-broken then ;
: irx-step ( -- result )
  irx-ip @ dup irx-state irx-s-last ! dup 1+ irx-ip ! irx-op irx-dispatch ;
: irx-steps ( -- result )
  begin irx-done? if irx-next exit then irx-step dup irx-going = while drop repeat ;
: irx-block ( start end fuel -- result )
  irx-enter if irx-steps irx-leave else irx-no-room then ;

\ Calls. A word runs on its caller's data stack with a return stack of its
\ own, which it must leave empty; a constant runs on empty stacks and must
\ leave one value. The callee gets one unit of fuel less than its caller.
: irx-def-block ( def -- start end ) irx-def dup irx-def-start @ swap irx-def-end @ ;
: irx-own-returns ( -- ) irx-rp @ irx-frame irx-frame-returns ! ;
: irx-own-stacks ( -- ) irx-sp @ irx-frame irx-frame-data ! irx-own-returns ;
: irx-ended? ( result -- flag ) dup irx-next = swap irx-exited = or ;
: irx-returned ( result -- result )
  dup irx-ended? if drop irx-ritems if irx-unbalanced else irx-next then then ;
: irx-one-value? ( -- flag ) irx-items 1 = irx-ritems 0= and ;
: irx-valued ( result -- result )
  dup irx-next = if drop irx-one-value? if irx-next else irx-bad-constant then exit then
  dup irx-exited = if drop irx-bad-constant then ;
: irx-run-word ( def fuel -- result )
  >r irx-def-block r> irx-enter 0= if irx-no-room exit then
  irx-own-returns irx-steps irx-returned irx-leave ;
: irx-run-constant ( def fuel -- result )
  >r irx-def-block r> irx-enter 0= if irx-no-room exit then
  irx-own-stacks irx-steps irx-valued irx-leave ;
: irx-callee ( def fuel -- result )
  over irx-kind@ case
    irx-kind-word of irx-run-word endof
    irx-kind-constant of irx-run-constant endof
    >r 2drop irx-unknown-word r> endcase ;
: irx-call ( def -- result )
  irx-fuel @ dup 0= if 2drop irx-out-of-fuel exit then 1- irx-callee ;

\ IF: pop a flag; nonzero runs the IF part, zero the ELSE part, with the
\ same fuel; after it, the block goes on past THEN.
: irx-flag ( -- x true | false ) irx-items if 1 irx-take true else false then ;
: irx-branch ( op x -- start end )
  if irx-ip @ swap irx-op-arg @ else dup irx-op-arg @ 1+ swap irx-op-end @ then ;
: irx-past ( op result -- result )
  dup irx-next = if drop irx-op-end @ 1+ irx-ip ! irx-going else nip then ;
: irx-do-if ( op -- result )
  irx-flag 0= if drop irx-underflow exit then
  over swap irx-branch irx-fuel @ irx-block irx-past ;

\ BEGIN test WHILE body REPEAT: each iteration needs fuel; the test and
\ body run with the block's fuel, and a completed body spends one unit of
\ it, so the rest of the block after REPEAT runs with what is left.
: irx-test-block ( op -- start end ) irx-ip @ swap irx-op-arg @ ;
: irx-body-block ( op -- start end ) dup irx-op-arg @ 1+ swap irx-op-end @ ;
\ After the test: next to run the body, or going once the loop is over.
: irx-tested ( op -- result )
  irx-flag 0= if drop irx-underflow exit then
  if drop irx-next else irx-op-end @ 1+ irx-ip ! irx-going then ;
: irx-loop-test ( op -- result )
  dup irx-test-block irx-fuel @ irx-block
  dup irx-next = if drop irx-tested else nip then ;
: irx-loop-body ( op -- result )
  irx-body-block irx-fuel @ irx-block dup irx-next = if -1 irx-fuel +! then ;
\ One iteration: next to iterate again.
: irx-iterate ( op -- result )
  irx-fuel @ 0= if drop irx-out-of-fuel exit then
  dup irx-loop-test dup irx-next = if drop irx-loop-body else nip then ;
: irx-do-begin ( op -- result )
  begin dup irx-iterate dup irx-next = while drop repeat nip ;

: irx-do-prim ( op -- result ) irx-op-arg @ irx-prim ;
: irx-do-lit ( op -- result )
  dup irx-op-end @ irx-unfit = if drop irx-unmodeled exit then irx-op-arg @ irx-lit ;
\ A callee that returned lets its caller go on.
: irx-do-call ( op -- result )
  irx-op-arg @ irx-call dup irx-next = if drop irx-going then ;
: irx-do-exit ( op -- result ) drop irx-exited ;
: irx-do-marker ( op -- result ) drop irx-broken ;
: irx-action! ( xt kind -- ) cells irx-actions + ! ;
' irx-do-prim irx-k-prim irx-action!      ' irx-do-lit irx-k-lit irx-action!
' irx-do-call irx-k-call irx-action!      ' irx-do-if irx-k-if irx-action!
' irx-do-marker irx-k-else irx-action!    ' irx-do-marker irx-k-then irx-action!
' irx-do-begin irx-k-begin irx-action!    ' irx-do-marker irx-k-while irx-action!
' irx-do-marker irx-k-repeat irx-action!  ' irx-do-exit irx-k-exit irx-action!

\ The outcome of a run's result.
: irx-outcome ( result -- outcome )
  case irx-next of outcome-ok endof
    irx-out-of-fuel of outcome-exhausted endof
    irx-no-room of outcome-full endof
    irx-unmodeled of outcome-unsupported endof
    outcome-invalid swap endcase ;

\ The data stack a run starts from and ends with, bottom first.
: irx-clear ( -- ) 0 irx-sp ! 0 irx-rp ! ;
: irx-push ( x -- outcome )
  irx-sp @ irx-data-capacity < if 1 irx-give outcome-ok else drop outcome-full then ;
: irx-depth ( -- n ) irx-sp @ ;
\ The caller checks 0 <= i < irx-depth.
: irx-item ( i -- x ) irx-cell @ ;

\ Run a word on the data stack, as the model's callWord does: [CALL name]
\ with fuel, from a return stack the word cannot see. The stack holds the
\ result afterwards; after a failure its contents mean nothing.
: irx-lookup ( c-addr u -- def ) irx-defs irx-find 0= if -1 then ;
: irx-runnable? ( fuel -- flag ) 0< 0= irx-state irx-s-loaded @ and ;
: irx-finish ( result -- outcome ) dup irx-state irx-s-result ! irx-outcome ;
: irx-root ( fuel -- ) 0 irx-frames# ! -1 irx-state irx-s-last ! 0 0 rot irx-enter drop ;
: irx-run ( fuel c-addr u -- outcome )
  rot dup irx-runnable? 0= if drop 2drop irx-broken irx-finish exit then
  irx-root irx-lookup irx-call irx-leave irx-finish ;
: irx-result ( -- result ) irx-state irx-s-result @ ;
\ The location of the instruction the last run started last, 0 0 if none.
: irx-last ( -- line column )
  irx-state irx-s-last @ dup 0< if drop 0 0 exit then
  irx-op dup irx-op-line @ swap irx-op-column @ ;
\ The model's name of a result, as the Lean comparisons print it.
: irx-result-text ( result -- c-addr u )
  case irx-next of s" next" endof irx-exited of s" exited" endof
    irx-underflow of s" underflow" endof irx-unmodeled of s" unmodeled" endof
    irx-unbalanced of s" unbalanced" endof irx-unknown-word of s" unknownWord" endof
    irx-bad-constant of s" badConstant" endof irx-out-of-fuel of s" outOfFuel" endof
    irx-no-room of s" full" endof s" broken" rot endcase ;
