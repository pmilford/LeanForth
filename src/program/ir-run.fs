\ Interpreter of the program IR, versions 0.1 and 0.2
\ (docs/programming/PROGRAM_IR.md). It loads the IR's text form, as the
\ program words (src/program/verify.fs), the IR 0.1 reader
\ src/program/ir-reader.fs and the Lean printer write it, and runs a word
\ with the semantics of ProgramIR.run in tests/reference/program-ir.lean on
\ host cells: wrapping arithmetic, separate data and return stacks, a
\ called word with a return stack of its own that it must leave empty, a
\ constant run on empty stacks, the model's explicit failures, and one unit
\ of fuel spent by each call and each loop iteration. Untrusted: it proves
\ nothing. Tests compare it with the host's own execution of the source and
\ with Lean's evaluation of the model (docs/programming/PROGRAM_IR_RUN.md).
\
\ IR 0.2's output words (out lines) take their cells and send what they
\ print, rendered as the model's Event.render says and .S as both Gforths
\ print it, to the context's output sink ( c-addr u -- ), which
\ irx-output-to sets; a new context discards it. Version names (x'1) are
\ names like any other.
\
\ Host assumptions: cells are two's complement and +, -, NEGATE, 1+ and 1-
\ wrap (src/lib/portability.fs). * keeps the low cell of the exact product
\ (UM* DROP). / and MOD run only where the model defines them (dividend at
\ least 0, divisor above 0, where floored and symmetric division agree) and
\ RSHIFT and LSHIFT only for a count below the cell width; everywhere else
\ they give the model's failure unmodeled, never a host result.
\
\ Outcomes (src/lib/outcome.fs). Loading: ok; invalid for text that is not
\ the IR 0.1 or 0.2 text form, including an IR 0.2 instruction under an
\ IR 0.1 version line, a name defined twice, a line of irx-line-chars
\ characters or more, and any line or second finish after irx-load-finish;
\ full when a capacity below is reached. A literal is read as the model's
\ parser reads it, so leading zeros change nothing; one beyond the host's
\ cells loads and, as in the model, runs as the failure unmodeled.
\ Running: ok when the word returns normally; exhausted when it runs out of
\ fuel; unsupported for the failure unmodeled; invalid for underflow, an
\ unbalanced return stack, an unknown word or a bad constant, and for a run
\ without a loaded program or with negative fuel; full when the stacks or
\ frames below run out of room, which the model, having no limits, never
\ does. irx-result tells which of the model's results ended the run.
\
\ State: two context records, irx-state (the loaded program, the machine's
\ stacks and the frames of a run), which irx-clear sets up in every
\ context, and irx-output (the output sink); and the stores irx-results,
\ irx-keywords, irx-prims and irx-outs and the dispatch tables irx-modes,
\ irx-top-actions, irx-body-actions and irx-actions, all filled while this
\ file loads and never changed afterwards. One load or run at a time in
\ each context. A program loaded in one context can be run only there.

require ../lib/lib.fs
decimal

\ Capacities.
512 constant irx-code-capacity    \ instructions in a program
64 constant irx-def-capacity      \ definitions, with names only called
36 constant irx-name-limit        \ longest name: 31 characters, ' and a version
16 constant irx-open-capacity     \ IF and BEGIN open while loading
3 constant irx-token-capacity     \ tokens on a line, with its location
128 constant irx-line-chars       \ lines must be shorter
128 constant irx-data-capacity    \ data-stack cells
32 constant irx-return-capacity   \ return-stack cells
64 constant irx-frame-capacity    \ blocks and calls nested in a run
2048 constant irx-texts-capacity  \ characters of out lines' texts, with their lengths

\ Named text: the rows of the tables below and the definitions start with it.
40 constant irx-text-room
begin-structure /irx-text
  field: irx-text-length
  irx-text-room chars +field irx-text-body
end-structure

: irx-text@ ( text -- c-addr u ) dup irx-text-body swap irx-text-length @ ;
: irx-text= ( c-addr u text -- flag ) irx-text@ compare 0= ;
\ The caller has checked that u fits.
: irx-text! ( c-addr u text -- ) 2dup irx-text-length ! irx-text-body swap chars move ;

\ The index of the first record of a store whose text is c-addr u.
: irx-find ( c-addr u store -- index true | false )
  dup store-count @ 0 ?do i over store-slot 2over rot irx-text=
    if drop 2drop i true unloop exit then loop drop 2drop false ;
\ A new row of a table made while this file loads, with its text.
: irx-new-row ( c-addr u store -- row index )
  store-new-slot 0= abort" irx: table full" >r dup >r irx-text! r> r> ;

\ Dispatch tables of n execution tokens, all xt until set by index.
: irx-table ( xt n "name" -- ) create 0 ?do dup , loop drop ;
: irx-entry! ( xt index table -- ) swap cells + ! ;

\ What running a block gives: the model's results and failures (Result and
\ Failure in program-ir.lean) and two of this interpreter's own, each with
\ its name as the Lean comparison prints it and the outcome of a run that
\ ends with it. The model's names are part of the comparison's interface
\ and outcomes cannot tell its failures apart, so the interpreter keeps
\ these results beside the outcomes. A result is its row's index.
begin-structure /irx-result-row
  /irx-text +field irx-result-name
  field: irx-result-outcome
end-structure
11 /irx-result-row 0 store: irx-results
: irx-result: ( outcome c-addr u "name" -- )
  irx-results irx-new-row >r irx-result-outcome ! r> constant ;
\ Internal: go on with the next instruction.
outcome-invalid s" going" irx-result: irx-going
\ The block ran to its end; the block ran EXIT (the run's own call turns
\ both into next, so a run never ends with exited).
outcome-ok s" next" irx-result: irx-next
outcome-invalid s" exited" irx-result: irx-exited
\ A data or return-stack item was missing.
outcome-invalid s" underflow" irx-result: irx-underflow
\ An operation the model gives no meaning.
outcome-unsupported s" unmodeled" irx-result: irx-unmodeled
\ A word returned with return-stack items.
outcome-invalid s" unbalanced" irx-result: irx-unbalanced
\ A call to a name the program does not define.
outcome-invalid s" unknownWord" irx-result: irx-unknown-word
\ A constant did not leave exactly one value.
outcome-invalid s" badConstant" irx-result: irx-bad-constant
\ A call or loop iteration with no fuel left.
outcome-exhausted s" outOfFuel" irx-result: irx-out-of-fuel
\ Beyond the capacities above; never a model result.
outcome-full s" full" irx-result: irx-no-room
\ A marker reached, so the code is corrupted; or no program to run.
outcome-invalid s" broken" irx-result: irx-broken
\ A result's row; any other value reads as broken.
: irx-result? ( x -- flag ) 0 irx-results store-count @ within ;
: irx-result-row ( result -- row )
  dup irx-result? 0= if drop irx-broken then irx-results store-slot ;
: irx-outcome ( result -- outcome ) irx-result-row irx-result-outcome @ ;
\ The model's name of a result, as the Lean comparisons print it.
: irx-result-text ( result -- c-addr u ) irx-result-row irx-result-name irx-text@ ;

\ Keywords of the text form. Each defines a constant, its index, which is
\ an instruction's kind; the keywords before word are instructions.
14 /irx-text 0 store: irx-keywords
: irx-keyword ( c-addr u "name" -- ) irx-keywords irx-new-row nip constant ;
s" prim" irx-keyword irx-k-prim         s" lit" irx-keyword irx-k-lit
s" call" irx-keyword irx-k-call         s" if" irx-keyword irx-k-if
s" else" irx-keyword irx-k-else         s" then" irx-keyword irx-k-then
s" begin" irx-keyword irx-k-begin       s" while" irx-keyword irx-k-while
s" repeat" irx-keyword irx-k-repeat     s" exit" irx-keyword irx-k-exit
s" out" irx-keyword irx-k-out
s" word" irx-keyword irx-k-word         s" constant" irx-keyword irx-k-constant
s" end" irx-keyword irx-k-end
irx-k-word constant irx-op-kinds
irx-keywords store-count @ constant irx-keyword-count
irx-keyword-count 14 <> [if] .( irx: keyword table ) abort [then]

\ The output words of IR 0.2, as out lines name them; each defines a
\ constant, its index; an out line with a text has the last index.
8 /irx-text 0 store: irx-outs
: irx-out-word ( c-addr u "name" -- ) irx-outs irx-new-row nip constant ;
s" ." irx-out-word irx-o-dot            s" u." irx-out-word irx-o-udot
s" cr" irx-out-word irx-o-cr            s" emit" irx-out-word irx-o-emit
s" space" irx-out-word irx-o-space      s" spaces" irx-out-word irx-o-spaces
s" .s" irx-out-word irx-o-dots
irx-outs store-count @ constant irx-o-text

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
40 /irx-prim 0 store: irx-prims
\ A row of the table: the primitive's name, then what the host does for it
\ (irx-effect!: the host word and its data items in and out), and for some
\ the return-stack items and a domain. Each word fills the last row.
: irx-row ( c-addr u -- ) irx-prims irx-new-row 2drop ;
: irx-last-row ( -- prim ) irx-prims store-count @ 1- irx-prims store-slot ;
: irx-effect! ( xt in out -- )
  irx-last-row tuck irx-prim-out ! tuck irx-prim-in ! irx-prim-action ! ;
: irx-row-returns ( rin rout -- ) irx-last-row tuck irx-prim-rout ! irx-prim-rin ! ;
: irx-partial ( xt -- ) irx-last-row irx-prim-domain ! ;

\ The cell width, counted, for RSHIFT's domain.
: irx-bits ( -- u ) 0 -1 begin dup while 1 rshift swap 1+ swap repeat drop ;
irx-bits constant irx-cell-bits

: irx-noop ( -- ) ;
: irx-times ( n1 n2 -- n3 ) um* drop ;
: irx-abs ( n -- n' ) dup 0< if negate then ;
: irx-divisible? ( n1 n2 -- n1 n2 flag ) over 0< 0= over 0> and ;
: irx-shiftable? ( x u -- x u flag ) dup 0< 0= over irx-cell-bits < and ;

\ The 40 primitives of IR 0.2, in the order of Prim in program-ir.lean:
\ IR 0.1's 38, then LSHIFT and -ROT.
s" dup" irx-row ' dup 1 2 irx-effect!          s" drop" irx-row ' drop 1 0 irx-effect!
s" swap" irx-row ' swap 2 2 irx-effect!        s" over" irx-row ' over 2 3 irx-effect!
s" nip" irx-row ' nip 2 1 irx-effect!          s" tuck" irx-row ' tuck 2 3 irx-effect!
s" rot" irx-row ' rot 3 3 irx-effect!          s" 2dup" irx-row ' 2dup 2 4 irx-effect!
s" 2drop" irx-row ' 2drop 2 0 irx-effect!
s" >r" irx-row ' irx-noop 1 0 irx-effect!      0 1 irx-row-returns
s" r>" irx-row ' irx-noop 0 1 irx-effect!      1 0 irx-row-returns
s" r@" irx-row ' dup 0 1 irx-effect!           1 1 irx-row-returns
s" +" irx-row ' + 2 1 irx-effect!              s" -" irx-row ' - 2 1 irx-effect!
s" *" irx-row ' irx-times 2 1 irx-effect!
s" /" irx-row ' / 2 1 irx-effect!              ' irx-divisible? irx-partial
s" mod" irx-row ' mod 2 1 irx-effect!          ' irx-divisible? irx-partial
s" negate" irx-row ' negate 1 1 irx-effect!    s" abs" irx-row ' irx-abs 1 1 irx-effect!
s" 1+" irx-row ' 1+ 1 1 irx-effect!            s" 1-" irx-row ' 1- 1 1 irx-effect!
s" =" irx-row ' = 2 1 irx-effect!              s" <>" irx-row ' <> 2 1 irx-effect!
s" <" irx-row ' < 2 1 irx-effect!              s" >" irx-row ' > 2 1 irx-effect!
s" 0=" irx-row ' 0= 1 1 irx-effect!            s" 0<>" irx-row ' 0<> 1 1 irx-effect!
s" 0<" irx-row ' 0< 1 1 irx-effect!            s" 0>" irx-row ' 0> 1 1 irx-effect!
s" and" irx-row ' and 2 1 irx-effect!          s" or" irx-row ' or 2 1 irx-effect!
s" xor" irx-row ' xor 2 1 irx-effect!          s" invert" irx-row ' invert 1 1 irx-effect!
s" rshift" irx-row ' rshift 2 1 irx-effect!    ' irx-shiftable? irx-partial
s" max" irx-row ' max 2 1 irx-effect!          s" min" irx-row ' min 2 1 irx-effect!
s" true" irx-row ' true 0 1 irx-effect!        s" false" irx-row ' false 0 1 irx-effect!
irx-prims store-count @ constant irx-prims-0.1
\ The two primitives new in IR 0.2.
s" lshift" irx-row ' lshift 2 1 irx-effect!    ' irx-shiftable? irx-partial
s" -rot" irx-row ' -rot 3 3 irx-effect!
irx-prims store-count @ 40 <> [if] .( irx: primitive table ) abort [then]

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

\ A machine stack: how many items it holds, its capacity, and its cells,
\ bottom first.
begin-structure /irx-stack
  field: irx-stack-depth
  field: irx-stack-capacity
  0 +field irx-stack-cells
end-structure
: irx-stack-size ( capacity -- u ) cells /irx-stack + ;

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
\ a definition's header, or a line inside a definition; none once the load
\ is finished.
0 constant irx-m-version
1 constant irx-m-source
2 constant irx-m-top
3 constant irx-m-body
4 constant irx-m-closed
5 constant irx-mode-count

begin-structure /irx-state
  field: irx-s-outcome     \ of the load: ok until the first problem
  field: irx-s-lines       \ lines read
  field: irx-s-mode        \ what the next line may be
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
  irx-data-capacity irx-stack-size +field irx-s-data
  irx-return-capacity irx-stack-size +field irx-s-returns
  field: irx-s-frames#
  irx-frame-capacity /irx-frame * +field irx-s-frames
  field: irx-s-result      \ how the last run ended
  field: irx-s-last        \ the instruction it started last, or -1
  field: irx-s-new         \ true when the version line is IR 0.2's
  field: irx-s-texts#      \ room used in irx-s-texts
  irx-texts-capacity aligned +field irx-s-texts   \ each text: its length, its characters
end-structure
/irx-state context-record: irx-state

\ Where out lines' output goes: a sink ( c-addr u -- ), and one character.
begin-structure /irx-output
  field: irx-output-sink
  1 chars aligned +field irx-output-char
end-structure
/irx-output context-record: irx-output
: irx-sink ( -- addr ) irx-output irx-output-sink ;
: irx-output-to ( xt -- ) irx-sink ! ;
: irx-discard-output ( c-addr u -- ) 2drop ;
: irx-output-setup ( -- ) ['] irx-discard-output irx-output-to ;
' irx-output-setup context-setup

\ Accessors.
: irx-code ( -- store ) irx-state irx-s-code ;
: irx-defs ( -- store ) irx-state irx-s-defs ;
: irx-op ( index -- op ) irx-code store-slot ;
: irx-def ( index -- def ) irx-defs store-slot ;
: irx-here ( -- index ) irx-code store-count @ ;
: irx-mode ( -- mode ) irx-state irx-s-mode @ ;
: irx-mode! ( mode -- ) irx-state irx-s-mode ! ;
: irx-current ( -- addr ) irx-state irx-s-current ;
: irx-open# ( -- addr ) irx-state irx-s-open# ;
: irx-tokens# ( -- addr ) irx-state irx-s-tokens# ;
: irx-token-cell ( i -- addr ) 2* cells irx-state irx-s-tokens + ;
: irx-token ( i -- c-addr u ) irx-token-cell 2@ ;
: irx-kind@ ( index -- kind )
  dup 0< if drop irx-kind-undefined else irx-def irx-def-kind @ then ;

\ The machine's data and return stacks.
: irx-data ( -- stack ) irx-state irx-s-data ;
: irx-rstack ( -- stack ) irx-state irx-s-returns ;
: irx-held ( stack -- n ) irx-stack-depth @ ;
: irx-room ( stack -- n ) dup irx-stack-capacity @ swap irx-held - ;
: irx-stack-cell ( i stack -- addr ) irx-stack-cells swap cells + ;
\ The cell just above the top item.
: irx-stack-top ( stack -- addr ) dup irx-held cells swap irx-stack-cells + ;
: irx-empty ( capacity stack -- ) tuck irx-stack-capacity ! 0 swap irx-stack-depth ! ;
: irx-rclear ( -- ) irx-return-capacity irx-rstack irx-empty ;
\ Empty both stacks; also sets them up in a new context.
: irx-clear ( -- ) irx-data-capacity irx-data irx-empty irx-rclear ;
' irx-clear context-setup

\ Moving n items between a machine stack and the host's data stack, in
\ stack order. The caller has checked depth and room.
: irx-shrink ( n stack -- addr ) swap negate over irx-stack-depth +! irx-stack-top ;
: irx-grow ( n stack -- addr ) tuck irx-stack-depth +! irx-stack-top ;
: irx-take ( n stack -- x1..xn )
  over if over swap irx-shrink swap 0 ?do dup @ swap cell+ loop drop else 2drop then ;
: irx-give ( x1..xn n stack -- )
  over if over swap irx-grow swap 0 ?do 1 cells - tuck ! loop drop else 2drop then ;
\ The same for one item, the common case: literals, flags, inputs.
: irx-put ( x stack -- ) tuck irx-stack-top ! 1 swap irx-stack-depth +! ;
: irx-pop ( stack -- x ) -1 over irx-stack-depth +! irx-stack-top @ ;
\ Push x onto the data stack when there is room.
: irx-pushed? ( x -- flag )
  irx-data irx-room 0> dup if swap irx-data irx-put else nip then ;

\ Loading stops at the first problem; later lines are skipped.
: irx-loading? ( -- flag ) irx-state irx-s-outcome @ ok? ;
: irx-stop ( outcome -- ) irx-loading? if irx-state irx-s-outcome ! else drop then ;
: irx-malformed ( -- ) outcome-invalid irx-stop ;
: irx-full ( -- ) outcome-full irx-stop ;
: irx-checked ( flag -- flag ) dup 0= if irx-malformed then ;
: irx-expect ( flag -- ) irx-checked drop ;

\ Splitting a line: its indentation, then tokens separated by one space.
: irx-space? ( c-addr u -- flag ) 1 min s"  " compare 0= ;
: irx-indent ( c-addr u -- c-addr' u' n )
  0 >r begin 2dup irx-space? while 1 /string r> 1+ >r repeat r> ;
\ The first token and the rest, which starts at the space after it.
: irx-split ( c-addr u -- rest-addr rest-u token-addr token-u )
  2dup s"  " search 0= if chars + 0 then dup >r 2swap r> - ;
: irx-keep ( c-addr u -- )
  dup 0= irx-tokens# @ irx-token-capacity = or if 2drop irx-malformed exit then
  irx-tokens# @ irx-token-cell 2! 1 irx-tokens# +! ;
: irx-tokens ( c-addr u -- ) begin irx-split irx-keep dup while 1 /string repeat 2drop ;

\ Numbers: decimal digits at the start of c-addr u, read into a double cell.
: irx-convert ( c-addr u -- ud c-addr' u' )
  0 0 2swap base @ >r decimal >number r> base ! ;
: irx-count ( c-addr u -- n c-addr' u' flag ) dup >r irx-convert rot drop dup r> < ;
: irx-colon? ( c-addr u -- c-addr' u' flag )
  2dup 1 min s" :" compare if false else 1 /string true then ;
\ A location "@line:column"; anything else after the @ is malformed.
: irx-part ( c-addr u -- n c-addr' u' ) irx-count irx-expect ;
: irx-location ( c-addr u -- line column )
  1 /string irx-part irx-colon? irx-expect irx-part nip 0= irx-expect ;
: irx-where! ( line column -- ) irx-state tuck irx-s-at-column ! irx-s-at-line ! ;
: irx-at-sign? ( c-addr u -- flag ) 1 min s" @" compare 0= ;
: irx-last-token ( -- c-addr u ) irx-tokens# @ 1- irx-token ;
\ Whether the line ends with a location, which is then not a token.
: irx-located? ( -- flag ) irx-tokens# @ if irx-last-token irx-at-sign? else false then ;
: irx-locate ( -- )
  irx-located? if irx-last-token irx-location -1 irx-tokens# +! else 0 0 then irx-where! ;
: irx-tokenize ( c-addr u -- )
  irx-indent irx-state irx-s-indent ! 0 irx-tokens# ! irx-tokens irx-locate ;

\ A literal: an optional minus sign and decimal digits; other text is
\ malformed. It is read as the model's parser reads it (String.toInt?),
\ so leading zeros change nothing. The model gives a literal outside the
\ cell no meaning, so one that does not fit a host cell loads as unfit and
\ runs as the failure unmodeled. Without its leading zeros, a magnitude
\ of more digits than max-n 1+ has (irx-cell-digits) fits no cell; one of
\ at most that many is below 10 * (max-n + 1), so a double cell holds it
\ exactly for any cell width of 4 bits or more.
: irx-width ( u -- n ) 0 <# #s #> nip ;
max-n 1+ irx-width constant irx-cell-digits
: irx-sign ( c-addr u -- c-addr' u' negative? )
  2dup 1 min s" -" compare 0= dup if >r 1 /string r> then ;
: irx-digits? ( c-addr u -- flag )
  dup if irx-convert nip nip nip 0= else 2drop false then ;
\ A zero before another digit.
: irx-padded? ( c-addr u -- flag )
  dup 1 > if 1 min s" 0" compare 0= else 2drop false then ;
: irx-unpadded ( c-addr u -- c-addr' u' ) begin 2dup irx-padded? while 1 /string repeat ;
\ The digits' value, or 0 1 (beyond every cell) when there are too many.
: irx-unsigned ( c-addr u -- ud )
  irx-unpadded dup irx-cell-digits > if 2drop 0 1 else irx-convert 2drop then ;
\ The largest magnitude that fits, unsigned: max-n 1+ is the smallest cell's.
: irx-limit ( negative? -- u ) if max-n 1+ else max-n then ;
\ The low cell of ud, and whether ud is at most the limit.
: irx-within ( ud negative? -- u flag ) irx-limit swap >r over u< 0= r> 0= and ;
: irx-signed ( u negative? -- n ) if negate then ;
: irx-magnitude ( c-addr u negative? -- n fits? )
  >r irx-unsigned r@ irx-within swap r> irx-signed swap ;
: irx-literal ( c-addr u -- n fits? true | false )
  irx-sign >r 2dup irx-digits? if r> irx-magnitude true exit then
  2drop r> drop irx-malformed false ;

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

\ An instruction new in IR 0.2 needs IR 0.2's version line.
: irx-new? ( -- ) irx-state irx-s-new @ irx-expect ;
: irx-new-prim? ( index -- index ) dup irx-prims-0.1 < 0= if irx-new? then ;

\ Lines inside a definition ( -- ), by keyword; any other is malformed.
: irx-body-prim ( -- )
  2 irx-plain? if 1 irx-token irx-prims irx-find
    if irx-new-prim? irx-k-prim swap irx-append else irx-malformed then then ;
\ out W: an output word by name (IR 0.2).
: irx-body-out ( -- )
  irx-new? 2 irx-plain? if 1 irx-token irx-outs irx-find
    if irx-k-out swap irx-append else irx-malformed then then ;
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
: irx-close-def ( -- )
  irx-here irx-current @ irx-def irx-def-end ! -1 irx-current ! irx-m-top irx-mode! ;
: irx-body-end ( -- )
  irx-open# @ 0= 1 0 irx-shape? and irx-checked if irx-close-def then ;
' irx-malformed irx-keyword-count irx-table irx-body-actions
: irx-body! ( xt kind -- ) irx-body-actions irx-entry! ;
' irx-body-prim irx-k-prim irx-body!       ' irx-body-lit irx-k-lit irx-body!
' irx-body-call irx-k-call irx-body!       ' irx-body-if irx-k-if irx-body!
' irx-body-else irx-k-else irx-body!       ' irx-body-then irx-k-then irx-body!
' irx-body-begin irx-k-begin irx-body!     ' irx-body-while irx-k-while irx-body!
' irx-body-repeat irx-k-repeat irx-body!   ' irx-body-exit irx-k-exit irx-body!
' irx-body-end irx-k-end irx-body!         ' irx-body-out irx-k-out irx-body!

\ out ." text": the text runs from after `." ` to the next quote, which
\ may be followed only by a location; it is kept with its length.
: irx-text-start ( -- c-addr u ) s\" out .\" " ;
: irx-text-line? ( c-addr u -- flag )
  irx-indent drop irx-text-start nip min irx-text-start compare 0= ;
: irx-closing-quote ( c-addr u -- text-addr text-u rest-addr rest-u true | false )
  2dup s\" \"" search 0= if 2drop 2drop false exit then
  2swap drop 2 pick over - 1 chars / 2swap 1 /string true ;
: irx-text-location ( rest-addr rest-u -- )
  0 irx-tokens# ! dup if over c@ bl = irx-expect 1 /string irx-tokens else 2drop then
  irx-locate irx-tokens# @ 0= irx-expect ;
: irx-text-size ( u -- size ) chars cell+ aligned ;
: irx-texts# ( -- addr ) irx-state irx-s-texts# ;
: irx-text-record ( offset -- addr ) irx-state irx-s-texts + ;
: irx-text-at ( offset -- c-addr u ) irx-text-record dup cell+ swap @ ;
: irx-store-text ( c-addr u -- offset true | false )
  dup irx-text-size irx-texts# @ + irx-texts-capacity > if 2drop irx-full false exit then
  irx-texts# @ >r dup irx-text-size irx-texts# +!
  r@ irx-text-record 2dup ! cell+ swap chars move r> true ;
: irx-text-op ( offset -- ) irx-k-out irx-o-text irx-add if irx-op irx-op-end ! else drop then ;
: irx-body-text ( c-addr u -- )
  irx-new? irx-indent irx-state irx-s-indent ! irx-text-start nip /string
  irx-closing-quote 0= if irx-malformed exit then irx-text-location
  irx-loading? 0 irx-plain? and if irx-store-text if irx-text-op then else 2drop then ;

\ A definition's header: "word name" or "constant name" at the left edge;
\ any other line between definitions is malformed.
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
' irx-malformed irx-keyword-count irx-table irx-top-actions
' irx-top-word irx-k-word irx-top-actions irx-entry!
' irx-top-constant irx-k-constant irx-top-actions irx-entry!

\ One line, in the current mode; once the load is finished, every line is
\ refused.
: irx-kind ( -- kind true | false )
  irx-tokens# @ if 0 irx-token irx-keywords irx-find else false then ;
: irx-act ( table -- ) irx-kind if cells + @ execute else drop irx-malformed then ;
: irx-statement ( c-addr u table -- )
  >r irx-tokenize irx-loading? if r> irx-act else r> drop then ;
: irx-version! ( new? -- ) irx-state irx-s-new ! irx-m-source irx-mode! ;
: irx-version-line ( c-addr u -- )
  2dup s" lf-ir 0.1" compare 0= if 2drop false irx-version! exit then
  s" lf-ir 0.2" compare if irx-malformed else true irx-version! then ;
: irx-source-line ( c-addr u -- )
  dup 7 > >r 7 min s" source " compare 0= r> and irx-checked if irx-m-top irx-mode! then ;
: irx-top-line ( c-addr u -- ) irx-top-actions irx-statement ;
: irx-body-line ( c-addr u -- )
  2dup irx-text-line? if irx-body-text else irx-body-actions irx-statement then ;
: irx-refused-line ( c-addr u -- ) 2drop irx-malformed ;
' irx-refused-line irx-mode-count irx-table irx-modes
' irx-version-line irx-m-version irx-modes irx-entry!
' irx-source-line irx-m-source irx-modes irx-entry!
' irx-top-line irx-m-top irx-modes irx-entry!
' irx-body-line irx-m-body irx-modes irx-entry!

\ Loading. irx-load-start forgets any program; lines then come one at a
\ time (irx-load-line, which suits the reader's output word) or from a
\ file (irx-load-file), and irx-load-finish gives the outcome and closes
\ the load. A program runs only after a finish that gave ok; a line or a
\ second finish after it is malformed, and the program no longer runs.
: irx-stores ( -- )
  irx-code-capacity /irx-op 0 irx-code store-init 0= abort" irx: code store"
  irx-def-capacity /irx-def 0 irx-defs store-init 0= abort" irx: definition store" ;
: irx-load-start ( -- )
  irx-state /irx-state erase -1 irx-current ! irx-clear irx-stores ;
\ A line is counted first, so that a refused one is the line reported.
: irx-in-mode ( c-addr u -- ) irx-mode cells irx-modes + @ execute ;
: irx-read ( c-addr u -- )
  dup irx-line-chars < if irx-in-mode else 2drop irx-malformed then ;
: irx-load-line ( c-addr u -- )
  irx-loading? if 1 irx-state irx-s-lines +! irx-read else 2drop then ;
: irx-load-finish ( -- outcome )
  irx-mode irx-m-top <> if irx-malformed then
  irx-m-closed irx-mode! irx-state irx-s-outcome @ ;
: irx-loaded? ( -- flag ) irx-mode irx-m-closed = irx-loading? and ;
\ Lines read so far: after a failed load, the line that stopped it.
: irx-load-lines ( -- n ) irx-state irx-s-lines @ ;

\ A file, line by line. A line of irx-line-chars or more fills the buffer,
\ which irx-load-line then refuses.
: irx-text ( -- c-addr ) irx-state irx-s-text ;
: irx-fetch ( fileid -- u true | false )
  >r irx-text irx-line-chars r> read-line if 2drop irx-malformed false exit then
  0= if drop false else true then ;
: irx-more? ( fileid -- flag )
  irx-fetch if irx-text swap irx-load-line irx-loading? else false then ;
: irx-load-file ( c-addr u -- outcome )
  irx-load-start r/o open-file if drop irx-malformed else
    begin dup irx-more? 0= until close-file drop then irx-load-finish ;

\ Frames of a run.
: irx-frames# ( -- addr ) irx-state irx-s-frames# ;
: irx-frame ( -- frame ) irx-frames# @ 1- /irx-frame * irx-state irx-s-frames + ;
: irx-ip ( -- addr ) irx-frame irx-frame-ip ;
: irx-fuel ( -- addr ) irx-frame irx-frame-fuel ;
\ Items the current block may use: those above its frame's bases.
: irx-items ( -- n ) irx-data irx-held irx-frame irx-frame-data @ - ;
: irx-ritems ( -- n ) irx-rstack irx-held irx-frame irx-frame-returns @ - ;

\ A primitive: underflow when its inputs are missing, no room when its
\ outputs would not fit, unmodeled outside its domain.
: irx-short? ( prim -- flag )
  dup irx-prim-in @ irx-items > swap irx-prim-rin @ irx-ritems > or ;
: irx-data-rise ( prim -- n ) dup irx-prim-out @ swap irx-prim-in @ - ;
: irx-return-rise ( prim -- n ) dup irx-prim-rout @ swap irx-prim-rin @ - ;
\ Whether a stack lacks room for n more items; most primitives add none.
: irx-crowds? ( n stack -- flag ) over 0> if irx-room > else 2drop false then ;
: irx-crowded? ( prim -- flag )
  dup irx-data-rise irx-data irx-crowds? swap irx-return-rise irx-rstack irx-crowds? or ;
: irx-inputs ( prim -- x1..xn r1..rk )
  dup irx-prim-rin @ >r irx-prim-in @ irx-data irx-take r> irx-rstack irx-take ;
: irx-in-domain? ( x... prim -- x... flag )
  irx-prim-domain @ ?dup if execute else true then ;
: irx-outputs ( y1..ym r1..rk prim -- )
  dup irx-prim-out @ >r irx-prim-rout @ irx-rstack irx-give r> irx-data irx-give ;
: irx-discard ( x... prim -- ) dup irx-prim-in @ swap irx-prim-rin @ + 0 ?do drop loop ;
: irx-apply ( prim -- result )
  >r r@ irx-inputs r@ irx-in-domain? 0= if r> irx-discard irx-unmodeled exit then
  r@ irx-prim-action @ execute r> irx-outputs irx-going ;
: irx-prim ( index -- result )
  irx-prims store-slot dup irx-short? if drop irx-underflow exit then
  dup irx-crowded? if drop irx-no-room exit then irx-apply ;
: irx-lit ( n -- result ) irx-pushed? if irx-going else irx-no-room then ;

\ Frames. A new block starts with its parent's bases (none at the root).
: irx-bases ( -- data returns )
  irx-frames# @ if irx-frame dup irx-frame-data @ swap irx-frame-returns @ else 0 0 then ;
: irx-bases! ( data returns -- ) irx-frame tuck irx-frame-returns ! irx-frame-data ! ;
: irx-block! ( start end fuel -- ) irx-fuel ! irx-frame irx-frame-end ! irx-ip ! ;
: irx-enter ( start end fuel -- flag )
  irx-frames# @ irx-frame-capacity = if 2drop drop false exit then
  irx-bases 1 irx-frames# +! irx-bases! irx-block! true ;
: irx-leave ( -- ) -1 irx-frames# +! ;

\ Running a block: one instruction after another, through irx-actions,
\ indexed by kind, until the end, EXIT or a failure. The markers ELSE,
\ THEN, WHILE and REPEAT keep the action below, which reports the code
\ corrupted, as would any kind whose action were never set.
: irx-do-marker ( op -- result ) drop irx-broken ;
' irx-do-marker irx-op-kinds irx-table irx-actions
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
: irx-enter-def ( def fuel -- flag ) >r irx-def-block r> irx-enter ;
: irx-own-returns ( -- ) irx-rstack irx-held irx-frame irx-frame-returns ! ;
: irx-own-stacks ( -- ) irx-data irx-held irx-frame irx-frame-data ! irx-own-returns ;
: irx-ended? ( result -- flag ) dup irx-next = swap irx-exited = or ;
: irx-returned ( result -- result )
  dup irx-ended? if drop irx-ritems if irx-unbalanced else irx-next then then ;
: irx-one-value? ( -- flag ) irx-items 1 = irx-ritems 0= and ;
: irx-valued ( result -- result )
  dup irx-next = if drop irx-one-value? if irx-next else irx-bad-constant then exit then
  dup irx-exited = if drop irx-bad-constant then ;
: irx-run-word ( def fuel -- result )
  irx-enter-def 0= if irx-no-room exit then
  irx-own-returns irx-steps irx-returned irx-leave ;
: irx-run-constant ( def fuel -- result )
  irx-enter-def 0= if irx-no-room exit then
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
: irx-flag ( -- x true | false ) irx-items if irx-data irx-pop true else false then ;
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

\ Output words (IR 0.2): `.`, `U.`, `EMIT` and `SPACES` take one cell
\ (underflow without one), the others none; what each prints goes to the
\ sink, as the model's Event.render gives it: a signed or unsigned decimal
\ and a blank, an LF, the byte x mod 256, blanks (none for a count below
\ one), the text; and .S as both Gforths print it (Forth-2012 leaves its
\ format to the system): <depth>, a blank, then the top nine cells at
\ most, deepest first, each with a blank. A block sees the cells above its
\ frame's base, as the model's word sees the whole stack and its constant
\ none of its caller's.
: irx-say ( c-addr u -- ) irx-sink @ execute ;
: irx-say-blank ( -- ) s"  " irx-say ;
: irx-say-byte ( x -- ) irx-output irx-output-char tuck c! 1 irx-say ;
: irx-in-decimal ( xt -- ) base @ >r decimal catch r> base ! throw ;
: irx-signed-text ( n -- ) dup abs 0 <# #s rot sign #> irx-say ;
: irx-unsigned-text ( u -- ) 0 <# #s #> irx-say ;
: irx-say-number ( n -- ) ['] irx-signed-text irx-in-decimal irx-say-blank ;
: irx-say-unsigned ( u -- ) ['] irx-unsigned-text irx-in-decimal irx-say-blank ;
: irx-say-blanks ( n -- ) 0 max 0 ?do irx-say-blank loop ;
: irx-say-depth ( n -- ) s" <" irx-say ['] irx-unsigned-text irx-in-decimal s" > " irx-say ;
: irx-say-stack ( -- )
  irx-items dup irx-say-depth irx-data irx-held dup rot 9 min - ?do
    i irx-data irx-stack-cell @ irx-say-number loop ;
: irx-takes? ( kind -- flag )
  dup irx-o-dot = over irx-o-udot = or over irx-o-emit = or swap irx-o-spaces = or ;
: irx-print ( op kind -- )
  case
    irx-o-dot of drop irx-data irx-pop irx-say-number endof
    irx-o-udot of drop irx-data irx-pop irx-say-unsigned endof
    irx-o-cr of drop 10 irx-say-byte endof
    irx-o-emit of drop irx-data irx-pop irx-say-byte endof
    irx-o-space of drop irx-say-blank endof
    irx-o-spaces of drop irx-data irx-pop irx-say-blanks endof
    irx-o-dots of drop irx-say-stack endof
    irx-o-text of irx-op-end @ irx-text-at irx-say endof
    nip endcase ;
: irx-do-out ( op -- result )
  dup irx-op-arg @ dup irx-takes? irx-items 0= and if 2drop irx-underflow exit then
  irx-print irx-going ;

: irx-action! ( xt kind -- ) irx-actions irx-entry! ;
' irx-do-prim irx-k-prim irx-action!      ' irx-do-lit irx-k-lit irx-action!
' irx-do-call irx-k-call irx-action!      ' irx-do-if irx-k-if irx-action!
' irx-do-begin irx-k-begin irx-action!    ' irx-do-exit irx-k-exit irx-action!
' irx-do-out irx-k-out irx-action!

\ The data stack a run starts from and ends with, bottom first: irx-clear,
\ then irx-push; afterwards irx-depth items, read by irx-item.
: irx-push ( x -- outcome ) irx-pushed? room>outcome ;
: irx-depth ( -- n ) irx-data irx-held ;
: irx-item ( i -- x true | false )
  dup 0 irx-depth within if irx-data irx-stack-cell @ true else drop false then ;

\ Run a word on the data stack, as the model's callWord does: [CALL name]
\ with fuel, from an empty return stack the word cannot see. The stack
\ holds the result afterwards; after a failure its contents mean nothing.
: irx-lookup ( c-addr u -- def ) irx-defs irx-find 0= if -1 then ;
: irx-runnable? ( fuel -- flag ) 0< 0= irx-loaded? and ;
: irx-finish ( result -- outcome ) dup irx-state irx-s-result ! irx-outcome ;
: irx-fresh-run ( -- ) irx-rclear 0 irx-frames# ! -1 irx-state irx-s-last ! ;
: irx-root ( fuel -- ) irx-fresh-run 0 0 rot irx-enter drop ;
: irx-run ( fuel c-addr u -- outcome )
  rot dup irx-runnable? 0= if drop 2drop irx-broken irx-finish exit then
  irx-root irx-lookup irx-call irx-leave irx-finish ;
: irx-result ( -- result ) irx-state irx-s-result @ ;
\ The location of the instruction the last run started last, 0 0 if none.
: irx-last ( -- line column )
  irx-state irx-s-last @ dup 0< if drop 0 0 exit then
  irx-op dup irx-op-line @ swap irx-op-column @ ;
