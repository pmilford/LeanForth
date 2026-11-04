\ Throwaway demo for ADR 0019, question 4(b): a symbolic vocabulary. The
\ same source runs through the same runner (cv.fs: isolation, the literal
\ gap check, the file's own words), but the words act on a symbolic stack
\ of terms instead of writing IR: dup on x leaves x x, > on a b leaves the
\ term (a > b), IF splits the path on its condition and THEN merges the
\ two arms with if-then-else terms, EXIT ends a path, a call applies the
\ callee's paths. Each word ends with its paths: a condition and the
\ outputs over its inputs, named from its stack comment. Loops are not
\ handled (they need invariants) and mark the word unsupported. Untrusted
\ by design: nothing here is a proof. Usage: gforth cv.fs sym.fs -e ...

true cv-quiet !
variable sym-skip          \ nonzero while the rest of a word is skipped
create sym-why 64 allot    variable sym-why#
: sym-skip! ( c-addr u -- )
  sym-skip @ if 2drop exit then 63 min dup sym-why# ! sym-why swap move true sym-skip ! ;

\ ---------------------------------------------------------------- terms
0 constant t-in  1 constant t-const  2 constant t-flag  3 constant t-sym
4 constant t-infix  5 constant t-f1  6 constant t-f2  7 constant t-ite
8 constant t-not  9 constant t-conj
4096 constant t-max
create t-op t-max cells allot  create t-a t-max cells allot
create t-b t-max cells allot   create t-c t-max cells allot
variable t#  1 t#  !       \ term 0 means "none"
: t-new ( op a b c -- t )
  t# @ t-max = abort" sym: terms full"
  t# @ >r r@ cells t-c + ! r@ cells t-b + ! r@ cells t-a + ! r@ cells t-op + ! r> 1 t# +! ;
: t-op@ ( t -- op ) cells t-op + @ ;  : t-a@ ( t -- x ) cells t-a + @ ;
: t-b@ ( t -- x ) cells t-b + @ ;    : t-c@ ( t -- x ) cells t-c + @ ;
: t-true ( -- t ) t-flag -1 0 0 t-new ;
create in-terms 32 cells allot
: in-reset ( -- ) in-terms 32 cells erase ;
: in-term ( k -- t ) dup cells in-terms + @ ?dup if nip exit then
  dup t-in swap 0 0 t-new dup rot cells in-terms + ! ;

\ ---------------------------------------------------------------- states
\ A state: live flag, data stack, return stack, inputs drawn, conditions
\ (term, polarity) of the path so far. Cells: 0 live, 1 depth, 2-33
\ data, 34 rdepth, 35-42 rdata, 43 inputs, 44 conds#, 45-76 conds.
77 cells constant /state
: st-depth ( st -- a ) cell+ ;        : st-data ( st -- a ) 2 cells + ;
: st-rdepth ( st -- a ) 34 cells + ;  : st-rdata ( st -- a ) 35 cells + ;
: st-inputs ( st -- a ) 43 cells + ;  : st-conds# ( st -- a ) 44 cells + ;
: st-conds ( st -- a ) 45 cells + ;
create cur /state allot
: st-copy ( from to -- ) /state move ;
: st-fresh ( st -- ) dup /state erase true swap ! ;

\ The data stack of cur; popping an empty stack draws the next input of
\ the word (the caller's cell just below everything seen so far).
: s-push ( t -- )
  cur st-depth @ 32 = if drop s" stack too deep" sym-skip! exit then
  cur st-depth @ cells cur st-data + ! 1 cur st-depth +! ;
: s-pop ( -- t )
  cur st-depth @ 0= if cur st-inputs @ in-term 1 cur st-inputs +! exit then
  -1 cur st-depth +! cur st-depth @ cells cur st-data + @ ;
: r-push ( t -- )
  cur st-rdepth @ 8 = if drop s" return stack too deep" sym-skip! exit then
  cur st-rdepth @ cells cur st-rdata + ! 1 cur st-rdepth +! ;
: r-pop ( -- t )
  cur st-rdepth @ 0= if s" return stack underflow" sym-skip! t-true exit then
  -1 cur st-rdepth +! cur st-rdepth @ cells cur st-rdata + @ ;
: cond+ ( st t polarity -- )
  rot dup st-conds# @ 16 = if drop 2drop s" too many conditions" sym-skip! exit then
  >r r@ st-conds# @ 2* cells r@ st-conds + 2! 1 r> st-conds# +! ;
: cond-term ( t polarity -- t' ) 0= if t-not swap 0 0 t-new then ;
: cond@ ( st i -- t ) 2* cells swap st-conds + 2@ cond-term ;
variable cj
\ The conjunction of the conditions of st from index start on.
: conj-from ( st start -- t )
  over st-conds# @ over = if 2drop t-true exit then
  2dup cond@ cj ! 1+ over st-conds# @ swap ?do
    dup i cond@ t-conj cj @ rot 0 t-new cj ! loop drop cj @ ;
\ Insert the inputs a state has not drawn yet below its stack, so that
\ two states agree on their inputs.
: st-widen ( st n -- )
  over st-inputs @ ?do
    dup st-depth @ 32 = if s" stack too deep" sym-skip! leave then
    dup st-data dup cell+ 2 pick st-depth @ cells move
    i in-term over st-data ! 1 over st-depth +! 1 over st-inputs +!
  loop drop ;

\ ---------------------------------------------------------------- printing
create names 8 32 * allot  create names# 8 cells allot  variable names-n
: in-name ( k -- c-addr u )
  names-n @ 1- swap - dup 0< if drop s" x?" exit then dup 32 * names + swap cells names# + @ ;
: .t ( t -- )
  dup t-op@ case
    t-in of t-a@ in-name type endof
    t-const of t-a@ 0 .r endof
    t-flag of t-a@ if ." true" else ." false" then endof
    t-sym of t-a@ pw-name type endof
    t-infix of ." (" dup t-a@ recurse space dup t-c@ count type space t-b@ recurse ." )"
      endof
    t-f1 of dup t-c@ count type ." (" t-a@ recurse ." )" endof
    t-f2 of dup t-c@ count type ." (" dup t-a@ recurse ." , " t-b@ recurse ." )" endof
    t-ite of ." (if " dup t-a@ recurse ."  then " dup t-b@ recurse ."  else " t-c@ recurse
      ." )" endof
    t-not of ." not " t-a@ recurse endof
    t-conj of dup t-a@ recurse ."  and " t-b@ recurse endof
  endcase ;
: .conds ( st -- )
  dup st-conds# @ 0= if drop ." always" exit then 0 conj-from .t ;
: .outs ( st -- )
  dup st-depth @ 0= if drop ." (nothing)" exit then
  dup st-depth @ 0 ?do i if space then dup st-data i cells + @ .t loop drop ;

\ ---------------------------------------------------------------- summaries
\ Up to 8 finished paths per word of the file, by its identity (pw-id).
40 constant w-max  8 constant p-max
w-max p-max * /state * allocate throw constant paths
create paths# w-max cells allot      \ -1: unsupported
create consts w-max cells allot      \ a constant's term
variable word-id
: path ( id i -- st ) swap p-max * + /state * paths + ;
: paths#@ ( id -- n ) cells paths# + @ ;
\ cur ends a path of the word being defined.
: finish ( -- )
  cur st-rdepth @ if s" return stack not empty at the end" sym-skip! exit then
  word-id @ paths#@ p-max = if s" too many paths" sym-skip! exit then
  cur word-id @ dup paths#@ path st-copy 1 word-id @ cells paths# + +! false cur ! ;
variable widest
: widen-all ( id -- )
  0 widest ! dup paths#@ 0 ?do dup i path st-inputs @ widest @ max widest ! loop
  dup paths#@ 0 ?do dup i path widest @ st-widen loop drop ;

\ ---------------------------------------------------------------- control
\ A frame: the condition, whether ELSE was seen, the state before IF (for
\ the other arm) and the yes arm's state once ELSE is seen.
2 cells 2 /state * + constant /frame
create frames 8 /frame * allot  variable frames#
: frame ( -- fr ) frames# @ 1- /frame * frames + ;
: f-else? ( fr -- a ) cell+ ;
: f-pre ( fr -- st ) 2 cells + ;  : f-yes ( fr -- st ) 2 cells + /state + ;
: sym-if ( -- )
  frames# @ 8 = if s" too deeply nested" sym-skip! exit then
  s-pop 1 frames# +! frame ! false frame f-else? !
  cur frame f-pre st-copy cur frame @ true cond+ ;
: sym-else ( -- )
  cur frame f-yes st-copy true frame f-else? !
  frame f-pre cur st-copy cur frame @ false cond+ ;
\ Merging two live arms: equal cells stay, different ones become
\ (if c then yes else no); conditions added inside an arm are kept as
\ (if c then those of yes else those of no).
variable parent#
: merge-cell ( i no yes -- )
  rot cells tuck + @ >r + dup @ r> 2dup = if 2drop drop exit then
  >r >r t-ite frame @ r> r> swap t-new swap ! ;
: extra ( st -- t|0 )
  dup st-conds# @ parent# @ 1+ > if parent# @ 1+ conj-from else drop 0 then ;
: ?true ( t|0 -- t ) ?dup 0= if t-true then ;
\ Arms that leave different depths (as in "if 2drop false else + true
\ then ;") stay two paths: the yes arm is parked, and only ; may follow.
create parked 4 /state * allot  variable parked#
: park ( st -- )
  parked# @ 4 = if drop s" too many paths" sym-skip! exit then
  parked parked# @ /state * + st-copy 1 parked# +! ;
: unpark ( -- ) parked# @ 0 ?do parked i /state * + cur st-copy finish loop 0 parked# ! ;
\ Whether to skip this word: after a parked arm only ; may follow.
: skipping? ( -- flag )
  parked# @ if s" code after arms that leave different depths" sym-skip! then sym-skip @ ;
: merge-live ( -- )
  frame f-yes st-inputs @ cur st-inputs @ max >r frame f-yes r@ st-widen cur r> st-widen
  frame f-yes st-depth @ cur st-depth @ <> frame f-yes st-rdepth @ cur st-rdepth @ <> or
  if frame f-yes park exit then
  cur st-depth @ 0 ?do i cur st-data frame f-yes st-data merge-cell loop
  cur st-rdepth @ 0 ?do i cur st-rdata frame f-yes st-rdata merge-cell loop
  frame f-yes extra cur extra parent# @ cur st-conds# !
  2dup or if >r >r t-ite frame @ r> ?true r> ?true t-new cur swap true cond+ else 2drop
  then ;
: merge ( -- )
  frame f-pre st-conds# @ parent# !
  frame f-yes @ 0= if exit then              \ yes arm ended: no arm goes on
  cur @ 0= if frame f-yes cur st-copy exit then
  merge-live ;
: sym-then ( -- )
  frame f-else? @ 0= if
    cur frame f-yes st-copy frame f-pre cur st-copy cur frame @ false cond+ then
  merge -1 frames# +! ;
: sym-exit ( -- ) cur @ if finish then ;
: sym-loop ( -- ) s" a loop: needs an invariant (plan 4.4.1)" sym-skip! ;

\ ---------------------------------------------------------------- calls
\ A call of a word with paths p0 ... pn: its inputs are the caller's
\ cells; each output is (if c0 then o0 else if c1 then o1 ... else on).
create actual 32 cells allot  variable callee  variable oj  variable acc
: subst ( t -- t' )
  dup t-op@ case
    t-in of t-a@ cells actual + @ endof
    t-infix of dup >r t-a@ recurse r@ t-b@ recurse r> t-c@ >r t-infix -rot r> t-new endof
    t-f2 of dup >r t-a@ recurse r@ t-b@ recurse r> t-c@ >r t-f2 -rot r> t-new endof
    t-conj of dup >r t-a@ recurse r> t-b@ recurse >r t-conj swap r> 0 t-new endof
    t-f1 of dup >r t-a@ recurse r> t-c@ >r t-f1 swap 0 r> t-new endof
    t-not of t-a@ recurse t-not swap 0 0 t-new endof
    t-ite of dup >r t-a@ recurse r@ t-b@ recurse r> t-c@ recurse >r >r >r t-ite r> r> r>
      t-new endof
  endcase ;
: out-of ( p -- t ) callee @ swap path st-data oj @ cells + @ subst ;
: cond-of ( p -- t ) callee @ swap path 0 conj-from subst ;
: out-term ( j -- t )
  oj ! callee @ paths#@ 1- dup out-of acc !
  0 ?do callee @ paths#@ 2 - i - >r t-ite r@ cond-of r> out-of acc @ t-new acc ! loop
  acc @ ;
: same-depths? ( -- depth true | false )
  callee @ 0 path st-depth @ callee @ paths#@ 1 ?do
    callee @ i path st-depth @ over <> if drop false unloop exit then loop true ;
: apply ( id -- )
  dup paths#@ dup 0< swap 0= or if drop s" calls a word that is not supported" sym-skip!
    exit then
  dup callee ! widen-all
  same-depths? 0= if s" calls a word whose paths leave different depths" sym-skip! exit then
  widest @ 0 ?do s-pop actual i cells + ! loop
  0 ?do i out-term s-push loop ;
: sym-call ( body -- )
  skipping? if drop exit then
  dup pw-kind @ k-constant = if t-sym swap 0 0 t-new s-push exit then
  cv-in-def @ 0= if drop why-outside cv-unsupported! then
  dup pw-done @ 0= if drop s" recursive call" sym-skip! exit then
  pw-id @ apply ;
: sym-lit ( n -- ) skipping? if drop exit then t-const swap 0 0 t-new s-push ;

\ ---------------------------------------------------------------- definitions
: name! ( c-addr u -- )
  names-n @ 8 = if 2drop exit then dup names-n @ cells names# + !
  names-n @ 32 * names + swap 31 min move 1 names-n +! ;
\ The input names: the words of a stack comment right after the name,
\ up to --. The comment itself is then read by ( as usual.
: names-end? ( c-addr u -- flag )
  dup 0= >r 2dup s" --" compare 0= >r s" )" compare 0= r> or r> or ;
: names? ( -- )
  0 names-n ! >in @ >r parse-name s" (" compare if r> >in ! exit then
  begin parse-name 2dup names-end? 0= while name! repeat 2drop r> >in ! ;
: .sym-word ( -- )
  ." sym " cv-def @ pw-name type
  sym-skip @ if ." : unsupported: " sym-why sym-why# @ type cr
    -1 word-id @ cells paths# + ! exit then
  word-id @ widen-all ."   (" widest @ 0 .r ."  inputs)" cr
  word-id @ paths#@ 0 ?do
    ."   when " word-id @ i path .conds ." :  " word-id @ i path .outs cr loop ;
: sym-colon ( -- )
  cv-in-def @ if why-nested cv-invalid! then
  cv-col cv-mark ! cv-name k-word swap cv-define dup cv-def ! pw-id @ word-id !
  0 word-id @ cells paths# + ! cv-read true cv-in-def !
  false sym-skip ! 0 frames# ! cur st-fresh in-reset names? ;
: sym-semicolon ( -- )
  cv-in-def @ 0= if why-outside cv-unsupported! then
  sym-skip @ 0= if cur @ if finish then unpark then
  .sym-word true cv-def @ pw-done ! false cv-in-def ! cur st-fresh 0 parked# ! ;
: sym-constant ( -- )
  cv-in-def @ if why-inside cv-unsupported! then
  s-pop >r cv-name k-constant swap cv-define cv-read true over pw-done !
  r@ over pw-id @ cells consts + ! ." sym " pw-name type ."  = " r> .t cr cur st-fresh ;

\ ---------------------------------------------------------------- vocabulary
wordlist constant sym-words
\ Words run even while a word is skipped: they read text or end words.
: sym-always ( xt "name" -- )
  get-current >r sym-words set-current create r> set-current ,
  does> >r cv-sync r> @ execute ;
: sym: ( xt "name" -- )
  get-current >r sym-words set-current create r> set-current ,
  does> >r cv-sync r> @ skipping? if drop exit then execute ;
: sym-name, ( "name" -- c-addr ) \ the next name, kept as a counted string
  >in @ parse-name rot >in ! here >r dup c, here swap dup allot move align r> ;
: sym-op ( op "name" -- ) \ an operation of two cells
  sym-name, get-current >r sym-words set-current create r> set-current , ,
  does> >r cv-sync r> skipping? if drop exit then
    2@ >r >r s-pop s-pop swap r> -rot r> t-new s-push ;
: infix: ( "name" -- ) t-infix sym-op ;
: func2: ( "name" -- ) t-f2 sym-op ;
: func1: ( "name" -- )
  sym-name, get-current >r sym-words set-current create r> set-current ,
  does> >r cv-sync r> skipping? if drop exit then @ >r s-pop t-f1 swap 0 r> t-new s-push ;

' sym-colon sym-always :          ' sym-semicolon sym-always ;
' sym-constant sym-always constant
' cv-decimal sym-always decimal   ' cv-paren sym-always (     ' cv-backslash sym-always \
' sym-if sym: if   ' sym-else sym: else   ' sym-then sym: then   ' sym-exit sym: exit
' sym-loop sym: begin   ' sym-loop sym: while   ' sym-loop sym: repeat
: s-dup ( -- ) s-pop dup s-push s-push ;
: s-drop ( -- ) s-pop drop ;
: s-swap ( -- ) s-pop s-pop >r s-push r> s-push ;
: s-over ( -- ) s-pop s-pop dup s-push swap s-push s-push ;
: s-nip ( -- ) s-pop s-pop drop s-push ;
: s-tuck ( -- ) s-pop s-pop over s-push s-push s-push ;
: s-rot ( -- ) s-pop s-pop s-pop >r s-push s-push r> s-push ;
: s-2dup ( -- ) s-pop s-pop dup s-push over s-push s-push s-push ;
: s-2drop ( -- ) s-drop s-drop ;
: s->r ( -- ) s-pop r-push ;
: s-r> ( -- ) r-pop s-push ;
: s-r@ ( -- ) r-pop dup r-push s-push ;
: s-true ( -- ) t-true s-push ;
: s-false ( -- ) t-flag 0 0 0 t-new s-push ;
: s-not ( -- ) s-pop t-not swap 0 0 t-new s-push ;
create zero-text 1 c, char 0 c,
: s-cmp0 ( c-addr -- ) >r s-pop t-const 0 0 0 t-new t-infix -rot r> t-new s-push ;
create lt-text 1 c, char < c,   create gt-text 1 c, char > c,
create ne-text 2 c, char < c, char > c,
create plus-text 1 c, char + c,  create minus-text 1 c, char - c,
: s-0< ( -- ) lt-text s-cmp0 ;   : s-0> ( -- ) gt-text s-cmp0 ;   : s-0<> ( -- ) ne-text s-cmp0 ;
: s-step ( c-addr -- ) >r s-pop t-const 1 0 0 t-new t-infix -rot r> t-new s-push ;
: s-1+ ( -- ) plus-text s-step ;   : s-1- ( -- ) minus-text s-step ;
' s-dup sym: dup     ' s-drop sym: drop   ' s-swap sym: swap   ' s-over sym: over
' s-nip sym: nip     ' s-tuck sym: tuck   ' s-rot sym: rot     ' s-2dup sym: 2dup
' s-2drop sym: 2drop ' s->r sym: >r       ' s-r> sym: r>       ' s-r@ sym: r@
' s-true sym: true   ' s-false sym: false ' s-not sym: 0=      ' s-0< sym: 0<
' s-0> sym: 0>       ' s-0<> sym: 0<>     ' s-1+ sym: 1+       ' s-1- sym: 1-
infix: +  infix: -  infix: *  infix: /  infix: =  infix: <>  infix: <  infix: >
infix: and  infix: or  infix: xor
func2: mod  func2: rshift  func2: max  func2: min
func1: negate  func1: abs  func1: invert

\ Run a file in this vocabulary.
: sym-run-file ( c-addr u -- outcome )
  sym-words cv-vocab ! ['] sym-lit cv-lit-xt ! ['] sym-call cv-call-xt !
  paths# w-max cells erase cur st-fresh false sym-skip ! cv-run-file ;
