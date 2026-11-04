\ Throwaway prototype for ADR 0019's "mode shift" question: a third
\ interpreter state, portable to Gforth 0.7.3 and 1.0. No alias words: the
\ words are Forth's own (DUP is FORTH-WORDLIST's DUP, found by
\ SEARCH-WORDLIST), and each has, beside its interpretation and
\ compilation semantics, *verification semantics*, kept in a table keyed
\ by the word's execution token. In verification state the text
\ interpreter performs those, as it performs compilation semantics in
\ compile state. A word without verification semantics is refused, and
\ so is a standard word redefined before the run (its token is not in the
\ table). Numbers are never converted by the host: a token that is no word
\ must be a plain decimal. Hosts without recognizers have no hook into
\ their own interpreter, so the verification-state interpreter is the
\ loop below, run inside the line as Forth's input source (PARSE-NAME and
\ PARSE are the host's). Reuses cv.fs for output, frames and definitions.
\ Usage: gforth cv.fs ms.fs -e 's" FILE" ms-run-file ...'

\ ---------------------------------------------------------------- semantics
\ Verification semantics: host word -> kind and datum (a primitive's
\ record from cv.fs, or the xt of an action). A host word is known by the
\ execution token SEARCH-WORDLIST gives and its name: Gforth 0.7.3 gives
\ every compile-only word (IF, THEN, ; ...) one shared token, so the token
\ alone does not tell them apart; Forth-2012 has no name tokens.
64 constant vt-max
create vt-xt vt-max cells allot  create vt-kind vt-max cells allot
create vt-x vt-max cells allot   create vt-name vt-max cells allot  variable vt#
0 constant v-prim  1 constant v-action
: host ( c-addr u -- xt ) forth-wordlist search-wordlist 0= abort" ms: no host word" ;
: name, ( c-addr u -- c-addr' ) here >r dup c, here swap dup allot move align r> ;
: vt! ( c-addr u xt kind x -- )
  vt# @ vt-max = abort" ms: table full"
  vt# @ >r r@ cells vt-x + ! r@ cells vt-kind + ! r@ cells vt-xt + ! name,
  r> cells vt-name + ! 1 vt# +! ;
create folded 32 allot  variable folded#  variable want-xt
: fold! ( c-addr u -- ) 31 min dup folded# ! folded swap move folded folded# @ cv-fold ;
: vt-same? ( i -- flag )
  dup cells vt-xt + @ want-xt @ = if cells vt-name + @ count folded folded# @ compare 0=
  else drop false then ;
: vt-find ( xt c-addr u -- i true | false )
  fold! want-xt ! vt# @ 0 ?do i vt-same? if i true unloop exit then loop false ;
\ "verifies NAME": NAME's verification semantics are to execute action.
: verifies ( action "name" -- ) >r parse-name 2dup host v-action r> vt! ;
\ "prim NAME": NAME writes "prim NAME" (with cv.fs's record of it).
: prim ( "name" -- )
  parse-name 2dup 2dup host >r cv-words search-wordlist 0= abort" ms: no record" >body
  r> v-prim rot vt! ;
: ms-backslash ( -- ) source nip >in ! ;

' cv-colon verifies :         ' cv-semicolon verifies ;
' cv-constant verifies constant   ' cv-decimal verifies decimal
' cv-paren verifies (         ' ms-backslash verifies \
' cv-if verifies if    ' cv-else verifies else    ' cv-then verifies then
' cv-begin verifies begin   ' cv-while verifies while   ' cv-repeat verifies repeat
' cv-exit verifies exit
prim dup  prim drop  prim swap  prim over  prim nip  prim tuck  prim rot  prim 2dup
prim 2drop  prim >r  prim r>  prim r@  prim +  prim -  prim *  prim /  prim mod
prim negate  prim abs  prim 1+  prim 1-  prim =  prim <>  prim <  prim >  prim 0=
prim 0<>  prim 0<  prim 0>  prim and  prim or  prim xor  prim invert  prim rshift
prim max  prim min  prim true  prim false

\ ---------------------------------------------------------------- the state
: ms-perform ( i -- )
  dup cells vt-x + @ swap cells vt-kind + @ v-prim = if cv-prim else execute then ;
\ A host word without verification semantics: a standard word outside IR
\ 0.1 (cv.fs reserves those names), or any other word.
\ Whether the name just looked up (folded) has verification semantics
\ under another token: the standard word was redefined before the run.
: vt-named? ( -- flag )
  false vt# @ 0 ?do i cells vt-name + @ count folded folded# @ compare 0= or loop ;
: ms-host ( c-addr u xt -- )
  >r 2dup r> -rot vt-find if nip nip ms-perform exit then
  vt-named? if 2drop why-replaced cv-unsupported! then
  cv-words search-wordlist if drop why-not-ir else why-unknown then cv-unsupported! ;
\ One token in verification state: the file's own words first, then
\ Forth's, as Forth finds names before numbers; else a plain decimal.
: ms-token ( c-addr u -- )
  over cv-line-addr @ - cv-tok ! dup cv-tok# !
  2dup cv-prog @ search-wordlist if nip nip >body cv-call exit then
  2dup forth-wordlist search-wordlist if ms-host exit then
  cv-literal? if cv-lit exit then why-unknown cv-unsupported! ;
wordlist constant ms-entry
get-current ms-entry set-current
\ The verification-state interpreter, for the rest of the input source.
: lf-verify-line ( -- ) begin parse-name dup while ms-token repeat 2drop ;
set-current

\ ---------------------------------------------------------------- runner
\ Each line runs as "lf-verify-line LINE", so that Forth's input source
\ is the line: the host's PARSE-NAME and PARSE read it, and >IN moves.
create ms-buf 160 allot
s" lf-verify-line " nip constant ms-prefix#
: ms-run-line ( c-addr u -- )
  1 cv-line# +! 0 cv-out# !
  dup 128 < 0= if 2drop s" " 0 why-unreadable cv-invalid cv-fail then
  s" lf-verify-line " ms-buf swap move
  dup cv-line-len ! ms-buf ms-prefix# + dup cv-line-addr ! swap move cv-check-chars
  ms-buf ms-prefix# cv-line-len @ + evaluate
  depth cv-base @ <> if s" " 0 why-interrupted cv-invalid cv-fail then ;
: ms-lines ( -- )
  begin cv-rest 2@ nip while cv-split if cv-cr then ms-run-line repeat cv-end-of-text ;
: ms-caught ( code -- )
  dup cv-throw = if drop exit then drop s" " 0 why-interrupted cv-invalid cv-report ;
\ Run text c-addr u in verification state, writing IR for path c-addr2 u2.
: ms-run ( c-addr u c-addr2 u2 -- outcome )
  cv-reset cv-quiet @ if 2drop else ." lf-ir 0.1" cr ." source " type cr then cv-rest 2!
  state @ if s" " 0 why-compiling cv-invalid cv-report cv-outcome @ exit then
  cv-save ms-entry 1 set-order decimal depth cv-base ! ms-prefix# cv-in-offset !
  ['] ms-lines catch ?dup if ms-caught then cv-restore 0 cv-in-offset ! cv-outcome @ ;
: ms-run-file ( c-addr u -- outcome )
  2dup cv-slurp 0= if cv-reset ." lf-ir 0.1" cr ." source " type cr
    s" " 0 why-unreadable cv-invalid cv-report cv-outcome @ exit then
  2swap ms-run ;
