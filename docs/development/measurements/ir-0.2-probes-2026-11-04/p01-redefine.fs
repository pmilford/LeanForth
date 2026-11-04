\ IR 0.2 probe 1 (ADR 0019 Amendment 1): redefinition and early binding
\ in plain Gforth. Each line prints "label: result", so the outputs of
\ Gforth 1.0.0 and 0.7.3 can be compared; Gforth's warnings ("redefined
\ pf") go to standard error. Run from this folder:
\   timeout -k 5 30 gforth p01-redefine.fs </dev/null
' . constant dot-xt
: show ( n -- ) dot-xt execute ;
: label ( c-addr u -- ) cr type ." : " ;

\ 1. Early binding: pg, compiled before the redefinition, keeps the old pf.
: pf 1 ;  : pg pf ;  : pf 2 ;  : ph pf ;
s" early binding: pg ph pf (expect 1 2 2)" label pg show ph show pf show

\ 2. The name is hidden until ; so the body's pk is the previous version.
: pk 10 ;  : pk pk 1+ ;  : pk pk 1+ ;
s" old version inside the new one (expect 12)" label pk show

\ 3. A name used in its own first definition is not found. A THROW from
\ inside a definition leaves Forth compiling, so probe-try ends that.
: leave-compiling ( -- ) postpone [ ;
: probe-try ( c-addr u -- code )
  ['] evaluate catch dup if nip nip then leave-compiling ;
s" : pq pq ;" probe-try
s" self call with no earlier version: THROW code (expect -13)" label show

\ 4. Case: Cw, cw and CW are one name; the latest wins.
: Cw 1 ;  : cw 2 ;  : CW 3 ;
s" case: versions of one name (expect 3)" label cw show

\ 5. Constants redefined, and a word redefined as a constant.
1 constant kk  : gk kk ;  2 constant kk  : hk kk ;
s" constant versions (expect 1 2)" label gk show hk show
: wc 7 ;  : uw wc ;  8 constant wc  : vw wc ;
s" a word, then a constant of that name (expect 7 8)" label uw show vw show

\ 6. RECURSE inside a redefinition calls the definition being made; the
\ plain name inside it calls the previous version.
: pr 100 ;
: pr ( n -- m ) dup 0> if 1- recurse then ;
s" RECURSE in the second pr: 3 pr (expect 0)" label 3 pr show
: pt 100 ;
: pt ( n -- m ) dup 0> if drop pt then ;
s" plain pt inside the second pt: 3 pt (expect 100)" label 3 pt show

\ 7. SEARCH-WORDLIST in a word list holding two headers of one name, in
\ two cases of letters: the newer is found, and the older's xt still runs.
wordlist constant wl
variable old-xt  variable new-xt
get-order wl swap 1+ set-order  get-current wl set-current
: dupname 1 ;  : DUPNAME 2 ;
: two-a 5 ;  ' two-a old-xt !  : two-a 6 ;  ' two-a new-xt !
set-current previous
s" dupname" wl search-wordlist
s" SEARCH-WORDLIST finds the newer (expect 2, then -1: not immediate)" label
swap execute show show
s" kept xts of both versions (expect 6 5)" label
new-xt @ execute show old-xt @ execute show

\ 8. A standard word redefined: code compiled before keeps the host's
\ word, code compiled after binds to the file's.
: early-dot ( n -- ) . ;
: . ( n -- ) drop ;
: late-dot ( n -- ) . ;
s" redefined dot: 5 early-dot 6 late-dot (expect 5 printed, then depth 0)" label
5 early-dot  6 late-dot  depth show
: dup ( a b -- a b a ) over ;
: late-dup ( a b -- a b a ) dup ;
s" redefined dup as over: 1 2 late-dup (expect 1 2 1, top first)" label
1 2 late-dup show show show
cr bye
