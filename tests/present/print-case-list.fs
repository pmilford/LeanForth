\ The term-printer cases shared by print-cases.fs (golden text) and
\ print-sweep.fs (every fuel level and visit limit). Each case is an xt
\ ( -- t ) building one term, handed to the including file's
\ uni ( xt c-addr u -- ) or, for universe arguments shown, univ. Every
\ term matches the expression of the same name in
\ tests/reference/printer-cases.lean.

\ Shared pieces.
: P ( -- t ) t-prop ;
: lu ( -- l ) s" u" lparam ;
: lv ( -- l ) s" v" lparam ;
: lw ( -- l ) s" w" lparam ;
: fixture-id ( -- )   \ declare fixtureId.{u} : {α : Sort u} → α → α
  lu ssort 0 t-var 1 t-var t-pi s" x" ex. t-pi s" α" im. s" fixtureId" declare ;
: hyg ( c-addr u -- id )   \ the hygienic name n._@.main._hyg.1
  nm s" _@" nm. s" main" nm. s" _hyg" nm. 1 nm# ;
: hyg. ( t kind c-addr u -- t ) hyg swap 2 pick -rot lf-pres-binder! must-ok ;

\ Sorts and universe levels.
:noname P ; s" prop" uni
:noname 1 t-sort ; s" type" uni
:noname 2 t-sort ; s" type-1" uni
:noname lu lv lmax ssort ; s" sort-max" uni
:noname lu lsucc lv lsucc lmax ssort ; s" type-max" uni
:noname lu lv limax ssort ; s" sort-imax" uni
:noname lu lsucc lsucc ssort ; s" type-succ" uni
:noname lu lv lmax lsucc lsucc ssort ; s" type-max-succ" uni
:noname lu lv lw lmax lmax ssort ; s" sort-max-right" uni
:noname lu lv lmax lw lmax ssort ; s" sort-max-left" uni
:noname lu lsucc lv lmax ssort ; s" sort-succ-max" uni

\ Binders: grouping, arrows, ∀, fun.
:noname P  0 t-var 1 t-var t-pi s" proof" ex.  t-pi s" P" im. ; s" identity-type" uni
:noname P  0 t-var 0 t-var t-lam s" proof" ex.  t-lam s" P" im. ; s" identity-value" uni
: A->B ( -- t ) 2 t-var 2 t-var t-pi s" x" ex. ;
:noname P P P  A->B A->B  4 t-var 3 t-var t-pi s" value" ex.
  t-pi s" g" ex. t-pi s" f" ex. t-pi s" C" im. t-pi s" B" im. t-pi s" A" im. ;
  s" composition-type" uni
:noname P P P  A->B A->B  4 t-var  1 t-var 2 t-var 0 t-var t-app t-app  t-lam s" value"
  ex.
  t-lam s" g" ex. t-lam s" f" ex. t-lam s" C" im. t-lam s" B" im. t-lam s" A" im. ;
  s" composition-value" uni
:noname lu lv lmax ssort 0 t-var 1 t-var t-pi s" x" ex. t-pi s" α" im. ; s" poly-type" uni
:noname 1 t-sort 0 t-var 1 t-var t-pi s" x" ex. t-pi s" α" ex. ; s" dep-explicit" uni
:noname P P 1 t-var t-pi s" y" ex. t-pi s" x" ex. ; s" rfc-1834" uni
:noname P 0 t-var 1 t-var t-pi s" h" ex. t-pi s" x" si. ; s" strict" uni
:noname P 0 t-var 1 t-var t-pi s" h" in. t-pi s" α" im. ; s" inst-named" uni
:noname P 0 t-var 1 t-var t-pi lf-binder-instance s" inst" hyg. t-pi s" α" im. ;
  s" inst-anon" uni
:noname P 0 t-var 0 t-var t-lam s" h" in. t-lam s" α" im. ; s" fun-inst-used" uni
:noname P 0 t-var 1 t-var 0 t-var t-lam s" x" ex. t-lam s" h" in. t-lam s" α" im. ;
  s" fun-inst-unused" uni
:noname P P 1 t-var t-lam s" β" si. t-lam s" α" si. ; s" fun-strict" uni
:noname P  0 t-var 1 t-var t-pi s" x" ex.  1 t-var  1 t-var 1 t-var 0 t-var t-app t-app
  t-lam s" x" ex. t-lam s" f" ex. t-lam s" A" im. ; s" nested-app" uni

\ Names restored without capture.
:noname P P 0 t-var t-lam s" x" ex. t-lam s" x" ex. ; s" shadow-fun" uni
:noname P P 1 t-var t-lam s" x" ex. t-lam s" x" ex. ; s" capture-fun" uni
:noname P P 0 t-var t-pi s" x" ex. t-pi s" x" ex. ; s" shadow-pi" uni
:noname P P 1 t-var t-pi s" x" ex. t-pi s" x" ex. ; s" capture-pi" uni
:noname P P P 2 t-var 1 t-var t-app 0 t-var t-app t-pi s" x" ex. t-pi s" x" ex. t-pi s" x"
  ex. ;
  s" capture-twice" uni
:noname P P P 2 t-var 1 t-var t-app 0 t-var t-app t-lam s" x" ex. t-lam s" x_1" ex. t-lam
  s" x" ex. ;
  s" capture-suffix" uni
:noname P 0 t-var t-lam lf-binder-default s" a" hyg. ; s" hygienic-fun" uni
:noname P 0 t-var t-lam dup 0 lf-binder-default lf-pres-binder! must-ok ;
  s" anonymous-fun" uni
:noname P P P P P P  5 t-var 4 t-var t-app 3 t-var t-app 2 t-var t-app 1 t-var t-app 0
  t-var t-app
  t-lam s" proof₁₂" ex. t-lam s" α'" ex. t-lam s" a_b" ex. t-lam s" h_2" ex. t-lam s" x₁"
  ex.
  t-lam s" x'" ex. ; s" name-shapes" uni

\ Parentheses.
: P->P ( -- t ) P P t-pi s" x" ex. ;
:noname P->P P t-pi s" h" ex.  0 t-var  P 0 t-var t-lam s" x" ex.  t-app t-lam s" g" ex. ;
  s" fun-last-arg" uni
:noname P->P P P t-pi s" p" ex. t-pi s" h" ex.  P  1 t-var P 0 t-var t-lam s" x" ex. t-app
  0 t-var t-app t-lam s" p" ex. t-lam s" f" ex. ; s" fun-inner-arg" uni
:noname P  P 0 t-var t-lam s" x" ex. 0 t-var t-app t-lam s" p" ex. ; s" beta-head" uni
\ A fun head's own binders give its parameter kinds: the implicit one hides.
:noname P  P 0 t-var 0 t-var t-lam s" b" ex. t-lam s" a" im.  0 t-var t-app 0 t-var t-app
  t-lam s" p" ex. ; s" fun-head-implicit" uni
:noname P 0 t-var t-pi s" x" ex. P t-pi s" h" ex. ; s" forall-domain" uni
:noname P->P P t-pi s" h" ex. ; s" arrow-domain" uni
:noname 2 t-sort P t-pi s" x" ex. 0 t-var 1 t-sort t-app t-lam s" f" ex. ; s" sort-arg"
  uni
:noname 3 t-sort P t-pi s" x" ex. 0 t-var 2 t-sort t-app t-lam s" f" ex. ; s" type1-arg"
  uni

\ Constants: hidden implicit arguments, @, universe arguments.
: fixture-use ( -- t )   \ fun {P : Prop} (h : P) => fixtureId.{0} P h
  fixture-id P 0 t-var  args{ lzero uarg s" fixtureId" t-const 1 t-var t-app 0 t-var t-app
  t-lam s" h" ex. t-lam s" P" im. ;
' fixture-use s" const-implicit" uni
:noname fixture-id args{ lzero lsucc uarg s" fixtureId" t-const ; s" const-bare" uni
:noname fixture-id args{ lzero lsucc uarg s" fixtureId" t-const P t-app ;
  s" const-partial" uni
:noname P args{ lu uarg s" undeclaredC" t-const 0 t-var t-app t-lam s" y" ex. ;
  s" const-unknown-levels" uni
:noname P args{ s" undeclaredK" t-const 0 t-var t-app t-lam s" y" ex. ; s" const-unknown"
  uni
:noname s" My" nm s" name" nm. s" space" nm. lf-name-generation @ cargs 0 lf-cref-new must
  lf-cterm-new must drop ; s" const-dotted" uni
' fixture-use s" universes-implicit" univ
:noname args{ lu lv lmax uarg lu lsucc uarg lzero uarg s" undeclaredL" t-const ;
  s" universes-list" univ
