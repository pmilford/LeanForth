\ LeanForth's side of tests/front/check_whnf.py (plan FE1c): over the Init
\ slice (tests/front/menv-slice.fs), the same free variables, let
\ variables and metavariables as tests/front/whnf-cases.lean, and one
\ line per case: the term lf-whnf-core gives, as an S-expression ((app F
\ A), (lam T B), (let T V B), #i, Name.{levels}, x, ?n), or what
\ lf-whnf-stuck finds (?n or none); "unsupported" or the outcome's name
\ otherwise. Test support only: printing recurses on the host stack,
\ which the small cases allow.

require ./menv-slice.fs
require ../../src/front/whnf.fs
menv-load lf-mctx-reset lf-lctx-reset

: must ( x flag -- x ) 0= abort" whnf-cases: no room" ;
: made ( x outcome -- x ) ok? 0= abort" whnf-cases: not made" ;
: app ( f a -- t ) lf-term-app must ;
: lam ( type body -- t ) lf-term-lam must ;
: bv ( i -- t ) lf-term-bvar must ;
: let ( type value body -- t ) rot swap lam 0 lf-let-make must ;
0 constant l0
l0 lf-level-succ must constant lv1

\ Constants: cn ( l1 .. lk k c-addr u -- term ).
create lv-pairs 8 cells allot
: lv! ( level i -- ) 2* cells lv-pairs + >r dup lf-level-identity drop swap r> 2! ;
variable cn-k  variable cn-name
: cn ( l1 .. lk k c-addr u -- term )
  menv-name cn-name ! dup cn-k ! 0 ?do cn-k @ 1- i - lv! loop
  cn-name @ lf-name-generation @ lv-pairs cn-k @ lf-cref-new must lf-cterm-new must drop ;
0 s" Nat" cn constant nat
0 s" Nat.zero" cn constant zero
0 s" Nat.succ" cn constant succ
: rec ( -- t ) lv1 1 s" Nat.rec" cn ;

\ Free variables, let variables and metavariables, with their names.
create names 32 cells allot  variable #names
: named ( term c -- ) #names @ 2* cells names + tuck cell+ ! ! 1 #names +! ;
: local ( type c -- fvar ) swap lf-lctx-local made tuck swap named ;
nat char m local constant fm   nat char z local constant fz   nat char s local constant fs
nat char k local constant fk   nat char x local constant fx   nat char a local constant fa
nat char b local constant fb
l0 l0 2 s" Prod" cn nat app nat app char p local constant fp
nat fs 0 bv app lam constant sfun
nat sfun lf-lctx-let made constant fg  fg char g named
nat mv-natural lf-mvar-new made constant ?n  ?n char n named
nat mv-natural lf-mvar-new made constant ?h  ?h char h named
nat mv-natural lf-mvar-new made constant ?f  ?f char f named
0 ?f sfun lf-mvar-assign made drop

: case-name ( term -- c true | false )
  #names @ 0 ?do dup i 2* cells names + @ = if drop i 2* cells names + cell+ @ true unloop exit then
  loop drop false ;
: .nm ( name -- ) dup lf-name-prefix@ ?dup if recurse ." ." then lf-name-text type ;
: .lv ( level -- )
  0 swap begin dup lf-level-tag@ lf-level-tag-succ = while lf-level-first@ swap 1+ swap repeat
  lf-level-tag@ lf-level-tag-zero = if 0 .r else drop ." ?l" then ;
: .levels ( slot -- )
  lf-cref-pairs 0 ?do i if ." ," then dup i lf-cref-pair@ drop .lv loop drop ;
: .const ( t -- ) lf-term-first@ lf-cref-slot dup lf-cref-name@ drop .nm ." .{" .levels ." }" ;
: .leaf ( t -- )
  dup case-name 0= if drop ." ??" exit then
  over lf-term-tag@ lf-tag-mvar = if ." ?" then emit drop ;
defer .t
: .pair ( t c-addr u -- ) ." (" type space dup lf-term-first@ .t space lf-term-second@ .t ." )" ;
: .let ( t -- )
  ." (let " dup lf-let-type .t space dup lf-let-value .t space lf-let-body .t ." )" ;
:noname ( t -- )
  dup lf-let? if .let exit then
  dup lf-term-tag@ case
    lf-tag-app of s" app" .pair endof  lf-tag-lam of s" lam" .pair endof
    lf-tag-pi of s" pi" .pair endof  lf-tag-bvar of ." #" lf-term-first@ 0 .r endof
    lf-tag-constant of .const endof  >r .leaf r> endcase ; is .t
: .outcome ( outcome -- ) dup outcome-unsupported = if drop ." unsupported" else outcome-text type then ;
: whnf-run ( term -- ) lf-whnf-core dup ok? if drop .t else nip .outcome then cr ;
: stuck-run ( term -- )
  lf-whnf-stuck dup ok? 0= if nip .outcome cr exit then
  drop if .t else ." none" then cr ;
