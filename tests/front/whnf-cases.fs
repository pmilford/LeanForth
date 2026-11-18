\ LeanForth's side of tests/front/check_whnf.py (plan FE1c): over the Init
\ slice (tests/front/menv-slice.fs), the same free variables, let
\ variables and metavariables as tests/front/whnf-cases.lean, and one
\ line per case: the term lf-whnf-core gives, as an S-expression ((app F
\ A), (lam T B), (let T V B), #i, Name.{levels}, x, ?n), or what
\ lf-whnf-stuck finds (?n or none), or the type lf-infer gives (Sort n
\ for a sort); "unsupported" or the outcome's name
\ otherwise. Test support only: printing recurses on the host stack,
\ which the small cases allow.

require ./menv-slice.fs
require ../../src/front/whnf.fs
require ../../src/front/infer.fs
menv-load lf-mctx-reset lf-lctx-reset

: must ( x flag -- x ) 0= abort" whnf-cases: no room" ;
: made ( x outcome -- x ) ok? 0= abort" whnf-cases: not made" ;
: app ( f a -- t ) lf-term-app must ;
: lam ( type body -- t ) lf-term-lam must ;
: bv ( i -- t ) lf-term-bvar must ;
: let ( type value body -- t ) rot swap lam 0 lf-let-make must ;
: sort ( level -- t ) dup lf-level-identity must lf-hterm-sort must drop ;
: tpi ( domain body -- t ) lf-term-pi must ;
0 constant l0
l0 lf-level-succ must constant lv1
lv1 lf-level-succ must constant lv2

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
create names 64 cells allot  variable #names   \ 32 names (defeq-cases.fs adds some)
: named ( term c -- ) #names @ 2* cells names + tuck cell+ ! ! 1 #names +! ;
\ Each free variable also enters the current local context (Lean's
\ withLocalDecl), which the metavariables made after it see.
: in-view ( fvar -- fvar )
  dup 0 0 lf-local-new made lf-mctx-view swap lf-view-push made lf-mctx-view! ;
: local ( type c -- fvar ) swap lf-lctx-local made in-view tuck swap named ;
nat char m local constant fm   nat char z local constant fz   nat char s local constant fs
nat char k local constant fk   nat char x local constant fx   nat char a local constant fa
nat char b local constant fb
l0 l0 2 s" Prod" cn nat app nat app char p local constant fp
nat fs 0 bv app lam constant sfun
nat sfun lf-lctx-let made in-view constant fg  fg char g named
nat mv-natural lf-mvar-new made constant ?n  ?n char n named
nat mv-natural lf-mvar-new made constant ?h  ?h char h named
nat mv-natural lf-mvar-new made constant ?f  ?f char f named
0 ?f sfun lf-mvar-assign made drop
nat mv-natural lf-mvar-new made constant ?q  ?q char q named

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
: nat-lit ( u -- t ) lf-hterm-cell 0= abort" whnf-cases: not made" drop ;
\ A natural literal as Lean's sx prints it (its fallback, ?? and the value).
: .lit ( t -- ) ." ?? " lf-lit-cell 0 .r ;
: .leaf ( t -- )
  dup lf-lit-leaf? over lf-lit-small? and if .lit exit then
  dup case-name 0= if drop ." ??" exit then
  over lf-term-tag@ lf-tag-mvar = if ." ?" then emit drop ;
defer .t
: .pair ( t c-addr u -- ) ." (" type space dup lf-term-first@ .t space lf-term-second@ .t ." )" ;
: .let ( t -- )
  ." (let " dup lf-let-type .t space dup lf-let-value .t space lf-let-body .t ." )" ;
: .proj ( t -- ) ." (proj " dup lf-proj-leaf lf-proj-idx 0 .r space lf-proj-struct .t ." )" ;
: projn ( e i c-addr u -- t ) menv-name swap lf-proj-of made ;
: proj ( e i -- t ) s" Prod" projn ;
:noname ( t -- )
  dup lf-let? if .let exit then
  dup lf-proj? if .proj exit then
  dup lf-term-tag@ lf-tag-symbolic-sort = if ." Sort " lf-term-first@ .lv exit then
  dup lf-term-tag@ case
    lf-tag-app of s" app" .pair endof  lf-tag-lam of s" lam" .pair endof
    lf-tag-pi of s" pi" .pair endof  lf-tag-bvar of ." #" lf-term-first@ 0 .r endof
    lf-tag-constant of .const endof  >r .leaf r> endcase ; is .t
: .outcome ( outcome -- ) dup outcome-unsupported = if drop ." unsupported" else outcome-text type then ;
: whnf-run ( term -- ) lf-whnf-core dup ok? if drop .t else nip .outcome then cr ;
: infer-run ( term -- ) lf-infer dup ok? if drop .t else nip .outcome then cr ;
create rxs-buf 8 cells allot
: rxs ( x0 .. xn-1 n -- addr n ) dup 0 ?do dup 1- i - cells rxs-buf + rot swap ! loop rxs-buf swap ;
: ibeta-run ( body addr m -- )
  lf-meta-instantiate-rev-beta dup ok? if drop .t else nip .outcome then cr ;
\ tests/front/check_unfold.py's term cases: unfoldDefinition?
\ (lf-meta-unfold: "1" and the term, or "0" for none) and whnf
\ (lf-meta-whnf) at a transparency.
: at-mode ( x mode xt -- i*x ) lf-defeq-mode >r swap lf-defeq-mode! execute r> lf-defeq-mode! ;
: unfold-run ( term mode -- )
  ['] lf-meta-unfold at-mode dup ok? 0= if nip nip .outcome cr exit then drop
  if ." 1 " .t else drop ." 0" then cr ;
: mwhnf-run ( term mode -- )
  ['] lf-meta-whnf at-mode dup ok? if drop .t else nip .outcome then cr ;
: stuck-run ( term -- )
  lf-whnf-stuck dup ok? 0= if nip .outcome cr exit then
  drop if .t else ." none" then cr ;
