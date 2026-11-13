\ The front end's Meta answers printed for tests/front/check_meta.py,
\ which compares them with pinned Lean's on the same cases (plan FE1c).
\ It runs the code the script generates: one line per case, the answer of
\ lf-meta-level-defeq (true, false, unsupported) and each named level
\ metavariable's instantiated value, or the term lf-meta-instantiate1 or
\ lf-meta-head-beta gives, as an S-expression ((app F A), (lam T B),
\ (pi T B), #i, Prop, x, y, ?m). Test support only: printing recurses on
\ the host stack, which the small cases allow.
require ../../src/main.fs
require ../../src/front/level-defeq.fs
require ../../src/front/instantiate.fs
require ../../src/front/level-params.fs

lf-author-begin
: must ( x flag -- x ) 0= abort" meta-cases: no room" ;
: .k ( n -- ) 0 .r ;

\ Levels and the case's named metavariables (up to 8).
0 constant zero
: lsucc ( l -- l' ) lf-level-succ must ;
: lmax ( a b -- l ) lf-level-max must ;
101 lf-level-param must constant u
102 lf-level-param must constant v
create mv-names 16 cells allot
variable #mv
: mv ( i -- leaf ) 2* cells mv-names + @ ;
: mv-char ( i -- c ) 2* cells mv-names + cell+ @ ;
: add-mv ( c -- ) lf-level-mvar-new ok? 0= abort" meta-cases: mvar"
  #mv @ 2* cells mv-names + tuck ! cell+ ! 1 #mv +! ;
: name? ( leaf -- c true | false )
  #mv @ 0 ?do dup i mv = if drop i mv-char true unloop exit then loop drop false ;
: .mv ( leaf -- ) name? if emit else ." ?_" then ;
defer .lev
: .lmax ( l -- ) ." (max " dup lf-level-first@ .lev space lf-level-second@ .lev ." )" ;
: .limax ( l -- ) ." (imax " dup lf-level-first@ .lev space lf-level-second@ .lev ." )" ;
: .lparam ( l -- ) lf-level-first@ 101 = if ." u" else ." v" then ;
: .lbase ( base -- )
  dup lf-level-tag@ case
    lf-level-tag-param of .lparam endof
    lf-level-tag-mvar of .mv endof
    lf-level-tag-max of .lmax endof
    lf-level-tag-imax of .limax endof
    >r drop ." ??" r> endcase ;
: (.lev) ( l -- )
  ld-offset over lf-level-tag@ lf-level-tag-zero = if nip .k exit then
  swap .lbase ?dup if ." +" .k then ;
' (.lev) is .lev
: .answer ( flag outcome -- )
  dup ok? if drop if ." true" else ." false" then exit then
  nip outcome-unsupported = if ." unsupported" else ." failed" then ;
: .values ( -- )
  #mv @ 0 ?do space i mv-char emit ." =" i mv lf-level-instantiate-mvars drop .lev loop ;
: level-case ( -- ) lf-mctx-reset 0 #mv ! ;
: level-run ( l r -- ) lf-meta-level-defeq .answer .values cr ;

\ Terms: Prop, two free variables x y : Prop, a metavariable ?m : Prop.
: app ( f a -- t ) lf-term-app must ;
: lam ( type body -- t ) lf-term-lam must ;
: tpi ( type body -- t ) lf-term-pi must ;
: bv ( i -- t ) lf-term-bvar must ;
: made ( x outcome -- x ) ok? 0= abort" meta-cases: not made" ;
: room ( outcome -- ) ok? 0= abort" meta-cases: no room" ;
100000 lf-term-capacity! room  100000 lf-level-capacity! room
0 lf-term-sort must constant prop
lf-mctx-reset lf-lctx-reset
prop lf-lctx-local made constant fx
prop lf-lctx-local made constant fy
prop mv-natural lf-mvar-new made constant hole
defer .t
: .pair ( t c-addr u -- ) ." (" type space dup lf-term-first@ .t space lf-term-second@ .t ." )" ;
: .fvar ( t -- ) dup fx = if drop ." x" exit then fy = if ." y" else ." ?f" then ;
: (.t) ( t -- )
  dup lf-term-tag@ case
    lf-tag-app of s" app" .pair endof  lf-tag-lam of s" lam" .pair endof
    lf-tag-pi of s" pi" .pair endof  lf-tag-bvar of ." #" lf-term-first@ .k endof
    lf-tag-sort of drop ." Prop" endof  lf-tag-mvar of drop ." ?m" endof
    lf-tag-fvar of .fvar endof  >r drop ." ??" r> endcase ;
' (.t) is .t
: .term ( term outcome -- )
  dup ok? if drop .t else nip outcome-unsupported = if ." unsupported" else ." failed" then then ;
: inst1-run ( body value -- ) lf-meta-instantiate1 .term cr ;
create xs-buf 8 cells allot
: xs ( x0 .. xk-1 k -- addr k )
  dup 0 ?do dup 1- i - cells xs-buf + rot swap ! loop xs-buf swap ;
: abst-run ( term addr n -- ) lf-meta-abstract .term cr ;

\ Universe parameters: Sort l and C.{l1, l2}; the names and levels of a
\ case in two buffers.
: sort-of ( level -- term ) dup lf-level-identity drop lf-hterm-sort must drop ;
create cpairs 4 cells allot
: cpair! ( level i -- ) 2* cells cpairs + >r dup lf-level-identity drop swap r> 2! ;
0 s" C" lf-name-str drop constant c-name
: const2 ( l1 l2 -- term )
  1 cpair! 0 cpair! c-name lf-name-generation @ cpairs 2 lf-cref-new must
  lf-cterm-new must drop ;
: .sort ( t -- ) lf-term-first@ dup 0= if drop ." Prop" else ." Sort " .lev then ;
: .const ( t -- )
  ." C.{" lf-term-first@ lf-cref-slot lf-cref-pairs 0 ?do
    i if ." ," then dup i lf-cref-pair@ drop .lev loop drop ." }" ;
:noname ( t -- )
  dup lf-term-tag@ case lf-tag-symbolic-sort of .sort endof
    lf-tag-constant of .const endof  >r (.t) r> endcase ; is .t
create names-buf 4 cells allot  create levels-buf 4 cells allot
: fill ( x0 .. xk-1 k buf -- ) over 0 ?do over i - 1- cells over + >r rot r> ! loop 2drop ;
: params ( n0 .. nk-1 k -- ) names-buf fill ;
: args ( l0 .. lk-1 k -- ) levels-buf fill ;
: .level ( level outcome -- )
  dup ok? if drop .lev else nip outcome-unsupported = if ." unsupported" else ." failed" then then ;
: lps-run ( level k -- ) >r names-buf levels-buf r> lf-meta-level-params .level cr ;
: limax ( a b -- l ) lf-level-imax must ;
: max-run ( u v -- ) lf-meta-max .level cr ;
: imax-run ( u v -- ) lf-meta-imax .level cr ;
: ilp-run ( term k -- ) >r names-buf levels-buf r> lf-meta-instantiate-level-params .term cr ;
: beta-run ( term -- ) lf-meta-head-beta .term cr ;
