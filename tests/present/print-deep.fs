\ Deep prints (plan task 6.2.0): the term printer, its Forth mode and
\ level printing keep their pending work on the print's frames, an
\ explicit stack that grows on the heap, so terms and levels 2,000 and
\ 10,000 deep print in the same host-stack cells as shallow ones (painted
\ here, on Gforth 0.7.3 and 1.0 alike), and a print whose stack the heap
\ will not grow is full, never a host-stack overflow. The terms are those
\ of tests/reference/depth-terms.lean: a lambda chain fun P h1 ... hn => h1
\ (binders n deep, each hk : P) and an application chain
\ fun P h => (fun x => x) ((fun x => x) (... h)) (applications n deep);
\ and a level alternating max and imax n deep. Test-only.
include ../support/heap-watch.fs
require ./build.fs
require ../../src/present/print-forth.fs
require ../support/stack-paint.fs

\ A sink that counts the bytes and keeps the first and the last 64.
64 constant window
create head-text window allot   variable head-len
create ring window allot        variable out-len
create tail-text window allot
: head+ ( c-addr u -- )
  window head-len @ - min tuck head-text head-len @ + swap move head-len +! ;
: ring-c! ( char -- ) out-len @ window mod ring + c! 1 out-len +! ;
: count-sink ( c-addr u -- ) 2dup head+ over + swap ?do i c@ ring-c! loop ;
: counting ( options -- ) 0 head-len ! 0 out-len ! ['] count-sink swap lf-print-setup ;
: tail-c ( i u -- char ) out-len @ swap - + window mod ring + c@ ;
: tail ( u -- c-addr u ) dup 0 ?do i over tail-c tail-text i + c! loop tail-text swap ;
: starts? ( c-addr u -- flag ) head-text over compare 0= ;
: ends? ( c-addr u -- flag ) dup tail compare 0= ;
\ A text followed by k closing parentheses (at most a window in all).
create expected window allot
: then-closing ( c-addr u k -- c-addr' u' )
  >r tuck expected swap move expected over + r@ [char] ) fill r> + expected swap ;

\ The terms. hk is the name of binder k.
: h-name ( k -- id ) 0 <# #s [char] h hold #> nm ;
: id-named ( t id -- t ) over swap lf-binder-default lf-pres-binder! must-ok ;
: lam-chain ( n -- t )
  dup 1- t-var 1 rot do i 1- t-var swap t-lam i h-name id-named -1 +loop
  t-prop swap t-lam s" P" ex. ;
: app-chain ( n -- t )
  1 t-var 0 t-var t-lam s" x" ex. 0 t-var rot 0 ?do over swap t-app loop nip
  0 t-var swap t-lam s" h" ex. t-prop swap t-lam s" P" ex. ;
\ max u (imax u (max u ... u)), n operators over u, the outermost a max.
: level-op ( a b odd? -- l ) if lmax else limax then ;
: level-chain ( n -- l )
  s" u" lparam dup rot 1 swap do over swap i 1 and level-op -1 +loop nip ;

\ Sizes. fun P h1 ... hn ↦ h1 has 12 + 2n bytes and the digits of 1 .. n
\ (↦ is 3 bytes); the application chain 12 + 14n bytes of fun P h ↦ and
\ (fun x ↦ x) heads, n - 1 pairs of parentheses and h: 16n + 11; the level
\ its keywords, 3 bytes of " u " per operator but the last ("u u"),
\ 2(n - 1) parentheses: 3 per max and 4 per imax, 5n - 1 more.
: digits ( n -- k ) 0 swap begin swap 1+ swap 10 / ?dup 0= until ;
: digits-to ( n -- k ) 0 swap 1+ 1 ?do i digits + loop ;
: lam-size ( n -- u ) dup 2* swap digits-to + 12 + ;
: app-size ( n -- u ) 16 * 11 + ;
: level-size ( n -- u ) dup 2/ 7 * over 1 and 3 * + swap 5 * + 1- ;

\ The prints, each with ample fuel, painted (return cells, data cells).
10000000 constant deep-fuel
variable the-term   variable result
: print-it ( -- ) the-term @ deep-fuel lf-print-term result ! ;
: forth-it ( -- ) the-term @ deep-fuel lf-print-forth-term result ! ;
: level-it ( -- ) the-term @ deep-fuel lf-print-level result ! ;
: painted ( t xt -- return-cells data-cells )
  swap the-term ! 0 counting stack-painted ;
: at-most ( n limit -- flag ) > 0= ;
: near? ( r1 d1 r2 d2 -- flag ) rot - abs 4 at-most >r - abs 4 at-most r> and ;

32768 lf-term-capacity! must-ok   16384 lf-name-capacity! must-ok
32768 lf-level-capacity! must-ok
fresh

\ Shallow, 31 deep: the cells to compare with.
: app-start ( -- c-addr u ) s" fun P h ↦ (fun x ↦ x) ((fun x ↦ x) (" ;
T{ 31 lam-chain ' print-it painted 2constant lam-31 result @ -> outcome-ok }T
T{ out-len @ s" fun P h1 h2 h3 h4" starts? s" h31 ↦ h1" ends? -> 31 lam-size true true }T
T{ 31 app-chain ' print-it painted 2constant app-31 result @ -> outcome-ok }T
T{ out-len @ app-start starts? s" x) h" 30 then-closing ends? -> 31 app-size true true }T
T{ 31 level-chain ' level-it painted 2constant level-31 result @ -> outcome-ok }T
T{ out-len @ s" max u (imax u (max u (" starts? s" max u u" 30 then-closing ends?
  -> 31 level-size true true }T

\ A stack the heap will not grow: the print that needs more room than any
\ before it is full, and leaves the printer idle; with the heap's room it
\ prints.
fresh
T{ 2000 app-chain the-term ! 0 counting 1 heap-refusals ! the-term @ deep-fuel lf-print-term
  heap-refusals @ lf-pp-busy? -> outcome-full 0 false }T
T{ 0 counting the-term @ deep-fuel lf-print-term out-len @ -> outcome-ok 2000 app-size }T

\ 2,000 and 10,000 deep, in the cells of 31.
: deep ( n -- )
  fresh dup lam-chain ['] print-it painted lam-31 near? result @
  rot dup lam-size out-len @ = >r
  fresh dup app-chain ['] print-it painted app-31 near? result @ rot app-size out-len @ = r> and ;
T{ 2000 deep -> true outcome-ok true outcome-ok true }T
T{ 10000 deep -> true outcome-ok true outcome-ok true }T
T{ app-start starts? s" " window then-closing ends? -> true true }T
\ The Forth mode and a level, 10,000 deep.
T{ fresh 31 app-chain ' forth-it painted 2constant forth-31 result @ -> outcome-ok }T
T{ fresh 10000 app-chain ' forth-it painted forth-31 near? result @ -> true outcome-ok }T
T{ fresh 10000 level-chain ' level-it painted level-31 near? result @ -> true outcome-ok }T
T{ out-len @ s" max u (imax u (max u (" starts? -> 10000 level-size true }T
\ The lambda chain's type, ∀ (P : Prop), P → ... → P, nests n arrows; its
\ print costs fuel quadratic in n (each Π asks Lean's quick test whether
\ it is a proposition, which walks the rest of the chain), so 2,000 deep.
: pi-chain ( n -- t )
  dup t-var 1 rot do i 1- t-var swap t-pi -1 +loop t-prop swap t-pi s" P" ex. ;
: statement-it ( -- ) the-term @ deep-fuel lf-print-statement result ! ;
: pi-size ( n -- u ) 6 * 17 + ;
T{ fresh 31 pi-chain ' statement-it painted 2constant pi-31 result @ out-len @
  -> outcome-ok 31 pi-size }T
T{ s" ∀ (P : Prop), P → P → P" starts? s" P → P → P" ends? -> true true }T
T{ fresh 2000 pi-chain ' statement-it painted pi-31 near? result @ out-len @
  -> true outcome-ok 2000 pi-size }T
lf-term-default lf-term-capacity! drop   lf-name-default lf-name-capacity! drop
lf-level-default lf-level-capacity! drop
bye
