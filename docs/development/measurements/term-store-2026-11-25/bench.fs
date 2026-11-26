\ Term-store micro-benchmarks (docs/design/TERM_STORE.md, 2026-11-25).
\ The same three operations as bench.c, on a 16-byte node (tag, first,
\ second, data: 32-bit fields) with a hash table whose slot keeps the
\ 32-bit hash beside the index plus one:
\   chase  follow random children down a random DAG, reading tag, data
\          and one child per step (a walk's reads and its closed test);
\   cons   hash-cons app(a, b) for random a, b (found or appended);
\   inst   instantiate bound variable 0 in a random tree, skipping closed
\          subterms by the data word, rebuilding with cons (recursive).
\ Each in up to four forms: cur (LeanForth's own words, src/core/terms.fs,
\ store nodes only), col (one colon word per field), raw (the field reads
\ written out in the step: what a macro or an inlined word gives), and C.
\ Gforth 1.0 (ul@, l!). Usage: gforth-fast bench.fs -e "all bye"
require ../../../../src/lib/lib.fs
require ../../../../src/core/terms.fs
only forth definitions

: ms. ( us -- ) 0 <# # # # [char] . hold #s #> type ."  ms" ;
: timed ( xt -- ) utime drop >r execute utime drop r> - ms. ;
: lcg ( x -- x' ) 1103515245 * 12345 + $FFFFFFFF and ;

\ ---- the raw store --------------------------------------------------------
0 value nbase   0 value ncount   0 value nmask   0 value acc
: node ( r -- addr ) 4 lshift nbase + ;
: t-tag ( r -- tag ) node ul@ ;
: t-first ( r -- a ) node 4 + ul@ ;
: t-second ( r -- b ) node 8 + ul@ ;
: t-data ( r -- d ) node 12 + ul@ ;
: store-new ( cells -- ) 4 lshift allocate throw to nbase 0 to ncount ;
: put ( tag a b data -- r )
  ncount node >r r@ 12 + l! r@ 8 + l! r@ 4 + l! r> l! ncount dup 1+ to ncount ;

\ ---- hash table with stored hashes (8-byte slots: hash, index + 1) -------
0 value tbl   0 value tmask
0 value kt  0 value ka  0 value kb  0 value kh
: table-new ( log2 -- ) 1 swap lshift dup 1- to tmask 3 lshift dup allocate throw
  dup to tbl swap erase ;
: slot ( i -- addr ) 3 lshift tbl + ;
: fmix ( h -- h' )
  dup 16 rshift xor $85EBCA6B * $FFFFFFFF and dup 13 rshift xor
  $C2B2AE35 * $FFFFFFFF and dup 16 rshift xor ;
: hash3 ( t a b -- h ) >r $9E3779B1 * xor $85EBCA6B * r> xor fmix ;
: same? ( r -- flag ) node dup ul@ kt = over 4 + ul@ ka = and swap 8 + ul@ kb = and ;
: tfind ( -- r true | i false )
  kh tmask and begin dup slot dup 4 + ul@ dup while
    swap ul@ kh = if 1- dup same? if nip true exit then then drop
    1+ tmask and repeat 2drop false ;
: loose ( d -- n ) $FFFFF and ;
: app-data ( -- d ) ka t-data loose kb t-data loose max ;
: data-of ( -- d ) kt 3 = if app-data else kt 2 = if ka 1+ else 0 then then ;
: enter ( i -- r ) kt ka kb data-of put tuck 1+ swap slot dup kh swap l! 4 + l! ;
: cons ( t a b -- r )
  to kb to ka to kt kt ka kb hash3 to kh tfind 0= if enter then ;

\ ---- chase ----------------------------------------------------------------
1 24 lshift constant steps
: rerun ( x -- x' r ) lcg dup 4 rshift nmask and ;
: raw-step ( x r -- x' r' )
  node dup ul@ 3 = if dup 12 + ul@ acc + to acc swap lcg tuck 1 and 4 * 4 + + ul@
  else drop rerun then ;
: col-step ( x r -- x' r' )
  dup t-tag 3 = if dup t-data acc + to acc swap lcg tuck 1 and if t-first else t-second then
  else drop rerun then ;
: cur-step ( x r -- x' r' )
  dup lf-term-tag@ lf-tag-app = if
    dup lf-term-data-word acc + to acc swap lcg tuck 1 and if lf-term-first@ else lf-term-second@ then
  else drop rerun then ;
: raw-chase ( -- ) 1 0 steps 0 do raw-step loop 2drop ;
: col-chase ( -- ) 1 0 steps 0 do col-step loop 2drop ;
: cur-chase ( -- ) 1 0 steps 0 do cur-step loop 2drop ;
\ A random DAG of n nodes: 1/8 leaves (bound variables 0..3), the rest
\ applications of two earlier nodes; the same in both stores.
: dag-raw ( n -- )
  dup 2* store-new dup 1- to nmask 1 swap 0 do
    lcg i 8 < over 7 and 0= or if 2 i 3 and 0 i 3 and 1+ put drop
    else dup 8 rshift i mod over 3 rshift i mod 3 -rot 0 put drop then
  loop drop ;
: dag-cur ( n -- )
  lf-term-reset dup 2* lf-term-capacity! drop false lf-term-sharing!
  1 swap 0 do
    lcg i 8 < over 7 and 0= or if i 3 and lf-term-bvar 0= abort" bvar" drop
    else dup 8 rshift i mod over 3 rshift i mod lf-term-app 0= abort" app" drop then
  loop drop ;
: chase-at ( log2 -- )
  1 swap lshift dup >r dag-raw r> dag-cur
  ."   raw " ['] raw-chase timed ."   col " ['] col-chase timed
  ."   cur " ['] cur-chase timed ."   sum " acc . cr nbase free throw 0 to acc ;

\ ---- cons -----------------------------------------------------------------
1 22 lshift constant conses
2048 constant width
: raw-conses ( -- )
  1 conses 0 do lcg dup 8 rshift width mod over 19 rshift width mod 3 -rot cons drop loop drop ;
: cur-conses ( -- )
  1 conses 0 do lcg dup 8 rshift width mod over 19 rshift width mod
    lf-term-app 0= abort" app" drop loop drop ;
: cons-bench ( -- )
  conses 2* width + store-new 23 table-new
  width 0 do 2 i 0 cons drop loop
  ."   raw " ['] raw-conses timed ."   made " ncount .
  lf-term-reset true lf-term-sharing! conses 2* lf-term-capacity! drop conses 2* lf-term-table-room
  width 0 do i lf-term-bvar 0= abort" bvar" drop loop
  ."   cur " ['] cur-conses timed cr nbase free throw tbl free throw ;

\ ---- instantiate ------------------------------------------------------------
0 value csub   0 value visits   0 value troot
: inst ( r -- r' )
  visits 1+ to visits
  dup t-data loose 0= if exit then
  dup t-tag 2 = if drop csub exit then          \ bound variable 0 (the only loose one)
  dup t-first recurse swap t-second recurse 3 -rot cons ;
\ A random tree of depth d: leaves a constant (tag 1) or, one in four,
\ bound variable 0; built with cons (equal subtrees shared).
: tree ( x d -- x' r )
  dup 0= if drop lcg dup 24 rshift 3 and if 1 0 0 cons else 2 0 0 cons then exit then
  1- >r r@ recurse r> swap >r recurse r> swap 3 -rot cons ;
: inst-root ( -- ) troot inst drop ;
: inst-bench ( -- )
  1 23 lshift store-new 23 table-new 1 0 0 cons to csub
  1 18 tree nip to troot 0 to visits
  ."   raw recursive " ['] inst-root timed
  ."   visits " visits . ."   nodes " ncount . cr nbase free throw tbl free throw ;

: all ( -- )
  ." chase 2^12 nodes, 2^24 steps:" cr 12 chase-at
  ." chase 2^22 nodes, 2^24 steps:" cr 22 chase-at
  ." cons 2^22 app(a,b), a,b < 2048:" cr cons-bench
  ." inst depth-18 tree:" cr inst-bench ;
