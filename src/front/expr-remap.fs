\ Renumbering the loose bound variables of an expression of the compact
\ store (plan row FE6; ADR 0021): the de Bruijn half of what Lean's
\ forallTelescope, mkForallFVars and mkLambdaFVars do when a generated
\ definition reorders a recursor's binders (src/front/constructions.fs).
\ Lean's liftLooseBVars and lowerLooseBVars are its shift; a swap moves
\ two adjacent groups of binders past each other. The result is built in
\ a scratch tier over a sealed input tier (core/compact-tier.fs), so a
\ result equal to an input expression has the input's number: hash-
\ consing makes "equal node for node" a comparison of numbers.
\
\ A remap record holds the pass (lib/frame.fs, first, so the visitor finds
\ the record at the frames address), the tier, the cutoff and the map. A
\ loose variable whose index b is at least the binders passed plus the
\ cutoff is renumbered: its place r = b - base goes through the map.
\   shift ( drop lift ): r < drop is refused (it would name a binder that
\     is gone: unsupported), others become r - drop + lift.
\   swap ( a h ): r < a becomes r + h; a <= r < a + h becomes r - a; the
\     rest stay.
\ An expression without such variables (its loose range, kept in every
\ record, at most the base) is kept as it is, so closed parts are never
\ walked. Applications, binders and projections are rebuilt; a variable
\ renumbered; a letE or mdata record is unsupported for now (eight
\ structures of Init hold one, plan row FE6). With remap-erase! set, the
\ pass also makes every binder anonymous and plain (name 0, default
\ information), to compare terms as Lean's Expr equality does; it then
\ walks every node but leaves. Each visit costs one unit of fuel
\ (remap-fuel per run, or what remap-fuel! sets): exhausted beyond it;
\ full when the tier or the pass's stack cannot grow; invalid for a busy
\ record. A node shared by several parents is visited once per path.
\ Untrusted front-end code: a wrong result is caught by the comparison
\ with Lean's and by the kernel's check.
\
\ Example (in the scratch tier s over an input tier):
\   create r /remap allot  s r remap-init
\   0 1 r remap-shift!  e 0 r remap-at   \ e with every loose variable + 1
\   r remap-free
\ State: none of its own; every word takes a remap record, which holds the
\ pass's heap block until remap-free.

require ../lib/lib.fs
require ../core/compact.fs

begin-structure /remap
  /frames +field remap-frames   \ fuel, visits, binders passed (the context)
  field: remap-tier             \ the tier results are built in
  field: remap-cutoff           \ variables below it plus the binders stay
  field: remap-map              \ xt ( r remap -- r' true | false )
  field: remap-x                \ the map's first number (drop, or a)
  field: remap-y                \ its second (lift, or h)
  field: remap-erase            \ true: binder names made anonymous too
  field: remap-limit            \ fuel for each run
end-structure

\ Visits allowed in one run.
1000000 constant remap-fuel

\ The maps.
: shift-map ( r remap -- r' true | false )
  2dup remap-x @ < if 2drop false exit then dup remap-y @ swap remap-x @ - + true ;
: swap-in? ( r remap -- flag ) dup remap-x @ swap remap-y @ + < ;
: swap-map ( r remap -- r' true )
  2dup remap-x @ < if remap-y @ + true exit then
  2dup swap-in? if remap-x @ - else drop then true ;

\ Reading the record and the expression being visited.
: remap-tier@ ( remap -- tier ) remap-tier @ ;
: remap-a ( e remap -- a ) remap-tier@ expr-a@ ;
: remap-b ( e remap -- b ) remap-tier@ expr-b@ ;
: remap-tag ( e remap -- tag ) remap-tier@ expr-tag@ ;
: remap-base ( remap -- n ) dup frame-context @ swap remap-cutoff @ + ;
: remap-loose? ( d remap -- flag ) swap data-range swap remap-base > ;
\ Nothing to change below e: no variable to renumber, and no binder to
\ rename when names are erased (a leaf, of depth 0).
: remap-clean? ( e remap -- flag )
  tuck remap-tier@ expr-data@ over remap-erase @ if nip data-depth else swap remap-loose? then
  0= ;

\ Variables: index b renumbered, or refused.
: remap-index ( b remap -- b' true | false )
  tuck remap-base - over dup remap-map @ execute
  if swap remap-base + true else drop false then ;
: remap-variable ( e remap -- e' outcome )
  tuck remap-a over remap-index
  if swap remap-tier@ expr-bvar else drop -1 outcome-unsupported then ;

\ Steps (lib/frame.fs). A visit's result: ( e' outcome remap 0 ). A visit
\ with two operands saves e, then a'; a projection its field index, then e.
: remap-keep ( e remap -- e outcome remap 0 ) outcome-ok swap 0 ;
: remap-bvar ( e remap -- e' outcome remap 0 ) dup >r remap-variable r> 0 ;
: remap-odd ( e remap -- -1 outcome remap 0 ) nip >r -1 outcome-unsupported r> 0 ;
\ After a failed child: the n values the visit saved dropped, no result.
: remap-failed ( x outcome remap n -- -1 outcome remap 0 )
  over frame-drop >r nip -1 swap r> 0 ;
\ The head of the expression saved i cells from the top; a binder's
\ without its name and binder information when names are erased (Lean's
\ Expr equality, which its exporter shares terms by, ignores both).
: plain-binder ( head -- head' ) head-tag tag-pi < if tag-lam else tag-pi then ;
: remap-anonymous ( head remap -- head' )
  remap-erase @ over head-tag binder-tag? and if plain-binder then ;
: remap-head ( i remap -- head )
  tuck frame-pick over remap-tier@ expr-head@ swap remap-anonymous ;
\ The record rebuilt; the visit's two saved cells dropped.
: remap-built ( head a' b' remap -- e' outcome remap 0 )
  dup >r remap-tier@ expr-make 2 r@ frame-drop r> 0 ;
: remap-joined ( b' outcome remap -- e' outcome remap 0 )
  over ok? 0= if 2 remap-failed exit then
  nip >r 1 r@ remap-head 0 r@ frame-pick rot r> remap-built ;
: remap-proj-joined ( a' outcome remap -- e' outcome remap 0 )
  over ok? 0= if 2 remap-failed exit then
  nip >r 0 r@ remap-head swap 1 r@ frame-pick r> remap-built ;
\ After the first child: a' saved, and e's second operand to visit.
: remap-hold ( a' remap -- b remap ) tuck frame-save 1 over frame-pick over remap-b swap ;
: remap-app-second ( a' outcome remap -- ... remap next )
  over ok? 0= if 1 remap-failed exit then nip remap-hold ['] remap-joined frame-call ;
: remap-binder-second ( a' outcome remap -- ... remap next )
  over ok? 0= if 1 remap-failed exit then nip remap-hold ['] remap-joined frame-under ;
\ e saved, and its first operand to visit.
: remap-down ( e remap -- a remap ) 2dup frame-save tuck remap-a swap ;
: remap-app ( e remap -- ... remap next ) remap-down ['] remap-app-second frame-call ;
: remap-binder ( e remap -- ... remap next )
  remap-down ['] remap-binder-second frame-call ;
: remap-proj ( e remap -- ... remap next )
  2dup remap-b over frame-save remap-down ['] remap-proj-joined frame-call ;
: remap-kind ( e remap tag -- ... remap next )
  dup binder-tag? if drop remap-binder exit then
  case tag-bvar of remap-bvar endof  tag-app of remap-app endof
    tag-proj of remap-proj endof  >r remap-odd r> endcase ;
: remap-visit ( e remap -- ... remap next )
  2dup remap-clean? if remap-keep exit then 2dup remap-tag remap-kind ;

\ The interface.
: remap-init ( tier remap -- )
  ['] remap-visit over frame-init remap-fuel over remap-limit ! remap-tier ! ;
: remap-free ( remap -- ) frame-free ;
: remap-fuel! ( visits remap -- ) remap-limit ! ;
: remap-set ( x y xt remap -- ) tuck remap-map ! tuck remap-y ! remap-x ! ;
: remap-shift! ( drop lift remap -- ) ['] shift-map swap remap-set ;
: remap-swap! ( a h remap -- ) ['] swap-map swap remap-set ;
\ Erase binder names (flag true) in the runs that follow, or keep them.
: remap-erase! ( flag remap -- ) remap-erase ! ;
: remap-cutoff! ( cutoff remap -- ) remap-cutoff ! ;
\ e with its loose variables at or past the cutoff renumbered by the map
\ set last: the result's number and ok, or -1 and the outcome (above).
: remap-run ( e remap -- e' outcome )
  dup remap-limit @ over frame-budget drop 0 swap frame-run ;
: remap-at ( e cutoff remap -- e' outcome ) tuck remap-cutoff! remap-run ;
