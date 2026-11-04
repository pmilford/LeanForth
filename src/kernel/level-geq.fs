\ Lean's is_geq on universe levels (level.cpp 523-544, Lean 4.35.0, commit
\ eb6cafb7): whether l1 >= l2 under every assignment, as far as Lean's
\ kernel sees it. is_geq normalizes both sides (level-normalize.fs, Lean's
\ normalize) and calls is_geq_core, which recurses through is_geq again:
\   equal (operator==) or l2 zero: true;
\   l2 a max: l1 >= each side;  l1 a max: either side >= l2 (else go on);
\   l2 an imax: l1 >= each side;  l1 an imax: its right side >= l2;
\   otherwise by offsets (to_offset): same base, or l2's base zero: the
\   offsets compare; equal positive offsets: the bases compare; else false.
\ Like normalize, it is incomplete on purpose; LeanForth copies it exactly
\ (owner rule). Its one user is the universe check of an inductive
\ type's constructor fields (inductive.cpp 478-485; check-block.fs, rule
\ U1 of ADR 0015). [kernel] code: experimental, not through the review
\ gate. Untrusted.
\ Preconditions: those of lf-level-equivalent (live levels whose graphs a
\ scope check validated; parameter IDs that are interned names).
\ State: none of its own; it runs inside one call of level-normalize's
\ state record (lf-lnorm-state), whose memo of normal forms serves every
\ recursive normalize of the call. Single-threaded within one context.
\ Stack use: is_geq_core recurses once per level of the normal forms (a
\ max chain of n arguments nests n frames), each frame at most 5 return
\ and 4 data cells (lf-geq-normalized, lf-geq-core, lf-geq-either or
\ lf-geq-both or lf-geq-rest, the deferred call). Each is counted as two
\ of normalize's level frames (7 return and 3 data cells each), on the
\ same counter, so the whole call stays within lf-level-depth-limit frames
\ and the need a caller already provides (lf-lnorm-return-cells,
\ lf-lnorm-data-cells); deeper is full, recorded as the depth limit
\ (review of the heap stores, rvKC3).

require ../lib/lib.fs
require ../core/levels.fs
require ./level-make.fs
require ./level-normalize.fs

\ Two levels' parts: tags, first and second children.
: lf-geq-zero? ( level -- flag ) lf-lmk-zero? ;
: lf-geq-tag? ( level tag -- flag ) swap lf-level-tag@ = ;
: lf-geq-max? ( level -- flag ) lf-level-tag-max lf-geq-tag? ;
: lf-geq-imax? ( level -- flag ) lf-level-tag-imax lf-geq-tag? ;
: lf-geq-lhs ( level -- level' ) lf-level-first@ ;
: lf-geq-rhs ( level -- level' ) lf-level-second@ ;

defer lf-geq ( l1 l2 -- flag )   \ is_geq: normalize both, then the core

\ l1 >= both sides of l2 (a max or an imax).
: lf-geq-both ( l1 l2 -- flag )
  2dup lf-geq-lhs lf-geq if lf-geq-rhs lf-geq else 2drop false then ;
\ Either side of l1 (a max) >= l2.
: lf-geq-either ( l1 l2 -- flag )
  over lf-geq-lhs over lf-geq if 2drop true else swap lf-geq-rhs swap lf-geq then ;
\ The offsets case (536-540): l1 = b1 + k1 and l2 = b2 + k2. The same
\ base, or b2 zero: k1 >= k2; else equal positive offsets: b1 >= b2.
: lf-geq-bases ( l1 l2 -- b1 b2 ) lf-lmk-offset drop swap lf-lmk-offset drop swap ;
: lf-geq-ks ( l1 l2 -- k1 k2 ) lf-lmk-offset nip swap lf-lmk-offset nip swap ;
: lf-geq-base-ok? ( l1 l2 -- flag ) lf-geq-bases dup lf-geq-zero? -rot lf-lmk-same? or ;
: lf-geq-offsets ( l1 l2 -- flag )
  2dup lf-geq-base-ok? if lf-geq-ks >= exit then
  2dup lf-geq-ks over = swap 0> and if lf-geq-bases lf-geq else 2drop false then ;
\ After the max and imax cases of l2 and l1.
: lf-geq-rest ( l1 l2 -- flag )
  dup lf-geq-imax? if lf-geq-both exit then
  over lf-geq-imax? if swap lf-geq-rhs swap lf-geq exit then
  lf-geq-offsets ;
: lf-geq-core ( l1 l2 -- flag )
  lf-lnorm-ok? 0= if 2drop false exit then
  2dup lf-lmk-same? over lf-geq-zero? or if 2drop true exit then
  dup lf-geq-max? if lf-geq-both exit then
  over lf-geq-max? if 2dup lf-geq-either if 2drop true exit then then
  lf-geq-rest ;
: lf-geq-enter ( -- flag )
  lf-lnorm-enter 0= if false exit then
  lf-lnorm-enter dup 0= if lf-lnorm-leave then ;
: lf-geq-leave ( -- ) lf-lnorm-leave lf-lnorm-leave ;
: lf-geq-normalized ( l1 l2 -- flag )
  lf-lnorm-ok? 0= if 2drop false exit then
  lf-geq-enter 0= if 2drop false exit then
  swap lf-lnorm-walk swap lf-lnorm-walk lf-geq-core lf-geq-leave ;
' lf-geq-normalized is lf-geq

\ Whether Lean's is_geq(l1, l2) holds, with fuel: (flag ok) when decided;
\ (false failure) as lf-level-equivalent gives it (unknown for parameter
\ names that cannot be ordered, exhausted, full, invalid). lf-lnorm-fuel
\ is the fuel left. Nothing stays allocated.
: lf-level-geq? ( l1 l2 fuel -- flag outcome )
  >r 2dup r@ lf-lnorm-usable? 0= if r> drop lf-lnorm-refused exit then
  r> lf-lnorm-begin ok? 0= if lf-lnorm-refused exit then
  lf-geq lf-lnorm-end lf-lnorm-result ;
