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
\ U1 of ADR 0015). [kernel] code: not through the review gate
\ (AGENTS.md). Untrusted.
\ Preconditions: those of lf-level-equivalent (live levels whose graphs a
\ scope check validated; parameter IDs that are interned names).
\ State: none of its own; it runs inside one call of level-normalize's
\ state record (lf-lnorm-state), whose memo of normal forms serves every
\ recursive normalize of the call. Single-threaded within one context.
\ Depth (plan task 6.2.0): is_geq_core's pending work waits on
\ normalize's frames (lib/frame.fs), an explicit stack that grows with the
\ depth of the normal forms, and each normalize runs as a loop of its own
\ on them (lf-lnorm-walk); a stack the heap cannot grow is full. A pair's
\ visit is a chain of steps ( ... frames -- ... frames next ) that ends
\ with ( flag frames 0 ).

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

\ is_geq of a pair (normalize both, then the core), continuing with cont
\ ( flag frames -- ... ). A visit the frames cannot hold is full and
\ gives false.
defer lf-geq-step ( l1 l2 frames -- ... frames next )
: lf-geq-call ( l1 l2 frames cont -- ... frames next )
  frame-need 2 pick frame-room? if ['] lf-geq-step frame-open exit then
  >r nip nip false swap dup frame-room@ lf-diag-frame-limit lf-lnorm-no-room r> ;
\ A pair whose answer is the next pair's.
: lf-geq-then ( l1 l2 frames -- ... frames next ) ['] frame-return lf-geq-call ;

\ l1 >= both sides of l2 (a max or an imax): the pair waits while l1 is
\ compared with the left side.
: lf-geq-both-back ( flag frames -- ... frames next )
  >r r@ frame-restore r@ frame-restore rot
  if lf-geq-rhs r> lf-geq-then else 2drop false r> 0 then ;
: lf-geq-both ( l1 l2 frames -- ... frames next )
  >r 2dup r@ frame-save r@ frame-save lf-geq-lhs r> ['] lf-geq-both-back lf-geq-call ;
\ The offsets case (536-540): l1 = b1 + k1 and l2 = b2 + k2. The same
\ base, or b2 zero: k1 >= k2; else equal positive offsets: b1 >= b2.
: lf-geq-bases ( l1 l2 -- b1 b2 ) lf-lmk-offset drop swap lf-lmk-offset drop swap ;
: lf-geq-ks ( l1 l2 -- k1 k2 ) lf-lmk-offset nip swap lf-lmk-offset nip swap ;
: lf-geq-base-ok? ( l1 l2 -- flag ) lf-geq-bases dup lf-geq-zero? -rot lf-lmk-same? or ;
: lf-geq-offsets ( l1 l2 frames -- ... frames next )
  >r 2dup lf-geq-base-ok? if lf-geq-ks >= r> 0 exit then
  2dup lf-geq-ks over = swap 0> and if lf-geq-bases r> lf-geq-then
  else 2drop false r> 0 then ;
\ After the max and imax cases of l2 and l1.
: lf-geq-rest ( l1 l2 frames -- ... frames next )
  over lf-geq-imax? if lf-geq-both exit then
  2 pick lf-geq-imax? if >r swap lf-geq-rhs swap r> lf-geq-then exit then
  lf-geq-offsets ;
\ Either side of l1 (a max) >= l2, else the rest: the pair waits.
: lf-geq-either-2 ( flag frames -- ... frames next )
  >r r@ frame-restore r@ frame-restore rot if 2drop true r> 0 else r> lf-geq-rest then ;
: lf-geq-either-1 ( flag frames -- ... frames next )
  >r if 2 r@ frame-drop true r> 0 exit then
  0 r@ frame-pick lf-geq-rhs 1 r@ frame-pick r> ['] lf-geq-either-2 lf-geq-call ;
: lf-geq-either ( l1 l2 frames -- ... frames next )
  >r 2dup r@ frame-save r@ frame-save swap lf-geq-lhs swap r> ['] lf-geq-either-1 lf-geq-call ;
: lf-geq-core ( l1 l2 frames -- ... frames next )
  >r lf-lnorm-ok? 0= if 2drop false r> 0 exit then
  2dup lf-lmk-same? over lf-geq-zero? or if 2drop true r> 0 exit then
  dup lf-geq-max? if r> lf-geq-both exit then
  over lf-geq-max? if r> lf-geq-either exit then
  r> lf-geq-rest ;
: lf-geq-normalized ( l1 l2 frames -- ... frames next )
  >r lf-lnorm-ok? 0= if 2drop false r> 0 exit then
  swap lf-lnorm-walk swap lf-lnorm-walk r> lf-geq-core ;
' lf-geq-normalized is lf-geq-step
\ is_geq to the end, as a loop of its own on the frames.
: lf-geq ( l1 l2 -- flag ) lf-lnorm-frames ['] lf-geq-call frame-through drop ;

\ Whether Lean's is_geq(l1, l2) holds, with fuel: (flag ok) when decided;
\ (false failure) as lf-level-equivalent gives it (unknown for parameter
\ names that cannot be ordered, exhausted, full, invalid). lf-lnorm-fuel
\ is the fuel left. Nothing stays allocated.
: lf-level-geq? ( l1 l2 fuel -- flag outcome )
  >r 2dup r@ lf-lnorm-usable? 0= if r> drop lf-lnorm-refused exit then
  r> lf-lnorm-begin ok? 0= if lf-lnorm-refused exit then
  lf-geq lf-lnorm-end lf-lnorm-result ;
