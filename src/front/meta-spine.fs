\ Application spines, constants' declarations and universe-argument lists
\ for the front end's Meta files (plan FE1c; front/whnf.fs, infer.fs,
\ beta-inst.fs), one copy of what each needed (Forth review of fe1c-2,
\ S2). Untrusted.
\ - lf-meta-push ( x slab -- outcome ): x as the slab's next cell; full
\   when the slab has no room.
\ - lf-meta-app? ( term -- flag ): an application.
\ - lf-meta-spine ( term slab -- head outcome ): the arguments of
\   f a1 .. an into the slab, emptied first, an first; the head f. A
\   refused cell gives -1 and full.
\ - lf-meta-arg ( i slab -- term ): argument i, a0 the first, of a spine.
\ - lf-meta-const-decl ( const -- d true | false ): the input's newest
\   declaration of a constant's name (Lean's find?; core/input.fs).
\ - lf-meta-levels-fill ( slot slab -- outcome ): a constant reference's
\   universe arguments, as levels, into the slab, emptied first.
\ Unchecked: the terms are live, the constant is one, the slab is a cell
\ slab. State: none of its own; every word takes its slab. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../core/terms.fs
require ../core/constant-references.fs
require ../core/input.fs

: lf-meta-push ( x slab -- outcome )
  tuck 1 swap slab-claim ok-then? if rot slab-at ! outcome-ok else nip nip then ;
: lf-meta-app? ( term -- flag ) lf-term-tag@ lf-tag-app = ;
: ms-peel ( term slab -- f outcome )
  over lf-term-second@ swap lf-meta-push swap lf-term-first@ swap ;
: lf-meta-spine ( term slab -- head outcome )
  dup slab-clear swap begin dup lf-meta-app? while
    over ms-peel ok-then? 0= if nip -1 swap exit then
  repeat nip outcome-ok ;
: lf-meta-arg ( i slab -- term ) tuck slab-count 1- swap - swap slab-at @ ;
: lf-meta-const-decl ( const -- d true | false )
  lf-term-first@ lf-cref-slot lf-cref-name@ drop lf-input-newest
  dup 0< if drop false else true then ;
: ms-level ( slot i -- level ) swap lf-cref-pairs drop swap lf-cref-pair@ drop ;
: lf-meta-levels-fill ( slot slab -- outcome )
  dup slab-clear swap dup lf-cref-pairs nip 0 ?do
    2dup i ms-level swap lf-meta-push dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;

base !   \ the BASE this file was loaded with
