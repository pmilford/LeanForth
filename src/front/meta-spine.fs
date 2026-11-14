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
\ - lf-meta-const-decl ( const -- d true | false ): the declaration of a
\   constant's name (Lean's find?), through front/meta-env.fs in either
\   mode; false also when a library declaration could not be decoded
\   (full, unsupported): the constant then reads as unknown (plan S2:
\   the outcome passed on).
\ - lf-meta-levels-fill ( slot slab -- outcome ): a constant reference's
\   universe arguments, as levels, into the slab, emptied first.
\ - lf-meta-named ( new old -- new outcome ): a rebuilt binder gets the
\   old one's name and kind (present/binder-table.fs), when it has them;
\   full when the table has no room for them (a rebuilt node that is an
\   input node keeps its record's: ok).
\ - lf-meta-mvar-free? ( term -- flag ): no metavariable in the term, as
\   far as the term store tells: a binary node's data word is known only
\   then (core/terms.fs), a leaf is no metavariable (Lean's !hasExprMVar;
\   a node whose word is unknown is taken to hold one).
\ - lf-meta-fvar-free? ( term -- flag ): the term's data word shows no
\   free variable (false when the store keeps no word for it).
\ - lf-meta-tag? ( term tag -- flag ): the term's tag is tag;
\   lf-meta-fvar? ( term -- flag ): a free variable.
\ - lf-meta-args# ( term -- n ): the number of arguments of its spine.
\ - lf-meta-pop ( slab -- x ): the slab's last cell, taken off.
\ Unchecked: the terms are live, the constant is one, the slab is a cell
\ slab (not empty for lf-meta-pop). State: none of its own; every word
\ takes its slab. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../core/terms.fs
require ../core/constant-references.fs
require ./meta-env.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../present/binder-table.fs

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
  lf-term-first@ lf-cref-slot lf-cref-name@ drop lf-menv-find
  ok? if true else drop false then ;
: ms-level ( slot i -- level ) swap lf-cref-pairs drop swap lf-cref-pair@ drop ;
: lf-meta-levels-fill ( slot slab -- outcome )
  dup slab-clear swap dup lf-cref-pairs nip 0 ?do
    2dup i ms-level swap lf-meta-push dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
: ms-full ( outcome -- outcome' ) outcome-full = if outcome-full else outcome-ok then ;
: lf-meta-named ( new old -- new outcome )
  lf-pres-binder@ if 2>r dup 2r> lf-pres-binder! ms-full else outcome-ok then ;
: ms-binary? ( term -- flag ) lf-term-tag@ lf-term-binary-tag? ;
: lf-meta-mvar-free? ( term -- flag )
  dup ms-binary? if lf-term-data@ dup if nip then exit then lf-term-tag@ lf-tag-mvar <> ;
: lf-meta-fvar-free? ( term -- flag ) lf-term-data@ if lf-data-fvar? 0= else false then ;
: lf-meta-tag? ( term tag -- flag ) swap lf-term-tag@ = ;
: lf-meta-fvar? ( term -- flag ) lf-tag-fvar lf-meta-tag? ;
: lf-meta-args# ( term -- n )
  0 swap begin dup lf-meta-app? while lf-term-first@ swap 1+ swap repeat drop ;
: lf-meta-pop ( slab -- x ) dup slab-count 1- over slab-at @ -1 rot slab-commit ;

base !   \ the BASE this file was loaded with
