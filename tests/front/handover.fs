\ The hand-over of a finished declaration to the kernel (plan row FE1f;
\ src/front/handover.fs, src/core/reach.fs, author/export.fs's
\ lf-author-export-reached, cli/check-lf.fs). Driven without the
\ elaborator (plan FE1e) by terms built directly: kernel-form values of
\ tests/author/19-add-zero.lf, and terms made through the metavariable
\ context and then assigned.
\ - the reach marks: what roots reach, through binders, Sorts and
\   universe arguments; holes reached and holes left elsewhere;
\ - the reached writer gives the kernel-form path's records, byte for byte,
\   for add_zero', also after a hand-over that instantiated holes in its
\   type and value while unassigned holes stay in the stores; the
\   all-nodes writer still refuses any hole anywhere;
\ - the hand-over: accepted when complete; refused (invalid) when a hole
\   remains reachable, term or level, also a stale one of an emptied
\   context, or when a universe parameter is unused (as Lean); a refusal
\   gives back every node it made and leaves the declaration as it was
\   (rollback), also when the heap fails at each allocation (full); a
\   term 10,000 applications deep;
\ - through the command line (cli-check, the path every text takes:
\   stage-produce, the feed, check-declaration): tests/front/00-add-zero.lf
\   stops as not supported until FE1e (exit 2) with no elaborator; with a
\   stand-in elaborator that builds add_zero's term directly, or through
\   assigned metavariables, the kernel accepts it with the same verdicts as
\   the kernel-form 19-add-zero.lf (exit 0); a hole left stops the text at
\   end with error 74 (exit 4, nothing checked); a wrong term is rejected
\   by the kernel (exit 1).
\ Every T{ }T checks the data stack's depth. Nothing here accepts a
\ theorem except through the kernel's check.
require ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/main.fs
decimal

: library ( -- c-addr u ) s" tests/author/init-slice.ndjson" ;
: add-zero-kernel ( -- c-addr u ) s" tests/author/19-add-zero.lf" ;
: add-zero-natural ( -- c-addr u ) s" tests/front/00-add-zero.lf" ;
T{ library true lfc-library-open -> outcome-ok }T
: d0 ( -- decl ) 0 lf-author-decl ;
: ty ( -- t ) d0 lf-fdecl-type @ ;
: va ( -- v ) d0 lf-fdecl-value @ ;
\ add_zero' in the kernel form, its type and value kept.
variable ty0  variable va0
: kernel ( -- ) lf-author-begin add-zero-kernel lf-author-file drop ty ty0 ! va va0 ! ;

\ Records, captured: the current capture and one kept for comparison.
16384 constant room
create caught room allot  variable caught#  variable lines
create reference room allot  variable reference#
: rec-sink ( c-addr u -- outcome )
  dup caught# @ + 1+ room > if 2drop outcome-full exit then
  tuck caught caught# @ + swap move caught# +! 10 caught caught# @ + c! 1 caught# +! 1 lines +!
  outcome-ok ;
: fresh ( -- ) 0 caught# ! 0 lines ! ;
: all-records ( -- outcome ) fresh ['] rec-sink lf-author-export ;
: reached-records ( -- outcome ) fresh ['] rec-sink lf-author-export-reached ;
: keep ( -- ) caught reference caught# @ move caught# @ reference# ! ;
: same-records? ( -- flag ) caught caught# @ reference reference# @ compare 0= ;

\ The stores' counts, kept and compared (rollback).
variable tc  variable lc  variable rc
: counts! ( -- ) lf-term-count @ tc ! lf-level-count @ lc ! lf-cref-count @ rc ! ;
: counts? ( -- flag )
  lf-term-count @ tc @ = lf-level-count @ lc @ = and lf-cref-count @ rc @ = and ;

\ Metavariables: natural ones, of a type the tests do not check.
: hole ( type -- mvar ) mv-natural lf-mvar-new drop ;
: assign ( mvar value -- ) lf-mvar-assign drop ;
\ A Pi like old (its domain, name and kind) around body.
: named-as ( new old -- new ) lf-pres-binder@ if 2>r dup 2r> lf-pres-binder! drop then ;
: pi-like ( old body -- t )
  over lf-term-first@ swap lf-tag-pi lf-term-binary drop swap named-as ;
\ Eq.{level}, a constant whose universe argument is level.
: eq-at ( level -- t )
  >r s" Eq" lfa-intern lf-name-generation @ r> dup lf-level-identity drop swap
  here 2! here 1 lf-cref-new drop lf-cterm-new drop drop ;

\ ---- The reach marks (core/reach.fs).
T{ kernel -> }T
T{ lf-reach-open ty lf-reach-term lf-reach-sweep -> true }T
\ The type reaches its domain, body and the level of Eq.{1}; not the value.
T{ ty lf-reached? ty lf-term-first@ lf-reached? ty lf-term-second@ lf-reached?
   -> true true true }T
T{ va lf-reached? va lf-term-second@ lf-reached? -> false false }T
T{ 1 lfa-level-number lf-level-reached? lf-reach-holes? -> true false }T
\ Numbers outside the stores are never reached or marked.
T{ -1 lf-reach-term lf-term-count @ lf-reach-term -1 lf-reached? -> false }T
T{ lf-term-count @ lf-reached? lf-level-count @ lf-level-reached? -> false false }T
T{ lf-reach-close -> }T
\ A hole made but reached by nothing is no hole of the roots; one reached is.
T{ ty hole drop ty va lf-holes-reached? -> false outcome-ok }T
T{ ty hole va lf-holes-reached? -> true outcome-ok }T
\ A level hole reached through a Sort, and through universe arguments.
variable lhole
T{ lf-level-mvar-new swap lhole ! -> outcome-ok }T
T{ lhole @ dup lf-level-identity drop lf-hterm-sort drop drop va lf-holes-reached?
   -> true outcome-ok }T
T{ lhole @ eq-at -1 lf-holes-reached? -> true outcome-ok }T
\ And through a max of levels: Sort (max ?l 1).
: sort-of ( level -- t ) dup lf-level-identity drop lf-hterm-sort drop drop ;
T{ lhole @ 1 lfa-level-number lf-level-tag-max lf-level-binary nip -> true }T
T{ lf-level-count @ 1- sort-of -1 lf-holes-reached? -> true outcome-ok }T
\ Only through a successor, and only through the second part of a max or
\ an imax (review fe1f M2): Sort (?l + 1), Sort (max 1 ?l), Sort (imax 1 ?l).
: second-to-1 ( level tag -- level' ) >r 1 lfa-level-number swap r> lf-level-binary drop ;
T{ lhole @ lf-level-succ drop sort-of -1 lf-holes-reached? -> true outcome-ok }T
T{ lhole @ lf-level-tag-max second-to-1 sort-of -1 lf-holes-reached? -> true outcome-ok }T
T{ lhole @ lf-level-tag-imax second-to-1 sort-of -1 lf-holes-reached? -> true outcome-ok }T
\ A corrupted negative count is taken as none (review fe1f L4).
T{ lf-term-count @ -1 lf-term-count ! ty va lf-holes-reached? rot lf-term-count !
   -> false outcome-ok }T
\ A Sort naming no level of the store (a broken node): the level is never
\ marked, nothing is written outside the table.
T{ 1000000 lf-term-symbolic-sort drop dup -1 lf-holes-reached? rot lf-term-tag@
   -> false outcome-ok lf-tag-symbolic-sort }T
\ Empty stores: nothing to reach, no hole.
T{ lf-author-begin -1 -1 lf-holes-reached? -> false outcome-ok }T
T{ kernel -> }T
\ No heap for either table: full, nothing reached, no block left.
T{ 1 heap-refusals ! ty va lf-holes-reached? -> false outcome-full }T
T{ 2 heap-refusals ! ty va lf-holes-reached? -> false outcome-full }T
T{ live-blocks @ ty va lf-holes-reached? 2drop live-blocks @ = -> true }T

\ ---- The writers on the kernel-form path's terms. Every node of this
\ run is reached: the reached writer gives the same records.
T{ kernel -> }T
T{ all-records lines @ -> outcome-ok 44 }T keep
T{ reached-records same-records? -> outcome-ok true }T
\ An unreached node, even one no record holds, is not written.
T{ 0 0 lf-tag-let lf-term-binary nip -> true }T
T{ all-records reached-records same-records? -> outcome-unsupported outcome-ok true }T
\ A hole the declarations do not reach blocks nothing; the all-nodes
\ writer refuses it, as before (ADR 0021 D2).
T{ ty hole drop reached-records same-records? -> outcome-ok true }T
T{ all-records lines @ -> outcome-invalid 0 }T
\ A hole they reach is refused before any line, whatever the front end
\ did: the value replaced by a hole by hand.
T{ ty hole d0 lf-fdecl-value ! reached-records lines @ -> outcome-invalid 0 }T
\ A sink's refusal and no heap for the marks, as for the other writer.
T{ kernel -> }T
: refusing ( c-addr u -- outcome ) 2drop outcome-invalid ;
T{ ' refusing lf-author-export-reached -> outcome-invalid }T
T{ 1 heap-refusals ! reached-records lines @ -> outcome-full 0 }T
T{ reached-records same-records? -> outcome-ok true }T
\ No heap for the second reach table, or for the numbering tables after
\ them (review fe1f L1): full, no line; every run of the reached writer
\ gives back every block it took.
T{ 2 heap-refusals ! reached-records lines @ -> outcome-full 0 }T
T{ 3 heap-refusals ! reached-records lines @ -> outcome-full 0 }T
T{ live-blocks @ reached-records live-blocks @ rot = -> outcome-ok true }T
T{ live-blocks @ 2 heap-refusals ! reached-records live-blocks @ rot = -> outcome-full true }T
\ A level hole nothing reaches is neither written nor refused by the
\ reached writer; the all-nodes writer refuses it.
T{ lf-level-mvar-new nip reached-records same-records? -> outcome-ok outcome-ok true }T
T{ all-records lines @ -> outcome-invalid 0 }T
T{ kernel -> }T
\ Universe levels (review fe1f M2): Type u, max u v, imax u v and a
\ constant at u + 1 give the same records from both writers, every level
\ being reached; none is ever written as zero.
: levels ( -- outcome )
  lf-author-begin s" kernel-form axiom A universe u u Type end A" lf-author-text drop
  s" axiom B universe u universe v u v level-max Sort end B" lf-author-text drop
  s" axiom C universe u universe v u v level-imax Sort end C" lf-author-text drop
  s" axiom Q universe u A u 1 level+ ^ end Q" lf-author-text ;
T{ levels all-records -> outcome-ok outcome-ok }T keep
T{ reached-records same-records? lf-author-count -> outcome-ok true 4 }T
T{ s\" {\"il\":2,\"succ\":1}" caught caught# @ 2swap search nip nip -> true }T
T{ s\" \"max\":[" caught caught# @ 2swap search nip nip -> true }T
T{ s\" \"imax\":[" caught caught# @ 2swap search nip nip -> true }T
\ add_zero's records again, the reference for the hand-over below.
T{ kernel all-records -> outcome-ok }T keep

\ ---- The hand-over (front/handover.fs).
\ Complete: the kernel-form terms are kept as they are.
T{ kernel d0 ty va lf-handover ty va -> outcome-ok ty0 @ va0 @ }T
\ A hole at the root of the value: refused, the declaration unchanged.
variable vh
T{ ty hole vh ! counts! d0 ty vh @ lf-handover counts? va -> outcome-invalid true va0 @ }T
\ Assigned: kept as its value, and the records are the kernel-form path's.
T{ vh @ va0 @ assign d0 ty vh @ lf-handover va -> outcome-ok va0 @ }T
T{ reached-records same-records? -> outcome-ok true }T

\ Holes under a binder: the type Pi (n : Nat), ?b with ?b assigned the
\ body, the value a hole ?v, and a hole ?u nothing reaches.
variable bh  variable tp
: setup ( -- )
  kernel ty hole bh ! ty bh @ pi-like tp ! ty hole vh ! ty hole drop
  bh @ ty lf-term-second@ assign ;
T{ setup -> }T
\ ?v is free: refused, and the Pi the instantiation made is given back.
T{ counts! d0 tp @ vh @ lf-handover counts? ty va -> outcome-invalid true ty0 @ va0 @ }T
\ ?v := the value: accepted; the type is a new Pi, named as the old, and
\ the records are the kernel-form path's, byte for byte.
T{ vh @ va0 @ assign counts! d0 tp @ vh @ lf-handover counts? -> outcome-ok false }T
T{ ty ty0 @ = ty tp @ = va va0 @ = -> false false true }T
T{ ty lf-term-tag@ ty lf-pres-binder@ nip nip -> lf-tag-pi true }T
T{ reached-records same-records? -> outcome-ok true }T
T{ all-records lines @ -> outcome-invalid 0 }T

\ A level hole: refused while free; assigned the level 1, accepted, the
\ constant rebuilt with it.
variable eqh
T{ kernel lf-level-mvar-new drop lhole ! -> }T
T{ lhole @ eq-at eqh ! d0 eqh @ va lf-handover ty -> outcome-invalid ty0 @ }T
T{ lhole @ 1 lfa-level-number lf-level-mvar-assign d0 eqh @ va lf-handover
   -> outcome-ok outcome-ok }T
T{ ty eqh @ = ty lf-term-first@ lf-cref-slot lf-cref-pairs nip -> false 1 }T
T{ ty lf-term-first@ lf-cref-slot lf-cref-pairs drop 0 lf-cref-pair@ drop
   -> 1 lfa-level-number }T

\ Universe parameters, as Lean's sortDeclLevelParams: k.{u} {a : Sort u}
\ (x : a) : a := x uses u in its type: accepted; used by neither,
\ refused (error 75), as pinned Lean refuses theorem unusedU.{u} : True
\ := trivial ("unused universe parameter 'u'"); and a second parameter v
\ named by hand and used by nothing refuses k, nothing kept.
: poly-of ( c-addr u -- ) lf-author-begin lf-author-text drop ty ty0 ! va va0 ! ;
: poly ( -- )
  s" kernel-form theorem k universe u u Sort implicit: a a explicit: x a := x end k" poly-of ;
: v-too ( -- )
  s" v" lfa-intern d0 lf-fdecl-universe d0 lf-fdecl-universes @ cells + !
  1 d0 lf-fdecl-universes +! ;
: why ( -- code ) lfh lfh-why @ ;
T{ poly d0 ty va lf-handover -> outcome-ok }T
T{ poly d0 ty lf-term-second@ dup lf-handover why -> outcome-invalid 75 }T
\ A parameter used by the value alone (review fe1f N1): a theorem's and an
\ axiom's are counted in the type alone, a definition's in both, as
\ pinned Lean 4.35.0 decides these (checked 2026-11-13, -DwarningAsError):
\   theorem t1.{v} : True := (fun (_ : Sort v) => True.intro) PUnit.{v}  refused
\   def d1.{v} : Nat := (fun (_ : Sort v) => 0) PUnit.{v}               accepted
\   theorem t2.{v} (α : Sort v) (a : α) : a = a := rfl                   accepted
\   axiom ax1.{v} : True                                                  refused
\   axiom ax2.{v} : Sort v                                                accepted
\   def d2.{v} : True := True.intro                                       refused
\ and with a hole too it reports only the unused parameter:
\   theorem t5.{v} : True := _                                            unused
\   def d3.{v} : Nat := _                                                 unused
\ Here with k's terms: Pi (x : a), a (no u) as the type, k's value (u in
\ its binder's type) as the value.
: kdef ( -- )
  s" kernel-form def k universe u u Sort implicit: a a explicit: x a := x end k" poly-of ;
: kaxiom ( -- )
  s" kernel-form axiom k universe u u Sort implicit: a a explicit: x a end k" poly-of ;
: u-free ( -- t ) ty lf-term-second@ ;
T{ poly d0 u-free va lf-handover why -> outcome-invalid 75 }T
T{ kdef d0 u-free va lf-handover -> outcome-ok }T
T{ kdef d0 ty va lf-handover -> outcome-ok }T
T{ kaxiom d0 u-free -1 lf-handover why -> outcome-invalid 75 }T
T{ kaxiom d0 ty -1 lf-handover -> outcome-ok }T
T{ kdef d0 u-free u-free lf-handover why -> outcome-invalid 75 }T
T{ poly v-too counts! d0 ty va lf-handover counts? why ty va
   -> outcome-invalid true 75 ty0 @ va0 @ }T
\ An unused parameter is told first, before a hole, as Lean tells t5 and
\ d3 (review fe1f L-a); with every parameter used, the hole.
T{ poly v-too d0 ty ty hole lf-handover why -> outcome-invalid 75 }T
T{ kdef d0 u-free ty hole lf-handover why -> outcome-invalid 75 }T
T{ poly d0 ty ty hole lf-handover why -> outcome-invalid 74 }T

\ A term that is no node, an axiom's missing value, and a hole's
\ instantiation not ported yet (the beta step of ?f Nat, ?f := a lambda):
\ never kept.
T{ kernel d0 lf-term-count @ va lf-handover ty -> outcome-invalid ty0 @ }T
\ A value that does not fit the kind (review fe1f M1): a theorem's must be
\ a node, so -1 and -2 are refused, nothing kept; an axiom's must be -1.
T{ d0 ty -1 lf-handover va why -> outcome-invalid va0 @ 76 }T
T{ d0 ty -2 lf-handover va -> outcome-invalid va0 @ }T
: axiom-a ( -- ) lf-author-begin s" kernel-form axiom A Prop end A" lf-author-text drop ;
T{ axiom-a d0 ty -1 lf-handover va -> outcome-ok -1 }T
T{ axiom-a d0 ty ty lf-handover va -> outcome-invalid -1 }T
\ The writers refuse a theorem or a definition whose value is no node,
\ put there by hand, never writing a number read outside their tables.
T{ kernel -1 d0 lf-fdecl-value ! all-records reached-records
   -> outcome-unsupported outcome-unsupported }T
T{ kernel -2 d0 lf-fdecl-value ! all-records -> outcome-unsupported }T
: def-a ( -- ) lf-author-begin s" kernel-form def a 0 Type := Prop end a" lf-author-text drop ;
T{ def-a -1 d0 lf-fdecl-value ! all-records reached-records
   -> outcome-unsupported outcome-unsupported }T
T{ s\" \"value\"" caught caught# @ 2swap search nip nip -> false }T
\ A Sort naming no level of the store as a theorem's type (review fe1f
\ N2): both writers refuse it (unsupported), reading no table outside.
: no-level ( -- ) kernel 1000000 lf-term-symbolic-sort drop d0 lf-fdecl-type ! ;
T{ no-level all-records reached-records -> outcome-unsupported outcome-unsupported }T
T{ s\" {\"thm\"" caught caught# @ 2swap search nip nip -> false }T
\ ?h t with ?h := the value: instantiateMVars beta-reduces it, as Lean
\ does (plan FE1c), so the hand-over takes a new value node.
variable fa
T{ kernel va hole dup va assign ty lf-term-first@ lf-tag-app lf-term-binary swap fa !
   -> true }T
T{ counts! d0 ty fa @ lf-handover counts? va va0 @ = -> outcome-ok false false }T
\ A step not ported yet (a let betaRev would zeta-reduce: ?g := let c :=
\ t; the value, applied): unsupported, nothing kept, the value as it was.
: let-over ( v body -- let ) over swap lf-term-lam drop false lf-let-make drop ;
variable fz
T{ kernel va hole dup ty lf-term-first@ va let-over assign
   ty lf-term-first@ lf-tag-app lf-term-binary swap fz ! -> true }T
T{ counts! d0 ty fz @ lf-handover counts? va -> outcome-unsupported true va0 @ }T

\ No heap at each allocation the hand-over makes (the instantiation's
\ walks of terms and of each constant's levels, the reach tables), the
\ k-th refused for k = 1, 2, ...: full, every node given back, the
\ declaration as it was, no block left; past the last one, accepted.
: full-at ( k -- outcome flag flag flag )
  >r setup vh @ va0 @ assign counts! live-blocks @ r> heap-refusals !
  d0 tp @ vh @ lf-handover 0 heap-refusals ! swap live-blocks @ = counts? ty ty0 @ = ;
T{ 1 full-at -> outcome-full true true true }T
variable all-full
: full-step ( k -- k' more? )
  1+ dup full-at and and swap dup ok? if 2drop false exit then
  outcome-full = and all-full @ and all-full ! true ;
: full-each ( -- k flag )
  true all-full ! 0 begin full-step 0= over 1000 > or until all-full @ ;
\ 22 allocations, each refused in turn (the instantiation's spine table
\ and argument slab among them, plan FE1c).
T{ full-each -> 23 true }T
T{ setup vh @ va0 @ assign d0 tp @ vh @ lf-handover ty ty0 @ = -> outcome-ok false }T

\ Made again in the same process: the same records.
T{ setup vh @ va0 @ assign d0 tp @ vh @ lf-handover -> outcome-ok }T
T{ reached-records same-records? -> outcome-ok true }T
\ A store whose count is not valid cannot be marked: refused, nothing kept.
T{ kernel lf-term-count @ -1 lf-term-count ! d0 ty0 @ va0 @ lf-handover swap lf-term-count !
   -> outcome-invalid }T
\ A hole of an emptied context (a declaration before, lf-mctx-reset as
\ every declaration's start does): stale, so never assigned, and still a
\ hole the hand-over refuses.
T{ kernel ty hole vh ! lf-mctx-reset vh @ va0 @ lf-mvar-assign -> outcome-invalid }T
T{ d0 ty vh @ lf-handover why -> outcome-invalid 74 }T
\ A term 10,000 applications deep over one hole: the instantiation's walk
\ and the reach marks use no host stack (dag-walk.fs heap stacks; one
\ sweep), refused while the hole is free, accepted once it is assigned (a
\ Pi, so no beta step is asked for).
: deepen ( t -- t' ) dup lf-tag-app lf-term-binary drop ;
: deep ( t n -- t' ) 0 ?do deepen loop ;
variable dt
lf-term-capacity constant rooms
T{ 30000 lf-term-capacity! -> outcome-ok }T
T{ kernel ty hole vh ! vh @ 10000 deep dt ! d0 dt @ va0 @ lf-handover why -> outcome-invalid 74 }T
T{ vh @ ty0 @ assign d0 dt @ va0 @ lf-handover ty dt @ = -> outcome-ok false }T
T{ ty lf-term-tag@ ty lf-term-first@ dup lf-term-first@ = -> lf-tag-app false }T
T{ kernel rooms lf-term-capacity! -> outcome-ok }T
T{ lfc-library-close -> }T

\ ---- Through the command line: the path of every text.
: tally ( k -- n ) cli-count-of @ ;
: check ( c-addr u -- code ) cli-options library cli-state opt-env 2! cli-check ;
\ No elaborator yet (plan FE1e): not supported, nothing checked.
T{ add-zero-natural check lf-author-code -> 2 71 }T
\ The kernel form's verdicts, the reference.
T{ add-zero-kernel check -> 0 }T
outcome-ok tally constant accepted
T{ accepted 0> -> true }T

\ Stand-in elaborators: add_zero's type and value, built directly, as
\ FE1e will build them from the syntax (Lean's term for
\ theorem add_zero' (n : Nat) : n + 0 = n := Eq.refl n, explicit).
create us 4 2* cells allot
: u! ( level i -- ) >r dup lf-level-identity drop swap r> 2* cells us + 2! ;
: u-zeros ( n -- ) 0 ?do 0 i u! loop ;
: one ( -- ) 1 lfa-level-number 0 u! ;
: cst ( c-addr u n -- t )
  >r lfa-intern lf-name-generation @ us r> lf-cref-new 0= abort" ref"
  lf-cterm-new 0= abort" const" drop ;
: app ( f a -- t ) lf-tag-app lf-term-binary 0= abort" app" ;
: bv ( i -- t ) lf-term-bvar 0= abort" bvar" ;
: raw-lit ( u -- t ) lf-hterm-cell 0= abort" lit" drop ;
: nat ( -- t ) s" Nat" 0 cst ;
: n-binder ( t -- t ) s" n" lfa-intern lf-binder-default lfa-name! ;
: pi-n ( dom body -- t ) lf-tag-pi lf-term-binary 0= abort" pi" n-binder ;
: lam-n ( dom body -- t ) lf-tag-lam lf-term-binary 0= abort" lam" n-binder ;
: hadd ( -- t ) 3 u-zeros s" HAdd.hAdd" 3 cst nat app nat app nat app ;
: inst ( -- t ) 1 u-zeros s" instHAdd" 1 cst nat app s" instAddNat" 0 cst app ;
: nat-zero ( -- t )
  1 u-zeros s" OfNat.ofNat" 1 cst nat app 0 raw-lit app
  s" instOfNatNat" 0 cst 0 raw-lit app app ;
: sum ( -- t ) hadd inst app 0 bv app nat-zero app ;
: stmt ( -- t ) one s" Eq" 1 cst nat app sum app 0 bv app ;
: refl-of ( t -- t' ) >r one s" Eq.refl" 1 cst nat app r> app ;
: add-zero-type ( -- t ) nat stmt pi-n ;
: direct ( -- type value ) add-zero-type nat 0 bv refl-of lam-n ;
\ Through the metavariable context: Eq.refl Nat ?a, ?a := n; ?u unused.
: ?nat ( -- mvar ) nat hole ;
: with-hole ( -- type value mvar ) add-zero-type ?nat dup >r refl-of nat swap lam-n r> ;
: assigned ( -- type value ) with-hole 0 bv assign ?nat drop ;
: unassigned ( -- type value ) with-hole drop ;
\ Eq.refl Nat 0 (a raw literal): a proof of 0 = 0, not of n + 0 = n.
: wrong ( -- type value ) add-zero-type nat 0 raw-lit refl-of lam-n ;
: elaborating ( xt -- ) is lf-front-elaborate ;

T{ ' direct elaborating add-zero-natural check -> 0 }T
T{ outcome-ok tally -> accepted }T
T{ ' assigned elaborating add-zero-natural check -> 0 }T
T{ outcome-ok tally -> accepted }T
\ A hole left: stopped at end with error 74, nothing checked.
T{ ' unassigned elaborating add-zero-natural check lf-author-code -> 4 74 }T
T{ lfa-error lfa-err-at @ lfa-pos> -> 13 1 }T
\ A wrong term reaches the kernel and is rejected there.
T{ ' wrong elaborating add-zero-natural check outcome-rejected tally -> 1 1 }T
\ A natural declaration, then the kernel form (tests/front/mixed.lf): the
\ hole the stand-in left unused blocks nothing; both accepted.
T{ ' assigned elaborating s" tests/front/mixed.lf" check outcome-ok tally -> 0 accepted 1+ }T
\ An axiom, a definition and a theorem (tests/front/three.lf, review fe1f
\ L1), each through the hand-over: someNat : Nat (a hole made and left
\ unused), two : Nat := 2 (a raw literal; it finds the axiom's hole stale,
\ its context emptied at its own start), and add_zero' with a note on its
\ type (its notes end set, L2). All accepted; the axiom NOT PROVED.
variable ax-hole  variable stale-seen
: noted ( type value -- type value ) over >r s" a note" lf-note-person r> lf-note-add 2drop ;
: per-kind ( -- type value )
  lf-front-header lf-fdecl-kind @ case
    lf-decl-axiom of nat dup hole ax-hole ! -1 endof
    lf-decl-def of ax-hole @ lf-mvar-live? 0= stale-seen ! nat 2 raw-lit endof
    >r direct noted r> endcase ;
: three ( -- c-addr u ) s" tests/front/three.lf" ;
T{ false stale-seen ! ' per-kind elaborating three check stale-seen @ -> 0 true }T
T{ outcome-ok tally cli-not-proved @ -> accepted 2 + 1 }T
\ The same process after all of that: the same verdicts.
T{ ' direct elaborating add-zero-natural check outcome-ok tally -> 0 accepted }T
\ The elaborator back to plan FE1e's place-holder.
T{ ' lfh-later elaborating add-zero-natural check -> 2 }T

\ The natural end's other refusals, read directly against the library: an
\ instantiation step not ported yet (a let that betaRev would zeta-reduce:
\ ?g Nat with ?g := let c := Nat; a lambda) is error 77, no room for the
\ hand-over's walk error 60, a theorem given no value (malformed, review
\ fe1f M1, L5) error 76. The beta step of ?f Nat with ?f := a lambda is
\ ported (plan FE1c): the reduced value reaches the kernel.
: natural ( -- outcome ) lf-author-begin add-zero-natural lf-author-file ;
: beta ( -- type value ) direct over hole dup rot assign nat app ;
: zeta ( -- type value ) direct over hole dup rot nat swap let-over assign nat app ;
: no-room-left ( -- type value ) direct 1 heap-refusals ! ;
: no-value ( -- type value ) direct drop -1 ;
T{ library true lfc-library-open -> outcome-ok }T
T{ ' zeta elaborating natural lf-author-code -> outcome-unsupported 77 }T
T{ ' beta elaborating natural lf-author-code -> outcome-ok 0 }T
T{ ' no-value elaborating natural lf-author-code -> outcome-invalid 76 }T
T{ ' no-room-left elaborating natural lf-author-code -> outcome-full 60 }T
T{ ' direct elaborating natural ty 0< va 0< -> outcome-ok false false }T
\ The header the elaborator reads: the statement and the proof kept as
\ nodes (n Eq.refl, an application), no by.
T{ lf-front-proof syn-kind@ lf-front-statement syn-kind@ lf-front-by
   -> syn-k-app syn-k-binrel -1 }T
\ A universe parameter neither the statement nor the proof uses stops
\ the natural text at end (error 75), as Lean refuses it.
: with-u ( -- outcome )
  lf-author-begin
  s" theorem add_zero' universe u Nat explicit: n n 0 + n = := n Eq.refl end add_zero'"
  lf-author-text ;
T{ ' direct elaborating with-u lf-author-code -> outcome-invalid 75 }T
\ The three declarations read directly: each own declaration's notes end
\ is set, add_zero's holding its one note (review fe1f L2), and the run
\ is marked as the front end's (L3); a kernel-form run is not.
: own-decl ( c-addr u -- i ) lfa-intern lfa-decl-find drop ;
: notes# ( c-addr u -- n ) own-decl lf-author-notes swap - ;
T{ ' per-kind elaborating lf-author-begin three lf-author-file lfa-front-made? -> outcome-ok true }T
T{ s" someNat" notes# s" two" notes# s" add_zero'" notes# -> 0 0 1 }T
T{ s" two" own-decl lfa-decl lf-fdecl-value @ lf-term-tag@ -> lf-tag-lit }T
T{ kernel lfa-front-made? -> false }T
T{ ' lfh-later elaborating lfc-library-close -> }T
bye
