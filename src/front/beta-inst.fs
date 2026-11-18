\ Instantiation with beta of the front end (plan FE1c; ADR 0021 D6): a
\ port of Lean 4.35.0's Expr.instantiateBetaRevRange
\ (Lean/Meta/InferType.lean), which inferType and Meta's telescopes use
\ to put arguments in for a type's bound variables.
\ lf-meta-instantiate-rev-beta ( body addr m -- term outcome ): the m
\ terms in cells at addr, a0 .. am-1, put in for body's loose bound
\ variables, #k (k < m, counted from the depth of each occurrence) by ak,
\ as Lean's instantiateRev, and each larger loose index m less; and where
\ an application's head is a bound variable, its image applied to its
\ arguments' images takes them by one head beta step (Lean's betaRev: a
\ motive put in for #1 in `#1 #0` becomes its body). A subterm with no
\ loose bound variable at its depth is kept (its data word tells), so is
\ a node whose parts do not change; a rebuilt binder keeps its name and
\ kind (present/binder-table.fs). The arguments must have no loose bound
\ variable (Lean lifts them under binders, liftLooseBVars), else
\ unsupported, never another term; a beta step under a binder, whose
\ arguments have loose ones, is front/instantiate.fs's: done where no
\ binder of the lambda's body needs them lifted, else unsupported.
\ The walk is offset-walk.fs's (pending (node, depth) pairs on a heap
\ stack, the image of each pair made once, as Lean's cache), so no depth
\ needs the host's stacks (plan task 6.2.0); the beta case is its own.
\ Outcomes: ok; invalid for a term that is not in the store (the body or
\ an argument) or a negative m; unsupported as above; full when a store
\ or the heap has no room. A failure gives -1 for the term. Untrusted.
\ State: the record ib-state (the arguments and the rebuild walk) and the
\ slab ib-spine, in the checker context; the walk's blocks are freed with
\ the context. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/mvar-leaves.fs
require ../core/annotations.fs
require ../present/binder-table.fs
require ./instantiate.fs
require ./meta-spine.fs

begin-structure /ib
  field: ib-xs                 \ the arguments: the address of their cells
  field: ib-xs#                \ and how many
  /ow +field ib-replace        \ the rebuild walk (offset-walk.fs)
end-structure
/ib context-record: ib-state
1 cells context-slab: ib-spine     \ the beta case's arguments, last first
:noname ( -- ) ib-state ib-replace ow-free ; context-teardown

: ib-head ( node -- head ) begin dup lf-term-app? while lf-term-first@ repeat ;
\ An application whose head is a bound variable: Lean's beta case.
: ib-beta? ( node -- flag )
  dup lf-term-app? if ib-head lf-term-bvar? else drop false then ;

\ Bound variables: #k below the depth is itself; one of the m an
\ argument; a larger one m less. A pair with no loose bound variable at
\ its depth is kept (in-closed?, instantiate.fs).
: ib-made ( index true | false -- image ) room-result ow-fail ;
: ib-x ( k -- x ) cells ib-state ib-xs @ + @ ;
: ib-m ( -- m ) ib-state ib-xs# @ ;
: ib-bvar ( node depth -- image )
  over lf-term-first@ swap - dup 0< if drop exit then
  dup ib-m < if nip ib-x exit then
  drop lf-term-first@ ib-m - lf-term-bvar ib-made ;
: ib-leaf ( node depth -- image ) over lf-term-bvar? if ib-bvar else drop then ;

\ The beta case: the head's image applied to the spine's arguments'
\ images (each at the depth, in ib-spine, last first), one head beta step
\ taken when the head's image is a lambda (Lean's betaRev).
: ib-spine-fill ( node -- outcome ) ib-spine lf-meta-spine nip ;
: ib-spine-arg ( i -- arg ) ib-spine lf-meta-arg ;
: ib-apply ( f depth -- f' )
  ib-spine slab-count 0 ?do
    i ib-spine-arg over ow-image rot swap lf-term-app ib-made swap
  loop drop ;
: ib-lam? ( term -- flag ) dup 0< if drop false else lf-term-lam? then ;
: ib-head-beta ( f -- f' )
  dup 0< if exit then lf-meta-head-beta ok-or-none ow-fail ;
: ib-head-image ( node depth -- image ) swap ib-head swap ib-bvar ;
: ib-beta-apply ( himage depth -- image )
  over >r ib-apply r> ib-lam? if ib-head-beta then ;
: ib-beta-image ( node depth -- image )
  over ib-spine-fill dup ok? 0= if ow-fail 2drop -1 exit then drop
  tuck ib-head-image swap ib-beta-apply ;
: ib-arg ( node depth -- arg depth ) swap lf-term-second@ swap ;
: ib-args-pushed? ( node depth -- pushed? )
  false -rot begin over lf-term-app? while
    2dup ib-arg ow-push-if if rot drop true -rot then ow-first
  repeat 2drop ;
: ib-step-beta ( node depth -- )
  2dup ib-args-pushed? if 2drop exit then 2dup ib-beta-image ow-done ;
\ The walk's own case: an application headed by a bound variable.
: ib-own ( node depth -- node depth false | true )
  over ib-beta? if ib-step-beta true else false then ;
' in-closed? ' ib-leaf ' ib-own ow-kind constant ib-kind
: ib-run ( body -- term outcome ) ib-kind ib-state ib-replace ow-run ;
\ The arguments: terms with no loose bound variable.
: ib-xs! ( addr m -- ) ib-state tuck ib-xs# ! ib-xs ! ;
: ib-x-ok ( x -- outcome )
  dup lf-term-root? 0= if drop outcome-invalid exit then
  lf-meta-loose ok-then? if 0= if outcome-ok else outcome-unsupported then then ;
: ib-args-ok ( -- outcome ) outcome-ok ib-m 0 ?do i ib-x ib-x-ok outcome-and loop ;
: lf-meta-instantiate-rev-beta ( body addr m -- term outcome )
  dup 0< if 2drop drop -1 outcome-invalid exit then ib-xs!
  dup lf-term-root? 0= if drop -1 outcome-invalid exit then
  ib-args-ok dup ok? 0= if nip no-result exit then drop
  ib-m 0= if outcome-ok exit then ib-run ;

base !   \ the BASE this file was loaded with
