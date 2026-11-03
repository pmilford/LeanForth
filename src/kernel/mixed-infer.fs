\ Experimental, untrusted mixed-term inference. Closed source roots only.
\ Signatures and nested dependencies are unchecked assumptions; no theorem
\ authority. One stable index/session, no raw writes, resets or concurrent
\ calls. Handles are local diagnostics. Fuel is shared by preflight,
\ traversal, specialization and transformations; bounded metadata, identity
\ scans and topological staging are additional work. Only a directly visible
\ Pi is applied; uncertain conversion is unknown.
\ State: one inference record, lf-minfer-job (fields lf-ijob-*): fuel, frame
\ depth, index token, the arena counts before the call, the binder context
\ and a copy of a reference's levels; a member of the checker context
\ (lib/context.fs). A node's intermediate results stay on the data stack.
\ Single-threaded within one context. lf-minfer-walk is deferred only for
\ the mutual recursion and set once, at load time, and shared.
\ Stack use: the recursion runs on the host stacks, about 6 return-stack and
\ up to 3 data-stack cells per level, at most lf-term-capacity levels (plus
\ the nested rebuild passes); a host stack overflow throws and never yields
\ a result. mixed-definition-probe.fs starts a job with lf-minfer-start,
\ calls lf-minfer-walk, lf-minfer-sort-level and lf-minfer-compare directly,
\ and reads lf-minfer-fuel afterwards.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/constant-term-scope.fs
require ../core/generation-handles.fs
require ../core/levels.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./mixed-convert.fs
require ./mixed-instantiate.fs
require ./mixed-shift.fs
require ./mixed-signature-audit.fs
require ./mixed-signature-probe.fs

begin-structure /lf-ijob
  field: lf-ijob-fuel      \ visits left
  field: lf-ijob-depth     \ active frames, at most lf-term-capacity
  field: lf-ijob-token     \ signature index token
  field: lf-ijob-terms     \ term count before the call; source nodes lie below
  field: lf-ijob-levels    \ level count before the call
  field: lf-ijob-crefs     \ reference count before the call
  field: lf-ijob-binders   \ binder domains in the context
  lf-term-capacity cells +field lf-ijob-domains
  lf-cref-argument-capacity 2* cells +field lf-ijob-actuals
end-structure
/lf-ijob context-record: lf-minfer-job

\ Fields of the record. Tests read the fuel left and the binder count, and
\ mixed-definition-probe reads the fuel left.
: lf-minfer-fuel ( -- addr ) lf-minfer-job lf-ijob-fuel ;
: lf-minfer-depth ( -- addr ) lf-minfer-job lf-ijob-depth ;
: lf-minfer-token ( -- addr ) lf-minfer-job lf-ijob-token ;
: lf-minfer-context-depth ( -- addr ) lf-minfer-job lf-ijob-binders ;

\ Helpers run on the fuel left and inference continues with what they leave.
\ They report only ok, invalid, exhausted or full, and the signature lookup
\ also unknown; outcome-sane passes any outcome on unchanged (so rejected or
\ unsupported too, once ADR 0008 step 3 lets helpers return them; still not
\ ok) and makes anything else invalid. A failed step has no type (-1).
: lf-minfer-refuel ( fuel-addr -- ) @ lf-minfer-fuel ! ;
: lf-minfer-none ( status -- type status ) -1 swap ;

\ The binder context: the domains of the binders around the node being
\ inferred, innermost last. A push fails when the context is full; each
\ push is popped after its body, whatever the outcome.
: lf-minfer-domain-cell ( i -- addr ) cells lf-minfer-job lf-ijob-domains + ;
: lf-minfer-push ( domain -- flag )
  lf-minfer-context-depth @ dup lf-term-capacity <
  if lf-minfer-domain-cell ! 1 lf-minfer-context-depth +! true else 2drop false then ;
: lf-minfer-pop ( -- ) -1 lf-minfer-context-depth +! ;
: lf-minfer-bound ( index -- domain )
  lf-minfer-context-depth @ 1- swap - lf-minfer-domain-cell @ ;

\ Shift a binder's stored domain into the current context; the shift checks
\ the whole graph again with the shared fuel.
: lf-minfer-shift ( node amount -- type status )
  over lf-term-identity 0= if 2drop -1 outcome-invalid exit then swap 0 swap
  lf-minfer-fuel @ lf-mixed-shift lf-mshift-fuel lf-minfer-refuel nip outcome-sane ;

\ Live nodes as handles; the right one is checked first.
: lf-minfer-handle ( node -- node identity true | false )
  dup lf-term-identity dup 0= if nip then ;
: lf-minfer-handles ( left right -- left lid right rid true | false )
  lf-minfer-handle 0= if drop false exit then 2>r
  lf-minfer-handle if 2r> true else 2r> 2drop false then ;

\ Compare two types by conservative beta conversion, and substitute an
\ argument into a Pi body; both validate their graphs with the shared fuel.
: lf-minfer-convert ( left lid right rid -- status )
  lf-minfer-fuel @ lf-mixed-convert lf-mconvert-fuel lf-minfer-refuel outcome-sane ;
: lf-minfer-compare ( left right -- status )
  lf-minfer-handles if lf-minfer-convert else outcome-invalid then ;
: lf-minfer-substitute ( body bid argument aid -- type status )
  lf-minfer-fuel @ lf-mixed-instantiate lf-minst-fuel lf-minfer-refuel nip outcome-sane ;
: lf-minfer-instantiate ( body argument -- type status )
  lf-minfer-handles if lf-minfer-substitute else -1 outcome-invalid then ;

\ A stamped symbolic Sort for an allocated level; an allocator failure (a
\ full store or a spent serial) is full and cannot yield a type.
: lf-minfer-sort ( level -- type status )
  dup lf-level-identity 0= if drop -1 outcome-invalid exit then
  lf-hterm-sort if drop outcome-ok else -1 outcome-full then ;
: lf-minfer-sort-type ( level -- type status )
  lf-level-succ if lf-minfer-sort else -1 outcome-full then ;

\ The level of an inferred Sort. Any other type is unknown, not a judgment.
: lf-minfer-sort-level ( node -- level status )
  lf-term-read 0= if -1 outcome-invalid exit then
  drop swap lf-tag-symbolic-sort = if outcome-ok else drop -1 outcome-unknown then ;

\ A constant: specialize its candidate signature to the reference's levels,
\ first copied into this record (specialization needs its input disjoint
\ from every arena and scratch area). Success continues with the fuel the
\ specialization left; a failure leaves no fuel.
: lf-minfer-actuals ( -- addr ) lf-minfer-job lf-ijob-actuals ;
: lf-minfer-copy ( slot -- addr count )
  lf-cref-pairs tuck 2* cells lf-minfer-actuals swap move lf-minfer-actuals swap ;
: lf-minfer-specialized ( root identity fuel' 0 | status -- type status )
  outcome-sane dup ok? if drop lf-minfer-fuel ! drop outcome-ok
  else 0 lf-minfer-fuel ! lf-minfer-none then ;
: lf-minfer-constant ( reference -- type status )
  lf-cref-slot dup lf-crec-name @ swap lf-minfer-copy 2>r lf-minfer-token @ swap 2r>
  lf-minfer-fuel @ lf-msp-specialize-fuel lf-minfer-specialized ;

\ A bound variable has its binder's domain, shifted past the binders between.
: lf-minfer-bvar ( index -- type status )
  dup lf-minfer-context-depth @ < if dup lf-minfer-bound swap 1+ lf-minfer-shift
  else drop -1 outcome-invalid then ;

defer lf-minfer-walk ( node -- type status )

\ After a step that succeeded, keep x and the step's result; otherwise drop
\ x and pass the failed ( result status ) on.
: lf-minfer-step? ( x result status -- x result true | result status false )
  dup ok? if drop true else rot drop false then ;

\ Application: the function's type must be a visible Pi (otherwise unknown),
\ the argument's type must convert to its domain, and the type is the Pi
\ body instantiated with the argument.
: lf-minfer-pi-parts ( type -- domain body true | outcome false )
  lf-term-read 0= if outcome-invalid false exit then
  rot lf-tag-pi = if true else 2drop outcome-unknown false then ;
: lf-minfer-argument ( domain argument -- status )
  lf-minfer-walk ok-then? if swap lf-minfer-compare else nip then ;
: lf-minfer-apply ( domain body argument -- type status )
  rot over lf-minfer-argument ok-then?
  if lf-minfer-instantiate else nip lf-minfer-none then ;
: lf-minfer-app ( function argument -- type status )
  swap lf-minfer-walk lf-minfer-step? 0= if exit then
  lf-minfer-pi-parts if rot lf-minfer-apply else nip lf-minfer-none then ;

\ Binders: the domain's type must be a Sort; the body is inferred with the
\ domain pushed on the binder context. A full context is full, checked
\ before the body's visit and so whatever fuel is left (ADR 0008).
: lf-minfer-domain ( domain -- level status )
  lf-minfer-walk dup ok? if drop lf-minfer-sort-level then ;
: lf-minfer-under ( domain body -- type status )
  swap lf-minfer-push if lf-minfer-walk lf-minfer-pop
  else drop -1 outcome-full then ;
\ A lambda's type is the Pi of its domain over its body's type; a failed
\ allocation is full.
: lf-minfer-lam-type ( domain body-type -- type status )
  lf-term-pi if outcome-ok else -1 outcome-full then ;
: lf-minfer-lam-body ( domain body -- type status )
  over swap lf-minfer-under lf-minfer-step? if lf-minfer-lam-type then ;
: lf-minfer-lam ( domain body -- type status )
  over lf-minfer-domain dup ok? if 2drop lf-minfer-lam-body else 2swap 2drop then ;
\ A Pi's type is Sort (imax u v) for a domain in Sort u and a body in
\ Sort v, or Sort 0 when v is the zero level.
: lf-minfer-imax ( u v -- level true | false )
  dup 0= if nip true else lf-level-imax then ;
: lf-minfer-pi-sort ( u v -- type status )
  lf-minfer-imax if lf-minfer-sort else -1 outcome-full then ;
: lf-minfer-pi-body ( level domain body -- type status )
  lf-minfer-under lf-minfer-step? 0= if exit then
  lf-minfer-sort-level lf-minfer-step? if lf-minfer-pi-sort then ;
: lf-minfer-pi ( domain body -- type status )
  over lf-minfer-domain dup ok? if drop -rot lf-minfer-pi-body else 2swap 2drop then ;

\ Infer an original source node; nodes made by this inference are output
\ data, never input. Constructors outside this subset are unknown.
: lf-minfer-leaf ( first tag -- type status )
  case lf-tag-symbolic-sort of lf-minfer-sort-type endof
    lf-tag-constant of lf-minfer-constant endof
    lf-tag-bvar of lf-minfer-bvar endof
    >r drop -1 outcome-unknown r> endcase ;
: lf-minfer-binary ( first second tag -- type status )
  case lf-tag-app of lf-minfer-app endof
    lf-tag-lam of lf-minfer-lam endof
    lf-tag-pi of lf-minfer-pi endof
    >r 2drop -1 outcome-unknown r> endcase ;
: lf-minfer-dispatch ( first second tag -- type status )
  dup lf-term-binary-tag? if lf-minfer-binary else nip lf-minfer-leaf then ;
: lf-minfer-source? ( node -- flag ) dup 0< 0= swap lf-minfer-job lf-ijob-terms @ < and ;
: lf-minfer-read ( node -- first second tag true | false )
  dup lf-minfer-source? 0= if drop false exit then lf-term-read dup if >r rot r> then ;
: lf-minfer-visit ( node -- type status )
  lf-minfer-read if lf-minfer-dispatch else -1 outcome-invalid then ;

\ Each visit costs one unit of fuel and holds one of at most
\ lf-term-capacity frames. No fuel left is exhausted and no free frame is
\ full (with neither, the fuel decides); both spend nothing.
: lf-minfer-room ( -- outcome )
  lf-minfer-fuel @ lf-minfer-depth @ lf-term-capacity < visit-outcome ;
: lf-minfer-enter ( -- ) -1 lf-minfer-fuel +! 1 lf-minfer-depth +! ;
: lf-minfer-in-frame ( node -- type status )
  lf-minfer-room ok-then? 0= if no-result exit then
  lf-minfer-enter lf-minfer-visit -1 lf-minfer-depth +! ;
' lf-minfer-in-frame is lf-minfer-walk

\ Preflight before any allocation: the closed root's binder scope, then the
\ whole signature index, each continuing with the fuel the last one left.
: lf-minfer-scope ( root identity -- status )
  0 lf-minfer-fuel @ lf-constant-term-scope outcome-sane
  dup ok? if lf-cts-fuel lf-minfer-refuel then ;
: lf-minfer-index ( -- status )
  lf-minfer-token @ lf-minfer-fuel @ lf-mixed-signature-audit outcome-sane
  dup ok? if lf-msa-fuel lf-minfer-refuel then ;
: lf-minfer-preflight ( root identity -- status )
  lf-minfer-scope dup ok? if drop lf-minfer-index then ;

\ The three arena counts before allocation, and their rollback; allocation
\ serials never rewind.
: lf-minfer-mark ( job -- )
  lf-term-count @ over lf-ijob-terms ! lf-level-count @ over lf-ijob-levels !
  lf-cref-count @ swap lf-ijob-crefs ! ;
: lf-minfer-rollback ( -- )
  lf-minfer-job dup lf-ijob-terms @ lf-term-count ! dup lf-ijob-levels @ lf-level-count !
  lf-ijob-crefs @ lf-cref-count ! ;
: lf-minfer-idle ( job -- ) 0 over lf-ijob-depth ! 0 swap lf-ijob-binders ! ;

\ Start a job on lf-minfer-job: the index token and nonnegative fuel, no
\ frames or binders in use, and the arena counts to roll back to. Neither
\ preflight allocates, so the counts are the same before and after it; the
\ definition probe starts a job after its own preflight. Only original
\ source nodes, those below the term count, are then inferred.
: lf-minfer-start ( token fuel -- )
  lf-minfer-job tuck lf-ijob-fuel ! tuck lf-ijob-token !
  dup lf-minfer-idle lf-minfer-mark ;

\ A failure reports no type and leaves zero fuel.
: lf-minfer-failed ( status -- type identity status ) 0 lf-minfer-fuel ! -1 0 rot ;
: lf-minfer-result ( type -- type identity status )
  dup lf-term-identity if outcome-ok exit then
  drop lf-minfer-rollback outcome-invalid lf-minfer-failed ;
: lf-minfer-run ( root -- type identity status )
  lf-minfer-walk
  dup ok? if drop lf-minfer-result else nip lf-minfer-rollback lf-minfer-failed then ;

\ ( token root identity fuel -- type identity status ) Full source and global
\ index preflight precede allocation. All failures restore three arena counts;
\ serials never rewind. Input traversal is limited to original source nodes.
\ Every failure reports zero remaining fuel conservatively.
: lf-mixed-infer ( token root identity fuel -- type identity status )
  dup 0< if 2drop 2drop outcome-invalid lf-minfer-failed exit then
  >r rot r> lf-minfer-start over swap lf-minfer-preflight
  dup ok? if drop lf-minfer-run else nip lf-minfer-failed then ;
