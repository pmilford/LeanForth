\ Lean's infer_proj (type_checker.cpp 247-292; plan task 5.2.2, ADR 0015
\ rules J1, J2): the type of a projection e.i of the structure S, the
\ application of a projection leaf to e (core/projections.fs), behind
\ mixed-infer.fs's hook lf-minfer-proj (set here, while loading).
\ [kernel] code: experimental, not through the review gate, not
\ independently audited.
\
\ In Lean's order: e's type inferred and put in whnf, Ty; Ty must be an
\ application of a constant named S, an inductive type with one
\ constructor and numParams + numIndices arguments; the constructor's
\ type at Ty's universe arguments is put in whnf binder by binder, its
\ parameters instantiated with Ty's first arguments, then its fields
\ before i, each dependent one with the projection e.j it stands for
\ (where Ty is a proposition, only a proof may be projected so); field
\ i's domain is the type -- a proof again when Ty is a proposition. Each
\ "must" that fails is Lean's invalidProj: rejected (diagnostic 91, the
\ leaf) while deciding, unknown aside (test P2). Lean's to_proj_idx
\ (more than 32 bits) cannot fail here: the stage refuses such an index.
\ Where a whnf or a lookup cannot follow Lean, its failure passes on
\ (unknown, K5, exhausted, full). Not yet as Lean: a structure that is a
\ type of the block being checked (Lean's environment holds it, but not
\ its constructor yet) is unknown. numIndices is the one LeanForth
\ computed (lf-env-shape), never the file's. The lookups record no
\ dependency, as whnf.fs's do not: the structure is in the closure of
\ what e's type names.
\ State: none of its own; every value stays on the data stack, as the
\ is_prop tests run inference again (aside, which may meet projections).
\ The computation keeps a frame on the stack: the leaf L, e closed E,
\ its type in whnf Ty, the flag P (Ty a proposition), and r, the
\ constructor's type so far; each phase gives it back with r' and an
\ outcome (r' -1 after a failure).

require ../lib/lib.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/name-equal.fs
require ../core/projections.fs
require ./environment.fs
require ./inductive-block.fs
require ./mixed-head.fs
require ./mixed-infer.fs
require ./whnf.fs

: lf-iproj-site ( -- site ) c" infer-proj lf-infer-proj" ;
\ invalidProj: rejected while deciding, unknown aside.
: lf-iproj-bad ( leaf -- -1 status )
  lf-minfer-deciding?
  if lf-iproj-site lf-diag-invalid-proj lf-minfer-reject no-result exit then
  0 lf-diag-invalid-proj lf-minfer-note -1 outcome-unknown ;
: lf-iproj-unknown ( -- -1 status ) -1 outcome-unknown ;

\ Spines: argument i of node, which has n arguments (as iota.fs).
: lf-iproj-arg ( node n i -- arg ) - 1- 0 ?do lf-term-first@ loop lf-term-second@ ;
: lf-iproj-n ( node -- n ) lf-mhead-spine nip ;
: lf-iproj-head ( node -- head ) lf-mhead-spine drop ;
: lf-iproj-pi? ( node -- flag ) lf-term-tag@ lf-tag-pi = ;

\ An inference aside, Lean's infer_only, which compares nothing: xt
\ ( x -- y status ) run with inference's rejection rules off (and no
\ step logged, mixed-infer.fs). Also iota.fs's (R3).
: lf-iproj-aside ( x xt -- y status )
  lf-minfer-aside @ >r true lf-minfer-aside ! execute r> lf-minfer-aside ! ;
\ is_prop (383-389), aside: x's type's whnf a Sort whose level is zero.
\ An inference that fails as invalid is unknown here.
: lf-iproj-zero ( x -- flag status )
  lf-minfer-walk ok-then? 0= if false swap exit then
  lf-minfer-whnf-job ok-then? 0= if false swap exit then
  lf-minfer-sort? 0= if false outcome-unknown exit then lf-minfer-zero? ;
: lf-iproj-prop? ( x -- flag status )
  ['] lf-iproj-zero lf-iproj-aside dup outcome-invalid = if drop outcome-unknown then ;

\ The structure's input declaration: Ty's head a constant named as the
\ leaf, which a usable slot holds as an inductive type with one
\ constructor and Ty's n arguments as its parameters and indices -- its
\ numIndices as LeanForth's block check computed it (lf-env-shape; review
\ rvCONV B2), never the file's, which Lean's replay ignores; a type
\ without a shape is unknown. (decl ok), the leaf rejected, or a failure.
: lf-iproj-arity ( d decl -- n outcome )
  lf-idecl-data lf-ity-params lf-more-field swap lf-env-shape
  ok-then? 0= if nip no-result exit then
  dup lf-shape-known and 0= if 2drop lf-iproj-unknown exit then
  lf-shape-indices + outcome-ok ;
: lf-iproj-fits ( leaf n d decl -- decl outcome )
  tuck lf-iproj-arity ok-then? 0= if >r 2drop drop r> no-result exit then
  rot = over lf-env-one-ctor? and if nip outcome-ok else drop lf-iproj-bad then ;
: lf-iproj-slot ( leaf n d -- decl outcome )
  dup lf-whnf-absent = if drop 2drop lf-iproj-unknown exit then
  dup 0< if 2drop lf-iproj-bad exit then
  dup lf-whnf-decl ok-then? 0= if nip nip nip no-result exit then
  dup lf-idecl-kind @ lf-kind-inductive =
  if lf-iproj-fits else 2drop drop lf-iproj-bad then ;
: lf-iproj-named? ( leaf const -- flag )
  lf-whnf-cref lf-crec-name @ swap lf-proj-name lf-name-same? ;
\ Lean's env().get (259): no such constant is unknownConstant, the
\ lookup's rejection (N1); one the check declares itself stays absent.
: lf-iproj-get ( const -- d outcome )
  lf-whnf-cref lf-crec-name @ dup lf-envsig-local
  if 2drop lf-whnf-absent outcome-ok else lf-env-lookup-pass then ;
: lf-iproj-struct ( leaf n Ty -- decl outcome )
  lf-iproj-head dup lf-whnf-const? 0= if 2drop lf-iproj-bad exit then
  2 pick over lf-iproj-named? 0= if 2drop lf-iproj-bad exit then
  lf-iproj-get ok-then? 0= if nip nip no-result exit then lf-iproj-slot ;
: lf-iproj-checked ( leaf Ty -- decl outcome ) dup lf-iproj-n swap lf-iproj-struct ;

\ The constructor, and its type at Ty's universe arguments
\ (instantiate_type_lparams: the stored type itself without any).
: lf-iproj-ctor ( decl -- decl' outcome )
  lf-idecl-data lf-ity-ctors@ drop @ lf-whnf-find ok-then? 0= if no-result exit then
  dup 0< if drop lf-iproj-unknown exit then lf-whnf-decl ;
: lf-iproj-at ( ctor Ty -- r outcome )
  lf-iproj-head lf-whnf-cref lf-cref-pairs
  dup 0= if 2drop lf-idecl-type @ outcome-ok exit then
  lf-whnf-pairs! ok-then? 0= if nip nip no-result exit then
  rot dup lf-idecl-type @ swap 2swap lf-minfer-frames lf-whnf-substitute ;

\ A parameter: r's whnf a Pi (else invalidProj), its body instantiated
\ with Ty's argument i.
: lf-iproj-param ( L E Ty P r i -- L E Ty P r' outcome )
  >r lf-minfer-whnf-job ok-then? 0= if r> drop no-result exit then
  dup lf-iproj-pi? 0= if drop r> drop 3 pick lf-iproj-bad exit then
  lf-term-second@ 2 pick dup lf-iproj-n r> lf-iproj-arg lf-minfer-instantiate ;
\ The structure, its constructor's type, the parameters.
: lf-iproj-start ( L E Ty P r -- L E Ty P r' outcome )
  drop 3 pick 2 pick lf-iproj-checked ok-then? 0= if no-result exit then
  dup lf-iproj-ctor ok-then? 0= if nip no-result exit then
  3 pick lf-iproj-at ok-then? 0= if nip no-result exit then
  swap lf-idecl-data lf-ity-params lf-more-field
  0 ?do i lf-iproj-param ok-then? 0= if no-result unloop exit then loop outcome-ok ;
\ P: whether Ty is a proposition.
: lf-iproj-prop ( L E Ty P r -- L E Ty P' r outcome )
  nip over lf-iproj-prop? ok-then? 0= if >r drop 0 -1 r> exit then swap outcome-ok ;
\ A field of a proposition's structure must be a proof to be projected
\ or stood for (has_loose_bvars branch, and the result).
: lf-iproj-guard ( L E Ty P domain -- L E Ty P outcome )
  over 0= if drop outcome-ok exit then
  lf-iproj-prop? ok-then? 0= if exit then if outcome-ok exit then
  3 pick lf-iproj-bad nip ;
\ mk_proj(S, i, e): the projection of E with a leaf of the same structure
\ and index i.
: lf-iproj-mk ( L E i -- node outcome ) rot lf-proj-name swap lf-proj-of ;
\ Field i before the projected one: r's whnf a Pi (else invalidProj); a
\ body that depends on it is instantiated with E.i, else taken as it is.
: lf-iproj-field ( L E Ty P r i -- L E Ty P r' outcome )
  >r lf-minfer-whnf-job ok-then? 0= if r> drop no-result exit then
  dup lf-iproj-pi? 0= if drop r> drop 3 pick lf-iproj-bad exit then
  dup lf-term-second@ lf-minfer-frames lf-whnf-loose? ok-then? 0=
  if nip r> drop no-result exit then
  0= if lf-term-second@ r> drop outcome-ok exit then
  >r r@ lf-term-first@ lf-iproj-guard dup ok? 0= if r> r> 2drop no-result exit then drop
  r> lf-term-second@ 4 pick 4 pick r> lf-iproj-mk ok-then? 0= if nip no-result exit then
  lf-minfer-instantiate ;
: lf-iproj-fields ( L E Ty P r -- L E Ty P r' outcome )
  4 pick lf-proj-idx 0 ?do
    i lf-iproj-field ok-then? 0= if no-result unloop exit then
  loop outcome-ok ;
\ The projected field: r's whnf a Pi (else invalidProj), its domain.
: lf-iproj-end ( L E Ty P r -- L E Ty P r' outcome )
  lf-minfer-whnf-job ok-then? 0= if no-result exit then
  dup lf-iproj-pi? 0= if drop 3 pick lf-iproj-bad exit then
  lf-term-first@ dup >r lf-iproj-guard dup ok? 0= if r> drop no-result exit then
  drop r> outcome-ok ;

\ The whole computation, from e's type T.
: lf-iproj-then ( frame outcome xt -- frame' outcome )
  over ok? if nip execute else drop then ;
: lf-iproj-result ( L E Ty P r outcome -- type status ) 2>r 2drop 2drop 2r> ;
: lf-iproj-compute ( L E T -- type status )
  lf-minfer-whnf-job ok-then? 0= if nip nip no-result exit then
  0 0 outcome-ok ['] lf-iproj-start lf-iproj-then ['] lf-iproj-prop lf-iproj-then
  ['] lf-iproj-fields lf-iproj-then ['] lf-iproj-end lf-iproj-then lf-iproj-result ;

\ The hook's steps: e's type is a child visit, the leaf and e saved
\ across it; e, a source term read under the scope, is then closed.
: lf-iproj-typed ( T status frames -- type status frames 0 )
  >r r@ frame-restore r@ frame-restore 2swap
  ok-then? 0= if nip nip lf-minfer-none r> 0 exit then
  rot lf-minfer-close ok-then? 0= if nip nip lf-minfer-none r> 0 exit then
  swap lf-iproj-compute r> 0 ;
: lf-iproj ( leaf e frames -- ... frames next )
  >r over r@ frame-save dup r@ frame-save nip r> ['] lf-iproj-typed lf-minfer-call ;
' lf-iproj is lf-minfer-proj
