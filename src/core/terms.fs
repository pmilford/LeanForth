\ Experimental bounded storage for the syntax of a small Lean expression subset.
\ Constructors validate indices and payload ranges only; they do not check scope,
\ types, universe semantics, declarations, or proofs. This is not a kernel API.
\ Nodes occupy three cells: tag, first field, second field. Child references
\ must name already allocated nodes, so constructors cannot create cycles.
\ The arena is global and single-threaded. Reset invalidates all old indices;
\ reused indices cannot be distinguished from stale ones. No host pointer or
\ cell layout is a portable serialization format.

64 constant lf-term-capacity
1 constant lf-tag-sort
2 constant lf-tag-bvar
3 constant lf-tag-app
4 constant lf-tag-lam
5 constant lf-tag-pi
create lf-term-storage lf-term-capacity 3 * cells allot
variable lf-term-count
variable lf-term-generation
0 lf-term-generation !

\ Empty storage and advance its epoch. Saturation permanently invalidates
\ this arena instead of wrapping; bare reused indices remain unauthenticated.
: lf-term-reset ( -- )
  0 lf-term-count !
  lf-term-generation @ dup 0< if drop exit then
  dup -1 1 rshift = if drop -1 else 1+ then lf-term-generation ! ;

\ Validate the mutable allocation count before using it for addressing.
: lf-term-count-valid? ( -- flag )
  lf-term-count @ dup 0< 0= swap lf-term-capacity <= and
  lf-term-generation @ 0< 0= and ;

\ Return true only for an index in a valid current allocation range.
: lf-term-valid? ( index -- flag )
  lf-term-count-valid? 0= if drop false exit then
  dup 0< 0= swap lf-term-count @ < and ;

\ Compute a slot address; this internal helper requires a valid index or the
\ current count during allocation, and must not be called on untrusted input.
: lf-term-slot ( index -- addr ) 3 * cells lf-term-storage + ;

\ Store a validated node; callers supply a supported tag and validated fields.
\ On exhaustion return false without changing the arena or allocation count.
: lf-term-add ( tag first second -- index true | false )
  lf-term-count-valid? 0= if 2drop drop false exit then
  lf-term-count @ lf-term-capacity >= if 2drop drop false exit then
  lf-term-count @ lf-term-slot >r
  r@ 2 cells + ! r@ cell+ ! r> !
  lf-term-count @ 1 lf-term-count +! true ;

\ Construct a sort with a concrete nonnegative universe level.
\ This stores syntax only; no universe or type judgment is performed.
: lf-term-sort ( level -- index true | false )
  dup 0< if drop false exit then
  lf-tag-sort swap 0 lf-term-add ;

\ Construct a nonnegative de Bruijn variable index. Scope is not checked.
: lf-term-bvar ( index -- index true | false )
  dup 0< if drop false exit then
  lf-tag-bvar swap 0 lf-term-add ;

\ Store a binary node after validating the tag and both child references.
\ Invalid tags, invalid children or exhaustion leave the arena unchanged.
: lf-term-binary ( left right tag -- index true | false )
  dup lf-tag-app = over lf-tag-lam = or over lf-tag-pi = or 0= if
    drop 2drop false exit
  then
  >r over lf-term-valid? over lf-term-valid? and 0= if
    r> drop 2drop false exit
  then
  r> -rot lf-term-add ;

\ Construct an application, with function and argument in that order.
: lf-term-app ( function argument -- index true | false )
  lf-tag-app lf-term-binary ;

\ Construct a lambda from an annotation and body. The body is not scope-checked.
: lf-term-lam ( annotation body -- index true | false )
  lf-tag-lam lf-term-binary ;

\ Construct a dependent function type from its domain and body, without typing.
: lf-term-pi ( domain body -- index true | false )
  lf-tag-pi lf-term-binary ;

\ Read a node by index, returning its tag and fields followed by true. Invalid
\ indices return only false; no memory is accessed for an invalid index.
: lf-term-read ( index -- tag first second true | false )
  dup lf-term-valid? 0= if drop false exit then
  lf-term-slot dup @ swap cell+ dup @ swap cell+ @ true ;
