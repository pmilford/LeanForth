\ Sort representation check (ADR 0007): concrete Sorts carry a universe
\ number, symbolic Sorts a level-store index under a distinct tag, and one
\ term graph must use only the mode its caller expects. Untrusted; not a
\ kernel or a type checker. Level validity, lifetime, context, scope, typing
\ and proof validity are not established here.
\ State: one walk record, lf-repr-walker, holding the stack, fuel and mode;
\ a member of the checker context (lib/context.fs). Single-threaded within
\ one context; callers prevent concurrent mutation of the term store.

require ../lib/lib.fs
require ./diagnostics.fs
require ./terms.fs

6 constant lf-tag-symbolic-sort
\ An input Sort of a term view (terms.fs) has its level in the leaf table.
lf-tag-symbolic-sort tag-sort lf-term-input-leaf-tag
\ A symbolic Sort is shared (terms.fs) only while its stamps hold:
\ generation-handles.fs stamps it with its own identity and its level's,
\ and constant-term-boundary.fs's lf-term-reusable? checks them (compact-
\ store plan step S4: levels are hash-consed, so equal Sorts are one node).
0 constant lf-repr-concrete
1 constant lf-repr-symbolic
lf-walk-room context-walk: lf-repr-walker

\ Fuel left after a check; callers that share one budget read it back.
: lf-repr-fuel ( -- addr ) lf-repr-walker walk-fuel ;

\ Store symbolic Sort syntax only. A nonnegative payload is not proof that a
\ level exists, is in scope, is live, or has Lean semantics.
: lf-term-symbolic-sort ( level-index -- index true | false )
  dup 0< if drop false else lf-tag-symbolic-sort swap 0 lf-term-add then ;

\ Visiting one node. A leaf has a nonnegative first field and a zero second
\ field; a Sort must also match the walk's mode (symbolic means "not
\ concrete"). Bound variables are syntax only: binding depth is not checked.
: lf-repr-leaf? ( first second -- flag ) 0= swap 0< 0= and ;
: lf-repr-concrete? ( walk -- flag ) walk-arg @ lf-repr-concrete = ;
: lf-repr-sort-leaf ( first second flag -- outcome ) -rot lf-repr-leaf? and flag>outcome ;
: lf-repr-sort ( first second walk -- outcome ) lf-repr-concrete? lf-repr-sort-leaf ;
: lf-repr-symbolic-sort ( first second walk -- outcome ) lf-repr-concrete? 0= lf-repr-sort-leaf ;
: lf-repr-bvar ( first second walk -- outcome ) drop lf-repr-leaf? flag>outcome ;
: lf-repr-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop walk-children exit then
  case lf-tag-sort of lf-repr-sort endof
    lf-tag-symbolic-sort of lf-repr-symbolic-sort endof
    lf-tag-bvar of lf-repr-bvar endof walk-bad-tag endcase ;
: lf-repr-visit ( walk -- outcome ) ['] lf-repr-dispatch lf-term-visit ;

\ Walk one root with the current mode and the fuel left.
: lf-repr-site ( -- site ) c" tagged-sort-boundary lf-repr-check" ;
: lf-repr-walk ( root -- status )
  ['] lf-repr-visit lf-repr-walker lf-repr-site lf-diag-run ;

\ Set an explicit mode and budget; false means a bad mode or negative fuel.
: lf-repr-mode? ( mode -- flag ) dup lf-repr-concrete = swap lf-repr-symbolic = or ;
: lf-repr-start ( mode fuel -- flag )
  lf-repr-walker walk-budget 0= if drop false exit then
  dup lf-repr-mode? if lf-repr-walker walk-arg ! true else drop false then ;

\ Check one reachable graph. Success establishes only representation and
\ node shape; nothing else, and never theorem validity.
: lf-repr-check ( root mode fuel -- status )
  lf-repr-start 0= if drop-invalid exit then
  dup lf-term-root? if lf-repr-walk else drop-invalid then ;

\ Check two roots against one budget, even when the first is Sort-free.
\ Counts and nodes are never changed.
: lf-repr-check-pair ( root1 root2 mode fuel -- status )
  lf-repr-start 0= if 2drop outcome-invalid exit then
  2dup lf-term-pair-valid? 0= if 2drop outcome-invalid exit then
  swap lf-repr-walk ok-then? if lf-repr-walk then ;
