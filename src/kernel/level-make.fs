\ Universe levels as Lean's kernel builds and compares them (ADR 0011,
\ Amendment 1): ports of Lean 4.35.0's level.cpp (commit eb6cafb7) --
\ structural equality (operator==, 125-150), is_not_zero (160-172),
\ is_explicit (54-64), to_offset (67-74), is_one (110), and the
\ simplifying constructors mk_max (81-104) and mk_imax (112-123). Lean's
\ mk_succ (33) is the raw constructor, lf-level-succ. [kernel] code:
\ experimental, not through the review gate. Untrusted.
\ Preconditions: every level given is a live node whose reachable graph
\ a scope check validated (children earlier, known tags), and the store
\ does not change during a call except by the words here; equal parameter
\ IDs denote equal names and different IDs different names (the name
\ store interns names), as level-compare and the witnesses of level-value
\ assume.
\ State: one record, lf-lmk-state: how many leading nodes have current
\ facts, and per node its class (the smallest index of a structurally
\ equal node, so two levels are equal exactly when their classes are) and
\ its flags (never zero; has a parameter). A member of the checker context
\ (lib/context.fs). Facts are computed in index order on demand; every
\ public word first forgets them all (a raw write keeps a node's index),
\ and a caller that rolls the level store back calls lf-lmk-truncate. The
\ two rule tables of mk_max and mk_imax are shared and read-only.
\ Bounded work: the facts of n nodes take at most n*n/2 node comparisons;
\ no fuel. Single-threaded within one context.

require ../lib/lib.fs
require ../core/levels.fs

begin-structure /lf-lmkrec
  field: lf-lmkrec-known                            \ facts current below this index
  lf-level-capacity cells +field lf-lmkrec-classes
  lf-level-capacity cells +field lf-lmkrec-flags
end-structure
/lf-lmkrec context-record: lf-lmk-state

1 constant lf-lmk-nonzero   \ flag: not zero under any assignment (is_not_zero)
2 constant lf-lmk-param     \ flag: has a parameter (has_param)

: lf-lmk-known ( -- addr ) lf-lmk-state lf-lmkrec-known ;
: lf-lmk-class-cell ( index -- addr ) cells lf-lmk-state lf-lmkrec-classes + ;
: lf-lmk-flags-cell ( index -- addr ) cells lf-lmk-state lf-lmkrec-flags + ;
\ Unchecked: facts of a node below lf-lmk-known.
: lf-lmk-class@ ( index -- class ) lf-lmk-class-cell @ ;
: lf-lmk-flags@ ( index -- flags ) lf-lmk-flags-cell @ ;
\ Forget every fact; facts at and above count, after a rollback to count.
: lf-lmk-forget ( -- ) 0 lf-lmk-known ! ;
: lf-lmk-truncate ( count -- ) lf-lmk-known @ min lf-lmk-known ! ;

\ ---------------------------------------------------------------------------
\ Facts of one node, from its children's. A node with an unknown tag or a
\ child that is not earlier (possible only off the validated graphs) is
\ its own class, never equal to another node, and has no flags.
: lf-lmk-earlier? ( child index -- flag ) 0 swap within ;
: lf-lmk-shape? ( index -- flag )
  dup lf-level-slot node@ rot case
    lf-level-tag-zero of 2drop drop true endof
    lf-level-tag-param of 2drop drop true endof
    lf-level-tag-succ of drop swap lf-lmk-earlier? endof
    dup lf-level-binary-tag? if >r rot tuck lf-lmk-earlier? -rot lf-lmk-earlier? and r>
    else >r 2drop drop false r> then endcase ;
\ Two nodes alike: same tag and the same parameter ID or child classes.
: lf-lmk-firsts ( i j -- f f' ) lf-level-first@ swap lf-level-first@ swap ;
: lf-lmk-seconds ( i j -- s s' ) lf-level-second@ swap lf-level-second@ swap ;
: lf-lmk-classes= ( x y -- flag ) lf-lmk-class@ swap lf-lmk-class@ = ;
: lf-lmk-children= ( i j -- flag )
  2dup lf-lmk-firsts lf-lmk-classes= -rot lf-lmk-seconds lf-lmk-classes= and ;
: lf-lmk-fields= ( i j tag -- flag )
  case lf-level-tag-zero of 2drop true endof
    lf-level-tag-param of lf-lmk-firsts = endof
    lf-level-tag-succ of lf-lmk-firsts lf-lmk-classes= endof
    >r lf-lmk-children= r> endcase ;
: lf-lmk-tags ( i j -- tag tag' ) lf-level-tag@ swap lf-level-tag@ swap ;
: lf-lmk-alike? ( i j -- flag )
  dup lf-lmk-shape? 0= if 2drop false exit then
  2dup lf-lmk-tags over = if lf-lmk-fields= else drop 2drop false then ;
: lf-lmk-class-of ( index -- class )
  dup 0 ?do dup i lf-lmk-alike? if drop i unloop exit then loop ;
\ Flags: zero none; a parameter has one; succ is never zero; max is never
\ zero when either side is not; imax when its right side is not.
: lf-lmk-child-flags ( index -- first second )
  dup lf-level-first@ lf-lmk-flags@ swap lf-level-second@ lf-lmk-flags@ ;
: lf-lmk-imax-flags ( index -- flags )
  lf-lmk-child-flags swap lf-lmk-param and or ;
: lf-lmk-succ-flags ( index -- flags )
  lf-level-first@ lf-lmk-flags@ lf-lmk-param and lf-lmk-nonzero or ;
: lf-lmk-flags-of ( index -- flags )
  dup lf-level-tag@ case
    lf-level-tag-zero of drop 0 endof
    lf-level-tag-param of drop lf-lmk-param endof
    lf-level-tag-succ of lf-lmk-succ-flags endof
    lf-level-tag-max of lf-lmk-child-flags or endof
    >r lf-lmk-imax-flags r> endcase ;
: lf-lmk-facts-of ( index -- class flags )
  dup lf-lmk-shape? if dup lf-lmk-class-of swap lf-lmk-flags-of else 0 then ;
: lf-lmk-compute ( index -- )
  dup >r lf-lmk-facts-of r@ lf-lmk-flags-cell ! r> lf-lmk-class-cell ! ;
\ Make the facts current up to index (nothing when they already are).
: lf-lmk-upto ( limit -- ) lf-lmk-known @ ?do i lf-lmk-compute loop ;
: lf-lmk-fill ( index -- )
  1+ dup lf-lmk-known @ > if dup lf-lmk-upto lf-lmk-known ! else drop then ;
: lf-lmk-class ( level -- class ) dup lf-lmk-fill lf-lmk-class@ ;
: lf-lmk-flags ( level -- flags ) dup lf-lmk-fill lf-lmk-flags@ ;

\ ---------------------------------------------------------------------------
\ Lean's level queries. lf-lmk-same? is operator==: structural equality,
\ parameters by ID.
: lf-lmk-same? ( l1 l2 -- flag ) lf-lmk-class swap lf-lmk-class = ;
: lf-lmk-nonzero? ( level -- flag ) lf-lmk-flags lf-lmk-nonzero and 0<> ;
: lf-lmk-param? ( level -- flag ) lf-lmk-flags lf-lmk-param and 0<> ;
: lf-lmk-zero? ( level -- flag ) lf-level-tag@ lf-level-tag-zero = ;
: lf-lmk-succ? ( level -- flag ) lf-level-tag@ lf-level-tag-succ = ;
: lf-lmk-max? ( level -- flag ) lf-level-tag@ lf-level-tag-max = ;
\ to_offset: the level under all its successors, and how many there are.
: lf-lmk-offset ( level -- base k )
  0 begin over lf-lmk-succ? while swap lf-level-first@ swap 1+ repeat ;
: lf-lmk-explicit? ( level -- flag ) lf-lmk-offset drop lf-lmk-zero? ;
\ is_one: succ zero.
: lf-lmk-one? ( level -- flag )
  dup lf-lmk-succ? if lf-level-first@ lf-lmk-zero? else drop false then ;

\ ---------------------------------------------------------------------------
\ mk_max and mk_imax as rule tables, in Lean's order. Each rule gives the
\ choice it makes, or 0 to pass to the next: 1 the first argument, 2 the
\ second, 3 (mk_imax only) mk_max of both. No rule applying is 0: a new
\ raw node.
: lf-lmk-choose ( l1 l2 rules n -- choice )
  cells over + swap ?do 2dup i @ execute ?dup if nip nip unloop exit then
  cell +loop 2drop 0 ;
\ Both explicit (82-83): the deeper, the first on a tie (get_depth of an
\ explicit level is its number of successors).
: lf-lmk-deeper ( l1 l2 -- choice )
  lf-lmk-offset nip swap lf-lmk-offset nip > if 2 else 1 then ;
: lf-lmk-explicit-rule ( l1 l2 -- choice )
  2dup lf-lmk-explicit? swap lf-lmk-explicit? and if lf-lmk-deeper else 2drop 0 then ;
\ Equal (84-85, and imax 119-120): the first.
: lf-lmk-same-rule ( l1 l2 -- choice ) lf-lmk-same? 1 and ;
\ A zero argument (86-89): the other one.
: lf-lmk-zero-rule ( l1 l2 -- choice )
  swap lf-lmk-zero? if drop 2 else lf-lmk-zero? 1 and then ;
\ l2 is a max with l1 as one argument (90-91).
: lf-lmk-in-max? ( l1 l2 -- flag )
  dup lf-lmk-max? 0= if 2drop false exit then
  2dup lf-level-first@ lf-lmk-same? if 2drop true exit then
  lf-level-second@ lf-lmk-same? ;
: lf-lmk-max-rule ( l1 l2 -- choice )
  2dup lf-lmk-in-max? if 2drop 2 else swap lf-lmk-in-max? 1 and then ;
\ The same base under different offsets (95-99): the larger offset.
: lf-lmk-bases ( l1 l2 -- base1 base2 k1 k2 )
  lf-lmk-offset rot lf-lmk-offset 2swap rot swap ;
: lf-lmk-base-rule ( l1 l2 -- choice )
  lf-lmk-bases 2swap lf-lmk-same? if > if 1 else 2 then else 2drop 0 then ;
create lf-lmk-max-rules
  ' lf-lmk-explicit-rule , ' lf-lmk-same-rule , ' lf-lmk-zero-rule ,
  ' lf-lmk-max-rule , ' lf-lmk-base-rule ,
\ mk_imax: a right side never zero gives mk_max (113-114); a zero right
\ side is the result (115-116); so is the right side when the left is zero
\ or one (117-118); equal sides give the left (119-120).
: lf-lmk-nonzero-rule ( l1 l2 -- choice ) nip lf-lmk-nonzero? 3 and ;
: lf-lmk-right-zero-rule ( l1 l2 -- choice ) nip lf-lmk-zero? 2 and ;
: lf-lmk-low-rule ( l1 l2 -- choice ) drop dup lf-lmk-zero? swap lf-lmk-one? or 2 and ;
create lf-lmk-imax-rules
  ' lf-lmk-nonzero-rule , ' lf-lmk-right-zero-rule , ' lf-lmk-low-rule ,
  ' lf-lmk-same-rule ,
: lf-lmk-max-choice ( l1 l2 -- choice ) lf-lmk-max-rules 5 lf-lmk-choose ;
: lf-lmk-imax-choice ( l1 l2 -- choice ) lf-lmk-imax-rules 4 lf-lmk-choose ;

\ The chosen argument; a new raw node can fail (full store or spent
\ serial), recorded by lf-level-add.
: lf-lmk-pick ( l1 l2 choice -- level ) 1 = if drop else nip then ;
: lf-lmk-max ( l1 l2 -- level true | false )
  2dup lf-lmk-max-choice ?dup if lf-lmk-pick true else lf-level-max then ;
: lf-lmk-imax ( l1 l2 -- level true | false )
  2dup lf-lmk-imax-choice case 0 of lf-level-imax endof 3 of lf-lmk-max endof
    >r r@ lf-lmk-pick true r> endcase ;
\ Whether mk_max or mk_imax (tag) of two levels gives anything but a new
\ node of that tag over them.
: lf-lmk-simplifies? ( l1 l2 tag -- flag )
  lf-level-tag-max = if lf-lmk-max-choice else lf-lmk-imax-choice then 0<> ;

\ ---------------------------------------------------------------------------
\ Public words, each on two live levels of a valid store; any other input
\ gives false (or, for equality, false) without reading a node.
: lf-lmk-begin? ( l1 l2 -- l1 l2 flag ) lf-lmk-forget 2dup lf-level-pair-valid? ;
\ Lean's operator== on two levels.
: lf-level-same? ( l1 l2 -- flag ) lf-lmk-begin? if lf-lmk-same? else 2drop false then ;
\ Lean's mk_max and mk_imax: an argument, or a new node (false when the
\ level store is full or its serial spent).
: lf-level-mk-max ( l1 l2 -- level true | false )
  lf-lmk-begin? if lf-lmk-max else 2drop false then ;
: lf-level-mk-imax ( l1 l2 -- level true | false )
  lf-lmk-begin? if lf-lmk-imax else 2drop false then ;
