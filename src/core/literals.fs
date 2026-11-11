\ Natural-number literals (plan task 5.2.3; ADR 0014 K7, rules L1-L3):
\ Lean's Expr.lit (.natVal n). LeanForth stores one as a leaf, tag
\ lf-tag-lit, whose second field is the number of limbs of n (lib/
\ bignum.fs's limbs: cells, least significant first, the top one not
\ zero, so 0 has none) and whose first field is the index of its limbs
\ in this context's limb slab (lf-lit-limbs), or 0 for n = 0. Term fields
\ are 32 bits wide (terms.fs), so even a one-limb n is kept in the slab
\ (compact-store plan step S3; before, it was the first field). The
\ representation is unique, so two literals are
\ Lean's == exactly when their counts and limbs are (lf-lit-same?). A
\ literal is a leaf of its own: every pass treats it as a closed term
\ without levels, as Lean's passes treat Expr.lit. The limbs live in the
\ context that made the literal, as its terms do (terms.fs); a rollback
\ of the term store leaves them (unreferenced) in the slab. String
\ literals stay unsupported forms (core/unsupported-forms.fs, U2).
\ Untrusted [import][kernel] data; nothing here checks types.
\ State: the limb slab, a member of the checker context.

require ../lib/lib.fs
\ lib/json.fs and lib/bignum.fs each define decimal-digit? (the same
\ test), and the second to load warns: json.fs is loaded first and the
\ warning silenced (Gforth's WARNINGS), until one keeps it private.
require ../lib/json.fs
[defined] warnings [if] warnings @ warnings off [then]
require ../lib/bignum.fs
[defined] warnings [if] warnings ! [then]
require ../lib/slab.fs
require ./generation-handles.fs
require ./terms.fs

11 constant lf-tag-lit
1 cells context-slab: lf-lit-limbs

: lf-lit-leaf? ( node -- flag ) lf-term-tag@ lf-tag-lit = ;
\ The limbs of a literal leaf: their address (valid until the slab grows)
\ and count.
: lf-lit-vector ( leaf -- addr n )
  dup lf-term-first@ lf-lit-limbs slab-at swap lf-term-second@ ;
\ Lean's ==, Nat.beq: the same count and limbs.
: lf-lit-limbs= ( a1 a2 n -- flag ) cells tuck compare 0= ;
: lf-lit-same? ( a b -- flag )
  lf-lit-vector rot lf-lit-vector rot over <> if 2drop drop false exit then
  lf-lit-limbs= ;
\ The value of a literal of at most one limb.
: lf-lit-small? ( leaf -- flag ) lf-term-second@ 2 < ;
: lf-lit-cell ( leaf -- u )
  dup lf-term-second@ if lf-term-first@ lf-lit-limbs slab-at @ else drop 0 then ;

\ A literal from n normalized limbs at addr: the first field, the limbs
\ kept in the slab when n is 1 or more (ok, or full).
: lf-lit-kept ( addr n -- first outcome )
  dup lf-lit-limbs slab-claim ok-then? 0= if >r 2drop r> no-result exit then
  >r r@ lf-lit-limbs slab-at swap cells move r> outcome-ok ;
: lf-lit-first ( addr n -- first outcome )
  dup 0= if 2drop 0 outcome-ok exit then lf-lit-kept ;
: lf-hterm-lit ( addr n -- index identity true | false )
  tuck lf-lit-first ok-then? 0= if 2drop false exit then
  lf-tag-lit swap rot lf-term-add lf-hterm-result ;
\ A literal from a number of lib/bignum.fs.
: lf-hterm-big ( big -- index identity true | false ) big-vector lf-hterm-lit ;
\ A literal of one cell's value, its limb passed through a cell of the
\ context.
1 cells context-record: lf-lit-one
: lf-hterm-cell ( u -- index identity true | false )
  lf-lit-one ! lf-lit-one dup @ 0<> 1 and lf-hterm-lit ;

\ Fields of a well-formed literal leaf (the audit,
\ core/constant-term-boundary.fs): a count of 0 with 0, or of 1 and more
\ limbs in the slab, the top one not 0.
: lf-lit-span? ( first n -- flag )
  2dup + lf-lit-limbs slab-count 1+ < >r over 0< 0= r> and
  if + 1- lf-lit-limbs slab-at @ 0<> else 2drop false then ;
: lf-lit-fields? ( first second -- flag )
  dup 0< if 2drop false exit then
  dup 0= if drop 0= exit then lf-lit-span? ;
: lf-lit-check ( first second walk -- outcome ) drop lf-lit-fields? flag>outcome ;

\ Scratch arenas on the heap for one computation (kernel/reduce-nat.fs,
\ the importer): the arena record and its memory in one block of cells.
: lf-lit-arena ( cells -- arena outcome )
  cells dup /big-arena + allocate if 2drop -1 outcome-full exit then
  dup >r /big-arena + swap r@ big-arena-init r> outcome-ok ;
: lf-lit-arena-free ( arena -- ) free drop ;
\ A literal leaf copied into arena as a number.
: lf-lit>big ( leaf arena -- big outcome )
  >r lf-lit-vector dup r@ arena-claim 0= if 2drop r> drop outcome-full no-result exit then
  >r r@ big-limbs swap cells move r> r> drop outcome-ok ;
\ The literal whose decimal digits are at addr u (the importer): as a
\ handle, or false for text that is not digits, or no room.
: lf-hterm-decimal ( addr u -- index identity true | false )
  dup 9 / 8 + lf-lit-arena ok? 0= if drop 2drop false exit then
  >r r@ decimal>big ok? if lf-hterm-big else drop false then r> lf-lit-arena-free ;
