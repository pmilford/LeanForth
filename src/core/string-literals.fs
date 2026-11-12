\ String literals (plan task 5.2.3, its string part; ADR 0015 L2, L4):
\ Lean's Expr.lit (.strVal s). LeanForth stores one as a leaf, tag
\ lf-tag-str, whose first field is the offset of s's UTF-8 bytes in this
\ context's byte slab (lf-str-bytes) and whose second field is their
\ number. The bytes are valid UTF-8 (lib/bytes.fs's utf8-valid?: Unicode
\ scalar values only, as a Lean String holds): lf-str-new refuses any
\ other text as invalid. Two literals are Lean's == exactly when their
\ bytes are (lf-str-same?), as Lean compares two strVal by their text. A
\ literal is a closed leaf without levels, as Lean's passes treat
\ Expr.lit; its type, its expansion into String.ofList and the rules that
\ use it are kernel/string-literals.fs's. The bytes live in the context
\ that made the literal, as its terms do; a rollback of the term store
\ leaves them (unreferenced) in the slab. No fixed length: the slab grows
\ on the heap, and no room is full, never a verdict.
\ Untrusted [import][kernel] data; nothing here checks types.
\ State: the byte slab, a member of the checker context.

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/slab.fs
require ./generation-handles.fs
require ./literals.fs
require ./terms.fs

13 constant lf-tag-str
\ An input literal of a term view (terms.fs) has its bytes in the leaf table.
lf-tag-str tag-str lf-term-input-leaf-tag
1 chars context-slab: lf-str-bytes

\ The bytes of a source context's fed input copied, as literals.fs's
\ lf-lit-copy copies limbs (14,045 bytes for Mathlib's first sixth).
: lf-str-copy ( source -- outcome ) lf-str-bytes swap lf-slab-copy-in ;
: lf-str-leaf? ( node -- flag ) lf-term-tag@ lf-tag-str = ;
\ One of Lean's Expr.lit: a natural-number literal (core/literals.fs) or
\ a string literal.
: lf-literal-tag? ( tag -- flag ) dup lf-tag-lit = swap lf-tag-str = or ;
\ A literal leaf's bytes: their address (valid until the slab grows) and
\ number.
: lf-str-text ( leaf -- addr u )
  dup lf-term-first@ lf-str-bytes slab-at swap lf-term-second@ ;
\ Lean's == on two string literals: the same bytes.
: lf-str-same? ( a b -- flag ) lf-str-text rot lf-str-text compare 0= ;

\ A literal of the text at addr u, as a handle: ok; invalid for text that
\ is not UTF-8 (nothing kept); full when the slab or the term store has
\ no room.
: lf-str-keep ( addr u -- first outcome )
  dup lf-str-bytes slab-claim ok-then? 0= if >r 2drop r> no-result exit then
  >r r@ lf-str-bytes slab-at swap move r> outcome-ok ;
\ The same literal's fields, its bytes kept in the slab but no node made:
\ an input literal of a term view (terms.fs), whose node is the tier's.
: lf-str-fields ( addr u -- first u outcome )
  2dup utf8-valid? 0= if 2drop 0 0 outcome-invalid exit then
  tuck lf-str-keep >r swap r> ;
: lf-str-new ( addr u -- index identity outcome )
  2dup utf8-valid? 0= if 2drop 0 0 outcome-invalid exit then
  tuck lf-str-keep ok-then? 0= if nip 0 0 rot exit then
  lf-tag-str swap rot lf-term-add lf-hterm-result
  if outcome-ok else 0 0 outcome-full then ;

\ Fields of a well-formed literal leaf (the audit,
\ core/constant-term-boundary.fs): both nonnegative, the bytes inside the
\ slab's units in use. Their UTF-8 is checked where they are read.
: lf-str-fields? ( first second -- flag )
  over 0< over 0< or if 2drop false exit then
  swap lf-str-bytes slab-count swap - swap - 0< 0= ;
: lf-str-check ( first second walk -- outcome ) drop lf-str-fields? flag>outcome ;
