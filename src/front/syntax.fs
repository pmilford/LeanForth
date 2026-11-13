\ The syntax store of natural LeanForth (ADR 0021 D8; plan task FE1a): the
\ trees the natural reader builds (reader.fs), shaped like Lean's syntax
\ after macro expansion, which the elaborator will read (plan FE1e). Each
\ node has a kind, three fields and its position in the author's text
\ (line * 65536 + column, author/source.fs). Kinds and fields:
\   syn-k-const   a: the declaration of the run it names (author/constants.fs)
\   syn-k-var     a: the binder slot of the variable (author/scopes.fs)
\   syn-k-num     a: the numeral's value (Lean's num literal, an OfNat numeral)
\   syn-k-app     a: the function node  b: the number of arguments, which
\                 are the a fields of the syn-k-arg nodes right after it
\   syn-k-arg     a: one argument node of the application before it
\   syn-k-binop   a: Lean's function name (a name ID)  b, c: the operands
\                 (Lean's binop% f a b)
\   syn-k-binrel  the same for a relation (Lean's binrel% f a b)
\   syn-k-hyp     a: the name of a hypothesis a tactic introduces  b: its
\                 argument in the tactic record (tactic-syntax.fs)
\ So 0 n + n = is binrel% Eq (binop% HAdd.hAdd 0 n) n, and x y f, with f
\ taking two explicit arguments, is app f [x, y]. An operator's name is
\ Lean's hygienic one (HAdd.hAdd✝, Eq✝ in Lean's expansion): it always
\ means the global constant, so the elaborator (plan FE1e) resolves it at
\ the root, never through namespace, open or a local binder. Nodes are in a heap
\ store that grows up to a limit, only the heap's (plan task 6.2.0);
\ indices stay valid until syn-reset, which a new declaration does, and
\ addresses until the next node. Untrusted: a tree says what was written,
\ never what it means; the kernel checks whatever the elaborator makes.
\ Words: syn-reset, syn-new ( kind pos -- node true | false ), syn-arg-new
\ ( node -- true | false ), the setters syn-a! syn-b! syn-c! ( node x --
\ node ), the readers syn-kind@ syn-a@ syn-b@ syn-c@ syn-at@ ( node -- x ),
\ syn-arg ( node i -- arg ), syn-count ( -- n ), syn-valid? ( node -- flag ).
\ State: the store header syn-store, a member of the checker context
\ (ADR 0009) whose block is on the heap, freed by its teardown word.

require ../lib/lib.fs

1 constant syn-k-const
2 constant syn-k-var
3 constant syn-k-num
4 constant syn-k-app
5 constant syn-k-arg
6 constant syn-k-binop
7 constant syn-k-binrel
8 constant syn-k-hyp

begin-structure /syn
  field: syn-kind
  field: syn-a
  field: syn-b
  field: syn-c
  field: syn-at        \ position in the author's text
end-structure

store-header context-record: syn-store
16 constant syn-room
max-n store-header - /syn cell+ / constant syn-limit
: syn-make ( -- )
  syn-room /syn 0 syn-store store-heap-init ok? 0= abort" syntax: no heap"
  syn-limit syn-store store-limit! ok? 0= abort" syntax: limit" ;
' syn-make context-setup
:noname ( -- ) syn-store store-heap-free ; context-teardown

: syn-reset ( -- ) syn-store store-clear ;
: syn-count ( -- n ) syn-store store-count @ ;
: syn-valid? ( node -- flag ) syn-store store-valid? ;
\ Node node's record (unchecked: a node this store gave).
: syn-node ( node -- addr ) syn-store store-slot ;

\ A new node of kind at pos, its fields 0: false when the heap refuses.
: syn-fill ( kind pos addr -- ) dup /syn erase tuck syn-at ! syn-kind ! ;
: syn-new ( kind pos -- node true | false )
  syn-store store-ready ok? 0= if 2drop false exit then
  syn-store store-new-slot 0= if 2drop false exit then >r syn-fill r> true ;

\ Fields.
: syn-kind@ ( node -- kind ) syn-node syn-kind @ ;
: syn-a@ ( node -- x ) syn-node syn-a @ ;
: syn-b@ ( node -- x ) syn-node syn-b @ ;
: syn-c@ ( node -- x ) syn-node syn-c @ ;
: syn-at@ ( node -- pos ) syn-node syn-at @ ;
: syn-a! ( node x -- node ) over syn-node syn-a ! ;
: syn-b! ( node x -- node ) over syn-node syn-b ! ;
: syn-c! ( node x -- node ) over syn-node syn-c ! ;

\ Applications: the arguments follow the node, one syn-k-arg node each,
\ made right after it (syn-arg-new, which also counts it).
: syn-arg-new ( app -- true | false )
  dup syn-at@ syn-k-arg swap syn-new 0= if drop false exit then
  drop dup syn-b@ 1+ syn-b! drop true ;
: syn-arg ( app i -- arg ) + 1+ syn-a@ ;
: syn-arg! ( app i arg -- ) >r + 1+ r> syn-a! drop ;
