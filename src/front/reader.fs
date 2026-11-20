\ The natural reader (ADR 0021 D8; plan task FE1a): the meanings of
\ LeanForth's words in natural form (author/form.fs), which build syntax
\ trees (syntax.fs) for the elaborator (plan FE1e) instead of kernel terms.
\ Nothing here elaborates: what needs elaboration stops the run as not
\ supported yet, at its token. The rules (design docs/design/FRONT_END.md
\ section 4.2):
\ - a name takes as many values from the stack as its type has explicit
\   binders, and builds the application f a1 .. ak, arguments in Lean's
\   order (x y f is f x y); a library constant's count is its type's
\   telescope (lfn-library-arity, which the command line sets: the importer
\   stage holds the type); a variable's comes from its binder's type as
\   written: 0 for a variable, or a constant that cannot unfold, at its
\   head. A count that depends on unfolding a definition stops the run
\   (error 73) until the elaborator's whnf exists (plan FE1c);
\ - a number is a numeral (Lean's OfNat), at its own position (form.fs);
\ - ' NAME is the function NAME, applied to nothing; f a $ applies f to
\   one more argument (an application made by a name gets it as its next
\   argument, as Lean's id g x);
\ - the operator words are Lean's macros of a constant: + - * / % binop%,
\   = ≠ < > ≤ ≥ binrel%, ^ rightact%; ¬ ∧ ∨ ↔ ∣ are the constants Not, And,
\   Or, Iff and Dvd.dvd applied as names; <= >= /\ \/ <-> are Lean's ASCII
\   spellings of ≤ ≥ ∧ ∨ ↔; each word is checked against the printer's
\   notation table while loading (present/notation-table.fs);
\ - binder words take a type as written; := takes the statement; by right
\   after := opens a tactic proof; end NAME of a declaration keeps the
\   proof's node, runs the elaborator (lf-front-elaborate, which
\   front/elab-decl.fs sets; error 71 without it) and hands the result
\   over (handover.fs), and tactic words need the tactic engine (error 72).
\ Values are LeanForth values (author/values.fs) of a kind of their own,
\ each naming a syntax node. Untrusted: a tree is what was written; only
\ the kernel's check of the elaborated term decides anything.
\ Words: lf-front-statement ( -- node ) the statement of the declaration
\ being read, or -1; lf-front-by ( -- pos ) the position of its by, or -1;
\ lf-front-proof ( -- node ) its proof's node from end NAME on, or -1;
\ lfn-library-arity ( name -- arity unfolds? true | false ), a deferred
\ word the command line sets (cli/check-lf.fs).
\ State: one context record, lfn-decl (the declaration being read), in
\ the checker context (ADR 0009); the syntax store's (syntax.fs).

require ../lib/lib.fs
require ../lib/name-table.fs
require ../lib/text-run.fs
require ../present/notation-table.fs
require ../present/print-job.fs
require ../author/runner.fs
require ./syntax.fs
require ./handover.fs

begin-structure /lfn-decl
  field: lfn-decl-statement     \ the statement's node, or -1 before :=
  field: lfn-decl-by            \ position of by, or -1
  field: lfn-decl-proof         \ the proof's node at end NAME, or -1
end-structure
/lfn-decl context-record: lfn-decl
\ A declaration's trees and metavariables (front/mvars.fs) are its own.
: lfn-fresh ( -- )
  syn-reset lf-mctx-reset -1 lfn-decl lfn-decl-statement ! -1 lfn-decl lfn-decl-by !
  -1 lfn-decl lfn-decl-proof ! ;
' lfn-fresh context-setup
' lfn-fresh is lfa-declaration-fresh
: lf-front-statement ( -- node ) lfn-decl lfn-decl-statement @ ;
: lf-front-by ( -- pos ) lfn-decl lfn-decl-by @ ;
: lf-front-proof ( -- node ) lfn-decl lfn-decl-proof @ ;

\ Nodes; a store the heap cannot grow stops the run (full).
: lfn-new ( kind pos -- node ) syn-new 0= if lfa-e-syntax-full lfa-fail then ;
: lfn-arg-new ( app -- ) syn-arg-new lfa-e-syntax-full lfa-must ;

\ Syntax values.
: lfn-value ( node -- value ) lfa-kind-syntax swap 0 lfa-item-new ;
: lfn-item ( item -- node )
  dup lfa-item-kind @ lfa-kind-syntax = lfa-e-universe-term lfa-must lfa-item-first @ ;
: lfn-numeral ( n -- node ) syn-k-num lfa-numeral-at lfn-new swap syn-a! ;
\ A value or a number taken from the stack, as a node.
: lfn>syntax ( cell -- node ) dup 0< if lfa-take lfn-item else lfn-numeral then ;
: lfn-two ( x y -- nx ny ) lfn>syntax >r lfn>syntax r> ;

\ How many explicit arguments a name takes (-1: it depends on unfolding).
defer lfn-library-arity ( name -- arity unfolds? true | false )
:noname ( name -- false ) drop false ; is lfn-library-arity
: lfn-library ( decl -- arity unfolds? )
  dup lfa-library? 0= if drop -1 true exit then
  lfa-decl-name lfn-library-arity 0= if -1 true then ;
: lfn-const-arity ( decl -- n ) lfn-library drop ;
\ The head of a type as written: 0 when it is a variable or a constant
\ that cannot unfold, else -1.
: lfn-const-head ( decl -- n ) lfn-library nip if -1 else 0 then ;
: lfn-head-arity ( node -- n )
  dup syn-kind@ case
    syn-k-var of drop 0 endof
    syn-k-const of syn-a@ lfn-const-head endof
    drop -1 swap endcase ;
: lfn-type-arity ( node -- n )
  dup syn-kind@ syn-k-app = if syn-a@ then lfn-head-arity ;
: lfn-var-arity ( slot -- n ) lfa-binder lfa-binder-domain @ lfn-type-arity ;

\ A name, run: its node, at the name's position, and how many arguments
\ it takes.
: lfn-ident-node ( item kind -- node )
  over lfa-item-at @ lfn-new swap lfa-item-first @ syn-a! ;
: lfn-ident ( item -- node n )
  dup lfa-item-kind @ lfa-kind-const =
  if syn-k-const lfn-ident-node dup syn-a@ lfn-const-arity exit then
  syn-k-var lfn-ident-node dup syn-a@ lfn-var-arity ;
\ The application of node to the n values below it: a node and n
\ argument slots, filled from the last, which is on top.
: lfn-app-new ( node -- app ) syn-k-app over syn-at@ lfn-new swap syn-a! ;
: lfn-slots ( app n -- app ) 0 ?do dup lfn-arg-new loop ;
: lfn-take-arg ( v app i -- app ) rot lfn>syntax >r over swap r> syn-arg! ;
: lfn-fill ( v1 .. vn app n -- app ) ?dup if 0 swap 1- do i lfn-take-arg -1 +loop then ;
: lfn-args ( v1 .. vn node n -- app ) >r lfn-app-new r@ lfn-slots r> lfn-fill ;
\ n values must be above the frame (author/scopes.fs).
: lfn-check ( node n -- node n ) 2>r 2r@ nip lfa-args 2r> ;
\ After ' the name takes nothing; a count that depends on unfolding stops.
: lfn-apply ( node n -- value )
  lfa-untick if drop lfn-value exit then
  dup 0< 0= lfa-e-arity-unknown lfa-must
  ?dup if lfn-check lfn-args then lfn-value ;
\ A name's value in natural form; a universe parameter alone stays one.
: lfn-universe-only? ( value -- flag )
  lfa-slot dup lfa-item-kind @ lfa-kind-name = swap lfa-item-first @ 0< and ;
: lfn-name ( value -- value' )
  dup lfn-universe-only? if lfa-tick-free exit then lfa-take lfn-ident lfn-apply ;
' lfn-name is lfa-name-natural

\ ' NAME: the next token, on this line, must be a name.
: lfn-peek ( -- c-addr u ) >in @ parse-name rot >in ! ;
: lfn-w-tick ( -- )
  lfn-peek dup 0<> lfa-e-no-name lfa-must lfa-number-like? 0= lfa-e-tick lfa-must
  lfa-here lfa-tick! ;
\ f a $: one more argument; an application made by a name takes it as
\ its next one, keeping its position.
: lfn-copy-args ( old new -- new )
  over syn-b@ 0 ?do dup lfn-arg-new over i syn-arg over i rot syn-arg! loop nip ;
: lfn-extend ( app -- app' ) dup syn-a@ lfn-app-new lfn-copy-args ;
: lfn-function ( node -- app )
  dup syn-kind@ syn-k-app = if lfn-extend else lfn-app-new then ;
: lfn-arg-add ( app arg -- app ) over lfn-arg-new over dup syn-b@ 1- rot syn-arg! ;
: lfn-w-app ( f a -- t ) 2 lfa-args lfn-two >r lfn-function r> lfn-arg-add lfn-value ;


\ Notation words (slice S3a-ops; owner, 2026-11-12 and 2026-11-20,
\ docs/project/OWNER_DECISIONS.md): Lean's notations of a constant
\ (Init/Notation.lean, Init/Core.lean), each building what Lean's macro
\ builds. An operator takes two values and builds the macro (binop%,
\ binrel% or rightact%, syntax.fs) of its constant; a notation name
\ (¬ ∧ ∨ ↔ ∣) is the constant of exactly that full name (Lean's hygienic
\ And✝: never a namespace's or the text's other And) applied as a name
\ is. A word is spelt as its constant's row in the printer's notation
\ table (present/notation-table.fs) in Unicode or in ASCII, so Lean's own
\ ASCII notation (<= >= /\ \/ <->) is a second word of the same constant;
\ where Lean has none (≠ ¬ ∣) the constant's name is the typed form. One
\ line gives a word its meaning (lfn-operator:, lfn-notation-name:): the
\ row is checked while loading (a missing or other spelling aborts), and
\ the natural meaning finds the word's entry by the token run. The words
\ are LF-WORDS's (author/words.fs, lfa-natural-words: reserved for the
\ printer, error 58 in kernel-form text, where ^ is the universe word),
\ the only syntax list a run searches (author/groups.fs): Forth's own
\ - / <= >= are not shadowed outside a run, and \/ /\ are tokens of
\ their own, never the comment word \.
\ The table: per word, the macro's kind (0: a notation name), then the
\ constant's name; two zero cells are an empty table (lib/name-table.fs),
\ read-only once loaded.
align here 0 , 0 , constant lfn-notations
: lfn-entry-kind ( entry -- kind ) name-entry-data @ ;
: lfn-entry-const ( entry -- c-addr u ) name-entry-data cell+ count ;
\ The entry of the word being run: every word that runs these has one.
: lfn-entry ( -- entry ) lfa-token lfn-notations name-table-find ;
: lfn-operands ( lhs rhs node -- node ) swap syn-c! swap syn-b! ;
: lfn-op-node ( entry -- node )
  dup lfn-entry-kind lfa-here lfn-new swap lfn-entry-const lfa-intern syn-a! ;
: lfn-w-operator ( a b -- t )
  2 lfa-args lfn-two lfn-entry lfn-op-node lfn-operands lfn-value ;
: lfn-root-const ( c-addr u -- decl )
  lfa-const-named 0= if lfa-e-unknown-constant lfa-fail then ;
: lfn-const-at ( decl -- node n )
  syn-k-const lfa-here lfn-new swap syn-a! dup syn-a@ lfn-const-arity ;
: lfn-w-named ( v1 .. vn -- t )
  lfn-entry lfn-entry-const lfn-root-const lfn-const-at lfn-apply ;
: lfn-w-notation ( v1 .. vn -- t )
  lfn-entry lfn-entry-kind if lfn-w-operator else lfn-w-named then ;
\ Registering (load-time words): the entry made (a word twice aborts);
\ its constant's row must spell it, in Unicode or ASCII, blanks trimmed.
: lfn-entry, ( c-addr u kind word-addr word-u -- entry )
  2dup lfn-notations name-table-find abort" reader.fs: a notation word twice"
  lfn-notations name-entry , counted, lfn-notations cell+ @ ;
: lfn-row ( entry -- row | 0 ) lfn-entry-const lf-nt-find ;
: lfn-mode-spells? ( entry mode -- flag )
  over lfn-row swap lf-nt-sym text-trim rot name-entry-name compare 0= ;
: lfn-spelt? ( entry -- flag )
  dup lfn-row 0= if drop false exit then
  dup lf-print-unicode lfn-mode-spells? swap lf-print-ascii lfn-mode-spells? or ;
: lfn-operator: ( c-addr u kind "word" -- )
  >in @ >r parse-name lfn-entry, lfn-spelt? 0=
  abort" reader.fs: a notation word its constant's row lacks"
  r> >in ! ['] lfn-w-notation lfa-natural! ;
: lfn-notation-name: ( c-addr u "word" -- ) 0 lfn-operator: ;
\ The meanings. Lean: infixl:65 + -, infixl:70 * / %, infix:50 = < >,
\ unicode(" ≤ ", " <= "), unicode(" ≥ ", " >= ") (Init/Notation.lean:
\ 284-288, 375-378), infix:50 ≠ (Init/Core.lean:880); notation ¬ and
\ unicode(" ∧ ", " /\\ "), unicode(" ∨ ", " \\/ ") (Notation.lean:404-406),
\ infix:20 ↔ and <-> (Core.lean:196-197), infix:50 ∣ (Notation.lean:280);
\ ^ is rightact% HPow.hPow (Notation.lean:311; owner, 2026-11-20).
s" HAdd.hAdd" syn-k-binop lfn-operator: +    s" HSub.hSub" syn-k-binop lfn-operator: -
s" HMul.hMul" syn-k-binop lfn-operator: *    s" HDiv.hDiv" syn-k-binop lfn-operator: /
s" HMod.hMod" syn-k-binop lfn-operator: %    s" HPow.hPow" syn-k-rightact lfn-operator: ^
s" Eq" syn-k-binrel lfn-operator: =          s" Ne" syn-k-binrel lfn-operator: ≠
s" LT.lt" syn-k-binrel lfn-operator: <       s" GT.gt" syn-k-binrel lfn-operator: >
s" LE.le" syn-k-binrel lfn-operator: ≤       s" LE.le" syn-k-binrel lfn-operator: <=
s" GE.ge" syn-k-binrel lfn-operator: ≥       s" GE.ge" syn-k-binrel lfn-operator: >=
s" Not" lfn-notation-name: ¬       s" Dvd.dvd" lfn-notation-name: ∣
s" And" lfn-notation-name: ∧       s" And" lfn-notation-name: /\
s" Or" lfn-notation-name: ∨        s" Or" lfn-notation-name: \/
s" Iff" lfn-notation-name: ↔       s" Iff" lfn-notation-name: <->


\ Binders: the type as written.
: lfn-binder ( t kind -- ) ['] lfn>syntax lfa-binder-of ;
: lfn-w-explicit ( t -- ) 1 lfa-args lf-binder-default lfn-binder ;
: lfn-w-implicit ( t -- ) 1 lfa-args lf-binder-implicit lfn-binder ;
: lfn-w-strict ( t -- ) 1 lfa-args lf-binder-strict lfn-binder ;
: lfn-w-instance ( t -- ) 1 lfa-args lf-binder-instance lfn-binder ;

\ := takes the statement, as in the kernel form (author/declarations.fs).
: lfn-w-define ( -- )
  lfa-define-check lfn>syntax lfn-decl lfn-decl-statement ! lfa-define-done ;
\ by: right after := (no value and no binder since), once.
: lfn-by-here? ( -- flag )
  lfa-above 0= lfa-inside? and lfa-params 0< 0= and lfa-depth lfa-params = and
  lf-front-by 0< and ;
: lfn-w-by ( -- ) lfn-by-here? lfa-e-by-here lfa-must lfa-here lfn-decl lfn-decl-by ! ;
\ end NAME of a declaration: the proof (or an axiom's statement) is in
\ place and kept as a node; then the elaborator (plan FE1e) and the
\ hand-over to the kernel (front/handover.fs), and the declaration is made.
: lfn-proof-shape ( above -- )
  lfa-proof-ready lf-front-by 0< if 1 = else 0= then lfa-e-proof lfa-must ;
: lfn-shape ( above -- )
  lfa-statement-only? if 1 = lfa-e-statement lfa-must else lfn-proof-shape then ;
: lfn-last ( above -- node ) if lfn>syntax else -1 then ;
: lfn-kept ( -- addr )
  lfa-statement-only? if lfn-decl lfn-decl-statement else lfn-decl lfn-decl-proof then ;
: lfn-keep ( node -- ) lfn-kept ! ;
: lfn-end-declaration ( above c-addr u -- )
  lfa-end-check dup lfn-shape lfn-last lfn-keep
  lf-front-elaborate lf-front-hand-over lfa-declared ;
: lfn-w-end ( -- ) lfa-end-head ['] lfn-end-declaration lfa-end-tail ;

\ The natural meanings (author/groups.fs, lfa-natural!).
' lfn-w-tick lfa-natural! '
' lfn-w-app lfa-natural! $
' lfn-w-explicit lfa-natural! explicit:
' lfn-w-implicit lfa-natural! implicit:
' lfn-w-strict lfa-natural! strict-implicit:
' lfn-w-instance lfa-natural! instance:
' lfn-w-define lfa-natural! :=
' lfn-w-by lfa-natural! by
' lfn-w-end lfa-natural! end
