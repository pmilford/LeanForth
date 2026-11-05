\ Test driver for the first checker's Lean differentials (plan tasks 2.2.1
\ and 2.2.3; tables first-checker and binder-domains of
\ tests/core/lean-differential.py). Test-only.
\
\ It reads cases as tests/reference/first-checker-terms.lean and
\ binder-domains-terms.lean print them (each line prefixed: fc-case,
\ fc-decl), builds each case's declarations into a fresh input -- terms,
\ levels, names and references, with equal nodes shared, and a leaf of
\ src/core/unsupported-forms.fs for each form the first checker does not
\ support -- and checks them in input order with check-declaration
\ (src/kernel/check-declaration.fs) through the checked environment's
\ serial publisher (lf-env-run). Each case then prints, for its last
\ declaration:
\   ROW <id> <outcome> <code> <n1> <n2> <step>
\ with the outcome and diagnostic of that declaration's check and the step
\ at which it ended (lf-check-step@), then
\   VERDICT <id> <text>
\ as lf-check-verdict. prints it. Every slot of the case is also checked:
\ an accepted one must give a valid handle that its snapshot accepts and an
\ empty axiom set; any other must give no handle. A violation aborts.
\ Nothing here accepts a theorem; it observes the kernel code under test.

require ../../src/main.fs
decimal

: must ( flag -- ) 0= abort" first-checker driver: refused" ;
100000 constant fc-fuel
fc-fuel lf-check-budget

\ ---------------------------------------------------------------------------
\ Reading tokens of the current line.
: fc-token ( -- c-addr u ) parse-name dup 0= abort" first-checker driver: missing token" ;
: fc-char ( -- char ) fc-token drop c@ ;
: fc-number ( -- n ) 0 0 fc-token >number nip abort" first-checker driver: number" drop ;
: fc-expect ( c-addr u -- ) fc-token compare abort" first-checker driver: syntax" ;
\ A name as Lean prints it, its components joined by dots (none of the
\ tables' names has a dot inside a component): interned component by
\ component, as Lean's hierarchical name, so that the names Lean's kernel
\ matches (Nat.succ, Bool.true) are recognised.
: fc-intern ( c-addr u -- name )
  0 -rot begin 2dup s" ." search while
    >r >r drop r@ over - lf-name-str must r> 1+ r> 1-
  repeat 2drop lf-name-str must ;
: fc-name ( -- name ) fc-token fc-intern ;

\ ---------------------------------------------------------------------------
\ Shared nodes: a new level or term node is made only when no live node
\ has the same tag and fields (the key).
begin-structure /fc-key
  field: fc-key-tag
  field: fc-key-first
  field: fc-key-second
end-structure
create fc-key /fc-key allot
: fc-key! ( tag first second -- )
  fc-key fc-key-second ! fc-key fc-key-first ! fc-key fc-key-tag ! ;
: fc-key@ ( -- tag first second )
  fc-key fc-key-tag @ fc-key fc-key-first @ fc-key fc-key-second @ ;
: fc-key= ( tag first second -- flag )
  fc-key fc-key-second @ = swap fc-key fc-key-first @ = and
  swap fc-key fc-key-tag @ = and ;
: fc-level-find ( -- index true | false )
  lf-level-count @ 0 ?do i lf-level-read must fc-key= if i true unloop exit then loop
  false ;
: fc-level ( tag first second -- index )
  fc-key! fc-level-find 0= if fc-key@ lf-level-add must then ;
: fc-term-find ( -- index true | false )
  lf-term-count @ 0 ?do i lf-term-read must fc-key= if i true unloop exit then loop
  false ;

\ Levels in prefix form: z, s l, m l l, i l l, p name.
: fc-level-param ( -- level ) fc-name lf-level-tag-param swap 0 fc-level ;
: fc-read-level ( -- level )
  fc-char case
    [char] z of 0 endof
    [char] s of recurse lf-level-tag-succ swap 0 fc-level endof
    [char] m of recurse recurse lf-level-tag-max -rot fc-level endof
    [char] i of recurse recurse lf-level-tag-imax -rot fc-level endof
    [char] p of fc-level-param endof
    true abort" first-checker driver: level" endcase ;

\ Terms. Symbolic Sorts are stamped and constants made through their
\ boundary words; both are shared like the other nodes.
: fc-sort ( level -- node )
  lf-tag-symbolic-sort over 0 fc-key! fc-term-find if nip exit then
  dup lf-level-identity must lf-hterm-sort must drop ;
: fc-binary ( left right tag -- node )
  >r 2dup r@ -rot fc-key! fc-term-find if nip nip r> drop exit then
  r> lf-term-binary must ;
: fc-bvar ( index -- node )
  lf-tag-bvar over 0 fc-key! fc-term-find if nip else lf-term-bvar must then ;
\ Reference arguments as (index identity) pairs, index first.
create fc-pairs 4096 2* cells allot   \ a constant's levels (no checker limit)
: fc-pair! ( level k -- )
  2* cells fc-pairs + >r dup lf-level-identity must swap r> 2! ;
: fc-levels ( n -- ) 0 ?do fc-read-level i fc-pair! loop ;
: fc-constant ( -- node )
  fc-name fc-number dup fc-levels >r
  lf-name-generation @ fc-pairs r> lf-cref-new must lf-cterm-new must drop ;
\ A form the first checker does not support becomes its leaf; free and
\ meta variables are invalid input, which no case of the tables holds.
\ Xlet is the leaf import/checker-input.fs still makes for a let (the
\ Lean printers write a let as E since plan task 4.2.3).
: fc-form ( c-addr u -- form )
  2dup s" Xlet" compare 0= if 2drop lf-form-let exit then
  2dup s" Xlit" compare 0= if 2drop lf-form-nat exit then
  2dup s" Xmdata" compare 0= if 2drop lf-form-mdata exit then
  s" Xproj" compare abort" first-checker driver: free or meta variable" lf-form-proj ;
: fc-unsupported ( c-addr u -- node )
  fc-form lf-tag-unsupported over 0 fc-key! fc-term-find if nip exit then
  lf-hterm-unsupported must drop ;
\ A let, E flag T v b (plan task 4.2.3): its leaf applied to v, then to
\ fun x : T => b, as core/let-terms.fs stores it; shared like the rest.
: fc-let-leaf ( flag -- node )
  lf-tag-let over 0 fc-key! fc-term-find if nip exit then lf-let-leaf must ;
: fc-let ( flag T v b -- node )
  rot swap lf-tag-lam fc-binary >r swap fc-let-leaf swap lf-tag-app fc-binary
  r> lf-tag-app fc-binary ;
: fc-read-term ( -- node )
  fc-token over c@ case
    [char] E of 2drop fc-number recurse recurse recurse fc-let endof
    [char] S of 2drop fc-read-level fc-sort endof
    [char] V of 2drop fc-number fc-bvar endof
    [char] A of 2drop recurse recurse lf-tag-app fc-binary endof
    [char] L of 2drop recurse recurse lf-tag-lam fc-binary endof
    [char] P of 2drop recurse recurse lf-tag-pi fc-binary endof
    [char] C of 2drop fc-constant endof
    [char] X of fc-unsupported endof
    true abort" first-checker driver: term" endcase ;

\ ---------------------------------------------------------------------------
\ Declarations.
create fc-buf /lf-idecl allot
: fc-kind ( c-addr u -- kind )
  2dup s" thm" compare 0= if 2drop lf-kind-theorem exit then
  2dup s" def" compare 0= if 2drop lf-kind-definition exit then
  2dup s" opq" compare 0= if 2drop lf-kind-opaque exit then
  s" ax" compare abort" first-checker driver: kind" lf-kind-axiom ;
: fc-safety ( c-addr u -- safety )
  2dup s" safe" compare 0= if 2drop lf-safety-safe exit then
  2dup s" unsafe" compare 0= if 2drop lf-safety-unsafe exit then
  s" partial" compare abort" first-checker driver: safety" lf-safety-partial ;
: fc-hint ( -- )
  fc-buf lf-idecl-kind @ lf-kind-definition =
  if lf-hint-regular 1 else lf-hint-opaque 0 then
  fc-buf lf-idecl-height ! fc-buf lf-idecl-hint ! ;
\ An optional HINT clause after the value (definitional-equality-
\ terms.lean): opaque, abbrev or regular with its height.
: fc-hint-kind ( c-addr u -- hint )
  2dup s" opaque" compare 0= if 2drop lf-hint-opaque exit then
  2dup s" abbrev" compare 0= if 2drop lf-hint-abbrev exit then
  s" regular" compare abort" first-checker driver: hint" lf-hint-regular ;
: fc-hint-clause ( -- )
  >in @ parse-name s" HINT" compare if >in ! exit then drop
  fc-token fc-hint-kind dup fc-buf lf-idecl-hint !
  lf-hint-regular = if fc-number else 0 then fc-buf lf-idecl-height ! ;
create fc-param-ids 4096 cells allot   \ a declaration's universe parameters
: fc-params ( -- )
  fc-param-ids fc-buf lf-idecl-params ! fc-number dup fc-buf lf-idecl-arity !
  0 ?do fc-name fc-param-ids i cells + ! loop ;
: fc-value ( -- value )
  >in @ fc-token s" none" compare 0= if drop -1 else >in ! fc-read-term then ;
: fc-head ( -- )
  fc-buf /lf-idecl erase
  fc-token 2drop fc-token fc-kind fc-buf lf-idecl-kind ! fc-token fc-safety
  fc-buf lf-idecl-safety ! fc-name fc-buf lf-idecl-name ! fc-params fc-hint ;
: fc-decl ( "declaration" -- )
  fc-head s" TYPE" fc-expect fc-read-term fc-buf lf-idecl-type !
  s" VALUE" fc-expect fc-value fc-buf lf-idecl-value ! fc-hint-clause
  fc-buf lf-input-add ok? must drop ;

\ ---------------------------------------------------------------------------
\ A fresh world for a case: u, v and w are the session's level context (a
\ superset of every declaration's parameters; rule L2, per declaration,
\ is check-declaration's), with one symbolic session; then the
\ declarations; then an environment.
create fc-id 80 allot
variable fc-id#
: fc-param ( c-addr u -- ) fc-intern lf-lscope-context-add must ;
: fc-world ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-input-reset s" u" fc-param s" v" fc-param s" w" fc-param lf-ssession-begin must ;
\ A universe parameter a case names beyond u, v and w joins the session's
\ level context before any term is built (the harness lists them after
\ fc-case), and the session starts again over it.
: fc-context ( "name" -- )
  fc-name dup lf-lscope-member? if drop exit then
  lf-lscope-context-add must lf-ssession-begin must ;
: fc-case ( "id" -- )
  fc-token dup fc-id# ! fc-id swap move fc-world ;

\ Every slot of the run: an accepted one has a handle valid in a view
\ and an empty axiom set; any other has no handle.
: fc-accepted-slot ( d -- )
  dup lf-env-handle ok? must lf-env-handle? ok? must lf-env-axioms ok? must 0= must ;
: fc-other-slot ( d -- ) lf-env-handle outcome-invalid = must 2drop ;
: fc-slot ( d -- ) dup lf-env-outcome ok? if fc-accepted-slot else fc-other-slot then ;
: fc-slots ( -- ) lf-input-count 0 ?do i fc-slot loop ;

\ The row of the case's last declaration; its diagnostic is the last
\ check's, read before the view.
: fc-last ( -- d ) lf-input-count 1- ;
: fc-.id ( -- ) fc-id fc-id# @ type space ;
: fc-row ( step -- )
  lf-diag@ nip >r >r >r ." ROW " fc-.id fc-last lf-env-outcome outcome-text type
  space r> r> r> . swap . . . cr ;
: fc-verdict ( -- ) ." VERDICT " fc-.id fc-last lf-check-verdict. cr ;
\ No new context after a THROW: a check that throws stops the run, and the
\ case fails.
: fc-no-maker ( -- context ior ) 0 -1 ;
: fc-check-all ( -- )
  ['] lf-check-declaration ['] fc-no-maker lf-env-run ok? must ;
: fc-report ( -- )
  lf-check-step@ lf-env-view ok? must fc-row fc-verdict fc-slots ;
: fc-run ( -- )
  lf-input-end ok? must 64 lf-env-new ok? must dup lf-env-use ok? must
  fc-check-all fc-report lf-env-free ok? must ;
