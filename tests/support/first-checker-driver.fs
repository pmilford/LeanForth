\ Test driver for the first checker's Lean differential (plan task 2.2.1;
\ table first-checker of tests/core/lean-differential.py). Test-only.
\
\ It reads the cases that tests/reference/first-checker-terms.lean prints
\ (each line prefixed: fc-case, fc-decl), builds each case's declarations
\ into a fresh input -- terms, levels, names and references, with equal
\ nodes shared -- and checks them in input order with the code paths that
\ exist before check-declaration (plan task 2.2.3): the checked
\ environment (N1, N2, L1-L3, K5: src/kernel/environment.fs) and the
\ definition and theorem probes (S1-S3, F1, D1-D5, inference). Accepted
\ earlier declarations become candidate signatures of the probes. The
\ declaration audit of 2.2.3 does not exist yet; this driver stands in for
\ it (U1: a kind other than a safe definition or theorem with a value; U2:
\ a let, literal, metadata, projection or free variable), and its rows say
\ so. Each case prints one line:
\   ROW <id> <outcome> <code> <n1> <n2> <source>
\ with the outcome and diagnostic of the case's own declaration, and source
\ "audit" when the stand-in audit decided, else "kernel".
\ Nothing here accepts a theorem; it observes the kernel code under test.

require ../../src/main.fs
decimal

: must ( flag -- ) 0= abort" first-checker driver: refused" ;
100000 constant fc-fuel

\ ---------------------------------------------------------------------------
\ Reading tokens of the current line.
: fc-token ( -- c-addr u ) parse-name dup 0= abort" first-checker driver: missing token" ;
: fc-char ( -- char ) fc-token drop c@ ;
: fc-number ( -- n ) 0 0 fc-token >number nip abort" first-checker driver: number" drop ;
: fc-expect ( c-addr u -- ) fc-token compare abort" first-checker driver: syntax" ;
: fc-intern ( c-addr u -- name ) 0 -rot lf-name-str must ;
: fc-name ( -- name ) fc-token fc-intern ;

\ ---------------------------------------------------------------------------
\ Per-declaration facts collected while reading: whether a term uses an
\ unsupported form, the universe parameters it uses and its constants
\ (name and number of universe arguments).
16 constant fc-uses-max
begin-structure /fc-facts
  field: fc-facts-unsupported
  field: fc-facts-params#
  field: fc-facts-consts#
  fc-uses-max cells +field fc-facts-params
  fc-uses-max 2* cells +field fc-facts-consts
end-structure
create fc-all-facts lf-input-capacity /fc-facts * allot
: fc-facts ( i -- addr ) /fc-facts * fc-all-facts + ;
: fc-current ( -- addr ) lf-input-count fc-facts ;
: fc-note-unsupported ( -- ) true fc-current fc-facts-unsupported ! ;
: fc-param# ( facts -- addr ) fc-facts-params# ;
: fc-note-param ( name -- )
  fc-current >r r@ fc-param# @ dup fc-uses-max < must
  cells r@ fc-facts-params + ! 1 r> fc-param# +! ;
: fc-note-const ( name n -- )
  fc-current >r r@ fc-facts-consts# @ dup fc-uses-max < must
  2* cells r@ fc-facts-consts + 2! 1 r> fc-facts-consts# +! ;

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
: fc-level-param ( -- level )
  fc-name dup fc-note-param lf-level-tag-param swap 0 fc-level ;
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
create fc-pairs lf-cref-argument-capacity 2* cells allot
: fc-pair! ( level k -- )
  2* cells fc-pairs + >r dup lf-level-identity must swap r> 2! ;
: fc-levels ( n -- ) 0 ?do fc-read-level i fc-pair! loop ;
: fc-constant ( -- node )
  fc-name fc-number 2dup fc-note-const dup fc-levels >r
  lf-name-generation @ fc-pairs r> lf-cref-new must lf-cterm-new must drop ;
\ An unsupported form leaves a placeholder: the audit stops its declaration.
: fc-unsupported ( c-addr u -- node ) 2drop fc-note-unsupported 0 fc-bvar ;
: fc-read-term ( -- node )
  fc-token over c@ case
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
: fc-params ( -- )
  fc-number dup fc-buf lf-idecl-arity !
  0 ?do fc-name fc-buf lf-idecl-params i cells + ! loop ;
: fc-value ( -- value )
  >in @ fc-token s" none" compare 0= if drop -1 else >in ! fc-read-term then ;
: fc-head ( -- )
  fc-buf /lf-idecl erase fc-current /fc-facts erase
  fc-token 2drop fc-token fc-kind fc-buf lf-idecl-kind ! fc-token fc-safety
  fc-buf lf-idecl-safety ! fc-name fc-buf lf-idecl-name ! fc-params fc-hint ;
: fc-decl ( "declaration" -- )
  fc-head s" TYPE" fc-expect fc-read-term fc-buf lf-idecl-type !
  s" VALUE" fc-expect fc-value fc-buf lf-idecl-value !
  fc-buf lf-input-add ok? must drop ;

\ ---------------------------------------------------------------------------
\ A fresh world for a case: u and v are the level context (a superset of
\ every declaration's parameters; rule L2 is the environment's), with one
\ symbolic session; then the declarations; then an environment.
create fc-id 80 allot
variable fc-id#
: fc-world ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-input-reset s" u" fc-intern lf-lscope-context-add must
  s" v" fc-intern lf-lscope-context-add must lf-ssession-begin must ;
: fc-case ( "id" -- )
  fc-token dup fc-id# ! fc-id swap move fc-world ;

\ The check of the declaration in this context's snapshot.
: fc-me ( -- i ) lf-env-cand lf-cand-decl @ ;
: fc-my ( -- facts ) fc-me fc-facts ;
: fc-decl@ ( -- decl ) fc-me lf-input-decl ;
variable fc-audited
: fc-in-scope? ( -- flag )
  fc-decl@ dup lf-idecl-kind @ dup lf-kind-theorem = swap lf-kind-definition = or
  over lf-idecl-safety @ lf-safety-safe = and swap lf-idecl-value @ 0< 0= and
  fc-my fc-facts-unsupported @ 0= and ;
: fc-audit ( -- outcome )
  fc-in-scope? if outcome-ok else true fc-audited ! outcome-unsupported then ;
\ L2 for each parameter a term uses.
: fc-param@ ( k -- name ) cells fc-my fc-facts-params + @ ;
: fc-l2 ( -- outcome )
  fc-my fc-param# @ 0 ?do i fc-param@ lf-env-param? dup ok? 0= if unloop exit then drop
  loop outcome-ok ;
\ N1, K5 and L1 for each constant; the accepted ones are recorded as
\ dependencies.
: fc-const@ ( k -- name n ) 2* cells fc-my fc-facts-consts + 2@ ;
: fc-constant-ok ( name n -- outcome )
  swap lf-env-resolve dup ok? if drop lf-env-arity? else nip nip then ;
: fc-constants ( -- outcome )
  fc-my fc-facts-consts# @ 0 ?do i fc-const@ fc-constant-ok dup ok? 0= if unloop exit then
    drop loop outcome-ok ;
\ The candidate signatures: the type of every dependency, with its
\ universe parameters as formals.
variable fc-token-cell
: fc-dep-decl ( k -- decl ) lf-cand-dep @ lf-input-decl ;
: fc-put ( decl -- )
  >r fc-token-cell @ r@ lf-idecl-name @ r@ lf-idecl-type @ dup lf-term-identity must
  r@ lf-idecl-params r> lf-idecl-arity @ fc-fuel lf-msp-put ok? must ;
: fc-index ( -- )
  lf-msp-begin must lf-msp-token must fc-token-cell !
  lf-cand-count@ 0 ?do i fc-dep-decl fc-put loop ;
: fc-root ( term -- term identity ) dup lf-term-identity must ;
: fc-theorem? ( -- flag ) fc-decl@ lf-idecl-kind @ lf-kind-theorem = ;
: fc-roots ( decl -- type tid value vid )
  dup lf-idecl-type @ fc-root rot lf-idecl-value @ fc-root ;
: fc-probe ( -- outcome )
  fc-index fc-token-cell @ fc-decl@ fc-roots
  fc-fuel fc-theorem? if lf-mixed-theorem-probe else lf-mixed-definition-probe then ;
: fc-steps ( -- outcome )
  fc-audit dup ok? 0= if exit then drop
  lf-env-own-name dup ok? 0= if exit then drop
  lf-env-own-params dup ok? 0= if exit then drop
  fc-l2 dup ok? 0= if exit then drop
  fc-constants dup ok? 0= if exit then drop fc-probe ;
: fc-check ( -- ) false fc-audited ! fc-steps lf-env-finish ;

\ Run every declaration of the case and print the last one's row.
: fc-source ( -- ) fc-audited @ if ." audit" else ." kernel" then ;
: fc-row ( -- )
  ." ROW " fc-id fc-id# @ type space lf-input-count 1- lf-env-outcome outcome-text type
  space lf-diag@ nip . swap . . fc-source cr ;
: fc-run ( -- )
  lf-input-end ok? must 64 lf-env-new ok? must dup lf-env-use ok? must
  ['] fc-check lf-env-run ok? must fc-row lf-env-free ok? must ;
