\ Statements Lean 4.35.0 fixes (plan tasks 5.3.1 and 5.2.4; ADR 0015 Q1,
\ ADR 0006 amendment 2026-11-05): whether a declaration's type is exactly
\ a fixed statement -- an allowlisted axiom's (axiom-allowlist.fs), one
\ of the four quotient constants' or Eq's (quot.fs) -- up to the names
\ of binders and the binder information, which Lean's expression
\ equality ignores (quot.cpp 33 and 41 compare with operator==), and up
\ to the names of universe parameters, which a constant's users never
\ see (they instantiate parameters by position). Part of the first
\ checker's [kernel] path (in core/ so that the presentation can name the
\ allowlist's axioms): not through the review gate (AGENTS.md).
\
\ A statement is a text: the term in prefix form, tokens separated by one
\ space.
\   P d b  a Pi           L d b  a lambda        A f a  an application
\   #n     bound variable n                      S l    a Sort of level l
\   C name k l1 .. lk    a constant: its dotted name (string parts only)
\                        and its k universe arguments
\ Levels: z zero, s l its successor, m l l max, i l l imax, uN the
\ declaration's universe parameter number N (from 0).
\ Any other node (a literal, projection, let term, free variable or
\ unsupported form) differs. The comparison is driven by the text: each
\ token is matched with the next pending node, whose children it then
\ pushes, and it stops at the first difference. Its work is therefore
\ bounded by the text, never by the term: a larger term differs as soon
\ as the text runs out. A pending node needs at least one token, so more
\ pending nodes than lf-stmt-room (at least any text's tokens, checked
\ when a text is made) means a difference, not a limit on terms. Each
\ token costs one unit of fuel (lf-stmt-fuel); out of fuel is exhausted.
\
\ lf-stmt-match ( term decl c-addr u -- flag outcome ): ok with whether
\ term, read with decl's universe parameters, is the text; exhausted
\ (false) when the fuel ran out. term is an audited root (V1). Then
\ lf-stmt-met@ ( -- n ) and lf-stmt-id ( k -- addr ) give the names of
\ the constants it met, in the text's order (the allowlist checks that
\ they are Lean's own).
\ lf-name-dotted? ( id c-addr u -- flag ): whether name id is the dotted
\ text (an audited name; string parts only), the comparison of Lean's
\ isConstOf and match_expr with a literal name, shared with the front
\ end (front/term-eqv.fs); lf-stmt-name? is the kernel's name for it
\ until the kernel's reuse batch (plan 9.4.8e).
\ Entries: lf-stmt: ( code arity "name" -- ) makes a statement entry,
\ followed by its constant's name, kept with lf-text, ( c-addr u -- ), and
\ its statement, kept with lf-statement: ( "tokens end-statement" -- )
\ from the tokens that follow, over several lines; lf-stmt-is? ( decl
\ entry -- flag outcome )
\ says whether decl has the entry's name, number of universe parameters
\ and statement.
\ State: one module record, lf-stmt-state (the text left, the
\ declaration, the fuel, the pending nodes and the constants met), a
\ member of the checker context; the entries are read-only data made while loading.

require ../lib/lib.fs
require ../lib/bytes.fs
require ./constant-references.fs
require ./constant-term-boundary.fs
require ./generation-handles.fs
require ./input.fs
require ./levels.fs
require ./name-equal.fs
require ./names.fs
require ./tagged-sort-boundary.fs
require ./terms.fs

96 constant lf-stmt-room   \ pending nodes, at least any text's tokens
0 constant lf-stmt-term    \ the kinds of a pending node
1 constant lf-stmt-level

begin-structure /lf-stmt
  2 cells +field lf-stmt-left  \ the text left: c-addr u, with 2@ 2!
  field: lf-stmt-decl     \ the declaration whose parameters uN names
  field: lf-stmt-budget   \ fuel left
  field: lf-stmt-depth    \ pending nodes
  lf-stmt-room 2* cells +field lf-stmt-items   \ pending (node kind) pairs
  field: lf-stmt-met      \ constants met so far
  lf-stmt-room cells +field lf-stmt-ids        \ their names, in the text's order
  field: lf-stmt-ntoks    \ building: the text's tokens
  lf-stmt-room 2* cells +field lf-stmt-toks    \ (address length), forward
  field: lf-stmt-sp       \ the top built value
  lf-stmt-room 2* cells +field lf-stmt-vals    \ (node identity), from the end down
  field: lf-stmt-pairs    \ the universe arguments
end-structure
/lf-stmt context-record: lf-stmt-state
: lf-stmt-fuel ( -- addr ) lf-stmt-state lf-stmt-budget ;

\ Texts: the next token, up to a space, each costing one unit of fuel.
: lf-stmt-text ( -- c-addr u ) lf-stmt-state lf-stmt-left 2@ ;
: lf-stmt-text! ( c-addr u -- ) lf-stmt-state lf-stmt-left 2! ;
: lf-stmt-span ( c-addr u -- n ) bl byte-index ;
: lf-stmt-token ( -- c-addr u )
  -1 lf-stmt-fuel +!
  lf-stmt-text 2dup lf-stmt-span >r 2dup r@ 1+ over min /string lf-stmt-text! drop r> ;
\ A decimal number filling the token.
: lf-stmt-number ( c-addr u -- n flag )
  dup 0= if nip false exit then 0 0 2swap >number nip or 0= ;
\ The number of tokens of a text; a text with more than lf-stmt-room
\ cannot be kept.
: lf-stmt-tokens ( c-addr u -- n )
  1 -rot begin bl byte-scan dup while 1 /string rot 1+ -rot repeat 2drop ;

\ Names, from the last part back: each string part matches, and the text
\ ends where the name does (the anonymous name, ID 0). The last dot's
\ offset, -1 for none.
: lf-stmt-dot ( c-addr u -- k|-1 )
  over -1 2swap begin [char] . byte-scan dup while
    2swap drop 2 pick over - 2swap 1 /string repeat 2drop nip ;
: lf-stmt-split ( c-addr u -- c-addr k part-addr part-u )
  2dup lf-stmt-dot dup 0< if drop over 0 2swap exit then
  >r over r@ 2swap r> 1+ /string ;
: lf-name-dotted? ( id c-addr u -- flag )
  begin dup while
    lf-stmt-split 2>r 2 pick 2r> lf-name-str-is? 0= if 2drop drop false exit then
    rot lf-name-prefix@ -rot
  repeat 2drop 0= ;
: lf-stmt-name? ( id c-addr u -- flag ) lf-name-dotted? ;

\ Pending nodes: pushed in the reverse of the text's order.
: lf-stmt-item ( k -- addr ) 2* cells lf-stmt-state lf-stmt-items + ;
: lf-stmt-depth@ ( -- n ) lf-stmt-state lf-stmt-depth @ ;
: lf-stmt-push ( x kind -- flag )
  lf-stmt-depth@ dup lf-stmt-room < 0= if drop 2drop false exit then
  dup 1+ lf-stmt-state lf-stmt-depth ! lf-stmt-item 2! true ;
: lf-stmt-pop ( -- x kind )
  -1 lf-stmt-state lf-stmt-depth +! lf-stmt-depth@ lf-stmt-item 2@ ;
: lf-stmt-lpush ( level -- flag ) lf-stmt-level lf-stmt-push ;

\ A term token for node: whether they agree, the node's children pushed.
: lf-stmt-children ( node -- flag )
  dup lf-term-second@ lf-stmt-term lf-stmt-push
  swap lf-term-first@ lf-stmt-term lf-stmt-push and ;
: lf-stmt-binary ( node tag -- flag )
  over swap lf-term-tag? if lf-stmt-children else drop false then ;

: lf-stmt-sort ( node -- flag )
  dup lf-tag-symbolic-sort lf-term-tag? 0= if drop false exit then
  lf-term-first@ lf-stmt-lpush ;
\ A constant: its name, then its number of universe arguments, each then
\ pushed, the first matched first.
: lf-stmt-arg ( addr k -- flag ) lf-cref-pair@ drop lf-stmt-lpush ;
: lf-stmt-args ( slot -- flag )
  lf-cref-pairs true swap begin dup while 1- >r over r@ lf-stmt-arg and r> repeat
  drop nip ;
\ The names of the constants a comparison met, in the text's order: one
\ per C token at most, so never more than lf-stmt-room.
: lf-stmt-id ( k -- addr ) cells lf-stmt-state lf-stmt-ids + ;
: lf-stmt-met@ ( -- n ) lf-stmt-state lf-stmt-met @ ;
: lf-stmt-meet ( id -- )
  lf-stmt-met@ dup lf-stmt-room < 0= if 2drop exit then
  tuck lf-stmt-id ! 1+ lf-stmt-state lf-stmt-met ! ;
: lf-stmt-const ( slot -- flag )
  lf-stmt-token 2 pick lf-crec-name @ -rot lf-name-dotted? 0= if drop false exit then
  dup lf-crec-name @ lf-stmt-meet
  lf-stmt-token lf-stmt-number 0= if 2drop false exit then
  over lf-crec-arity @ = if lf-stmt-args else drop false then ;
: lf-stmt-const? ( node -- flag )
  dup lf-term-const? if lf-const-slot lf-stmt-const
  else drop false then ;
\ Whether a token (not empty) starts with the text given.
: lf-stmt-prefix? ( c-addr u c-addr2 u2 -- c-addr u flag )
  2over drop over 2swap compare 0= ;
\ A one-letter token's number: its letter's place in letters counted from
\ the end, the last letter 1 (so letters lists them backwards); 0 for a
\ longer token or no letter of them. Found with SEARCH: no byte is read.
: lf-stmt-letter# ( c-addr u letters u2 -- n )
  2swap dup 1 = if search and nip else 2drop 2drop 0 then ;
: lf-stmt-letter ( node c-addr u -- flag )
  s" CSALP" lf-stmt-letter# case
    1 of lf-tag-pi lf-stmt-binary endof  2 of lf-tag-lam lf-stmt-binary endof
    3 of lf-tag-app lf-stmt-binary endof  4 of lf-stmt-sort endof
    5 of lf-stmt-const? endof  nip false swap endcase ;
: lf-stmt-bvar-token ( node c-addr u -- flag )
  1 /string lf-stmt-number if lf-term-bvar-is? else 2drop false then ;
: lf-stmt-term-token ( node c-addr u -- flag )
  dup 0= if 2drop drop false exit then
  s" #" lf-stmt-prefix? if lf-stmt-bvar-token else lf-stmt-letter then ;

\ A level token for level.
: lf-stmt-ltag? ( level tag -- flag ) swap lf-level-tag@ = ;
: lf-stmt-lchildren ( level -- flag )
  dup lf-level-second@ lf-stmt-lpush swap lf-level-first@ lf-stmt-lpush and ;
: lf-stmt-lbinary ( level tag -- flag )
  over swap lf-stmt-ltag? if lf-stmt-lchildren else drop false then ;
: lf-stmt-succ ( level -- flag )
  dup lf-level-tag-succ lf-stmt-ltag? 0= if drop false exit then
  lf-level-first@ lf-stmt-lpush ;
\ uN: the declaration's parameter number N, compared by name.
: lf-stmt-param ( level n -- flag )
  over lf-level-tag-param lf-stmt-ltag? 0= if 2drop false exit then
  lf-stmt-state lf-stmt-decl @ lf-idecl-params@ 2 pick swap u< 0=
  if 2drop drop false exit then
  swap lf-param@ swap lf-level-first@ lf-name-same? ;
: lf-stmt-lletter ( level c-addr u -- flag )
  s" imsz" lf-stmt-letter# case
    1 of lf-level-tag-zero lf-stmt-ltag? endof  2 of lf-stmt-succ endof
    3 of lf-level-tag-max lf-stmt-lbinary endof
    4 of lf-level-tag-imax lf-stmt-lbinary endof  nip false swap endcase ;
: lf-stmt-param-token ( level c-addr u -- flag )
  1 /string lf-stmt-number if lf-stmt-param else 2drop false then ;
: lf-stmt-level-token ( level c-addr u -- flag )
  dup 0= if 2drop drop false exit then
  s" u" lf-stmt-prefix? if lf-stmt-param-token else lf-stmt-lletter then ;

\ The comparison: one token per pending node until none is left; then the
\ text must be used up.
: lf-stmt-step ( -- flag )
  lf-stmt-pop >r lf-stmt-token r> lf-stmt-term =
  if lf-stmt-term-token else lf-stmt-level-token then ;
: lf-stmt-spent? ( -- flag ) lf-stmt-fuel @ 0< ;
: lf-stmt-loop ( -- flag )
  begin lf-stmt-depth@ 0> while
    lf-stmt-step 0= if false exit then lf-stmt-spent? if false exit then
  repeat lf-stmt-text nip 0= ;
: lf-stmt-start ( term decl c-addr u -- )
  lf-stmt-text! lf-stmt-state tuck lf-stmt-decl !
  0 over lf-stmt-met ! 0 swap lf-stmt-depth !
  lf-stmt-term lf-stmt-push drop ;
: lf-stmt-match ( term decl c-addr u -- flag outcome )
  lf-stmt-start lf-stmt-loop
  lf-stmt-spent? if drop false outcome-exhausted else outcome-ok then ;

\ Entries: the code (an axiom's bit, a quotient constant's number), the
\ number of universe parameters, then two kept texts, the constant's name
\ (lf-text,) and its statement (lf-statement:), each a count followed by
\ its bytes. A statement is written as the tokens that follow
\ lf-statement:, over as many lines as needed, up to end-statement; it is
\ kept with one space between tokens.
: lf-stmt: ( code arity "name" -- ) create swap , , ;
: lf-text, ( c-addr u -- ) dup , here over allot swap move align ;
: lf-next-token ( -- c-addr u )
  begin parse-name dup 0= while 2drop refill 0= abort" statement: no end" repeat ;
: lf-keep ( count-addr c-addr u -- count-addr )
  dup 3 pick +! here over allot swap move ;
: lf-space ( -- c-addr u ) s"  " ;   \ one space: S" skips only the first
: lf-keep-token ( count-addr c-addr u -- count-addr )
  2>r dup @ if lf-space lf-keep then 2r> lf-keep ;
: lf-kept-fits ( count-addr -- )
  cell-count lf-stmt-tokens lf-stmt-room > abort" statement: too many tokens" ;
: lf-statement: ( "tokens end-statement" -- )
  here 0 , begin lf-next-token 2dup s" end-statement" compare while lf-keep-token repeat
  2drop lf-kept-fits align ;
: lf-stmt-code ( entry -- code ) @ ;
: lf-stmt-arity ( entry -- n ) cell+ @ ;
: lf-stmt-kept ( addr -- c-addr u ) cell-count ;
: lf-stmt-named ( entry -- c-addr u ) 2 cells + lf-stmt-kept ;
: lf-stmt-statement ( entry -- c-addr u ) lf-stmt-named + aligned lf-stmt-kept ;
\ Whether decl is the entry's constant: name, universe parameters, statement.
: lf-stmt-own? ( decl entry -- flag )
  2dup lf-stmt-arity swap lf-idecl-arity @ =
  >r lf-stmt-named rot lf-idecl-name @ -rot lf-name-dotted? r> and ;
: lf-stmt-is? ( decl entry -- flag outcome )
  2dup lf-stmt-own? 0= if 2drop false outcome-ok exit then
  >r dup lf-idecl-type @ swap r> lf-stmt-statement lf-stmt-match ;

\ ---------------------------------------------------------------------------
\ Building (ADR 0015 Q1: Lean's add_quot builds the quotient constants'
\ types itself): lf-stmt-build ( entry pairs -- root outcome ) makes the
\ entry's statement a term in the current stores, uN the level of pair N
\ at pairs (a constant reference's level array, as many pairs as the
\ entry has universe parameters), each constant by its dotted name (made
\ where it is new); ok; full when a store refuses a node or a name;
\ exhausted (root -1) when lf-stmt-fuel runs out, one unit a token. The
\ text is split into tokens first, a constant's name and count marked (a
\ negative length); then read from the end, each token's node is made
\ from the values its children left on a stack. Both are bounded by the
\ text, so by lf-stmt-room.
: lf-stmt-tok ( k -- addr ) 2* cells lf-stmt-state lf-stmt-toks + ;
: lf-stmt-tok@ ( k -- c-addr u ) lf-stmt-tok 2@ ;
: lf-stmt-ntoks@ ( -- n ) lf-stmt-state lf-stmt-ntoks @ ;
: lf-stmt-add ( c-addr u -- )
  lf-stmt-ntoks@ dup 1+ lf-stmt-state lf-stmt-ntoks ! lf-stmt-tok 2! ;
: lf-stmt-split-all ( c-addr u -- )
  lf-stmt-text! 0 lf-stmt-state lf-stmt-ntoks !
  begin lf-stmt-text nip while lf-stmt-token lf-stmt-add repeat ;
: lf-stmt-c? ( c-addr u -- flag ) dup 0< if 2drop false else s" C" compare 0= then ;
: lf-stmt-mark ( k -- ) lf-stmt-tok dup @ negate swap ! ;   \ 2! keeps u first
: lf-stmt-marks ( -- )
  lf-stmt-ntoks@ 2 - 0 max 0 ?do
    i lf-stmt-tok@ lf-stmt-c? if i 1+ lf-stmt-mark i 2 + lf-stmt-mark then
  loop ;
: lf-stmt-operand ( k -- c-addr u ) lf-stmt-tok@ negate ;

\ The value stack, growing down: handles (node identity), so that the k
\ levels of a constant lie in its reference's order at the top. Nodes
\ are made as handles (generation-handles.fs), which the audit requires.
: lf-stmt-sp@ ( -- addr ) lf-stmt-state lf-stmt-sp @ ;
: lf-stmt-sp+ ( n -- ) cells lf-stmt-state lf-stmt-sp +! ;
: lf-stmt-push2 ( node identity -- ) -2 lf-stmt-sp+ lf-stmt-sp@ cell-pair! ;
: lf-stmt-pop2 ( -- node identity ) lf-stmt-sp@ cell-pair@ 2 lf-stmt-sp+ ;
: lf-stmt-pop1 ( -- node ) lf-stmt-pop2 drop ;
: lf-stmt-put ( node identity true | false -- flag ) dup if drop lf-stmt-push2 true then ;

\ A dotted name, part by part from the first.
: lf-stmt-part ( c-addr u -- n ) [char] . byte-index ;
: lf-stmt-after ( c-addr u n -- c-addr' u' ) 1+ over min /string ;
: lf-stmt-next-part ( prefix c-addr u -- id c-addr' u' flag )
  2dup lf-stmt-part >r rot 2 pick r@ lf-name-str
  0= if r> drop 0 -rot false exit then -rot r> lf-stmt-after true ;
: lf-stmt-intern ( c-addr u -- id flag )
  0 -rot begin dup while lf-stmt-next-part 0= if 2drop false exit then repeat 2drop true ;
\ A constant: its reference, the k levels popped, then its node.
: lf-stmt-ref ( id k -- cref identity true | false )
  >r lf-name-generation @ lf-stmt-sp@ r@ lf-cref-new r> 2* lf-stmt-sp+ ;
: lf-stmt-b-const ( k -- flag )
  dup 1+ lf-stmt-operand lf-stmt-intern 0= if 2drop false exit then
  swap 2 + lf-stmt-operand lf-stmt-number 0= if 2drop false exit then
  lf-stmt-ref 0= if false exit then lf-cterm-new lf-stmt-put ;
: lf-stmt-b-binary ( xt -- flag ) >r lf-stmt-pop2 lf-stmt-pop2 r> execute lf-stmt-put ;
: lf-stmt-b-lbinary ( xt -- flag )
  >r lf-stmt-pop1 lf-stmt-pop1 r> execute lf-hlevel-result lf-stmt-put ;
: lf-stmt-b-number ( c-addr u -- n flag ) 1 /string lf-stmt-number ;
: lf-stmt-b-param ( c-addr u -- flag )
  lf-stmt-b-number 0= if drop false exit then
  lf-stmt-state lf-stmt-pairs @ swap lf-cref-pair@ lf-stmt-push2 true ;
: lf-stmt-b-succ ( -- flag ) lf-stmt-pop2 lf-hlevel-succ lf-stmt-put ;
: lf-stmt-b-sort ( -- flag ) lf-stmt-pop2 lf-hterm-sort lf-stmt-put ;
\ Level letter n: 1 z, 2 s, 3 m, 4 i; another n is none.
: lf-stmt-b-level ( n -- flag )
  case
    1 of lf-hlevel-zero lf-stmt-put endof  2 of lf-stmt-b-succ endof
    3 of ['] lf-level-max lf-stmt-b-lbinary endof
    4 of ['] lf-level-imax lf-stmt-b-lbinary endof  false swap endcase ;
\ Letter n: 1 P, 2 L, 3 A, 4 S, then the level letters.
: lf-stmt-b-letter ( c-addr u -- flag )
  s" imszSALP" lf-stmt-letter# case  1 of ['] lf-hterm-pi lf-stmt-b-binary endof
    2 of ['] lf-hterm-lam lf-stmt-b-binary endof
    3 of ['] lf-hterm-app lf-stmt-b-binary endof  4 of lf-stmt-b-sort endof
    dup 4 - lf-stmt-b-level swap endcase ;
: lf-stmt-b-bvar ( c-addr u -- flag )
  lf-stmt-b-number if lf-hterm-bvar lf-stmt-put else drop false then ;
: lf-stmt-b-plain ( c-addr u -- flag )
  s" #" lf-stmt-prefix? if lf-stmt-b-bvar exit then
  s" u" lf-stmt-prefix? if lf-stmt-b-param exit then lf-stmt-b-letter ;
\ Token k: skipped when marked, a constant at C, else its node.
: lf-stmt-b-token ( k -- flag )
  dup lf-stmt-tok@ dup 0< if 2drop drop true exit then
  2dup lf-stmt-c? if 2drop lf-stmt-b-const else rot drop lf-stmt-b-plain then ;
: lf-stmt-b-run ( -- flag )
  lf-stmt-ntoks@ begin dup while 1- dup lf-stmt-b-token 0= if drop false exit then repeat
  drop true ;
: lf-stmt-b-start ( entry pairs -- )
  lf-stmt-state tuck lf-stmt-pairs !
  dup lf-stmt-vals lf-stmt-room 2* cells + swap lf-stmt-sp !
  lf-stmt-statement lf-stmt-split-all lf-stmt-marks ;
: lf-stmt-build ( entry pairs -- root outcome )
  lf-stmt-b-start lf-stmt-spent? if -1 outcome-exhausted exit then
  lf-stmt-b-run if lf-stmt-pop1 outcome-ok else -1 outcome-full then ;
