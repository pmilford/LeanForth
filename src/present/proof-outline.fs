\ The proof outline (ADR 0013 L7, plan task 2.4.4; owner decisions D2 and
\ D4): a short, readable proof of one checked declaration, printed from
\ the derivation log its check wrote (src/core/derivation-log.fs), in
\ Unicode (LaTeX comes later as a printer mode, plan task 8.6.1). Every
\ line names the log steps it covers and the earlier lines it uses; every
\ formula is a term the checker computed (an input object, or a copy the
\ log kept), printed by the term printer; only the English sentences are
\ fixed templates, tagged structured-template with their identifiers in
\ the footer. With detail, every step of the log is listed instead.
\ Untrusted presentation code: the checker never loads it, and nothing it
\ prints is evidence of anything. The verdict and the axiom list are the
\ caller's, read from the checked environment (lf-outline); like all of
\ src/present/ the printer loads nothing from src/kernel/. It does not
\ take that verdict on trust (M1 of the review of 2026-11-03): it prints
\ nothing but a refusal unless the log is the one the verdict belongs to
\ (lf-ol-matches?): taken over this input, which is still intact; the
\ check of the log's declaration published the caller's outcome (the
\ log's header); and, when the log is complete, its last step is that
\ publish step.
\
\ What is printed. The header: kind and name, the verdict with its label
\ and axioms, the statement (or type), the input line (lf-outline-source),
\ and the log's size and completeness. Then, only for a declaration the
\ environment accepted, with a complete log whose steps the recognisers
\ below cover, the outline; otherwise why there is none (D2: never from an
\ incomplete log), and for a proof no recogniser covers, its steps.
\
\ Recognisers (the lambda and application fragment of phase 2), on the
\ value's inference step and its premises:
\ - a chain of lambda steps (one fun): one line per binder, or per group
\   of binders ranging over propositions or over types ("Let A, B, C be
\   propositions." [∀-introduction]; "Let x : A."; "Assume f : A → B."
\   [assumption], when the binder's domain is a proposition, its type
\   Prop), then the body's lines, indented, then one discharge line with
\   the lambda steps' result ("Discharging 4, 3, 2 and 1 gives ...");
\ - an application spine (a head applied to arguments): the arguments'
\   lines, then one line for the whole application with its type and the
\   reason: →-elimination when the head is a proof and the function's type
\   does not depend on its argument, ∀-elimination when it does, and
\   "by applying" when the head is not a proof (a definition's value);
\ - a variable: no line, it points to its binder's line;
\ - a constant: a "Recall" line with its type at the levels used;
\ - the declaration's final comparison: "This is the statement."
\ A step is a proof when it is a variable whose binder's domain is a
\ proposition, a constant naming a theorem, an application whose head is
\ a proof, or a lambda whose body is one.
\ State: a small context record, lf-ol-input (the input's name and the
\ declaration's line, set before printing), and one cell, lf-ol-held,
\ pointing to a heap block (about 25 KB) that exists only while
\ lf-outline prints (the context's teardown frees one left by a THROW):
\ the verdict given, the line count, indent, templates used, the current
\ line's steps and uses, and per step its concluding line, its binder's
\ line and whether it is a proof. Printing state is log-view.fs's.

require ./log-view.fs
require ../core/diagnostics.fs

32 constant lf-ol-set-capacity

\ Templates, one bit each, named in the footer.
1 constant lf-tpl-let-props
2 constant lf-tpl-let-types
4 constant lf-tpl-let
8 constant lf-tpl-assume
16 constant lf-tpl-implies-elim
32 constant lf-tpl-forall-elim
64 constant lf-tpl-apply
128 constant lf-tpl-recall
256 constant lf-tpl-discharge
512 constant lf-tpl-statement
10 constant lf-tpl-count
: lf-tpl-name ( k -- c-addr u )
  case 0 of s" let-props/v0" endof 1 of s" let-types/v0" endof 2 of s" let/v0" endof
    3 of s" assume/v0" endof 4 of s" implies-elim/v0" endof 5 of s" forall-elim/v0" endof
    6 of s" apply/v0" endof 7 of s" recall/v0" endof 8 of s" discharge/v0" endof
    >r s" statement/v0" r> endcase ;

\ Binder classes.
0 constant lf-class-let       \ ranges over a type's elements
1 constant lf-class-prop      \ ranges over propositions: its domain is Prop
2 constant lf-class-type      \ ranges over types: its domain is another Sort
3 constant lf-class-assume    \ an assumption: its domain is a proposition

begin-structure /lf-olin
  field: lf-olin-source      \ the input's name, address
  field: lf-olin-len         \ ... length; 0 for none
  field: lf-olin-line        \ the declaration's line in it
end-structure
/lf-olin context-record: lf-ol-input

begin-structure /lf-ol
  field: lf-olr-lines        \ lines numbered so far
  field: lf-olr-indent       \ spaces before a body line's sentence
  field: lf-olr-templates    \ the templates used
  field: lf-olr-outcome      \ the published outcome the caller gave
  field: lf-olr-axioms       \ the axiom set the caller gave, -1 when unknown
  field: lf-olr-steps#
  field: lf-olr-refs#
  lf-ol-set-capacity cells +field lf-olr-steps   \ steps the current line covers
  lf-ol-set-capacity cells +field lf-olr-refs    \ lines it uses
  lf-log-record-capacity cells +field lf-olr-line-of
  lf-log-record-capacity cells +field lf-olr-intro
  lf-log-record-capacity cells +field lf-olr-proof
end-structure
1 cells context-record: lf-ol-held
: lf-ol ( -- addr ) lf-ol-held @ ;
\ The block, as log-view.fs's (lf-lv-open, lf-lv-close).
: lf-ol-open ( -- flag )
  lf-ol if true exit then /lf-ol allocate0 if drop false exit then lf-ol-held ! true ;
: lf-ol-close ( -- ior )
  lf-ol dup 0= if exit then free dup 0= if 0 lf-ol-held ! then ;
:noname ( -- ) lf-ol-close throw ; context-teardown

: lf-ol-field ( offset -- addr ) lf-ol + ;
: lf-ol-of ( s offset -- addr ) lf-ol-field swap 1- cells + ;
\ Per step s: the line that concludes it, the line that introduces its
\ binder (a lambda step), and whether it is a proof.
: lf-ol-line-of ( s -- addr ) 0 lf-olr-line-of lf-ol-of ;
: lf-ol-intro ( s -- addr ) 0 lf-olr-intro lf-ol-of ;
: lf-ol-proof ( s -- addr ) 0 lf-olr-proof lf-ol-of ;
: lf-ol-line# ( -- n ) 0 lf-olr-lines lf-ol-field @ ;
: lf-ol-indent ( -- addr ) 0 lf-olr-indent lf-ol-field ;
: lf-ol-used ( bit -- ) 0 lf-olr-templates lf-ol-field tuck @ or swap ! ;

\ Two small sets: the steps a line covers and the lines it uses. Zero and
\ repeats are not added; a full set drops the rest (never past 32).
: lf-ol-has? ( x addr n -- flag )
  0 ?do 2dup i cells + @ = if 2drop true unloop exit then loop 2drop false ;
: lf-ol-add ( x addr count -- )
  >r over 0> 0= if 2drop r> drop exit then
  2dup r@ @ lf-ol-has? r@ @ lf-ol-set-capacity < 0= or if 2drop r> drop exit then
  r@ @ cells + ! 1 r> +! ;
: lf-ol-steps ( -- addr count ) 0 lf-olr-steps lf-ol-field 0 lf-olr-steps# lf-ol-field ;
: lf-ol-refs ( -- addr count ) 0 lf-olr-refs lf-ol-field 0 lf-olr-refs# lf-ol-field ;
: lf-ol-step+ ( s -- ) lf-ol-steps lf-ol-add ;
: lf-ol-ref+ ( line -- ) lf-ol-refs lf-ol-add ;
: lf-ol-in? ( x addr count -- flag ) @ lf-ol-has? ;
: lf-ol-step? ( s -- flag ) lf-ol-steps lf-ol-in? ;
: lf-ol-ref? ( line -- flag ) lf-ol-refs lf-ol-in? ;
: lf-ol-sets-clear ( -- ) 0 0 lf-olr-steps# lf-ol-field ! 0 0 lf-olr-refs# lf-ol-field ! ;

\ A line: number and indent, the sentence (in the buffer, padded to the
\ rule column), the rule with the lines it uses, the steps it covers as
\ runs (s27–s29), then any continuation line.
: lf-ol-number ( -- )
  1 0 lf-olr-lines lf-ol-field +! s"   " lf-lv-put lf-ol-line# lf-lv-n 5 lf-lv-flush
  lf-ol-indent @ lf-lv-spaces ;
: lf-ol-sentence ( -- ) 46 lf-ol-indent @ - lf-lv-flush ;
: lf-ol-uses ( -- )
  0 lf-olr-refs# lf-ol-field @ 0= if exit then s"  ← " lf-lv-put
  true lf-ol-line# 1+ 1 ?do i lf-ol-ref? if dup 0= if s" , " lf-lv-put then drop false
    i lf-lv-n then loop drop ;
: lf-ol-rule ( c-addr u -- ) s" [" lf-lv-put lf-lv-put lf-ol-uses s" ]" lf-lv-put
  35 lf-lv-flush ;
: lf-ol-run ( s -- s' ) begin 1+ dup lf-ol-step? 0= until 1- ;
: lf-ol-runs ( -- )
  true lf-log-count 1+ 1 ?do i lf-ol-step? i 1- lf-ol-step? 0= and
    if dup 0= if s" , " lf-lv-put then drop false i lf-lv-step i lf-ol-run
      dup i <> if s" –" lf-lv-put lf-lv-step else drop then then loop drop ;
: lf-ol-end ( -- ) lf-ol-runs 0 lf-lv-flush lf-lv-cr lf-ol-sets-clear ;
: lf-ol-more ( -- ) lf-ol-indent @ 7 + lf-lv-spaces ;
: lf-ol-more-end ( -- ) 0 lf-lv-flush lf-lv-cr ;

\ Reading the steps.
: lf-ol-rule? ( s rule -- flag ) over 0> if swap lf-lv-rule = else 2drop false then ;
: lf-ol-lambda? ( s -- flag ) lf-rule-lambda lf-ol-rule? ;
: lf-ol-application? ( s -- flag ) lf-rule-application lf-ol-rule? ;
\ The first and second inference premises (-1 for none: the recognisers
\ ask only where they exist).
: lf-ol-first ( s -- p ) 0 lf-lv-inference 0= if -1 then ;
: lf-ol-second ( s -- p ) 1 lf-lv-inference 0= if -1 then ;
\ Whether a level reference, or a term reference's Sort, is zero.
: lf-ol-level-zero? ( lref -- flag )
  dup 0< 0= if lf-level-read if 2drop lf-level-tag-zero = else false then exit then
  dup lf-log-copy? 0= if drop false exit then lf-log-copy-index
  dup lf-log-level-copies < if lf-log-level-slot node-tag @ lf-level-tag-zero = else
  drop false then ;
: lf-ol-prop? ( ref -- flag )
  lf-lv-node 0= if false exit then rot case
    lf-tag-sort of drop 0= endof lf-tag-symbolic-sort of drop lf-ol-level-zero? endof
    nip nip false swap endcase ;
: lf-ol-sort? ( ref -- flag )
  lf-lv-tag 0= if false exit then dup lf-tag-sort = swap lf-tag-symbolic-sort = or ;

\ Lambda chains. A lambda step's domain is its node's first field; its
\ first inference premise infers the domain, its second the body.
: lf-ol-domain ( r -- ref ) lf-lv-a 1 lf-lv-child-ref 0= if lf-log-none then ;
: lf-ol-assumption? ( r -- flag ) lf-ol-first lf-lv-out-ref lf-ol-prop? ;
: lf-ol-class ( r -- class )
  dup lf-ol-domain dup lf-ol-sort?
  if nip lf-ol-prop? if lf-class-prop else lf-class-type then exit then
  drop lf-ol-assumption? if lf-class-assume else lf-class-let then ;
: lf-ol-same? ( r class -- flag ) over lf-ol-lambda? if swap lf-ol-class = else
  2drop false then ;
: lf-ol-group# ( r class -- n )
  0 -rot begin 2dup lf-ol-same? while >r lf-ol-second r> rot 1+ -rot repeat 2drop ;
: lf-ol-innermost ( s -- r ) begin dup lf-ol-second dup lf-ol-lambda? while
  nip repeat drop ;
\ A binder's display name, in its lambda's scope with the lambda itself.
: lf-ol-name ( r -- ) dup lf-lv-at if lf-lv-a lf-lv-push lf-lv-name-here else drop
  lf-lv-fail then ;
\ The binder of lambda step r is introduced on this line.
: lf-ol-introduce ( r class -- )
  lf-class-assume = over lf-ol-proof ! lf-ol-line# over lf-ol-intro !
  lf-ol-first lf-ol-step+ ;

\ A group of binders over propositions or types: one line.
: lf-ol-names ( r class n -- r' )
  0 ?do i if s" , " lf-lv-put then over lf-ol-name 2dup lf-ol-introduce >r
  lf-ol-second r> loop drop ;
: lf-ol-group-text ( class n -- )
  1 > if lf-class-prop = if s"  be propositions." else s"  be types." then
  else lf-class-prop = if s"  be a proposition." else s"  be a type." then
  then lf-lv-put ;
: lf-ol-group ( r class -- r' )
  lf-ol-number s" Let " lf-lv-put 2dup lf-ol-group# >r tuck r@ lf-ol-names swap
  dup r> lf-ol-group-text lf-ol-sentence lf-class-prop = if lf-tpl-let-props
  else lf-tpl-let-types then lf-ol-used s" ∀-introduction" lf-ol-rule lf-ol-end ;
\ One binder: "Let x : A." or "Assume h : A."
: lf-ol-single ( r class -- r' )
  lf-ol-number dup lf-class-assume = if s" Assume " else s" Let " then lf-lv-put
  over lf-ol-name s"  : " lf-lv-put over dup lf-ol-domain swap lf-lv-formula s" ."
  lf-lv-put
  lf-ol-sentence 2dup lf-ol-introduce lf-class-assume =
  if lf-tpl-assume lf-ol-used s" assumption" else lf-tpl-let lf-ol-used s" ∀-introduction"
  then lf-ol-rule lf-ol-end lf-ol-second ;
: lf-ol-binders ( s -- )
  begin dup lf-ol-lambda? while dup lf-ol-class
    dup lf-class-prop = over lf-class-type = or if lf-ol-group else lf-ol-single
  then repeat drop ;

\ The discharge line of the chain from s0: the binder lines, latest first,
\ and the chain's result; it uses them and the body's line.
: lf-ol-intros ( s0 -- )
  begin dup lf-ol-lambda? while dup lf-ol-intro @ lf-ol-ref+ dup lf-ol-step+
  lf-ol-second repeat drop ;
: lf-ol-sep ( k n -- )
  over 0= if 2drop exit then 1- = if s"  and " else s" , " then lf-lv-put ;
: lf-ol-intro-list ( -- )
  0 lf-olr-refs# lf-ol-field @ 0 lf-ol-line# 1+ 1 ?do
    lf-ol-line# 1+ i - dup lf-ol-ref? if >r 2dup swap lf-ol-sep r> lf-lv-n 1+ else drop
    then
  loop 2drop ;
: lf-ol-kinds ( s0 -- assume? other? )
  false false rot begin dup lf-ol-lambda? while
    dup lf-ol-class lf-class-assume = if rot drop true -rot else nip true swap then
    lf-ol-second
  repeat drop ;
: lf-ol-introduction ( s0 -- c-addr u )
  lf-ol-kinds 2dup and if 2drop s" →/∀-introduction" exit then
  drop if s" →-introduction" else s" ∀-introduction" then ;
: lf-ol-discharge ( s0 -- )
  dup lf-ol-intros lf-ol-number s" Discharging " lf-lv-put lf-ol-intro-list s"  gives"
  lf-lv-put lf-ol-sentence dup lf-ol-innermost lf-ol-second dup lf-ol-line-of @ lf-ol-ref+
  lf-ol-proof @ over lf-ol-proof ! dup lf-ol-introduction lf-ol-rule lf-ol-end
  lf-tpl-discharge lf-ol-used lf-ol-more dup lf-lv-out-ref over lf-lv-formula s" ."
  lf-lv-put
  lf-ol-more-end lf-ol-line# swap lf-ol-line-of ! ;

defer lf-ol-walk ( s -- )
\ A lambda chain: its binders, its body (indented), its discharge.
: lf-ol-lambda ( s -- )
  dup lf-ol-binders 2 lf-ol-indent +! dup lf-ol-innermost lf-ol-second lf-ol-walk
  -2 lf-ol-indent +! lf-ol-discharge ;

\ A variable points to its binder's line and is a proof when its binder
\ is an assumption.
: lf-ol-bvar ( ref -- k true | false )
  lf-lv-node 0= if false exit then drop swap lf-tag-bvar = if true else drop false then ;
: lf-ol-var-binder ( s -- r true | false )
  dup lf-lv-a lf-ol-bvar 0= if drop false exit then over lf-lv-depth@ swap - 1-
  lf-lv-binder ;
: lf-ol-var ( s -- )
  dup lf-ol-var-binder 0= if drop exit then
  dup lf-ol-intro @ 2 pick lf-ol-line-of ! lf-ol-proof @ swap lf-ol-proof ! ;

\ A constant: "Recall c : T, accepted above as dN."
: lf-ol-resolved ( c -- d )
  dup lf-lv-premises 0 ?do dup i lf-lv-premise dup lf-lv-rule lf-rule-resolve =
    if nip lf-lv-out-ref unloop exit then drop loop drop -1 ;
: lf-ol-theorem-slot? ( d -- flag )
  dup 0 lf-input-count within if lf-input-decl lf-idecl-kind @ lf-kind-theorem = else
  drop false then ;
: lf-ol-typed ( s -- )
  dup lf-lv-a over lf-lv-formula s"  : " lf-lv-put dup lf-lv-out-ref swap lf-lv-formula ;
: lf-ol-recall ( c -- )
  dup lf-ol-step+ lf-ol-number s" Recall " lf-lv-put dup lf-ol-typed s" ," lf-lv-put
  lf-ol-sentence s" earlier declaration" lf-ol-rule lf-ol-end lf-tpl-recall lf-ol-used
  lf-ol-more s" accepted above as d" lf-lv-put dup lf-ol-resolved lf-lv-n s" ." lf-lv-put
  lf-ol-more-end lf-ol-line# over lf-ol-line-of !
  dup lf-ol-resolved lf-ol-theorem-slot? swap lf-ol-proof ! ;

\ Applications: the head and arguments of a spine, the head's lines
\ first, then the arguments' from the innermost application out.
: lf-ol-head ( s -- h ) begin dup lf-ol-application? while lf-ol-first repeat ;
: lf-ol-spine ( s -- )
  dup lf-ol-application? if dup lf-ol-first recurse lf-ol-second
  lf-ol-walk else lf-ol-walk
  then ;
: lf-ol-spine-sets ( s -- )
  dup lf-ol-application? 0= if lf-ol-line-of @ lf-ol-ref+ exit then
  dup lf-ol-step+ dup lf-ol-second lf-ol-line-of @ lf-ol-ref+ lf-ol-first recurse ;
\ Whether term (in the term store) mentions bound variable k.
defer lf-ol-mentions? ( term k -- flag )
: lf-ol-in-children ( k first second inner -- flag )
  >r rot tuck r> + lf-ol-mentions? if 2drop true else lf-ol-mentions? then ;
: lf-ol-mentions-in ( term k -- flag )
  swap lf-term-read 0= if drop false exit then rot case
    lf-tag-bvar of drop = endof lf-tag-app of 0 lf-ol-in-children endof
    lf-tag-lam of 1 lf-ol-in-children endof lf-tag-pi of 1 lf-ol-in-children endof
    >r 2drop drop false r> endcase ;
\ Deeper than the walks' bound, a term counts as mentioning k (so the
\ line says ∀-elimination, which reads true of every Pi).
: lf-ol-mentions ( term k -- flag )
  lf-lv-deeper 0= if 2drop true exit then lf-ol-mentions-in lf-lv-shallower ;
' lf-ol-mentions is lf-ol-mentions?
\ Whether a function's type (a reference) is a Pi, and one whose body uses
\ its binder.
: lf-ol-pi? ( ref -- flag ) lf-lv-tag if lf-tag-pi = else false then ;
: lf-ol-dependent? ( ref -- flag )
  lf-lv-term 0= if lf-lv-release false exit then
  dup lf-tag-pi lf-pp-is? if lf-term-second@ 0 lf-ol-mentions? else drop false
  then lf-lv-release ;
\ An application's template: by applying, unless its head is a proof
\ whose type is a Pi (once the checker unfolds definitions, a function's
\ type may be a constant whose value is a Pi: that reads "by applying").
: lf-ol-template ( s -- template )
  dup lf-ol-head lf-ol-proof @ 0= if drop lf-tpl-apply exit then
  lf-ol-first lf-lv-out-ref dup lf-ol-pi? 0= if drop lf-tpl-apply exit then
  lf-ol-dependent? if lf-tpl-forall-elim else lf-tpl-implies-elim then ;
: lf-ol-elimination ( template -- c-addr u )
  case lf-tpl-implies-elim of s" →-elimination" endof
    lf-tpl-forall-elim of s" ∀-elimination" endof >r s" application" r> endcase ;
\ The reasons: "because f turns any proof of A into a proof of B.",
\ "because h holds for every x, in particular for a.", "by applying f."
: lf-ol-fn-at ( s -- ) dup lf-ol-first lf-lv-a swap lf-lv-formula ;
: lf-ol-implies ( s -- )
  s" because " lf-lv-put dup lf-ol-fn-at s"  turns any proof of " lf-lv-put
  dup lf-ol-first lf-lv-out-ref 1 2 pick lf-lv-part s"  into a proof of " lf-lv-put
  dup lf-lv-out-ref swap lf-lv-formula s" ." lf-lv-put ;
: lf-ol-pi-name ( ref s -- )
  lf-lv-at 0= if drop lf-lv-fail exit then
  lf-lv-term if lf-lv-push lf-lv-name-here else lf-lv-fail then lf-lv-release ;
: lf-ol-forall ( s -- )
  s" because " lf-lv-put dup lf-ol-fn-at s"  holds for every " lf-lv-put
  dup lf-ol-first lf-lv-out-ref over lf-ol-pi-name s" , in particular for " lf-lv-put
  dup lf-ol-second lf-lv-a swap lf-lv-formula s" ." lf-lv-put ;
: lf-ol-head-text ( h s -- )
  over lf-lv-rule lf-rule-constant = if drop lf-lv-a lf-pp-const-name
    if lf-lv-name-id else lf-lv-fail then exit then
  swap lf-lv-a swap lf-lv-formula ;
: lf-ol-applying ( s -- )
  s" by applying " lf-lv-put dup lf-ol-head swap lf-ol-head-text s" ." lf-lv-put ;
: lf-ol-reason ( s template -- )
  case lf-tpl-implies-elim of lf-ol-implies endof
    lf-tpl-forall-elim of lf-ol-forall endof >r lf-ol-applying r> endcase ;
: lf-ol-app-line ( s -- )
  dup lf-ol-spine-sets lf-ol-number s" Then " lf-lv-put dup lf-ol-typed s" ," lf-lv-put
  lf-ol-sentence dup lf-ol-template dup lf-ol-used dup lf-ol-elimination
  lf-ol-rule lf-ol-end
  lf-ol-more over swap lf-ol-reason lf-ol-more-end
  lf-ol-line# over lf-ol-line-of ! dup lf-ol-head lf-ol-proof @ swap lf-ol-proof ! ;
: lf-ol-app ( s -- ) dup lf-ol-first lf-ol-spine dup lf-ol-second lf-ol-walk
  lf-ol-app-line ;

\ The walk over the value's derivation: one word per recognised rule.
: lf-ol-walk-step ( s -- )
  dup lf-lv-rule case lf-rule-variable of lf-ol-var endof
    lf-rule-constant of lf-ol-recall endof lf-rule-application of lf-ol-app endof
    lf-rule-lambda of lf-ol-lambda endof nip endcase ;
' lf-ol-walk-step is lf-ol-walk

\ Whether the recognisers cover the derivation of step s.
defer lf-ol-known? ( s -- flag )
: lf-ol-known-app ( s -- flag )
  dup 0 lf-lv-inference 0= if drop false exit then lf-ol-known? 0= if drop false exit then
  1 lf-lv-inference if lf-ol-known? else false then ;
: lf-ol-known-lam ( s -- flag ) 1 lf-lv-inference if lf-ol-known? else false then ;
: lf-ol-known-step ( s -- flag )
  dup lf-lv-outcome ok? 0= if drop false exit then
  dup lf-lv-rule case lf-rule-variable of drop true endof
    lf-rule-constant of drop true endof lf-rule-application of lf-ol-known-app endof
    lf-rule-lambda of lf-ol-known-lam endof nip false swap endcase ;
' lf-ol-known-step is lf-ol-known?

\ The declaration's steps: its own (the last declaration step), the
\ value's inference, the final comparison and the type formation.
: lf-ol-declaration ( -- D true | false )
  lf-log-count 0= if false exit then
  1 lf-log-count do i lf-lv-rule lf-rule-declaration = if i true unloop exit then
  -1 +loop false ;
: lf-ol-premise-rule ( s rule -- p true | false )
  over lf-lv-premises 0 ?do over i lf-lv-premise dup lf-lv-rule 2 pick =
    if nip nip true unloop exit then drop loop 2drop false ;
: lf-ol-formation ( D -- F true | false )
  dup lf-rule-proposition lf-ol-premise-rule if nip true exit then
  lf-rule-type lf-ol-premise-rule ;

\ The header.
: lf-ol-decl ( -- decl ) lf-log-decl lf-input-decl ;
: lf-ol-theorem? ( -- flag ) lf-ol-decl lf-idecl-kind @ lf-kind-theorem = ;
: lf-ol-line ( c-addr u -- ) lf-lv-put 0 lf-lv-flush lf-lv-cr ;
\ A declaration's kind, as its title says it.
: lf-ol-kind ( kind -- c-addr u )
  case lf-kind-theorem of s" Theorem " endof lf-kind-definition of s" Definition " endof
    lf-kind-axiom of s" Axiom " endof lf-kind-opaque of s" Opaque " endof
    >r s" Declaration " r> endcase ;
: lf-ol-title ( -- )
  lf-ol-decl lf-idecl-kind @ lf-ol-kind lf-lv-put
  lf-ol-decl lf-idecl-name @ lf-lv-name-id 0 lf-lv-flush lf-lv-cr ;
\ The verdict, as the caller read it from the checked environment
\ (lf-outline): the published outcome and, when accepted, the axiom set.
\ An accepted result carries the label every accepted result carries (as
\ check-declaration's lf-check-label prints it; AGENTS.md).
: lf-ol-label ( -- c-addr u ) s" accepted (experimental, not independently audited)" ;
: lf-ol-outcome ( -- outcome ) 0 lf-olr-outcome lf-ol-field @ ;
: lf-ol-accepted? ( -- flag ) lf-ol-outcome ok? ;
: lf-ol-axioms ( -- )
  0 lf-olr-axioms lf-ol-field @ dup 0< if drop s" axioms: ?" lf-lv-put exit then
  ?dup if s" axioms: bits " lf-lv-put lf-lv-n else s" axioms: none" lf-lv-put then ;
: lf-ol-diagnostic ( -- )
  lf-diag-clear? if exit then s"   Diagnostic: " lf-lv-put lf-diag@ nip
  lf-diag-name lf-lv-put
  s"  (" lf-lv-put swap lf-lv-n s" , " lf-lv-put lf-lv-n s" )" lf-ol-line ;
: lf-ol-verdict ( -- )
  s"   " lf-lv-put lf-ol-accepted?
  if lf-ol-label lf-lv-put s" ; " lf-lv-put lf-ol-axioms 0 lf-lv-flush lf-lv-cr exit then
  lf-ol-outcome outcome-sane outcome-text lf-ol-line lf-ol-diagnostic ;
: lf-ol-statement-text ( -- )
  lf-ol-theorem? if s"   Statement: " else s"   Type:      " then lf-lv-put
  lf-ol-decl lf-idecl-type @ lf-lv lf-lv-fuel @
  lf-ol-theorem? if lf-print-statement else lf-print-term then lf-lv-printed
  0 lf-lv-flush lf-lv-cr ;
: lf-ol-source-name ( -- c-addr u ) lf-ol-input dup lf-olin-source @ swap lf-olin-len @ ;
: lf-ol-source ( -- )
  lf-ol-source-name dup 0= if 2drop exit then s"   Input:     " lf-lv-put lf-lv-put
  s"  line " lf-lv-put lf-ol-input lf-olin-line @ lf-lv-n 0 lf-lv-flush lf-lv-cr ;
: lf-ol-bound ( bound -- c-addr u )
  case lf-bound-records of s" records" endof lf-bound-marks of s" open rules" endof
    lf-bound-terms of s" term copies" endof lf-bound-levels of s" level copies" endof
    lf-bound-work of s" a formula too large to copy" endof
    lf-bound-refs of s" constant references" endof
    lf-bound-interrupted of s" the check stopped with rules open" endof
    lf-bound-memory of s" no memory for the log" endof
    >r s" a node it could not read" r> endcase ;
: lf-ol-cut ( -- ) s" truncated at step " lf-lv-put lf-log-cut swap lf-lv-n s"  ("
  lf-lv-put
  lf-ol-bound lf-lv-put s" )" lf-lv-put ;
: lf-ol-formed ( -- )
  lf-ol-declaration 0= if exit then lf-ol-formation 0= if exit then
  lf-ol-theorem? if s"  The statement is a proposition: " else s"  The type is a type: "
  then
  lf-lv-put dup lf-lv-step s"  (from " lf-lv-put lf-lv-start 1+ lf-lv-step s" )."
  lf-lv-put ;
: lf-ol-log-text ( -- )
  s"   Checker log: " lf-lv-put lf-log-level 0= if s" off." lf-ol-line exit then
  lf-log-count lf-lv-n s"  steps, " lf-lv-put
  lf-log-complete? if s" complete." lf-lv-put lf-ol-formed else s" incomplete: " lf-lv-put
  lf-ol-cut s" ." lf-lv-put then 0 lf-lv-flush lf-lv-cr ;
: lf-ol-header ( -- )
  lf-ol-title lf-ol-verdict lf-ol-statement-text lf-ol-source lf-ol-log-text ;

\ The footer: what is checked and what is template.
: lf-ol-templates ( -- )
  true lf-tpl-count 0 ?do 1 i lshift 0 lf-olr-templates lf-ol-field @ and
    if dup 0= if s" , " lf-lv-put then drop false i lf-tpl-name lf-lv-put then loop drop ;
: lf-ol-footer ( -- )
  s" ∎" lf-ol-line
  s" Rules, formulas and step numbers come from the checker's log; the sentences are"
  lf-ol-line s" fixed templates (structured-template), not checked reasoning." lf-ol-line
  s" Templates: " lf-lv-put lf-ol-templates s" ." lf-ol-line ;

\ The outline proper, for declaration step D.
: lf-ol-whnfs ( E -- )
  dup lf-lv-start 1+ ?do i lf-lv-rule lf-rule-whnf = if i lf-ol-step+ then loop ;
: lf-ol-statement ( D -- )
  dup lf-rule-defeq lf-ol-premise-rule 0= if drop exit then
  dup lf-ol-whnfs swap lf-ol-first lf-ol-line-of @ lf-ol-ref+ dup lf-ol-step+
  lf-ol-number lf-ol-theorem? if s" This is the statement." else
  s" This is the declared type."
  then lf-lv-put lf-ol-sentence s" definitional equality" lf-ol-rule lf-ol-end drop
  lf-tpl-statement lf-ol-used ;
: lf-ol-proof-title ( -- )
  lf-lv-cr lf-ol-theorem? if s" Proof (reconstructed from the proof term)."
  else s" Construction (reconstructed from the value)." then lf-ol-line ;
: lf-ol-outline ( D -- )
  lf-ol-proof-title dup lf-ol-first lf-ol-walk lf-ol-statement lf-ol-footer ;

\ Why no outline is printed, and the steps where they explain.
: lf-ol-list ( -- ) lf-lv-cr s" Steps." lf-ol-line lf-log-count lf-lv-list ;
: lf-ol-none ( c-addr u -- ) lf-lv-cr lf-ol-line ;
: lf-ol-truncated ( -- )
  lf-lv-cr s" No proof outline: the declaration is accepted, but the checker's log was "
  lf-lv-put lf-ol-cut s" ; the verdict is unaffected." lf-ol-line ;
: lf-ol-uncovered ( -- )
  s" No outline template covers this proof; its steps follow." lf-ol-none lf-ol-list ;
: lf-ol-recognised ( -- D true | false )
  lf-ol-declaration 0= if false exit then
  dup lf-lv-outcome ok? 0= if drop false exit then
  dup 0 lf-lv-inference 0= if drop false exit then lf-ol-known? dup 0= if nip then ;
: lf-ol-not-accepted ( -- )
  s" No proof outline: the declaration was not accepted." lf-ol-none ;
: lf-ol-no-formulas ( -- )
  s" Proof outline not available: the log was kept without formulas (level steps)."
  lf-ol-none ;
\ Why no outline can be printed, said: true; or false when one can.
: lf-ol-refused? ( -- flag )
  lf-ol-accepted? 0= if lf-ol-not-accepted true exit then
  lf-log-level lf-log-terms <> if lf-ol-no-formulas true exit then
  lf-log-complete? 0= if lf-ol-truncated true exit then false ;
: lf-ol-body ( detail -- )
  if lf-ol-list exit then lf-log-level 0= if exit then lf-ol-refused? if exit then
  lf-ol-recognised if lf-ol-outline else lf-ol-uncovered then ;

\ Public words.
\ The input's name and the declaration's line in it, printed in the
\ header of the next outline (a length of 0 prints none). The name is not
\ copied: it must stay where it is until then.
: lf-outline-source ( c-addr u line -- )
  lf-ol-input tuck lf-olin-line ! tuck lf-olin-len ! lf-olin-source ! ;

\ Whether the log is the one the caller's verdict belongs to (see the
\ header): the same intact input; the header's published slot and outcome
\ the log's declaration and the caller's outcome; and the last step of a
\ complete log that publish step. A log kept off has only its header.
: lf-ol-same-input? ( -- flag )
  lf-input-intact? lf-input-fingerprint lf-log-input = and ;
: lf-ol-header-agrees? ( -- flag )
  lf-log-published lf-ol-outcome = swap lf-log-decl = and ;
: lf-ol-publish-step? ( rec -- flag )
  dup logrec-rule @ lf-rule-publish = over logrec-a @ lf-log-decl = and
  swap logrec-outcome @ lf-ol-outcome = and ;
: lf-ol-log-agrees? ( -- flag )
  lf-log-level 0= lf-log-complete? 0= or if true exit then
  lf-log-count ?dup 0= if false exit then lf-log-record lf-ol-publish-step? ;
: lf-ol-matches? ( -- flag )
  lf-ol-same-input? lf-ol-header-agrees? and lf-ol-log-agrees? and ;
: lf-ol-foreign ( -- )
  s" No outline: the checker's log does not belong to this declaration's published"
  lf-lv-put s"  verdict, or the input changed since the check." lf-ol-line ;

\ Print the outline of the declaration whose check wrote this context's
\ log, or with detail true every step of the log, to TYPE: after the
\ check, in the context that ran it, its input intact. outcome and axioms
\ are the verdict the caller read from the checked environment for that
\ declaration (lf-env-outcome, and lf-env-axioms's bits when accepted, -1
\ when they could not be read); the printer never reads the environment,
\ and prints only a refusal unless the log agrees (lf-ol-matches?).
: lf-ol-clear ( -- )
  0 0 lf-olr-lines lf-ol-field ! 0 lf-ol-indent ! 0 0 lf-olr-templates lf-ol-field !
  lf-ol-sets-clear 0 lf-olr-line-of lf-ol-field lf-log-record-capacity 3 * cells erase ;
: lf-ol-verdict! ( outcome axioms -- )
  0 lf-olr-axioms lf-ol-field ! 0 lf-olr-outcome lf-ol-field ! ;
: lf-ol-blocks ( -- flag )
  lf-ol-open 0= if false exit then 0 100000 lf-lv-setup dup 0= if lf-ol-close drop then ;
: lf-ol-no-memory ( -- ) ." No proof outline: no memory for the printer." cr ;
: lf-ol-print ( detail -- )
  lf-ol-matches? if lf-ol-header lf-ol-body else drop lf-ol-foreign then lf-lv-cr ;
: lf-outline ( outcome axioms detail -- )
  >r lf-ol-blocks 0= if 2drop r> drop lf-ol-no-memory exit then
  lf-ol-verdict! lf-ol-clear r> lf-ol-print lf-lv-done lf-ol-close drop ;
