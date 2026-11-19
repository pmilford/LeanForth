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
\ publish step. Nor does it print anything from a log that fails the
\ structural check of log-check.fs (N1 of the second review).
\
\ What is printed. The header: kind and name, the verdict with its
\ axioms, the statement (or type), the input line (lf-outline-source),
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
\ Depth (plan task 6.2.0): the walk over the derivation, the check that
\ the recognisers cover it and the scan for a bound variable run on
\ growable work stacks (lib/walk.fs), so no depth of a proof is tied to
\ the host's stacks; the walk's room is made before anything is printed.
\ State: a small context record, lf-ol-input (the input's name and the
\ declaration's line, set before printing), and one cell, lf-ol-held,
\ pointing to a heap block (about 25 KB) that exists only while
\ lf-outline prints (the context's teardown frees one left by a THROW):
\ the verdict given, the line count, indent, templates used, the current
\ line's steps and uses, and per step its concluding line, its binder's
\ line and whether it is a proof; and three walk records of the context.
\ Printing state is log-view.fs's.

require ../lib/bounds.fs
require ./log-view.fs
require ./log-check.fs
require ./statement-forms.fs
require ../core/axiom-allowlist.fs
require ../core/diagnostics.fs
require ../core/tagged-sort-boundary.fs

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
\ The block, as log-view.fs's (lib/blocks.fs's block-reused, block-free).
: lf-ol-open ( -- flag ) /lf-ol lf-ol-held block-reused ;
: lf-ol-close ( -- ior ) lf-ol-held block-free ;
:noname ( -- ) lf-ol-close throw ; context-teardown

\ The style of the next outlines: LaTeX (true) or plain text (false, a new
\ context's). A list of every step (detail) is always plain.
4 cells context-record: lf-ol-style
: lf-outline-latex! ( flag -- ) lf-ol-style ! ;
\ Where the next outlines go: an xt ( c-addr u -- ), or 0 for TYPE.
: lf-outline-sink! ( xt|0 -- ) lf-ol-style cell+ ! ;
\ How plain-style outlines show names: namer ( id -- c-addr u flag ) for a
\ declaration's name and escape ( c-addr u -- c-addr' u' flag ) for text
\ from outside, the input's file name (never the term printer's, which is
\ escaped already: log-view.fs lf-lv-put), each an xt or 0 (as they are,
\ the default); the text of either is
\ valid until the next call, and a false flag means it must not be shown.
: lf-outline-names! ( namer escape -- ) lf-ol-style 3 cells + ! lf-ol-style 2 cells + ! ;
: lf-ol-set-names ( -- ) lf-ol-style 2 cells + @ lf-lv lf-lv-decl-namer !
  lf-ol-style 3 cells + @ lf-lv lf-lv-escape ! ;

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
: lf-ol-add ( x addr count -- )
  >r over 0> 0= if 2drop r> drop exit then
  2dup r@ @ cells-has? r@ @ lf-ol-set-capacity < 0= or if 2drop r> drop exit then
  r@ @ cells + ! 1 r> +! ;
: lf-ol-steps ( -- addr count ) 0 lf-olr-steps lf-ol-field 0 lf-olr-steps# lf-ol-field ;
: lf-ol-refs ( -- addr count ) 0 lf-olr-refs lf-ol-field 0 lf-olr-refs# lf-ol-field ;
: lf-ol-step+ ( s -- ) lf-ol-steps lf-ol-add ;
: lf-ol-ref+ ( line -- ) lf-ol-refs lf-ol-add ;
: lf-ol-in? ( x addr count -- flag ) @ cells-has? ;
: lf-ol-step? ( s -- flag ) lf-ol-steps lf-ol-in? ;
: lf-ol-ref? ( line -- flag ) lf-ol-refs lf-ol-in? ;
: lf-ol-sets-clear ( -- ) 0 0 lf-olr-steps# lf-ol-field ! 0 0 lf-olr-refs# lf-ol-field ! ;

\ A line: number and indent, the sentence (in the buffer, padded to the
\ rule column), the rule with the lines it uses, the steps it covers as
\ runs (s27–s29), then any continuation line.
: lf-ol-number ( -- )
  1 0 lf-olr-lines lf-ol-field +! s"   " lf-lv-put lf-ol-line# lf-lv-n 5 lf-lv-col
  lf-ol-indent @ lf-lv-spaces ;
: lf-ol-sentence ( -- ) 46 lf-ol-indent @ - lf-lv-col ;
: lf-ol-from ( -- c-addr u ) lf-lv-tex? if s"  $\leftarrow$ " else s"  ← " then ;
: lf-ol-dash ( -- c-addr u ) lf-lv-tex? if s" --" else s" –" then ;
\ The rules' names, each with its plain and its LaTeX spelling in one word, so
\ that no rule can reach the LaTeX unspelled.
: lf-rn-forall-intro ( -- c-addr u )
  lf-lv-tex? if s" $\forall$-introduction" else s" ∀-introduction" then ;
: lf-rn-implies-intro ( -- c-addr u )
  lf-lv-tex? if s" $\to$-introduction" else s" →-introduction" then ;
: lf-rn-both-intro ( -- c-addr u )
  lf-lv-tex? if s" $\to$/$\forall$-introduction" else s" →/∀-introduction" then ;
: lf-rn-implies-elim ( -- c-addr u )
  lf-lv-tex? if s" $\to$-elimination" else s" →-elimination" then ;
: lf-rn-forall-elim ( -- c-addr u )
  lf-lv-tex? if s" $\forall$-elimination" else s" ∀-elimination" then ;
: lf-ol-uses ( -- )
  0 lf-olr-refs# lf-ol-field @ 0= if exit then lf-ol-from lf-lv-put
  true lf-ol-line# 1+ 1 ?do i lf-ol-ref? if dup 0= if s" , " lf-lv-put then drop false
    i lf-lv-n then loop drop ;
: lf-ol-rule ( c-addr u -- ) s" [" lf-lv-put lf-lv-put lf-ol-uses s" ]" lf-lv-put
  35 lf-lv-col ;
: lf-ol-run ( s -- s' ) begin 1+ dup lf-ol-step? 0= until 1- ;
: lf-ol-runs ( -- )
  true lf-log-count 1+ 1 ?do i lf-ol-step? i 1- lf-ol-step? 0= and
    if dup 0= if s" , " lf-lv-put then drop false i lf-lv-step i lf-ol-run
      dup i <> if lf-ol-dash lf-lv-put lf-lv-step else drop then then loop drop ;
: lf-ol-end ( -- ) lf-ol-runs 0 lf-lv-flush lf-lv-eol lf-ol-sets-clear ;
\ A continuation line: under the sentence and the rule, in LaTeX style one cell
\ over the last three columns.
: lf-ol-more ( -- )
  lf-lv-tex? if s" & \multicolumn{3}{@{}p{0.72\linewidth}@{}}{" lf-lv-out then
  lf-ol-indent @ 7 + lf-lv-spaces ;
: lf-ol-more-end ( -- )
  0 lf-lv-flush lf-lv-tex? if s" }" lf-lv-out then lf-lv-eol ;

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
  dup lf-log-level-copies < if lf-log-level-node@ 2drop lf-level-tag-zero = else
  drop false then ;
: lf-ol-prop? ( ref -- flag )
  lf-lv-node 0= if false exit then rot case
    lf-tag-sort of drop 0= endof lf-tag-symbolic-sort of drop lf-ol-level-zero? endof
    nip nip false swap endcase ;
: lf-ol-sort? ( ref -- flag )
  lf-lv-tag 0= if false exit then lf-sort-tags lf-tag-in? ;

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
: lf-ol-name ( r -- )
  dup lf-lv-at if lf-lv-a lf-lv-name-of-node else drop lf-lv-fail then ;
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
  else lf-tpl-let-types then lf-ol-used lf-rn-forall-intro lf-ol-rule lf-ol-end ;
\ One binder: "Let x : A." or "Assume h : A."
: lf-ol-single ( r class -- r' )
  lf-ol-number dup lf-class-assume = if s" Assume " else s" Let " then lf-lv-put
  lf-lv-math-open over lf-ol-name s"  : " lf-lv-put over dup lf-ol-domain swap lf-lv-formula
  lf-lv-math-close s" ." lf-lv-put
  lf-ol-sentence 2dup lf-ol-introduce lf-class-assume =
  if lf-tpl-assume lf-ol-used s" assumption" else lf-tpl-let lf-ol-used lf-rn-forall-intro
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
  lf-ol-kinds 2dup and if 2drop lf-rn-both-intro exit then
  drop if lf-rn-implies-intro else lf-rn-forall-intro then ;
: lf-ol-discharge ( s0 -- )
  dup lf-ol-intros lf-ol-number s" Discharging " lf-lv-put lf-ol-intro-list s"  gives"
  lf-lv-put lf-ol-sentence dup lf-ol-innermost lf-ol-second dup lf-ol-line-of @ lf-ol-ref+
  lf-ol-proof @ over lf-ol-proof ! dup lf-ol-introduction lf-ol-rule lf-ol-end
  lf-tpl-discharge lf-ol-used lf-ol-more dup lf-lv-out-ref over lf-lv-formula s" ."
  lf-lv-put
  lf-ol-more-end lf-ol-line# swap lf-ol-line-of ! ;

\ The walk over the value's derivation takes its tasks one at a time from
\ a stack (a paired walk record of lib/walk.fs, used as a growable stack
\ of a step and the task's xt ( s -- )), the task pushed last first:
\ walking a step (lf-ol-walk) prints its own lines and pushes what it
\ leaves for later, so the walk keeps no depth on the host's stacks. Its
\ room is made before the outline is printed (lf-ol-tasks-room?): the
\ derivation is a tree, so each step is the subject of at most three
\ tasks (its walk, its application line, its discharge). A task that
\ cannot be pushed all the same prints "?".
lf-walk-room context-walk2: lf-ol-tasks
: lf-ol-later ( s xt -- ) lf-ol-tasks walk-push-pair 0= if lf-lv-fail then ;
: lf-ol-tasks-room? ( -- flag )
  lf-ol-tasks walk-clear lf-log-count 6 * 2 + lf-ol-tasks walk-room-for? ;
: lf-ol-run-tasks ( -- )
  begin lf-ol-tasks walk-pending @ 0> while lf-ol-tasks walk-pop-pair execute repeat ;
defer lf-ol-walk ( s -- )
: lf-ol-walk-later ( s -- ) ['] lf-ol-walk lf-ol-later ;
\ A lambda chain: its binders now, then its body (indented) and its
\ discharge.
: lf-ol-discharged ( s0 -- ) -2 lf-ol-indent +! lf-ol-discharge ;
: lf-ol-lambda ( s -- )
  dup lf-ol-binders 2 lf-ol-indent +! dup ['] lf-ol-discharged lf-ol-later
  lf-ol-innermost lf-ol-second lf-ol-walk-later ;

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
  lf-lv-math-open dup lf-lv-a over lf-lv-formula s"  : " lf-lv-put dup lf-lv-out-ref swap
  lf-lv-formula lf-lv-math-close ;
\ Where a recalled constant comes from: its slot, or -- for a recursor
\ Lean's kernel generated, which no slot holds (ADR 0015 decision 12) --
\ the kernel.
: lf-ol-recalled ( d -- )
  dup 0< if drop s" generated by Lean's kernel for an earlier inductive type." lf-lv-put
  exit then
  s" accepted above as d" lf-lv-put lf-lv-n s" ." lf-lv-put ;
: lf-ol-recall ( c -- )
  dup lf-ol-step+ lf-ol-number s" Recall " lf-lv-put dup lf-ol-typed s" ," lf-lv-put
  lf-ol-sentence s" earlier declaration" lf-ol-rule lf-ol-end lf-tpl-recall lf-ol-used
  lf-ol-more dup lf-ol-resolved lf-ol-recalled
  lf-ol-more-end lf-ol-line# over lf-ol-line-of !
  dup lf-ol-resolved lf-ol-theorem-slot? swap lf-ol-proof ! ;

\ Applications: the head and arguments of a spine, the head's lines
\ first, then the arguments' from the innermost application out: walking
\ down the spine from the outermost application, each argument's walk is
\ pushed, the head's last.
: lf-ol-head ( s -- h ) begin dup lf-ol-application? while lf-ol-first repeat ;
: lf-ol-spine ( s -- )
  begin dup lf-ol-application? while dup lf-ol-second lf-ol-walk-later lf-ol-first repeat
  lf-ol-walk-later ;
: lf-ol-spine-sets ( s -- )
  begin dup lf-ol-application? while
    dup lf-ol-step+ dup lf-ol-second lf-ol-line-of @ lf-ol-ref+ lf-ol-first
  repeat lf-ol-line-of @ lf-ol-ref+ ;
\ Whether term (in the term store) mentions bound variable k: a paired
\ walk of its own (lib/walk.fs; a node and the binders above it in the
\ term), with the formula fuel. A walk that cannot finish (out of fuel or
\ room) counts as mentioning k (so the line says ∀-elimination, which
\ reads true of every Pi); a node that cannot be read mentions nothing,
\ and the walk goes on with the rest. A hit is reported as rejected, a
\ stop signal here (lf-pp-hit?), never a verdict.
lf-walk-room context-walk2: lf-ol-scan
: lf-ol-scan-dispatch ( first second walk tag -- outcome )
  dup lf-tag-bvar = if drop nip lf-pp-var-is exit then
  dup lf-term-binary-tag? if lf-pp-scan-binary else drop 2drop drop outcome-ok then ;
: lf-ol-scan-visit ( walk -- outcome )
  lf-term-walk-read if lf-ol-scan-dispatch else outcome-ok then ;
: lf-ol-mentions? ( term k -- flag )
  lf-ol-scan walk-arg ! lf-lv lf-lv-fuel @ lf-ol-scan walk-budget drop
  0 ['] lf-ol-scan-visit lf-ol-scan walk-run-pair lf-pp-hit?
  dup ok? if drop else outcome-invalid <> nip then ;
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
  case lf-tpl-implies-elim of lf-rn-implies-elim endof
    lf-tpl-forall-elim of lf-rn-forall-elim endof >r s" application" r> endcase ;
\ The reasons: "because f turns any proof of A into a proof of B.",
\ "because h holds for every x, in particular for a.", "by applying f."
: lf-ol-fn-at ( s -- ) dup lf-ol-first lf-lv-a swap lf-lv-formula ;
: lf-ol-implies ( s -- )
  s" because " lf-lv-put dup lf-ol-fn-at s"  turns any proof of " lf-lv-put
  dup lf-ol-first lf-lv-out-ref 1 2 pick lf-lv-part s"  into a proof of " lf-lv-put
  dup lf-lv-out-ref swap lf-lv-formula s" ." lf-lv-put ;
: lf-ol-pi-name ( ref s -- )
  lf-lv-at 0= if drop lf-lv-fail exit then
  lf-lv-term if lf-lv-name-of-node else lf-lv-fail then lf-lv-release ;
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
\ An application: its function's spine, then its argument, then its line.
: lf-ol-app ( s -- )
  dup ['] lf-ol-app-line lf-ol-later dup lf-ol-second lf-ol-walk-later
  lf-ol-first lf-ol-spine ;

\ Walking a step: one word per recognised rule.
: lf-ol-walk-step ( s -- )
  dup lf-lv-rule case lf-rule-variable of lf-ol-var endof
    lf-rule-constant of lf-ol-recall endof lf-rule-application of lf-ol-app endof
    lf-rule-lambda of lf-ol-lambda endof nip endcase ;
' lf-ol-walk-step is lf-ol-walk

\ Whether the recognisers cover the derivation of step s: a walk over the
\ inference premises it needs (lib/walk.fs; each an earlier step than its
\ parent), which stops at the first step they do not cover, reported as
\ rejected (a stop signal here, never a verdict).
lf-walk-room context-walk: lf-ol-premises
: lf-ol-known-premise ( walk s i -- outcome )
  rot >r lf-lv-inference if r> walk-child else r> drop outcome-rejected then ;
: lf-ol-known-app ( s walk -- outcome )
  2dup swap 0 lf-ol-known-premise dup ok?
  if drop swap 1 lf-ol-known-premise else nip nip then ;
: lf-ol-known-lam ( s walk -- outcome ) swap 1 lf-ol-known-premise ;
\ A CASE with one arm per recognised rule (read as a table).
: lf-ol-known-rule ( s walk rule -- outcome )
  case lf-rule-variable of 2drop outcome-ok endof
    lf-rule-constant of 2drop outcome-ok endof
    lf-rule-application of lf-ol-known-app endof
    lf-rule-lambda of lf-ol-known-lam endof
    >r 2drop outcome-rejected r> endcase ;
: lf-ol-known-visit ( walk -- outcome )
  dup walk-node @ dup lf-lv-outcome ok? 0= if 2drop outcome-rejected exit then
  tuck lf-lv-rule lf-ol-known-rule ;
: lf-ol-known? ( s -- flag )
  max-n lf-ol-premises walk-budget drop
  ['] lf-ol-known-visit lf-ol-premises walk-run ok? ;

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
: lf-ol-line ( c-addr u -- ) lf-lv-put 0 lf-lv-flush lf-lv-eol ;
\ A declaration's kind, as its title says it.
: lf-ol-kind ( kind -- c-addr u )
  case lf-kind-theorem of s" Theorem " endof lf-kind-definition of s" Definition " endof
    lf-kind-axiom of s" Axiom " endof lf-kind-opaque of s" Opaque " endof
    >r s" Declaration " r> endcase ;
: lf-ol-title ( -- )
  lf-lv-tex? if s" \textbf{" lf-lv-put then
  lf-ol-decl lf-idecl-kind @ lf-ol-kind lf-lv-put lf-lv-tex? if s" }" lf-lv-put then
  lf-ol-decl lf-idecl-name @ lf-lv-name-id 0 lf-lv-flush lf-lv-eol ;
\ The verdict, as the caller read it from the checked environment
\ (lf-outline): the published outcome and, when accepted, the axiom set,
\ as check-declaration's lf-check-verdict. prints them.
: lf-ol-outcome ( -- outcome ) 0 lf-olr-outcome lf-ol-field @ ;
: lf-ol-accepted? ( -- flag ) lf-ol-outcome ok? ;
\ The axiom set as check-declaration's lf-check-axioms. prints it: the
\ allowlist's names of its listed bits, then "unlisted" (NOT PROVED).
: lf-ol-axiom ( bits bit -- bits )
  2dup and 0= if drop exit then
  dup lf-axiom-unlisted = if s" unlisted" else dup lf-axiom-name then lf-lv-put
  2* 1- invert over and if s" , " lf-lv-put then ;
: lf-ol-axioms ( -- )
  0 lf-olr-axioms lf-ol-field @ dup 0< if drop s" axioms: ?" lf-lv-put exit then
  ?dup 0= if s" axioms: none" lf-lv-put exit then
  s" axioms: " lf-lv-put lf-axiom-propext lf-ol-axiom lf-axiom-choice lf-ol-axiom
  lf-axiom-sound lf-ol-axiom lf-axiom-unlisted lf-ol-axiom drop ;
: lf-ol-diagnostic ( -- )
  lf-diag-clear? if exit then s"   Diagnostic: " lf-lv-put lf-diag@ nip
  lf-diag-name lf-lv-put
  s"  (" lf-lv-put swap lf-lv-n s" , " lf-lv-put lf-lv-n s" )" lf-ol-line ;
\ NOT PROVED, as the command line's reports mark it (review N11): an axiom
\ outside the allowlist. Axioms not read (-1, "axioms: ?") would be marked
\ so too; the command line never gives them (cli/tally.fs decl-axioms).
: lf-ol-not-proved. ( -- )
  0 lf-olr-axioms lf-ol-field @ lf-allowlist-bits invert and
  if s" ; NOT PROVED: depends on an axiom" lf-lv-put then ;
: lf-ol-verdict ( -- )
  s"   " lf-lv-put lf-ol-accepted?
  if s" accepted; " lf-lv-put lf-ol-axioms lf-ol-not-proved. 0 lf-lv-flush lf-lv-eol exit
  then
  lf-ol-outcome outcome-sane outcome-text lf-ol-line lf-ol-diagnostic ;
\ The statement (or the type), in the forms selected (statement-forms.fs); a
\ declaration with no type says so.
: lf-ol-kind-word ( -- c-addr u ) lf-ol-theorem? if s" Statement" else s" Type" then ;
: lf-ol-statement-text ( -- )
  lf-ol-decl lf-idecl-type @ 0< if
    lf-ol-theorem? if s"   Statement: " else s"   Type:      " then lf-lv-put
    s" none" lf-ol-line exit then
  lf-ol-decl lf-ol-kind-word lf-print-forms ;
: lf-ol-source-name ( -- c-addr u ) lf-ol-input dup lf-olin-source @ swap lf-olin-len @ ;
\ The input's name: as it is, or escaped in the typewriter font (LaTeX).
: lf-ol-source-name. ( c-addr u -- )
  lf-lv-tex? if s" \texttt{" lf-lv-put 0 lf-lv-flush lf-sf-tex s" }" lf-lv-put
  else lf-lv-put-text then ;
: lf-ol-source ( -- )
  lf-ol-source-name dup 0= if 2drop exit then s"   Input:     " lf-lv-put
  lf-ol-source-name.
  s"  line " lf-lv-put lf-ol-input lf-olin-line @ lf-lv-n 0 lf-lv-flush lf-lv-eol ;
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
  lf-ol-cut s" ." lf-lv-put then 0 lf-lv-flush lf-lv-eol ;
: lf-ol-header ( -- )
  lf-ol-title lf-ol-verdict lf-ol-statement-text lf-ol-source lf-ol-log-text ;

\ The footer: what is checked and what is template.
: lf-ol-templates ( -- )
  true lf-tpl-count 0 ?do 1 i lshift 0 lf-olr-templates lf-ol-field @ and
    if dup 0= if s" , " lf-lv-put then drop false i lf-tpl-name lf-lv-put then loop drop ;
\ In LaTeX style the table ends and the footer is a small paragraph.
: lf-ol-table-end ( -- ) s\" \\end{tabular}}\n" lf-lv-out ;
: lf-ol-small-open ( -- ) s\" \\begin{flushleft}\\small\n" lf-lv-out ;
: lf-ol-tex-open ( -- ) lf-lv-tex? if s\" \\begin{flushleft}\n" lf-lv-out then ;
: lf-ol-tex-close ( -- ) lf-lv-tex? if s\" \\end{flushleft}\n" lf-lv-out then ;
: lf-ol-end-mark ( -- c-addr u ) lf-lv-tex? if s" $\blacksquare$" else s" ∎" then ;
: lf-ol-footer ( -- )
  lf-lv-tex? if lf-ol-table-end lf-ol-small-open then
  lf-ol-end-mark lf-ol-line
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
\ In LaTeX style the title ends the header's paragraph and the lines are the
\ rows of a table: number, sentence, rule and uses, steps.
: lf-ol-table ( -- )
  s\" \\par\\noindent{\\small\n\\begin{tabular}{@{}r@{\\hspace{1em}}" lf-lv-out
  s\" p{0.46\\linewidth}@{\\hspace{1em}}p{0.27\\linewidth}l@{}}\n" lf-lv-out ;
: lf-ol-proof-words ( -- c-addr u )
  lf-ol-theorem? if s" Proof (reconstructed from the proof term)."
  else s" Construction (reconstructed from the value)." then ;
: lf-ol-proof-title ( -- )
  lf-lv-tex? if lf-ol-tex-close s" \noindent\textit{" lf-lv-put lf-ol-proof-words
    lf-lv-put s" }" lf-lv-put 0 lf-lv-flush lf-lv-cr lf-ol-table exit then
  lf-lv-cr lf-ol-proof-words lf-ol-line ;
: lf-ol-outline ( D -- )
  lf-ol-proof-title lf-ol-tasks walk-clear
  dup lf-ol-first lf-ol-walk-later lf-ol-run-tasks lf-ol-statement lf-ol-footer ;

\ Why no outline is printed, and the steps where they explain.
: lf-ol-list ( -- ) lf-lv-cr s" Steps." lf-ol-line lf-log-count lf-lv-list ;
: lf-ol-none ( c-addr u -- ) lf-lv-gap lf-ol-line ;
: lf-ol-truncated ( -- )
  lf-lv-gap s" No proof outline: the declaration is accepted, but the checker's log was "
  lf-lv-put lf-ol-cut s" ; the verdict is unaffected." lf-ol-line ;
: lf-ol-uncovered ( -- )
  lf-lv-tex? if s" No outline template covers this proof; --detail lists its steps."
    lf-ol-none exit then
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
: lf-ol-postulate? ( -- flag )
  lf-ol-decl lf-idecl-kind @ dup lf-kind-axiom = swap lf-kind-quotient = or ;
: lf-ol-unproved ( -- )
  s" No proof outline: an axiom or a quotient constant has no proof; Lean's kernel takes it as given."
  lf-ol-none ;
\ Why no outline can be printed, said: true; or false when one can.
: lf-ol-refused? ( -- flag )
  lf-ol-accepted? 0= if lf-ol-not-accepted true exit then
  lf-ol-postulate? if lf-ol-unproved true exit then
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
: lf-ol-publish-step? ( s -- flag )
  dup lf-log-rule@ lf-rule-publish = over lf-log-a@ lf-log-decl = and
  swap lf-log-outcome@ lf-ol-outcome = and ;
: lf-ol-log-agrees? ( -- flag )
  lf-log-level 0= lf-log-complete? 0= or if true exit then
  lf-log-count ?dup 0= if false exit then lf-ol-publish-step? ;
: lf-ol-matches? ( -- flag )
  lf-ol-same-input? lf-ol-header-agrees? and lf-ol-log-agrees? and ;
: lf-ol-foreign ( -- )
  s" No outline: the checker's log does not belong to this declaration's published"
  lf-lv-put s"  verdict, or the input changed since the check." lf-ol-line ;
\ A log the structural check (log-check.fs) rejects: nothing is printed
\ from it (a log kept off has nothing to check).
: lf-ol-flaw ( -- part ) lf-log-level if lf-log-flaw else 0 then ;
: lf-ol-malformed ( part -- )
  s" No outline: the checker's log fails its structural check (part " lf-lv-put lf-lv-n
  s" ); nothing is printed from it." lf-ol-line ;

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
  lf-ol-tasks-room? 0= if false exit then
  lf-ol-open 0= if false exit then lf-ol-style cell+ @ 100000 lf-lv-setup
  dup 0= if lf-ol-close drop then ;
: lf-ol-no-memory ( -- ) ." No proof outline: no memory for the printer." cr ;
: lf-ol-print ( detail -- )
  lf-ol-tex-open
  lf-ol-matches? 0= if drop lf-ol-foreign lf-ol-tex-close lf-lv-cr exit then
  lf-ol-flaw ?dup if lf-ol-malformed drop lf-ol-tex-close lf-lv-cr exit then
  lf-ol-header lf-ol-body lf-ol-tex-close lf-lv-cr ;
: lf-outline ( outcome axioms detail -- )
  >r lf-ol-blocks 0= if 2drop r> drop lf-ol-no-memory exit then
  lf-ol-verdict! lf-ol-clear lf-ol-set-names
  r@ 0= lf-ol-style @ and lf-lv-latex! r> lf-ol-print
  lf-lv-done lf-ol-close drop ;
