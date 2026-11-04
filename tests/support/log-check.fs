\ A structural check of the current context's derivation log
\ (src/core/derivation-log.fs; ADR 0013, test plan item 2), for the log's
\ tests: steps numbered from 1 with known rules; every start below its
\ step and sub-derivations nested; every reference defined (an input
\ object below the input marks, a copy already made, none, or unkept only
\ at level steps); every copy referring only to input objects and earlier
\ copies; a publish step only last, using the step before it, which is
\ the check's declaration step (or none); a truncated
\ log ending exactly before the step it could not write (a consistent
\ prefix). lc-why tells which part failed. Test-only.

require ../../src/core/derivation-log.fs

variable lc-failed   \ the first part that failed, 0 when none
: lc-fail ( part -- ) lc-failed @ 0= if lc-failed ! else drop then ;
: lc-why ( -- part ) lc-failed @ ;

\ Rules: a known code (the catalogue's last entry has code 0).
: lc-known? ( rule -- flag ) lf-log-entry lf-log-entry-code 0<> ;
\ Nesting: every record t in (start, s) has its own start >= start.
: lc-nested? ( s -- flag )
  dup lf-log-record logrec-start @ swap over 1+ ?do
    i lf-log-record logrec-start @ over < if drop false unloop exit then loop drop true ;
: lc-start? ( s -- flag ) dup lf-log-record logrec-start @ dup 0< 0= -rot > and ;

\ References of a kind.
: lc-mark ( k -- n ) lf-input-intact? if lf-input-mark mark-count @ else drop max-n then ;
: lc-copy-ok? ( ref copies -- flag ) swap lf-log-copy-index swap < ;
: lc-sentinel? ( ref -- flag )
  dup lf-log-none = swap lf-log-unkept = lf-log-level lf-log-steps = and or ;
: lc-term-ok? ( ref -- flag )
  dup lc-sentinel? if drop true exit then
  dup 0< 0= if 0 lc-mark < exit then lf-log-term-copies lc-copy-ok? ;
: lc-level-ok? ( ref -- flag )
  dup lc-sentinel? if drop true exit then
  dup 0< 0= if 1 lc-mark < exit then lf-log-level-copies lc-copy-ok? ;
: lc-ref-ok? ( ref kind -- flag )
  case lf-ref-term of lc-term-ok? endof lf-ref-level of lc-level-ok? endof
    lf-ref-none of lf-log-none = endof nip true swap endcase ;
: lc-refs? ( s -- flag )
  lf-log-record >r r@ logrec-rule @
  r@ logrec-a @ over 0 lf-log-kind lc-ref-ok? r@ logrec-b @ 2 pick 2 lf-log-kind lc-ref-ok?
  and r> logrec-out @ rot 4 lf-log-kind lc-ref-ok? and ;

\ Copies: each child an input object or an earlier copy.
: lc-child? ( ref k -- flag ) over 0< 0= if drop 0 lc-mark < exit then
  swap lf-log-copy-index > ;
\ A constant: a reference below the input mark, or a copied reference
\ whose arguments are all defined level references.
: lc-args? ( k -- flag )
  lf-log-cref-slot dup logcref-args @ swap logcref-count @ true swap 0 ?do
    over i + lf-log-arg-ref lc-level-ok? and loop nip ;
: lc-cref? ( cref -- flag )
  dup 0< 0= if 3 lc-mark < exit then
  lf-log-copy-index dup lf-log-cref-copies < if lc-args? else drop false then ;
: lc-leaf? ( first tag -- flag )
  dup lf-tag-symbolic-sort = if drop lc-level-ok? exit then
  lf-tag-constant = if lc-cref? else drop true then ;
: lc-term-copy? ( k -- flag )
  dup lf-log-term-slot node@ rot dup lf-term-binary-tag? if drop 2 pick lc-child? >r
    over lc-child? nip r> and exit then
  nip lc-leaf? nip ;
: lc-copies? ( -- flag )
  true lf-log-term-copies 0 ?do i lc-term-copy? and loop ;

\ The publish step, and the end of a truncated log. A publish step is the
\ last, its start is its premise's, and its premise, when there is one,
\ is the check's declaration step.
: lc-start-of ( s -- start ) dup 0> if lf-log-premise else drop 0 then ;
: lc-after-declaration? ( s -- flag )
  1- dup 0= if drop true exit then lf-log-record logrec-rule @ lf-rule-declaration = ;
: lc-publish? ( s -- flag )
  dup lf-log-record logrec-rule @ lf-rule-publish <> if drop true exit then
  dup lc-after-declaration? over lf-log-count = and
  swap dup 1- lc-start-of swap lf-log-record logrec-start @ = and ;
: lc-prefix? ( -- flag ) lf-log-cut drop ?dup if lf-log-count 1+ = else true then ;

\ Premise kinds per rule (ADR 0013 test plan item 2), for a step whose
\ outcome is ok: an application has at least two inference premises (the
\ function's and the argument's), one defeq and one instantiate; a lambda
\ and a Pi two inference premises (the domain's and the body's); a
\ variable only shifts; a Sort only universe-parameter steps (a symbolic
\ Sort's parameters); a proposition or type step one
\ inference premise; a declaration one fresh-name, one formation (a
\ proposition or type step) and one defeq. A failed step is not checked:
\ its premises include the steps of its failure's analysis.
: lc-count ( s xt -- n )
  >r dup lf-log-record logrec-start @ swap 1- 0 swap
  begin dup 3 pick > while
    dup lf-log-record logrec-rule @ r@ execute if swap 1+ swap then lf-log-premise
  repeat drop nip r> drop ;
: lc-infer? ( rule -- flag ) lf-rule-sort lf-rule-form between? ;
: lc-defeq? ( rule -- flag ) lf-rule-defeq = ;
: lc-instantiate? ( rule -- flag ) lf-rule-instantiate = ;
: lc-other? ( rule -- flag ) lf-rule-shift <> ;
: lc-unparameter? ( rule -- flag ) lf-rule-universe-parameter <> ;
: lc-fresh? ( rule -- flag ) lf-rule-fresh-name = ;
: lc-formation? ( rule -- flag ) dup lf-rule-proposition = swap lf-rule-type = or ;
: lc-application? ( s -- flag )
  dup ['] lc-infer? lc-count 2 >= over ['] lc-defeq? lc-count 1 = and
  swap ['] lc-instantiate? lc-count 1 = and ;
: lc-declaration? ( s -- flag )
  dup ['] lc-fresh? lc-count 1 = over ['] lc-formation? lc-count 1 = and
  swap ['] lc-defeq? lc-count 1 = and ;
: lc-inferences ( s -- n ) ['] lc-infer? lc-count ;
: lc-kinds? ( s rule -- flag )
  case lf-rule-application of lc-application? endof
    lf-rule-lambda of lc-inferences 2 = endof lf-rule-pi of lc-inferences 2 = endof
    lf-rule-variable of ['] lc-other? lc-count 0= endof
    lf-rule-sort of ['] lc-unparameter? lc-count 0= endof
    lf-rule-proposition of lc-inferences 1 = endof lf-rule-type of lc-inferences 1 = endof
    lf-rule-declaration of lc-declaration? endof >r drop true r> endcase ;
: lc-premises? ( s -- flag )
  dup lf-log-record dup logrec-outcome @ ok? 0= if 2drop true exit then
  logrec-rule @ lc-kinds? ;

: lc-step ( s -- )
  dup lf-log-record logrec-rule @ lc-known? 0= if 1 lc-fail then
  dup lc-start? 0= if 2 lc-fail then dup lc-nested? 0= if 3 lc-fail then
  dup lc-refs? 0= if 4 lc-fail then dup lc-publish? 0= if 5 lc-fail then
  lc-premises? 0= if 9 lc-fail then ;
\ Whether the log passes: true, or false with lc-why the first part that
\ failed (1 rule, 2 start, 3 nesting, 4 reference, 5 publish, 6 copy,
\ 7 truncation, 8 no log, 9 premise kinds).
: lc-valid? ( -- flag )
  0 lc-failed ! lf-log-level 0= if 8 lc-fail then
  lf-log-count 0 ?do i 1+ lc-step loop
  lc-copies? 0= if 6 lc-fail then lc-prefix? 0= if 7 lc-fail then lc-why 0= ;
