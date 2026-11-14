\ The structural check of the current context's derivation log
\ (src/core/derivation-log.fs; ADR 0013, test plan item 2): the outline
\ printer prints nothing from a log that fails it (proof-outline.fs), and
\ the log's tests check every log they make with it
\ (tests/support/log-check.fs). lf-log-flaw gives 0 for a log that
\ passes, else the first part that failed, steps in order, each step's
\ parts in order (a later part runs only when the earlier ones passed):
\   1 a step's rule is not in the catalogue;
\   2 a step's start is not below it (or below 0);
\   3 sub-derivations are not nested: a record between a step's start and
\     the step starts before it;
\   4 a reference is undefined: not an input object below the input
\     marks, a copy already made, none, or unkept (only at level steps);
\   5 a publish step that is not the last, whose start is not its
\     premise's, or whose premise (when there is one) is not the check's
\     declaration step or inductive-block step;
\   9 an ok step's premises are not of the kinds its rule needs: an
\     application at least two inference premises (the function's and the
\     argument's), one defeq and one instantiate; a lambda and a Pi two
\     inference premises (the domain's and the body's); a variable only
\     shifts; a Sort only universe-parameter steps (a symbolic Sort's
\     parameters); a proposition or type step one inference premise; a
\     declaration one fresh-name, one formation (a proposition or type
\     step) and one defeq. A failed step is not checked this way: its
\     premises include the steps of its failure's analysis. Premises are
\     followed only while they are strictly earlier;
\ then, for the whole log,
\   6 a term copy has a child that is not an input object or an earlier
\     copy, or a copied constant reference an undefined argument;
\   7 a truncated log does not end just before the step it could not write;
\   8 there is no log.
\ Untrusted presentation code: it reads the log only through its value
\ words and the input marks through lf-input-mark-count, and decides
\ nothing but whether a log may be printed from.
\ State: none.

require ../lib/bounds.fs
require ../core/derivation-log.fs
require ../core/input.fs

\ Rules: a known code (the catalogue's last entry has code 0).
: lf-lc-known? ( s -- flag ) lf-log-rule@ lf-log-entry lf-log-entry-code 0<> ;
\ Start: 0 <= start < s.
: lf-lc-start? ( s -- flag ) dup lf-log-premise swap index? ;
\ Nesting: every record t in (start, s) has its own start >= start
\ (start < s, part 2).
: lf-lc-nested? ( s -- flag )
  dup lf-log-premise swap over 1+ ?do
    i lf-log-premise over < if drop false unloop exit then loop drop true ;

\ References of a kind.
: lf-lc-mark ( k -- n ) lf-input-intact? if lf-input-mark-count else drop max-n then ;
: lf-lc-copy-ok? ( ref copies -- flag ) swap lf-log-copy-index swap < ;
: lf-lc-sentinel? ( ref -- flag )
  dup lf-log-none = swap lf-log-unkept = lf-log-level lf-log-steps = and or ;
: lf-lc-term-ok? ( ref -- flag )
  dup lf-lc-sentinel? if drop true exit then
  dup 0< 0= if 0 lf-lc-mark < exit then lf-log-term-copies lf-lc-copy-ok? ;
: lf-lc-level-ok? ( ref -- flag )
  dup lf-lc-sentinel? if drop true exit then
  dup 0< 0= if 1 lf-lc-mark < exit then lf-log-level-copies lf-lc-copy-ok? ;
: lf-lc-ref-ok? ( ref kind -- flag )
  case lf-ref-term of lf-lc-term-ok? endof lf-ref-level of lf-lc-level-ok? endof
    lf-ref-none of lf-log-none = endof nip true swap endcase ;
: lf-lc-refs? ( s -- flag )
  dup lf-log-rule@ >r dup lf-log-a@ r@ lf-kind-a lf-lc-ref-ok?
  over lf-log-b@ r@ lf-kind-b lf-lc-ref-ok? and
  swap lf-log-out@ r> lf-kind-out lf-lc-ref-ok? and ;

\ Copies: each child an input object or an earlier copy.
: lf-lc-child? ( ref k -- flag ) over 0< 0= if drop 0 lf-lc-mark < exit then
  swap lf-log-copy-index > ;
\ A constant: a reference below the input mark, or a copied reference
\ whose arguments are all defined level references.
: lf-lc-args? ( k -- flag )
  lf-log-cref@ 2swap 2drop swap true swap 0 ?do
    over i + lf-log-arg-ref lf-lc-level-ok? and loop nip ;
: lf-lc-cref? ( cref -- flag )
  dup 0< 0= if 3 lf-lc-mark < exit then
  lf-log-copy-index dup lf-log-cref-copies < if lf-lc-args? else drop false then ;
: lf-lc-leaf? ( first tag -- flag )
  dup lf-tag-symbolic-sort = if drop lf-lc-level-ok? exit then
  lf-tag-constant = if lf-lc-cref? else drop true then ;
\ Copy k's fields, each read from the log's pool.
: lf-lc-tag ( k -- tag ) lf-log-term-node@ 2drop ;
: lf-lc-first ( k -- first ) lf-log-term-node@ drop nip ;
: lf-lc-second ( k -- second ) lf-log-term-node@ nip nip ;
: lf-lc-pair? ( k -- flag )
  dup lf-lc-first over lf-lc-child? swap dup lf-lc-second swap lf-lc-child? and ;
: lf-lc-leaf-copy? ( k -- flag ) dup lf-lc-first swap lf-lc-tag lf-lc-leaf? ;
: lf-lc-term-copy? ( k -- flag )
  dup lf-lc-tag lf-term-binary-tag? if lf-lc-pair? else lf-lc-leaf-copy? then ;
: lf-lc-copies? ( -- flag )
  true lf-log-term-copies 0 ?do i lf-lc-term-copy? and loop ;

\ The publish step, and the end of a truncated log.
: lf-lc-start-of ( s -- start ) dup 0> if lf-log-premise else drop 0 then ;
: lf-lc-check-step? ( s -- flag )
  1- dup 0= if drop true exit then
  lf-log-rule@ dup lf-rule-declaration = swap lf-rule-inductive-block = or ;
: lf-lc-publish? ( s -- flag )
  dup lf-log-rule@ lf-rule-publish <> if drop true exit then
  dup lf-lc-check-step? over lf-log-count = and
  swap dup 1- lf-lc-start-of swap lf-log-premise = and ;
: lf-lc-prefix? ( -- flag ) lf-log-cut drop ?dup if lf-log-count 1+ = else true then ;

\ Premise kinds (part 9): how many of step s's premises have a rule for
\ which xt ( rule -- flag ) holds: s-1, then each start of the last, while
\ above s's start and strictly earlier than the one before; xt and s's
\ start wait on the return stack. A log that passed the other parts
\ always has them earlier; the guard keeps a damaged one from looping.
\ lf-lc-premises counts them all (log-view.fs lists them).
: lf-lc-next ( p -- p' ) dup lf-log-premise tuck > 0= if drop 0 then ;
: lf-lc-above? ( p start -- flag ) over < swap 0> and ;
: lf-lc-count ( s xt -- n )
  over lf-log-premise 2>r 1- 0 swap begin dup 2r@ nip lf-lc-above? while
    dup lf-log-rule@ 2r@ drop execute if swap 1+ swap then lf-lc-next
  repeat drop 2r> 2drop ;
: lf-lc-any? ( rule -- flag ) drop true ;
: lf-lc-premises ( s -- n ) ['] lf-lc-any? lf-lc-count ;
: lf-lc-infer? ( rule -- flag ) lf-rule-sort lf-rule-form between? ;
: lf-lc-defeq? ( rule -- flag ) lf-rule-defeq = ;
: lf-lc-instantiate? ( rule -- flag ) lf-rule-instantiate = ;
: lf-lc-other? ( rule -- flag ) lf-rule-shift <> ;
: lf-lc-unparameter? ( rule -- flag ) lf-rule-universe-parameter <> ;
: lf-lc-fresh? ( rule -- flag ) lf-rule-fresh-name = ;
: lf-lc-formation? ( rule -- flag ) dup lf-rule-proposition = swap lf-rule-type = or ;
: lf-lc-one? ( s xt -- flag ) lf-lc-count 1 = ;
: lf-lc-none? ( s xt -- flag ) lf-lc-count 0= ;
: lf-lc-inferences ( s -- n ) ['] lf-lc-infer? lf-lc-count ;
: lf-lc-application? ( s -- flag )
  dup lf-lc-inferences 2 >= over ['] lf-lc-defeq? lf-lc-one? and
  swap ['] lf-lc-instantiate? lf-lc-one? and ;
: lf-lc-binder? ( s -- flag ) lf-lc-inferences 2 = ;
: lf-lc-formed? ( s -- flag ) lf-lc-inferences 1 = ;
: lf-lc-shifts? ( s -- flag ) ['] lf-lc-other? lf-lc-none? ;
: lf-lc-parameters? ( s -- flag ) ['] lf-lc-unparameter? lf-lc-none? ;
\ A declaration step: its name's freshness, then its type's formation and
\ the comparison of its value's type with it; one without a value (an
\ axiom: a formation, no comparison; a quotient record: neither, plan
\ tasks 5.3.1, 5.2.4) only the freshness and no comparison.
: lf-lc-valued? ( s -- flag ) lf-log-b@ lf-log-none <> ;
: lf-lc-unvalued-kinds? ( s -- flag )
  dup ['] lf-lc-fresh? lf-lc-one? swap ['] lf-lc-defeq? lf-lc-none? and ;
: lf-lc-valued-kinds? ( s -- flag )
  dup ['] lf-lc-fresh? lf-lc-one? over ['] lf-lc-formation? lf-lc-one? and
  swap ['] lf-lc-defeq? lf-lc-one? and ;
: lf-lc-declaration? ( s -- flag )
  dup lf-lc-valued? if lf-lc-valued-kinds? else lf-lc-unvalued-kinds? then ;
\ The kinds by rule: the inference rules', then the others' (a CASE each,
\ read as a table); a rule not listed needs nothing.
: lf-lc-infer-kinds? ( s rule -- flag )
  case lf-rule-application of lf-lc-application? endof
    lf-rule-variable of lf-lc-shifts? endof lf-rule-sort of lf-lc-parameters? endof
    lf-rule-lambda of lf-lc-binder? endof lf-rule-pi of lf-lc-binder? endof
    >r drop true r> endcase ;
: lf-lc-kinds? ( s rule -- flag )
  case lf-rule-proposition of lf-lc-formed? endof lf-rule-type of lf-lc-formed? endof
    lf-rule-declaration of lf-lc-declaration? endof tuck lf-lc-infer-kinds? swap endcase ;
: lf-lc-premises? ( s -- flag )
  dup lf-log-outcome@ ok? 0= if drop true exit then dup lf-log-rule@ lf-lc-kinds? ;

\ The parts of step s, in order, each (xt part); then step s's first
\ failing part, or 0.
create lf-lc-parts
  ' lf-lc-known? , 1 , ' lf-lc-start? , 2 , ' lf-lc-nested? , 3 , ' lf-lc-refs? , 4 ,
  ' lf-lc-publish? , 5 , ' lf-lc-premises? , 9 ,
6 constant lf-lc-parts#
: lf-lc-part ( s k -- part ) 2* cells lf-lc-parts + 2@ rot swap execute if drop 0 then ;
: lf-lc-step ( s -- part )
  lf-lc-parts# 0 do dup i lf-lc-part ?dup if nip unloop exit then loop drop 0 ;
: lf-lc-steps ( -- part )
  lf-log-count 0 ?do i 1+ lf-lc-step ?dup if unloop exit then loop 0 ;

\ Whether the current context's log passes: 0, or the first part that
\ failed (see the header).
: lf-log-flaw ( -- part )
  lf-log-level 0= if 8 exit then lf-lc-steps ?dup if exit then
  lf-lc-copies? 0= if 6 exit then lf-lc-prefix? 0= if 7 exit then 0 ;
