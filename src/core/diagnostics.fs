\ Diagnostics: why a check failed, in a first, minimal form (plan section
\ 6.7). A failing site records a reason code, its own name (module and
\ word) as a counted string, and two numbers, such as a store's count and
\ capacity; docs/programming/DIAGNOSTICS.md is the catalogue. The first
\ failure recorded wins: later ones are ignored until the caller clears
\ the record with lf-diag-clear. Recording never changes an outcome, a
\ result or fuel, and no check reads the record: it only explains a
\ failure the outcome already reports. A record may also hold a failure
\ that a caller recovered from, so read it only after a failed outcome,
\ having cleared it before the call. Untrusted.
\ State: one record, lf-diagnostic, a member of the checker context
\ (lib/context.fs), so each context explains its own failures; a new
\ context starts clear. Site names are counted strings compiled into the
\ recording words, shared and read-only.

require ../lib/lib.fs

\ Reason codes; tests pin the numbers, never the wording. Unless a code
\ says otherwise, its numbers are what was used and the limit.
0 constant lf-diag-none
\ Out of fuel (outcome exhausted): the fuel left (0; negative if corrupted), 0.
1 constant lf-diag-fuel
\ Out of room (outcome full).
2 constant lf-diag-terms-full
3 constant lf-diag-levels-full
4 constant lf-diag-names-full
5 constant lf-diag-name-bytes-full     \ bytes needed, capacity
6 constant lf-diag-references-full
7 constant lf-diag-signatures-full
8 constant lf-diag-serial-spent        \ the store's serial, identities needed
9 constant lf-diag-work-stack-full     \ cells pending, capacity
10 constant lf-diag-frame-limit
11 constant lf-diag-depth-limit
12 constant lf-diag-binders-full
13 constant lf-diag-cell-maximum       \ the value, the amount to add
14 constant lf-diag-heap-failed        \ bytes, ior (no site in core or kernel)
\ Invalid input (outcome invalid).
20 constant lf-diag-bad-argument       \ the value, 0
21 constant lf-diag-stale-handle       \ index, identity
22 constant lf-diag-malformed          \ the node being visited, 0
23 constant lf-diag-out-of-scope       \ variable index or parameter ID, binders
24 constant lf-diag-corrupted          \ a store's count, capacity
\ Not decided by the cautious rules (outcome unknown).
30 constant lf-diag-undecided          \ the left and right node that differ
31 constant lf-diag-not-pi             \ the function's type, 0
32 constant lf-diag-not-sort           \ the type, 0
33 constant lf-diag-no-signature       \ the constant's name ID, 0
34 constant lf-diag-symbolic-level     \ the level, 0
\ A construct not implemented yet (outcome unknown until ADR 0008 step 3).
40 constant lf-diag-unsupported        \ the node's tag, 0
\ Rejected by a typing rule of ADR 0011 (outcome rejected); 50-54 are the
\ checked environment's rules (kernel/environment.fs). A rejection
\ replaces the record of the undecided step it decides.
55 constant lf-diag-type-expected      \ S1: the declared type's type, reduced, 0
56 constant lf-diag-domain-type        \ S2: a binder domain's type, reduced, 0
57 constant lf-diag-not-proposition    \ S3: the statement's Sort level, 0
58 constant lf-diag-function-expected  \ F1: the function's type, reduced, 0
59 constant lf-diag-argument-apart     \ D1-D5, an argument: the rules used, 0
60 constant lf-diag-value-apart        \ D1-D5, the value: the rules used, 0

begin-structure /lf-diag
  field: lf-diag-code       \ reason code; lf-diag-none while clear
  field: lf-diag-site       \ counted string: module and word, or 0
  field: lf-diag-first      \ the numbers, as the code's entry says
  field: lf-diag-second
end-structure
/lf-diag context-record: lf-diagnostic

\ Clearing, reading and recording. lf-diag-note records only into a clear
\ record, so the first failure wins.
: lf-diag-clear ( -- ) lf-diagnostic /lf-diag erase ;
: lf-diag-code@ ( -- code ) lf-diagnostic lf-diag-code @ ;
: lf-diag-clear? ( -- flag ) lf-diag-code@ lf-diag-none = ;
: lf-diag@ ( -- n1 n2 site code )
  lf-diagnostic dup lf-diag-first @ swap dup lf-diag-second @ swap
  dup lf-diag-site @ swap lf-diag-code @ ;
: lf-diag! ( n1 n2 site code -- )
  lf-diagnostic tuck lf-diag-code ! tuck lf-diag-site ! tuck lf-diag-second !
  lf-diag-first ! ;
: lf-diag-note ( n1 n2 site code -- ) lf-diag-clear? if lf-diag! else 2drop 2drop then ;
\ Out of fuel at site, with the fuel left.
: lf-diag-exhausted ( fuel site -- ) 0 swap lf-diag-fuel lf-diag-note ;

\ After a walk (lib/walk.fs) ended with outcome: exhausted records the
\ fuel left, full the work stack's cells pending and capacity, invalid the
\ node being visited (malformed), unknown the pair being compared
\ (undecided, for paired walks); ok records nothing. A failure that a
\ check inside the walk recorded first is kept.
: lf-diag-walk-fuel ( walk site -- ) swap walk-fuel @ swap lf-diag-exhausted ;
: lf-diag-walk-room ( walk site -- )
  >r dup walk-pending @ swap walk-capacity @ r> lf-diag-work-stack-full lf-diag-note ;
: lf-diag-walk-node ( walk site -- ) >r walk-node @ 0 r> lf-diag-malformed lf-diag-note ;
: lf-diag-walk-pair ( walk site -- )
  >r dup walk-node @ swap walk-context @ r> lf-diag-undecided lf-diag-note ;
: lf-diag-walk ( outcome walk site -- outcome )
  2>r dup case outcome-exhausted of 2r> lf-diag-walk-fuel endof
    outcome-full of 2r> lf-diag-walk-room endof
    outcome-invalid of 2r> lf-diag-walk-node endof
    outcome-unknown of 2r> lf-diag-walk-pair endof 2r> 2drop endcase ;

\ After a recursive pass (lib/frame.fs) ended with outcome: exhausted
\ records the fuel left, full the frame limit (every frame in use; the
\ pass's other room failures record themselves first).
: lf-diag-frames-fuel ( frames site -- ) swap frame-fuel @ swap lf-diag-exhausted ;
: lf-diag-frames-room ( frames site -- )
  >r frame-limit @ dup r> lf-diag-frame-limit lf-diag-note ;
: lf-diag-frames ( outcome frames site -- outcome )
  2>r dup case outcome-exhausted of 2r> lf-diag-frames-fuel endof
    outcome-full of 2r> lf-diag-frames-room endof 2r> 2drop endcase ;

\ Why a store (lib/store.fs) refused a new record: it fails its own checks
\ (corrupted: count and capacity), it has no free record (code: count and
\ capacity), or its identity serial is spent (the serial, 1).
: lf-diag-why ( code store -- code' )
  dup store-count-valid? 0= if 2drop lf-diag-corrupted exit then
  store-room? if drop lf-diag-serial-spent then ;
: lf-diag-filled ( store -- count capacity ) dup store-count @ swap store-capacity @ ;
: lf-diag-numbers ( store code -- n1 n2 )
  lf-diag-serial-spent = if store-serial @ 1 else lf-diag-filled then ;
: lf-diag-store ( store site code -- )
  >r over r> swap lf-diag-why >r swap r@ lf-diag-numbers rot r> lf-diag-note ;

\ Printing: the code's name, the site and the numbers, or "no diagnostic".
: lf-diag-room-name ( code -- c-addr u )
  case lf-diag-fuel of s" fuel exhausted" endof
    lf-diag-terms-full of s" term store full" endof
    lf-diag-levels-full of s" level store full" endof
    lf-diag-names-full of s" name store full" endof
    lf-diag-name-bytes-full of s" name bytes full" endof
    lf-diag-references-full of s" reference store full" endof
    lf-diag-signatures-full of s" signature index full" endof
    lf-diag-serial-spent of s" identity serial spent" endof
    >r s" unknown code" r> endcase ;
: lf-diag-limit-name ( code -- c-addr u )
  case lf-diag-work-stack-full of s" work stack full" endof
    lf-diag-frame-limit of s" frame limit" endof
    lf-diag-depth-limit of s" depth limit" endof
    lf-diag-binders-full of s" binder context full" endof
    lf-diag-cell-maximum of s" value at cell maximum" endof
    lf-diag-heap-failed of s" heap allocation failed" endof
    lf-diag-room-name 0 endcase ;
: lf-diag-input-name ( code -- c-addr u )
  case lf-diag-bad-argument of s" invalid input: bad argument" endof
    lf-diag-stale-handle of s" invalid input: stale handle" endof
    lf-diag-malformed of s" invalid input: malformed graph" endof
    lf-diag-out-of-scope of s" invalid input: out of scope" endof
    lf-diag-corrupted of s" invalid input: corrupted store" endof
    lf-diag-limit-name 0 endcase ;
: lf-diag-rule-name ( code -- c-addr u )
  case lf-diag-type-expected of s" rejected: type expected (S1)" endof
    lf-diag-domain-type of s" rejected: binder domain not a type (S2)" endof
    lf-diag-not-proposition of s" rejected: theorem type not a proposition (S3)" endof
    lf-diag-function-expected of s" rejected: function expected (F1)" endof
    lf-diag-argument-apart of s" rejected: argument type mismatch (D1-D5)" endof
    lf-diag-value-apart of s" rejected: declared type mismatch (D1-D5)" endof
    lf-diag-input-name 0 endcase ;
: lf-diag-name ( code -- c-addr u )
  case lf-diag-undecided of s" undecided: terms or levels differ" endof
    lf-diag-not-pi of s" undecided: function type not a Pi" endof
    lf-diag-not-sort of s" undecided: type not a Sort" endof
    lf-diag-no-signature of s" undecided: no candidate signature" endof
    lf-diag-symbolic-level of s" undecided: symbolic level" endof
    lf-diag-unsupported of s" unsupported construct" endof
    lf-diag-rule-name 0 endcase ;
: lf-diag-site. ( site -- ) ?dup if count type else ." no site" then ;
: lf-diag. ( -- )
  lf-diag-clear? if ." no diagnostic" exit then
  lf-diag@ lf-diag-name type ."  at " lf-diag-site. ." : " swap . . ;
