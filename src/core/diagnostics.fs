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
\ context starts clear. Site names are counted strings, one word per
\ module (lf-X-site), and the catalogue of printed names is a table; both
\ are shared and read-only.

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
15 constant lf-diag-deps-full          \ dependencies recorded, capacity
16 constant lf-diag-pool-full          \ dependencies needed, pool capacity
\ Invalid input or state (outcome invalid).
20 constant lf-diag-bad-argument       \ the value, 0
21 constant lf-diag-stale-handle       \ index, identity
22 constant lf-diag-malformed          \ the node being visited (-1 none), 0
23 constant lf-diag-out-of-scope       \ variable index or parameter ID, binders
24 constant lf-diag-corrupted          \ a store's count, capacity
25 constant lf-diag-env-handle         \ handle identity, slot
26 constant lf-diag-too-early          \ the slot not final, the declaration
27 constant lf-diag-no-snapshot        \ snapshot identity, current identity or 0
28 constant lf-diag-recheck            \ the declaration, the re-check that failed
29 constant lf-diag-publisher-fault    \ the declaration, the THROW code
\ Not decided by the cautious rules (outcome unknown).
30 constant lf-diag-undecided          \ the left and right node that differ
31 constant lf-diag-not-pi             \ the function's type, 0
32 constant lf-diag-not-sort           \ the type, 0
33 constant lf-diag-no-signature       \ the constant's name ID, 0
34 constant lf-diag-symbolic-level     \ the level, 0
35 constant lf-diag-dependency-undecided   \ the slot, its outcome
36 constant lf-diag-shared-level      \ K6: the level node Lean may keep or rebuild, 0
\ A construct not implemented yet (outcome unknown in inference; the
\ declaration audit makes it unsupported), a dependency that is
\ unsupported, or a declaration outside the first checker's scope.
40 constant lf-diag-unsupported        \ the node's tag, 0
41 constant lf-diag-dependency-unsupported \ the slot, 0
42 constant lf-diag-unsupported-kind   \ the declaration's kind, its safety (U1)
43 constant lf-diag-unsupported-form   \ the form, the node (U2)
\ Rejected by a rule of ADR 0011 (outcome rejected): 50-54 by the checked
\ environment, 55-61 by comparison and inference, where a rejection
\ replaces the record of the undecided step it decides.
50 constant lf-diag-unknown-constant   \ name ID, the declaration (N1)
51 constant lf-diag-already-declared   \ name ID, the accepted slot (N2)
52 constant lf-diag-level-count        \ levels given, parameters (L1)
53 constant lf-diag-undeclared-param   \ name ID, 0 (L2)
54 constant lf-diag-duplicate-param    \ the declaration, 0 (L3)
55 constant lf-diag-type-expected      \ S1: the declared type's type, reduced, 0
56 constant lf-diag-domain-type        \ S2: a binder domain's type, reduced, 0
57 constant lf-diag-not-proposition    \ S3: the statement's Sort level, 0
58 constant lf-diag-function-expected  \ F1: the function's type, reduced, 0
59 constant lf-diag-argument-apart     \ D1-D5, an argument: the rules used, 0
60 constant lf-diag-value-apart        \ D1-D5, the value: the rules used, 0
61 constant lf-diag-body-type          \ S4: a Pi body's type, reduced, 0
\ An inductive block (ADR 0015; plan task 5.2.1a, kernel/check-block.fs):
\ its shape (invalid), its scope (unsupported), a step that needs
\ unfolding (unknown), and Lean's rejections of inductive.cpp and of
\ Lean's replay (rejected).
62 constant lf-diag-block-shape        \ B0 (invalid): the block's first member, 0
63 constant lf-diag-block-scope        \ unsupported: the first member, a reason
                                       \ (1, 2 and 3 are no longer given)
64 constant lf-diag-needs-unfolding    \ K1 (unknown): the node Lean may unfold, 0
65 constant lf-diag-reserved-prefix    \ T0: the block's first member, 0
66 constant lf-diag-nonuniform         \ C1: the occurrence's node, its binder depth
67 constant lf-diag-param-binders      \ T1: the type's binders, numParams
68 constant lf-diag-block-not-sort     \ T2: the type's result, reduced, 0
69 constant lf-diag-ctor-param         \ C2: the D rules used, 0
70 constant lf-diag-universe-too-big   \ U1: the constructor, the field's binder
71 constant lf-diag-return-type        \ C3: the constructor, 0
72 constant lf-diag-duplicate-ctor     \ C4: the constructor, 0
73 constant lf-diag-invalid-constructor \ B3: the constructor's member, the field
74 constant lf-diag-invalid-recursor   \ B3: the recursor's member, the field
75 constant lf-diag-no-such-recursor   \ B3: the recursor's member, 0
76 constant lf-diag-ctors-full         \ full: the block's constructors, capacity
77 constant lf-diag-generated-recursor \ unknown: the name, the slot that holds it
78 constant lf-diag-empty-block        \ rejected: the block's declaration, 0
79 constant lf-diag-non-positive       \ P1: the constructor, the field's binder
80 constant lf-diag-non-valid          \ P2: the constructor, the field's binder
\ Lean's weak head normal form (ADR 0014; plan task 4.2.2c,
\ kernel/whnf.fs): routes LeanForth does not port yet (unknown).
81 constant lf-diag-iota-pending       \ unknown: the recursor at the head, 0
82 constant lf-diag-name-matched       \ K7 (unknown): the constant at the head, 0
\ Mutual blocks (plan task 5.2.5a).
83 constant lf-diag-mutual-params      \ T3: the D rules used, 0
84 constant lf-diag-param-count        \ T3: the type, the parameter binders found
85 constant lf-diag-universe-mismatch  \ T4: the type, 0
\ Nat.pow and Nat.shiftLeft, until plan task 5.2.3 (review rvN1 B1;
\ retired: no check gives it since).
86 constant lf-diag-nat-count-op       \ unsupported: the declaration, 0
\ Lean's is_def_eq (ADR 0014; plan task 4.2.2d, kernel/defeq.fs): steps
\ that could answer yes where LeanForth does not port them yet, or that a
\ bare comparison, which has no typer, cannot run (87 and 88: ported by
\ plan tasks 4.2.5 and 4.2.4; a check always has a typer) (unknown).
87 constant lf-diag-proof-pending      \ no typer: the left term, the right
88 constant lf-diag-eta-pending        \ no typer: the left term, the right
89 constant lf-diag-structure-pending  \ structure eta or unit-like: left, right
90 constant lf-diag-not-defeq          \ rejected (Lean's no): left, right
\ Projections (plan task 5.2.2; 87 to 90 are plan task 4.2.2d's).
91 constant lf-diag-invalid-proj       \ J2 (rejected): the projection's leaf, 0
\ Literals (plan task 5.2.3, kernel/reduce-nat.fs).
92 constant lf-diag-nat-count          \ L1 (rejected): the operation's head, the count's limbs
93 constant lf-diag-nat-size           \ full: the operation's head, 0
\ Let terms (plan task 4.2.3, kernel/mixed-infer.fs).
94 constant lf-diag-let-value-apart    \ rejected (letTypeMismatch): 0, 0
\ Quotients (plan task 5.2.4, kernel/quot.fs).
95 constant lf-diag-quot-eq            \ Q1 (rejected): the declaration, 0
96 constant lf-diag-quot-type          \ Q1 (rejected): the declaration, 0
\ Nested inductive blocks (plan task 5.2.5b, kernel/inductive-nested.fs).
97 constant lf-diag-nested-local       \ N2 (rejected): the occurrence's node, its binders
98 constant lf-diag-nested-shape       \ N1, N3 (rejected): the node or name, 0

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
\ node being visited (malformed; -1 when the walk ended before its first
\ visit), unknown the pair being compared (undecided: the node and, in a
\ paired walk, its context cell, else 0); ok records nothing. A failure
\ that a check inside the walk recorded first is kept.
: lf-diag-walk-fuel ( walk site -- ) swap walk-fuel @ swap lf-diag-exhausted ;
: lf-diag-walk-room ( walk site -- )
  >r dup walk-pending @ swap walk-capacity @ r> lf-diag-work-stack-full lf-diag-note ;
: lf-diag-walk-node ( walk site -- ) >r walk-node @ 0 r> lf-diag-malformed lf-diag-note ;
: lf-diag-walk-right ( walk -- node|0 )
  dup walk-paired? if walk-context @ else drop 0 then ;
: lf-diag-walk-pair ( walk site -- )
  >r dup walk-node @ swap lf-diag-walk-right r> lf-diag-undecided lf-diag-note ;
: lf-diag-walk ( outcome walk site -- outcome )
  2>r dup case outcome-exhausted of 2r> lf-diag-walk-fuel endof
    outcome-full of 2r> lf-diag-walk-room endof
    outcome-invalid of 2r> lf-diag-walk-node endof
    outcome-unknown of 2r> lf-diag-walk-pair endof 2r> 2drop endcase ;

\ After a pass on a frames record (lib/frame.fs) ended with outcome:
\ exhausted records the fuel left, full the frames' stack, which the heap
\ could not grow: its cells in use and its capacity (the pass's other room
\ failures record themselves first).
: lf-diag-frames-fuel ( frames site -- ) swap frame-fuel @ swap lf-diag-exhausted ;
: lf-diag-frames-room ( frames site -- )
  >r frame-room@ r> lf-diag-frame-limit lf-diag-note ;
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
\ The code and numbers of a refusal the store's state explains.
: lf-diag-refusal ( code store -- n1 n2 code' )
  tuck lf-diag-why tuck lf-diag-numbers rot ;
: lf-diag-store ( store site code -- ) rot lf-diag-refusal >r rot r> lf-diag-note ;

\ The catalogue of printed names, in code order: each entry is a code, the
\ name's length and its characters, aligned. The last entry, lf-diag-none,
\ names every code the catalogue does not list. Shared and read-only.
: lf-diag-entry, ( code c-addr u -- ) rot , dup , here swap dup allot move align ;
: lf-diag-entry-code ( entry -- code ) @ ;
: lf-diag-entry-name ( entry -- c-addr u ) cell+ dup cell+ swap @ ;
: lf-diag-entry-next ( entry -- entry' ) lf-diag-entry-name + aligned ;
create lf-diag-catalogue
  lf-diag-fuel s" fuel exhausted" lf-diag-entry,
  lf-diag-terms-full s" term store full" lf-diag-entry,
  lf-diag-levels-full s" level store full" lf-diag-entry,
  lf-diag-names-full s" name store full" lf-diag-entry,
  lf-diag-name-bytes-full s" name bytes full" lf-diag-entry,
  lf-diag-references-full s" reference store full" lf-diag-entry,
  lf-diag-signatures-full s" signature index full" lf-diag-entry,
  lf-diag-serial-spent s" identity serial spent" lf-diag-entry,
  lf-diag-work-stack-full s" work stack full" lf-diag-entry,
  lf-diag-frame-limit s" frame limit" lf-diag-entry,
  lf-diag-depth-limit s" depth limit" lf-diag-entry,
  lf-diag-binders-full s" binder context full" lf-diag-entry,
  lf-diag-cell-maximum s" value at cell maximum" lf-diag-entry,
  lf-diag-heap-failed s" heap allocation failed" lf-diag-entry,
  lf-diag-deps-full s" dependency list full" lf-diag-entry,
  lf-diag-pool-full s" dependency pool full" lf-diag-entry,
  lf-diag-bad-argument s" invalid input: bad argument" lf-diag-entry,
  lf-diag-stale-handle s" invalid input: stale handle" lf-diag-entry,
  lf-diag-malformed s" invalid input: malformed graph" lf-diag-entry,
  lf-diag-out-of-scope s" invalid input: out of scope" lf-diag-entry,
  lf-diag-corrupted s" invalid input: corrupted store" lf-diag-entry,
  lf-diag-env-handle s" invalid: environment handle" lf-diag-entry,
  lf-diag-too-early s" invalid: check started too early" lf-diag-entry,
  lf-diag-no-snapshot s" invalid: no snapshot" lf-diag-entry,
  lf-diag-recheck s" invalid: publisher re-check failed" lf-diag-entry,
  lf-diag-publisher-fault s" invalid: internal fault" lf-diag-entry,
  lf-diag-undecided s" undecided: terms or levels differ" lf-diag-entry,
  lf-diag-not-pi s" undecided: function type not a Pi" lf-diag-entry,
  lf-diag-not-sort s" undecided: type not a Sort" lf-diag-entry,
  lf-diag-no-signature s" undecided: no candidate signature" lf-diag-entry,
  lf-diag-symbolic-level s" undecided: symbolic level" lf-diag-entry,
  lf-diag-dependency-undecided s" undecided: dependency undecided" lf-diag-entry,
  lf-diag-shared-level s" undecided: Lean's level depends on sharing (K6)" lf-diag-entry,
  lf-diag-unsupported s" unsupported construct" lf-diag-entry,
  lf-diag-dependency-unsupported s" unsupported: dependency unsupported" lf-diag-entry,
  lf-diag-unsupported-kind s" unsupported: declaration kind (U1)" lf-diag-entry,
  lf-diag-unsupported-form s" unsupported: term form (U2)" lf-diag-entry,
  lf-diag-unknown-constant s" rejected: unknown constant" lf-diag-entry,
  lf-diag-already-declared s" rejected: name already declared" lf-diag-entry,
  lf-diag-level-count s" rejected: wrong number of universe levels" lf-diag-entry,
  lf-diag-undeclared-param s" rejected: undeclared universe parameter" lf-diag-entry,
  lf-diag-duplicate-param s" rejected: duplicate universe parameter" lf-diag-entry,
  lf-diag-type-expected s" rejected: type expected (S1)" lf-diag-entry,
  lf-diag-domain-type s" rejected: binder domain not a type (S2)" lf-diag-entry,
  lf-diag-not-proposition s" rejected: theorem type not a proposition (S3)" lf-diag-entry,
  lf-diag-function-expected s" rejected: function expected (F1)" lf-diag-entry,
  lf-diag-argument-apart s" rejected: argument type mismatch (D1-D5)" lf-diag-entry,
  lf-diag-value-apart s" rejected: declared type mismatch (D1-D5)" lf-diag-entry,
  lf-diag-body-type s" rejected: Pi body not a type (S4)" lf-diag-entry,
  lf-diag-block-shape s" invalid input: inductive block shape (B0)" lf-diag-entry,
  lf-diag-block-scope
    s" unsupported: inductive block outside tasks 5.2.1a-b, 5.2.5a" lf-diag-entry,
  lf-diag-needs-unfolding
    s" undecided: Lean may unfold a definition here (K1)" lf-diag-entry,
  lf-diag-reserved-prefix s" rejected: reserved prefix _nested (T0)" lf-diag-entry,
  lf-diag-nonuniform s" rejected: non-uniform occurrence of the type (C1)" lf-diag-entry,
  lf-diag-param-binders s" rejected: too few parameter binders (T1)" lf-diag-entry,
  lf-diag-block-not-sort
    s" rejected: inductive type not ending in a Sort (T2)" lf-diag-entry,
  lf-diag-ctor-param s" rejected: constructor parameter mismatch (C2)" lf-diag-entry,
  lf-diag-universe-too-big
    s" rejected: constructor field universe too big (U1)" lf-diag-entry,
  lf-diag-return-type s" rejected: invalid constructor return type (C3)" lf-diag-entry,
  lf-diag-duplicate-ctor s" rejected: duplicate constructor name (C4)" lf-diag-entry,
  lf-diag-invalid-constructor
    s" rejected: constructor differs from Lean's (B3)" lf-diag-entry,
  lf-diag-invalid-recursor s" rejected: recursor differs from Lean's (B3)" lf-diag-entry,
  lf-diag-no-such-recursor
    s" rejected: recursor Lean does not generate (B3)" lf-diag-entry,
  lf-diag-ctors-full s" inductive block: too many constructors" lf-diag-entry,
  lf-diag-generated-recursor
    s" undecided: a constant Lean's kernel holds, no slot accepted" lf-diag-entry,
  lf-diag-empty-block s" rejected: an inductive block without types" lf-diag-entry,
  lf-diag-non-positive
    s" rejected: non-positive occurrence of the type (P1)" lf-diag-entry,
  lf-diag-non-valid s" rejected: non-valid occurrence of the type (P2)" lf-diag-entry,
  lf-diag-iota-pending
    s" undecided: a recursor reduction LeanForth does not port yet" lf-diag-entry,
  lf-diag-name-matched
    s" undecided: a constant Lean's kernel matches by name (K7)" lf-diag-entry,
  lf-diag-mutual-params
    s" rejected: mutual types' parameters differ (T3)" lf-diag-entry,
  lf-diag-param-count
    s" rejected: a mutual type has too few parameters (T3)" lf-diag-entry,
  lf-diag-universe-mismatch
    s" rejected: mutual types in different universes (T4)" lf-diag-entry,
  lf-diag-nat-count-op
    s" unsupported: a declaration named Nat.pow or Nat.shiftLeft" lf-diag-entry,
  lf-diag-proof-pending
    s" undecided: proof irrelevance may decide (no typer)" lf-diag-entry,
  lf-diag-eta-pending s" undecided: eta may decide (no typer)" lf-diag-entry,
  lf-diag-structure-pending
    s" undecided: structure eta or a unit-like type may decide" lf-diag-entry,
  lf-diag-not-defeq s" rejected: not definitionally equal" lf-diag-entry,
  lf-diag-invalid-proj s" rejected: invalid projection (J2)" lf-diag-entry,
  lf-diag-nat-count
    s" rejected: Nat.pow or Nat.shiftLeft by 2^32 or more (L1)" lf-diag-entry,
  lf-diag-nat-size
    s" full: a Nat over the size limit, or no memory to compute it" lf-diag-entry,
  lf-diag-let-value-apart s" rejected: let value type mismatch" lf-diag-entry,
  lf-diag-quot-eq
    s" rejected: Eq is not the type quotients need (Q1)" lf-diag-entry,
  lf-diag-quot-type
    s" rejected: not one of Lean's four quotient constants (Q1)" lf-diag-entry,
  lf-diag-nested-local
    s" rejected: nested occurrence's parameter has a local variable (N2)" lf-diag-entry,
  lf-diag-nested-shape
    s" rejected: ill-formed nested inductive declaration (N1, N3)" lf-diag-entry,
  lf-diag-none s" unknown code" lf-diag-entry,
: lf-diag-end? ( code entry -- flag ) lf-diag-entry-code tuck = swap lf-diag-none = or ;
\ The entry of code, or the last entry.
: lf-diag-entry ( code -- entry )
  lf-diag-catalogue begin 2dup lf-diag-end? 0= while lf-diag-entry-next repeat nip ;

\ Printing: the code's name, the site and the numbers, or "no diagnostic".
: lf-diag-name ( code -- c-addr u ) lf-diag-entry lf-diag-entry-name ;
: lf-diag-site. ( site -- ) ?dup if count type else ." no site" then ;
: lf-diag. ( -- )
  lf-diag-clear? if ." no diagnostic" exit then
  lf-diag@ lf-diag-name type ."  at " lf-diag-site. ." : " swap . . ;
