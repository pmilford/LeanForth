\ Unit tests of tactic batch 3c (plan row TB2) over decide's slice of Init
\ in an authoring run, by the classes of docs/development/
\ TEST_COVERAGE_REVIEW.md: author/scopes.fs's brackets and runner.fs's
\ reading on (lists over several lines), reader.fs's << >> and ⟨ ⟩,
\ syntax.fs's syn-slots, syn-node-new and syn-last!, elab-term.fs's
\ anonymous constructor (each of its errors, the nested rest, the
\ constructor's explicit fields, a private constructor not ported) and
\ lf-elab-final, elab-pending.fs's message rest and below, tactic-core.fs's
\ lf-tac-refine through by-refine and by-exists[ (tests/support/
\ tactic-text.fs):
\ 1. outcomes: each word accepted, each refusal with its code (21, 42, 83,
\    132, 133, 139, 458, 460, 462-467);
\ 2. malformed input: a list never closed (a tactic word, end, :=, the
\    text's end, a mismatched closer), a ( comment never closed, a value
\    taken from before <<, a binder inside << >>;
\ 3. stack effects and records: each T{ }T checks the depth; every field of
\    the brackets, the nodes and the error's parts;
\ 5. resources (tests/support/meta-sweeps.fs): the bracket slab and the
\    syntax store refused, and the words through their text with every heap
\    allocation refused in turn: the answer or full, never another answer;
\ 6. state: the brackets cleared when the scope closes, the error's parts
\    cleared by its reset, the first error's kept.
\ The terms are checked node for node with pinned Lean by check.py.
\ Nothing here accepts a theorem: only the kernel's check does.
require ../../../support/tester.fs
include ../../../support/heap-watch.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/decide-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/decide-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: made ( x outcome -- x ) ok? 0= abort" batch-f test: not made" ;
: nm ( c-addr u -- id ) lfa-intern ;
: token ( -- c-addr u ) lfa-error lfa-err-token lfa-error lfa-err-length @ ;
: at@ ( -- line col ) lfa-error lfa-err-at @ lfa-pos> ;
: step@ ( i -- addr ) lf-tactic-step ;
create stmt 512 allot  variable stmt#
: stmt+ ( c-addr u -- ) tuck stmt stmt# @ + swap move stmt# +! ;
: st ( c-addr u -- c-addr' u' )
  0 stmt# ! s" Nat explicit: a Nat explicit: b " stmt+ stmt+ stmt stmt# @ ;
: hk ( -- c-addr u ) s" a b = explicit: h b a = explicit: k a b = b a = ∧" st ;
: hk1 ( -- c-addr u ) s" a b = explicit: h b a = explicit: k a b =" st ;
: ran ( c-addr u -- code ) lf-author-begin lf-author-text drop lf-author-code ;

\ ---- 3. The node of << >>: its kind, items in order, place (<<'s).
T{ hk s" << ' h ' k >> by-exact" tactic-ran -> 0 }T
: anon@ ( -- node ) 1 0 lf-tac-arg ;
T{ anon@ syn-kind@ anon@ syn-b@ anon@ 0 syn-arg syn-kind@ anon@ 1 syn-arg syn-kind@
   -> syn-k-anon 2 syn-k-var syn-k-var }T
\ (<< at its own place, its first item three columns on: << ' h)
T{ anon@ 0 syn-arg syn-at@ anon@ syn-at@ - anon@ 1 syn-arg syn-at@ anon@ syn-at@ - -> 5 9 }T
T{ hk s" ⟨ ' h ' k ⟩ by-exact" tactic-ran anon@ syn-b@ -> 0 2 }T
\ (the two spellings close each other: one pair of words)
T{ hk s" ⟨ ' h ' k >> by-exact" tactic-ran hk s" << ' h ' k ⟩ by-exact" tactic-ran -> 0 0 }T
\ Nested: the inner node an item; empty: no item.
T{ s" a b = explicit: h b a = explicit: k a b = b a = a b = ∧ ∧" st
   s" << ' h << ' k ' h >> >> by-exact" tactic-ran anon@ syn-b@ anon@ 1 syn-arg syn-kind@
   -> 0 2 syn-k-anon }T
T{ s" True" st s" << >> by-exact" tactic-ran anon@ syn-b@ -> 0 0 }T
lf-tac-forget

\ ---- 2. Malformed brackets: >> with no << (83); a tactic word, end or
\ := before >> (458 at <<, its own line); a value from before << (the
\ bracket is a frame: missing values, 23); a binder opened inside (21).
T{ hk s" >> by-exact" tactic-ran -> 83 }T
T{ hk s" << ' h by-exact" tactic-ran token s" <<" compare -> 458 0 }T
T{ hk s" << ' h" tactic-ran token s" <<" compare -> 458 0 }T
T{ hk s\" ⟨ ' h\n ' k by-rfl" tactic-ran token s" ⟨" compare at@ drop -> 458 0 1 }T
T{ s" theorem t Nat explicit: a << a := by by-rfl end t" ran token s" <<" compare -> 458 0 }T
T{ hk s" ' h ' k << + >> by-exact" tactic-ran -> lfa-e-missing }T
T{ hk s" << Nat explicit: x >> by-exact" tactic-ran -> 21 }T
\ (in a statement, where no tactic word checks the binders again)
T{ s" theorem t << Nat explicit: x >> := by by-rfl end t" ran token s" >>" compare
   -> 21 0 }T
\ A bracket of rules closed by >>, a << closed by ]: the other's closing
\ word is missing (458); <- right inside << (83).
T{ hk s" by-rw[ << ' h >> by-exact" tactic-ran token s" by-rw[" compare -> 458 0 }T
T{ hk s" by-rw[ << ' h ]" tactic-ran token s" <<" compare -> 458 0 }T
T{ hk s" by-rw[ << ' h <- >> ]" tactic-ran -> 83 }T
lf-tac-forget

\ ---- 3. The brackets' records (scopes.fs): mark, binders, place, closer
\ and word; the frame; the items counted; dropped.
lf-author-begin
: closer1 ( -- c ) c" ]" ;
: closer2 ( -- c ) c" >>" ;
: line1 ( -- c-addr u ) s" aaa" ;
line1 lfa-line!
: open1 ( -- ) line1 lfa-token! closer1 lfa-bracket-open ;
T{ lfa-bracketed? lfa-list-closer -> false 0 }T
T{ open1 lfa-bracketed? lfa-list-closer -> true closer1 }T
T{ depth lfb lfb-mark @ = lfa-frame lfb lfb-mark @ = -> true true }T
T{ lfb lfb-binders @ lfb lfb-at @ lfb lfb-word cell-count s" aaa" compare
   -> lfa-depth lfa-here 0 }T
T{ 9 closer1 0 lfa-bracket-close -> 9 1 lfa-here }T
T{ lfa-bracketed? -> false }T
\ A mismatched closer: 458 at the bracket's word; none open: the code.
: close2 ( -- n pos ) closer2 83 lfa-bracket-close ;
T{ open1 ' close2 catch drop lf-author-code token s" aaa" compare -> 458 0 }T
lfa-error-reset lfa-scope-close
T{ ' close2 catch drop lf-author-code lfa-bracketed? -> 83 false }T
\ The scope closed: every bracket gone.
T{ open1 open1 lfa-brackets slab-count lfa-scope-close lfa-brackets slab-count -> 2 0 }T
lfa-error-reset

\ ---- 5. A bracket refused by the heap: full, 65, nothing open.
: refuse-first ( -- ) lfa-brackets sweep-slab-anew 1 heap-refusals ! ;
T{ refuse-first ' open1 catch drop 0 heap-refusals ! lf-author-code lfa-bracketed? -> 65 false }T
lfa-error-reset lfa-scope-close

\ ---- 1. Lists over several lines (runner.fs's reading on): each item at
\ its own line; \ and ( comments skipped; a ( never closed is 42; the
\ text's end before ] is 458 at the list's word.
T{ hk1 s\" by-revert[ h\n k ] by-intro[ x \\ first\n ( note ) y ] x by-exact" tactic-ran -> 0 }T
T{ 1 0 lf-tac-arg-at lfa-pos> drop 1 1 lf-tac-arg-at lfa-pos> drop
   2 0 lf-tac-arg-at lfa-pos> drop 2 1 lf-tac-arg-at lfa-pos> drop -> 1 2 2 3 }T
T{ 3 step@ tac-at @ lfa-pos> drop -> 3 }T
T{ hk s\" by-revert[ h\n ( never closed\n k ]" tactic-ran -> 42 }T
T{ s\" theorem t Nat explicit: a a a = := by by-intro[ x\n y" ran token s" by-intro[" compare
   -> 458 0 }T
\ The rest of a line read into runs on (no nesting); a list of terms over
\ lines needs nothing of its own.
T{ hk1 s\" by-revert[\n h k ] by-intro[ x\n y ] ' x by-exact" tactic-ran -> 0 }T
T{ hk s\" by-exists[\n ' h\n ]" tactic-ran -> 0 }T
\ by-exists[ takes one term at least (460, at ]).
T{ hk s" by-exists[ ]" tactic-ran token s" ]" compare -> 460 0 }T
lf-tac-forget

\ ---- 3. syntax.fs: syn-node-new's slots, syn-last!.
: nd ( n -- node ) syn-k-anon 0 syn-node-new 0= abort" batch-f test: no node" ;
T{ 3 nd dup syn-b@ swap syn-kind@ -> 3 syn-k-anon }T
T{ 2 nd 77 syn-last! dup 1 syn-arg swap 0 syn-arg -> 77 0 }T
T{ 0 nd syn-b@ -> 0 }T
\ A store that refuses a node, or its slots: false.
: full-at ( store -- limit )
  dup store-limit @ swap dup store-count @ swap store-limit! drop ;
: limit-back ( limit store -- ) store-limit! drop ;
T{ syn-store full-at 1 syn-k-anon 0 syn-node-new swap syn-store limit-back -> false }T
: one-room ( store -- limit ) dup store-limit @ swap dup store-count @ 1+ swap store-limit! drop ;
T{ syn-store one-room 1 syn-k-anon 0 syn-node-new swap syn-store limit-back -> false }T

\ ---- 1. The elaborator's ⟨ ⟩ (anon.lf has whnf's id A): a negation
\ (133), its errors (462 have := ⟨⟩, 464 False, 465 Or, 466 too few, 467
\ items for no field), postponing (132).
T{ s" a b = explicit: h a b = ¬" st s" << >> by-exact" tactic-ran -> 133 }T
T{ s" a b = explicit: h a b =" st s" << ' h ' h >> by-have" tactic-ran -> 462 }T
T{ s" a b = explicit: h False" st s" << ' h >> by-exact" tactic-ran -> 464 }T
T{ s" a b = explicit: h a b = b a = ∨" st s" << ' h >> by-exact" tactic-ran -> 465 }T
T{ hk s" << ' h >> by-exact" tactic-ran -> 466 }T
T{ s" a b = explicit: h a b =" st s" << ' h >> by-exact" tactic-ran -> 467 }T
T{ s" a b = explicit: h a b =" st s" << >> a + a = by-have" tactic-ran -> 132 }T
\ (an argument whose type is a metavariable: whnfR at it, Lean postpones)
T{ s" a b = explicit: h a b =" st s" ' And.intro << >> $ << >> $ by-have" tactic-ran -> 132 }T
lf-tac-forget
\ After a list read on into the next line, the rest of that line runs: a
\ comment there is read to its end (source.fs's lfa-read! by address), so
\ a number-like token in it is no stray number.
T{ hk1 s\" by-revert[\n h k ] \\ see 0x10\n by-intro[ x y ] x by-exact" tactic-ran -> 0 }T
\ The message's rest and the type, kept for the detail: Prop (which
\ natural text cannot write yet) is no inductive type (463), with the
\ note below.
: prop ( -- t ) 0 lf-term-symbolic-sort lf-made! ;
lf-elab-reset
: anon0 ( -- node ) 0 nd ;
T{ anon0 prop lf-elab-term nip lf-elab-error drop lf-elab-rest s" is not an inductive type"
   compare lf-elab-below ' et-usage. = lf-elab-error-term 0< 0=
   -> outcome-invalid 463 0 true true }T
\ The first error's parts are kept: a later rest or below is dropped.
T{ s" more" lf-elab-rest+ ' drop lf-elab-below! lf-elab-rest nip lf-elab-below ' et-usage. =
   -> 24 true }T
\ Reset: none.
T{ lf-elab-error-reset lf-elab-rest nip lf-elab-below lf-elab-error-term -> 0 0 -1 }T
\ The rest is cut at its room.
: long+ ( -- ) 20 0 do s" 0123456789" lf-elab-rest+ loop ;
T{ long+ lf-elab-rest nip -> ep-rest# }T
lf-elab-error-reset
\ lf-elab-final: a root ⟨ ⟩ of unknown type is 462 (at the node); a
\ known type elaborates.
T{ anon0 -1 lf-elab-final nip lf-elab-error drop -> outcome-invalid 462 }T
lf-elab-error-reset
T{ anon0 s" True" lf-mk-const0 lf-elab-final nip -> outcome-ok }T
lf-elab-reset

\ ---- The constructor: explicit fields after the parameters; private:
\ not ported (139).
: ctor ( c-addr u -- d ) nm lf-menv-find made ;
T{ s" And.intro" ctor et-fields s" Eq.refl" ctor et-fields s" Exists.intro" ctor et-fields
   -> 2 outcome-ok 0 outcome-ok 2 outcome-ok }T
T{ s" _private.X.0.Foo.mk" nm et-private? s" And.intro" nm et-private? -> true false }T
T{ s" _private.X.0.Foo.mk" nm et-ctor-decl nip lf-elab-error drop -> outcome-unsupported 139 }T
lf-elab-error-reset
\ The rest nested: ⟨a, b, c⟩ for two fields, the second ⟨b, c⟩, each at
\ the node's place.
: items3 ( -- node )
  3 nd dup 0 101 syn-arg! dup 1 102 syn-arg! dup 2 103 syn-arg! ;
T{ items3 2 et-split made dup syn-b@ over 0 syn-arg rot 1 syn-arg dup syn-b@ over 0 syn-arg
   rot 1 syn-arg -> 2 101 2 102 103 }T
T{ items3 1 et-split made dup syn-b@ swap 0 syn-arg dup syn-b@ swap 2 syn-arg -> 1 3 103 }T

\ ---- 5. Resources: the words through their text with every heap
\ allocation refused in turn: the answer or full.
: frames-anew ( -- ) lfa-brackets sweep-slab-anew ;
' frames-anew sweep-slabs-xt !
: full-code? ( code -- flag ) dup if lf-author-outcome outcome-full = then ;
: text-full ( c-addr u c-addr' u' -- code outcome )
  tactic-ran dup full-code? if drop -1 outcome-full else outcome-ok then ;
: p-anon ( x -- code outcome ) drop hk s" << ' h ' k >> by-exact" text-full ;
: p-exists ( x -- code outcome )
  drop s" a b = explicit: h b a = explicit: k a b = b a = a b = ∧ ∧" st
  s\" by-exists[ ' h\n ' k ]" text-full ;
: p-lines ( x -- code outcome )
  drop hk1 s\" by-revert[ h\n k ] by-intro[ x\n y ] x by-exact" text-full ;
T{ 0 ' p-anon heap-sweep swept? 0 ' p-exists heap-sweep swept? 0 ' p-lines heap-sweep swept?
   -> true true true }T
lf-tac-forget
.( batch-f test.fs: all tests passed) cr
