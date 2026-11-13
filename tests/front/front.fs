\ Unit tests of the front end's first steps (plan tasks FE1a and FE1b;
\ ADR 0021): the natural reader's syntax trees, with positions, every
\ refusal with its code, line and column, the kernel-form marker, numerals,
\ ' and $, and the operator words (src/front/reader.fs, syntax.fs,
\ author/form.fs); and the metavariable context: new, assign, the occurs
\ check, stale leaves, kinds and depth, level metavariables, delayed
\ assignments and instantiation over deep terms (src/front/mvars.fs,
\ dag-walk.fs). Every T{ }T checks the data stack's depth. The export
\ writer's refusal of a metavariable is in tests/author/author.fs.
\ Nothing here checks or accepts a theorem.
require ../support/tester.fs
require ../../src/main.fs

: nrun ( c-addr u -- outcome ) lf-author-begin lf-author-text ;
: err ( -- code line col ) lf-author-code lfa-error lfa-err-at @ lfa-pos> ;
: see-at ( -- line col ) lfa-error lfa-err-see @ lfa-pos> ;
: nfails ( c-addr u -- code line col ) nrun drop err ;
: kind ( node -- k ) syn-kind@ ;
: at ( node -- line col ) syn-at@ lfa-pos> ;
: named? ( id c-addr u -- flag ) lfa-intern = ;
: last-node ( -- node ) syn-count 1- ;
T{ s" tests/author/init-slice.ndjson" true lfc-library-open -> outcome-ok }T

\ ---- FE1a. Natural form is the default: 0 n + n = is
\ binrel% Eq (binop% HAdd.hAdd 0 n) n, each node at its token.
T{ s" theorem t Nat explicit: n 0 n + n = := n Eq.refl end t" nfails -> 71 1 50 }T
lf-front-statement constant st
T{ st kind st at -> syn-k-binrel 1 35 }T
T{ st syn-a@ s" Eq" named? -> true }T
T{ st syn-b@ kind st syn-b@ at -> syn-k-binop 1 31 }T
T{ st syn-b@ syn-a@ s" HAdd.hAdd" named? -> true }T
T{ st syn-b@ syn-b@ dup kind over syn-a@ rot at -> syn-k-num 0 1 27 }T
T{ st syn-b@ syn-c@ dup kind over syn-a@ rot at -> syn-k-var 0 1 29 }T
T{ st syn-c@ dup kind over syn-a@ rot at -> syn-k-var 0 1 33 }T
\ The proof n Eq.refl: Eq.refl takes its one explicit argument.
syn-count 2 - constant proof
T{ proof kind proof syn-b@ proof at -> syn-k-app 1 1 42 }T
T{ proof syn-a@ kind proof 0 syn-arg kind -> syn-k-const syn-k-var }T
T{ proof syn-a@ syn-a@ lfa-decl-name s" Eq.refl" named? -> true }T
\ The binder's type as written; the declaration starts on an empty stack.
T{ 0 kind 0 at -> syn-k-const 1 11 }T
T{ lf-front-by -> -1 }T

\ Arguments in Lean's order: ' Nat.succ n congrArg is congrArg Nat.succ n
\ (congrArg takes f and h explicitly); ' gives the function unapplied.
T{ s" theorem t Nat explicit: n 0 n + n = := ' Nat.succ n congrArg end t" nfails
   -> 71 1 62 }T
syn-count 3 - constant ca
T{ ca kind ca syn-b@ -> syn-k-app 2 }T
T{ ca syn-a@ syn-a@ lfa-decl-name s" congrArg" named? -> true }T
T{ ca 0 syn-arg dup kind swap syn-a@ lfa-decl-name s" Nat.succ" named? -> syn-k-const true }T
T{ ca 1 syn-arg kind -> syn-k-var }T
\ f a $ applies once more; an application made by a name gets the
\ argument as its next one (Lean's id g x), a function from ' a new one.
T{ s" theorem t Nat explicit: n 0 n + n = := n Eq.refl n $ end t" nfails -> 71 1 54 }T
T{ last-node 2 - dup kind over syn-b@ rot syn-a@ syn-a@ lfa-decl-name s" Eq.refl" named?
   -> syn-k-app 2 true }T
T{ s" theorem t Nat explicit: n 0 n + n = := ' Nat.succ n $ end t" nfails -> 71 1 55 }T
T{ last-node 1- dup kind swap syn-b@ -> syn-k-app 1 }T
\ * and ≤ are binop% HMul.hMul and binrel% LE.le; numerals keep their
\ value and column, also across lines.
T{ s\" theorem t\n  2 3 * 7 \xE2\x89\xA4\n:= by\nend t" nfails -> 71 4 1 }T
T{ lf-front-statement dup kind swap syn-a@ s" LE.le" named? -> syn-k-binrel true }T
T{ lf-front-statement syn-b@ dup kind swap syn-a@ s" HMul.hMul" named? -> syn-k-binop true }T
T{ lf-front-statement syn-c@ dup syn-a@ swap at -> 7 2 9 }T
T{ lf-front-statement syn-b@ syn-b@ dup syn-a@ swap at -> 2 2 3 }T
T{ lf-front-by lfa-pos> -> 3 4 }T
T{ s\" theorem t\n 123456789\n 1 = := by end t" nfails -> 71 3 12 }T
T{ lf-front-statement syn-b@ dup syn-a@ swap at -> 123456789 2 2 }T

\ Tactic words, by and end: not supported yet, nothing checked.
T{ s" theorem t Nat explicit: n 0 n + n = := by n by-induction end t" nfails
   -> 72 1 45 }T
T{ lf-author-code lf-author-outcome -> outcome-unsupported }T
T{ s" theorem t Nat explicit: n 0 n + n = := by end t" nfails -> 71 1 43 }T
T{ s" theorem t Nat explicit: n 0 n + n = := by by-rfl end t" nfails -> 72 1 43 }T
T{ s" axiom a Nat end a" nfails -> 71 1 13 }T
\ A kernel-form word in natural text, and the marker.
T{ s" theorem t Prop explicit: p p := p end t" nfails -> 70 1 11 }T
T{ lf-author-code lf-author-outcome -> outcome-unsupported }T
T{ s" theorem t Nat explicit: n n n fun := n end t" nfails -> 70 1 31 }T
T{ s" theorem t 0 lit# := n end t" nfails -> 70 1 13 }T
T{ s" kernel-form theorem t Prop explicit: p p := p end t" nrun -> outcome-ok }T
T{ s" kernel-form kernel-form theorem t Prop explicit: p p := p end t" nrun -> outcome-ok }T
T{ s" kernel-form theorem t Prop explicit: p p := p by-rfl end t" nfails -> 72 1 47 }T
T{ s" kernel-form theorem t Prop explicit: p ' p := p end t" nfails -> 58 1 40 }T
T{ s" theorem t kernel-form Prop := Prop end t" nfails -> 57 1 11 }T
T{ s" namespace N kernel-form theorem t Prop explicit: p p := p end t end N" nrun
   -> outcome-ok }T
\ lf-author-begin starts in natural form again.
T{ s" theorem t Prop := Prop end t" nfails -> 70 1 11 }T

\ Malformed natural text: every refusal with its code and place.
T{ s" theorem t Nat explicit: n 0 + := n end t" nfails -> 3 1 29 }T
T{ s" theorem t Nat explicit: n n $ := n end t" nfails -> 3 1 29 }T
T{ s" theorem t Nat explicit: n n n = := Eq.refl end t" nfails -> 3 1 36 }T
T{ s" theorem t Nat explicit: n n n = := '" nfails -> 2 1 36 }T
T{ s" theorem t Nat explicit: n n n = := ' 5 end t" nfails -> 59 1 36 }T
T{ s" theorem t Nat explicit: n n n = := ' + end t" nfails see-at -> 59 1 38 1 36 }T
T{ s" theorem t Nat explicit: n n n = := ' ' n end t" nfails see-at -> 59 1 38 1 36 }T
T{ s" theorem t Nat explicit: n n n = by := n end t" nfails -> 69 1 33 }T
T{ s" theorem t Nat explicit: n n n = := n by end t" nfails -> 69 1 38 }T
T{ s" theorem t Nat explicit: n n n = := by by end t" nfails -> 69 1 39 }T
T{ s" theorem t Nat explicit: n n n = := Nat explicit: m by end t" nfails -> 69 1 52 }T
T{ s" theorem t Nat explicit: n n n = end t" nfails -> 19 1 33 }T
T{ s" theorem t Nat explicit: n n n = := n n end t" nfails -> 20 1 40 }T
T{ s" theorem t Nat explicit: n n n = := by n end t" nfails -> 20 1 41 }T
T{ s" theorem t Nat explicit: n n n = := n end u" nfails -> 22 1 38 }T
T{ s" theorem t Nat explicit: n n n = n := n end t" nfails -> 18 1 35 }T
T{ s" theorem t Nat explicit: n 1234567890 n = := n end t" nfails -> 35 1 27 }T
T{ s" theorem t Nat explicit: n 0x3 n = := n end t" nfails -> 35 1 27 }T
\ A universe parameter is no term; ' takes no universe either.
T{ s" theorem t universe u Nat explicit: n n u = := n end t" nfails -> 7 1 42 }T
T{ s" theorem t universe u Nat explicit: n ' u := n end t" nfails see-at -> 59 1 40 1 38 }T
\ The count of a name's arguments that depends on unfolding a definition
\ (Nat.add, a definition, heads the variable's type) is not supported yet.
T{ s" theorem t 1 2 Nat.add explicit: x x := x end t" nfails -> 73 1 35 }T
T{ lf-author-code lf-author-outcome -> outcome-unsupported }T
\ So is a type written with an operator: its head needs elaboration.
T{ s" theorem t 0 0 = explicit: h h := h end t" nfails -> 73 1 29 }T
\ The other binder words, a variable as a type (no arguments), and
\ namespaces in natural form.
T{ s" theorem t Nat implicit: a Nat strict-implicit: b Nat instance: c a b = := a end t"
   nfails -> 71 1 77 }T
T{ s" theorem t Nat explicit: n n explicit: x x x = := x end t" nfails -> 71 1 52 }T
T{ s" namespace N theorem t Nat explicit: n n n = := n end t end N" nfails -> 71 1 50 }T
T{ s" namespace N end N" nrun -> outcome-ok }T
\ A constant of the text itself (only kernel-form text makes one) has no
\ argument count the reader knows; nor has a library constant the
\ library cannot describe.
T{ s" kernel-form axiom ax Prop end ax" nrun 0 lfn-library -> outcome-ok -1 true }T
: no-arity ( name -- false ) drop false ;
' no-arity is lfn-library-arity
T{ s" theorem t Nat explicit: n n n = := n end t" nfails -> 73 1 11 }T
' lfc-arity is lfn-library-arity
\ Values outside a declaration: the text ends with values left.
T{ s" Nat" nfails drop drop -> 33 }T
T{ s" 1 2 +" nfails -> 4 1 5 }T
\ The run restores the caller's settings and leaves the stack as it was.
T{ base @ get-current s" theorem t Nat explicit: n n := n end t" nrun drop
   base @ get-current rot = -rot = -> true true }T

\ Out of room: a syntax store that may hold 3 nodes stops the run full
\ (68) at the word that needed a fourth; nothing is left on the stack.
T{ syn-reset 3 syn-store store-limit! -> outcome-ok }T
T{ s" theorem t Nat explicit: n 0 n + n = := n end t" nfails -> 68 1 31 }T
\ And with room for an application but not its argument (Nat, n, n,
\ Eq.refl, the application: five nodes).
T{ 5 syn-store store-limit! -> outcome-ok }T
T{ s" theorem t Nat explicit: n n := n Eq.refl end t" nfails -> 68 1 34 }T
T{ lf-author-code lf-author-outcome -> outcome-full }T
T{ syn-limit syn-store store-limit! -> outcome-ok }T

\ The syntax store on its own: kinds, fields, arguments, positions.
T{ syn-reset syn-count -> 0 }T
T{ syn-k-app 65537 syn-new -> 0 true }T
T{ 0 syn-arg-new 0 syn-arg-new 0 syn-b@ syn-count -> true true 2 3 }T
T{ 0 1 7 syn-arg! 0 1 syn-arg 0 0 syn-arg 0 at -> 7 0 1 1 }T
T{ 5 syn-valid? 2 syn-valid? -> false true }T
T{ syn-reset 0 syn-valid? -> false }T

\ ---- FE1b. The metavariable context, in a fresh run (stores, a session).
lf-author-begin lf-mctx-reset
T{ 0 lf-term-sort -> 0 true }T
0 constant prop
: app ( f a -- t ) lf-term-app 0= abort" app" ;
: new ( kind -- mvar ) prop swap lf-mvar-new ok? 0= abort" new" ;
mv-natural new constant m1
T{ m1 lf-mvar-live? m1 lf-mvar-type m1 lf-mvar-kind -> true prop true mv-natural true }T
T{ m1 lf-mvar-value m1 lf-mvar-assignable? m1 lf-mvar-lctx -> false true 0 true }T
T{ m1 lf-mvar? prop lf-mvar? prop lf-mvar-live? -> true false false }T
\ New: a type that is no term, or a kind out of range, is invalid.
T{ 999 mv-natural lf-mvar-new -> -1 outcome-invalid }T
T{ prop 3 lf-mvar-new -> -1 outcome-invalid }T
T{ prop -1 lf-mvar-new -> -1 outcome-invalid }T
\ Assignment, once; then instantiation replaces it.
m1 prop app constant m1p
T{ m1 prop lf-mvar-assign m1 lf-mvar-value -> outcome-ok prop true }T
T{ m1 prop lf-mvar-assign -> outcome-invalid }T
T{ m1p lf-instantiate-mvars swap dup lf-term-first@ swap lf-term-second@
   -> outcome-ok prop prop }T
T{ prop lf-instantiate-mvars -> prop outcome-ok }T
T{ m1 999 lf-mvar-assign -> outcome-invalid }T
T{ prop prop lf-mvar-assign -> outcome-invalid }T
\ The occurs check: ?a := ?a x, and ?b := ?c with ?c := ?b x.
mv-natural new constant ma
T{ ma ma prop app lf-mvar-assign ma lf-mvar-value -> outcome-invalid false }T
T{ ma ma prop app lf-mvar-occurs? -> true outcome-ok }T
T{ ma prop lf-mvar-occurs? -> false outcome-ok }T
mv-natural new constant mb  mv-natural new constant mc
T{ mc mb prop app lf-mvar-assign -> outcome-ok }T
T{ mb mc lf-mvar-assign mb lf-mvar-value -> outcome-invalid false }T
T{ mb prop lf-mvar-assign -> outcome-ok }T
T{ mc lf-instantiate-mvars swap lf-term-first@ -> outcome-ok prop }T
\ Kinds and depth: a goal (synthetic opaque) is never assignable by
\ unification, an outer metavariable not inside a deeper context.
mv-opaque new constant goal
T{ goal lf-mvar-assignable? -> false }T
mv-synthetic new constant inst
T{ inst lf-mvar-assignable? lf-mctx-deeper inst lf-mvar-assignable? -> true false }T
T{ lf-mctx-depth mv-natural new lf-mvar-assignable? -> 1 true }T
T{ lf-mctx-shallower lf-mctx-shallower lf-mctx-depth inst lf-mvar-assignable? -> 0 true }T
T{ goal prop lf-mvar-assign goal lf-mvar-value -> outcome-ok prop true }T
\ Stale leaves: after a reset none of them is live or assignable.
T{ lf-mctx-reset m1 lf-mvar-live? ma lf-mvar-live? ma prop lf-mvar-assign
   -> false false outcome-invalid }T
T{ ma lf-mvar-type ma lf-mvar-value -> false false }T
\ A new leaf with the old number is another metavariable.
T{ mv-natural new dup lf-term-first@ swap m1 = -> 0 false }T
\ A leaf whose epoch is wrong, or a number beyond the store, is no leaf.
T{ 0 77 lf-mvar-leaf drop lf-mvar-live? 50 mctx-epoch@ lf-mvar-leaf drop lf-mvar-live?
   -> false false }T

\ Level metavariables: Sort ?u becomes Sort 1 once ?u := succ zero.
lf-mctx-reset
T{ lf-level-mvar-new -> lf-level-count @ 1- outcome-ok }T
lf-level-count @ 1- constant u
T{ u lf-level-mvar-live? u lf-level-mvar-value -> true false }T
T{ 0 lf-level-succ -> lf-level-count @ 1- true }T
lf-level-count @ 1- constant one
T{ u lf-level-succ drop dup u swap lf-level-mvar-assign -> lf-level-count @ 1- outcome-invalid }T
T{ u one lf-level-mvar-assign u lf-level-mvar-value -> outcome-ok one true }T
T{ u one lf-level-mvar-assign -> outcome-invalid }T
T{ u lf-level-instantiate-mvars -> one outcome-ok }T
: sort-of ( level -- term ) dup lf-level-identity drop lf-hterm-sort 0= abort" sort" drop ;
T{ u sort-of lf-instantiate-mvars swap lf-term-first@ -> outcome-ok one }T
T{ u lf-level-succ drop lf-level-instantiate-mvars swap lf-level-slot node-first @
   -> outcome-ok one }T
T{ 99999 lf-level-instantiate-mvars -> -1 outcome-invalid }T
\ A constant over ?u gets a new reference with ?u's value (C.{1}).
create pair 2 cells allot
: const-over ( level -- term )
  dup lf-level-identity drop swap pair 2!
  0 s" C" lf-name-str drop lf-name-generation @ pair 1 lf-cref-new 0= abort" cref"
  lf-cterm-new 0= abort" cterm" drop ;
: const-level ( term -- level ) lf-term-first@ lf-cref-slot lf-cref-pairs drop 0 lf-cref-pair@ drop ;
u const-over constant cu
T{ cu const-level cu lf-instantiate-mvars swap dup cu = swap const-level
   -> u outcome-ok false one }T
T{ one const-over dup lf-instantiate-mvars drop = -> true }T
T{ lf-mctx-reset u lf-level-mvar-live? u one lf-level-mvar-assign -> false outcome-invalid }T
\ With the level store sharing by content, a new level metavariable of the
\ same number is another leaf (another epoch), and the old one stays stale.
true lf-term-sharing! lf-mctx-reset
T{ lf-level-mvar-new nip -> outcome-ok }T
lf-level-count @ 1- constant u0
T{ lf-mctx-reset lf-level-mvar-new -> lf-level-count @ 1- outcome-ok }T
T{ u0 lf-level-mvar-live? lf-level-count @ 1- dup u0 = swap lf-level-mvar-live? -> false false true }T
false lf-term-sharing!

\ Binders keep their name and kind when a part changes.
lf-mctx-reset mv-natural new constant body
prop body lf-tag-lam lf-term-binary drop constant lam
T{ lam 0 s" x" lf-name-str drop lf-binder-implicit lf-pres-binder! -> outcome-ok }T
T{ body prop lf-mvar-assign lam lf-instantiate-mvars nip -> outcome-ok outcome-ok }T
T{ lam lf-instantiate-mvars drop dup lam = swap lf-term-second@ -> false prop }T
T{ lam lf-instantiate-mvars drop lf-pres-binder@ drop nip -> lf-binder-implicit }T

\ Delayed assignments: recorded, read back, and left in place by
\ instantiation (a hole stays, so the export writer refuses the term).
lf-mctx-reset lf-lctx-reset
T{ prop lf-lctx-local nip -> outcome-ok }T
lf-term-count @ 1- lf-term-base + constant x
mv-natural new constant pend  mv-natural new constant dm
T{ x lf-delay-fvar prop lf-delay-fvar -> outcome-ok outcome-invalid }T
T{ dm pend 2 lf-mvar-delay -> outcome-invalid }T
T{ dm pend 1 lf-mvar-delay -> outcome-ok }T
: first-fvar ( pending addr n true -- pending fvar n true ) >r >r @ r> r> ;
T{ dm lf-mvar-delayed first-fvar -> pend x 1 true }T
T{ dm prop lf-mvar-assign dm pend 1 lf-mvar-delay -> outcome-invalid outcome-invalid }T
T{ pend lf-mvar-delayed -> false }T
T{ dm lf-instantiate-mvars -> dm outcome-ok }T
\ Once the pending one is assigned, Lean would put the value in: not
\ supported yet (plan FE1c), never another term.
T{ pend prop lf-mvar-assign dm lf-instantiate-mvars -> outcome-ok -1 outcome-unsupported }T
\ So is Lean's beta step for ?f a when ?f := fun x : Prop => Prop; ?f alone
\ is the lambda.
mv-natural new constant f
prop prop lf-tag-lam lf-term-binary drop constant fun1
T{ f fun1 lf-mvar-assign f lf-instantiate-mvars -> outcome-ok fun1 outcome-ok }T
T{ f prop app lf-instantiate-mvars -> -1 outcome-unsupported }T
T{ prop f app lf-instantiate-mvars nip -> outcome-ok }T
T{ mv-natural new lf-mvar-lctx -> 1 true }T

\ Out of room: a context whose store may hold one more metavariable
\ makes it, then refuses the next (full), changing nothing.
T{ lf-mctx-reset 1 mv-exprs store-limit! -> outcome-ok }T
T{ prop mv-natural lf-mvar-new nip prop mv-natural lf-mvar-new mv-exprs store-count @
   -> outcome-ok -1 outcome-full 1 }T
T{ 1 mv-levels store-limit! lf-level-mvar-new nip lf-level-mvar-new
   -> outcome-ok outcome-ok -1 outcome-full }T
T{ /mvd mv-limit mv-exprs store-limit! /mvl mv-limit mv-levels store-limit! -> outcome-ok outcome-ok }T
\ Resources: a term 10,000 applications deep around a metavariable is
\ instantiated on the heap stack (no host-stack depth), every node rebuilt.
lf-mctx-reset 200000 lf-term-capacity! drop
mv-natural new constant deep
: nest ( t n -- t' ) 0 ?do prop app loop ;
deep 10000 nest constant tower
T{ deep prop lf-mvar-assign tower lf-instantiate-mvars nip -> outcome-ok outcome-ok }T
: firsts ( t n -- t' ) 0 ?do lf-term-first@ loop ;
T{ tower lf-instantiate-mvars drop 10000 firsts -> prop }T
\ A broken (cyclic) assignment, made by hand past the occurs check, ends
\ the walk invalid, never with a term.
lf-mctx-reset mv-natural new constant cy
: cycle! ( mvar -- term ) dup prop app tuck swap lf-term-first@ mv-decl mvd-value ! ;
T{ cy cycle! lf-instantiate-mvars -> -1 outcome-invalid }T
T{ cy cy lf-mvar-occurs? -> true outcome-invalid }T
T{ cy prop lf-mvar-assign -> outcome-invalid }T

T{ lfc-library-close -> }T
T{ depth -> 0 }T
cr .( front.fs: all tests passed) cr
bye
