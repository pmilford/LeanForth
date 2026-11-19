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
\ The reader alone: end NAME stops with 71 as before the elaborator
\ (src/front/elab-decl.fs sets these hooks; tests/front/elab.fs tests it).
' lfh-later is lf-front-elaborate   ' lfr-unelaborated is lf-front-by-statement

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

\ Tactic proofs are read whole and go to the runner, which stops at end
\ until plan FE1e elaborates the statement (71, as for a term proof;
\ tests/front/tactic-syntax.fs and tactic-run.fs have the rest); nothing
\ is checked.
T{ s" theorem t Nat explicit: n 0 n + n = := by n by-induction end t" nfails
   -> 71 1 58 }T
T{ lf-author-code lf-author-outcome -> outcome-unsupported }T
T{ s" theorem t Nat explicit: n 0 n + n = := by end t" nfails -> 71 1 43 }T
T{ s" theorem t Nat explicit: n 0 n + n = := by by-rfl end t" nfails -> 71 1 50 }T
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
T{ s" theorem t Nat explicit: n n n = := by n end t" nfails -> 86 1 41 }T
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
\ Values outside a declaration: natural text may build a term there (for
\ #check, plan S1), but the text must not end with values left; kernel
\ form refuses a term outside a declaration at its word.
T{ s" Nat" nfails drop drop -> 33 }T
T{ s" 1 2 +" nfails drop drop -> 33 }T
T{ s" kernel-form Nat Nat ->" nfails -> 4 1 21 }T
\ The run restores the caller's settings and leaves the stack as it was.
T{ base @ get-current s" theorem t Nat explicit: n n := n end t" nrun drop
   base @ get-current rot = -rot = -> true true }T

\ Out of room: the numerals' positions (author/form.fs) grow (the author
\ review's R5): 513 numbers in one declaration are not too many; at a
\ limit set (here 512) the 513th stops the run full (64), on the line it
\ ends.
create text 4096 allot  variable text#
: text0 ( -- ) 0 text# ! ;
: text+ ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
: times ( c-addr u n -- ) 0 ?do 2dup text+ loop 2drop ;
: text$ ( -- c-addr u ) text text# @ ;
text0 s\" theorem t\n" text+ s" 1 " 300 times s\" \n" text+ s" 1 " 212 times s\" \n" text+
T{ text$ nfails drop drop lf-author-code lf-author-outcome -> 33 outcome-invalid }T
text0 s\" theorem t\n" text+ s" 1 " 300 times s\" \n" text+ s" 1 " 213 times s\" \n" text+
T{ text$ nfails drop drop lf-author-code lf-author-outcome -> 33 outcome-invalid }T
lfa-form-reset  512 lfa-numerals store-limit! drop
T{ text$ nfails drop lf-author-code lf-author-outcome -> 64 3 outcome-full }T
lf-author-begin  1 cells lfa-store-limit lfa-numerals store-limit! drop
\ Values grow (author/values.fs, the author review's R5): a statement of
\ 256 arrows, 513 values in one declaration, once full (64) at 512.
\ (The term store's limit raised for the run's 513 nodes, then put back.)
lf-term-capacity constant terms-were  lf-author-begin  4096 lf-term-capacity! drop
text0 s" def t 0 Type := Prop" text+ s"  Prop ->" 256 times s"  end t" text+
T{ lf-author-begin lf-author-kernel text$ lf-author-text -> outcome-ok }T
lf-author-begin  terms-were lf-term-capacity! drop

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
T{ m1 lf-mvar-value m1 lf-mvar-assignable? m1 lf-mvar-view -> false true lf-view-empty true }T
T{ m1 lf-mvar-tag -> 0 true }T
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
variable dscope
T{ inst lf-mvar-assignable? false lf-mctx-depth{ swap dscope ! inst lf-mvar-assignable?
   -> true outcome-ok false }T
T{ lf-mctx-depth lf-mctx-level-depth mv-natural new lf-mvar-assignable? -> 1 1 true }T
T{ dscope @ }lf-mctx-depth lf-mctx-depth lf-mctx-level-depth inst lf-mvar-assignable?
   -> outcome-ok 0 0 true }T
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
\ A level metavariable's depth is the context's when it was made; a stale
\ leaf, a level that is no metavariable or not in the store has -1.
T{ u lf-level-mvar-depth one lf-level-mvar-depth 99999 lf-level-mvar-depth -> -1 -1 -1 }T
T{ lf-level-mvar-new drop true lf-mctx-depth{ drop dscope ! lf-level-mvar-new drop
   dscope @ }lf-mctx-depth drop lf-level-mvar-depth swap lf-level-mvar-depth -> 1 0 }T
\ levelAssignDepth (Lean's incDepth): kept by a depth dscope that allows
\ level assignments, else the new depth; an outer level metavariable is
\ then assignable, or not; both depths come back at the dscope's end.
lf-level-mvar-new drop constant lu0
T{ true lf-mctx-depth{ drop dscope ! lf-mctx-level-depth lu0 lf-level-assignable-mvar?
   -> 0 true outcome-ok }T
variable scope2
T{ false lf-mctx-depth{ drop scope2 ! lf-mctx-level-depth lu0 lf-level-assignable-mvar?
   -> 2 false outcome-ok }T
\ The outer dscope while the inner is open, or a depth dscope closed as a
\ mark, is refused; in order, each closes.
T{ dscope @ }lf-mctx-depth scope2 @ lf-mctx-rollback scope2 @ lf-mctx-commit
   -> outcome-invalid outcome-invalid outcome-invalid }T
T{ scope2 @ }lf-mctx-depth dscope @ }lf-mctx-depth lf-mctx-depth lf-mctx-level-depth
   -> outcome-ok outcome-ok 0 0 }T
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
\ Once the pending one is assigned (?pend := Prop), ?dm alone stays (as
\ in Lean's instantiate_mvars) and ?dm x is the value with x abstracted
\ and the argument put in: Prop. (Both were unsupported before plan FE1c
\ ported the step.)
T{ pend prop lf-mvar-assign dm lf-instantiate-mvars -> outcome-ok dm outcome-ok }T
T{ dm x app lf-instantiate-mvars -> prop outcome-ok }T
\ With one argument more than its free variables, the value put in is
\ applied to the rest: ?dm x x is Prop x.
T{ dm x app x app lf-instantiate-mvars swap dup lf-term-first@ swap lf-term-second@
   -> outcome-ok prop x }T
\ A delayed assignment whose pending one is unassigned stays applied.
mv-natural new constant pend3  mv-natural new constant dm3
T{ x lf-delay-fvar dm3 pend3 1 lf-mvar-delay -> outcome-ok outcome-ok }T
T{ dm3 x app lf-instantiate-mvars swap lf-term-first@ -> outcome-ok dm3 }T
\ Lean's beta step: ?f Prop with ?f := fun x : Prop => Prop is Prop; ?f
\ alone is the lambda. (Unsupported before plan FE1c.)
mv-natural new constant f
prop prop lf-tag-lam lf-term-binary drop constant fun1
T{ f fun1 lf-mvar-assign f lf-instantiate-mvars -> outcome-ok fun1 outcome-ok }T
T{ f prop app lf-instantiate-mvars -> prop outcome-ok }T
\ An argument with a loose bound variable is put in where no binder of
\ the value lies around it (fun z => ?f z is fun z => Prop; plan FE1g-4;
\ under such a binder Lean lifts it, unsupported: tests/front/meta.fs).
\ Not ported, unsupported: a value that betaRev would zeta-reduce (?g
\ Prop with ?g := let c := Prop; fun a => a).
: lam2 ( type body -- t ) lf-term-lam 0= abort" lam" ;
: parts2 ( t -- a b ) dup lf-term-first@ swap lf-term-second@ ;
T{ prop f 0 lf-term-bvar drop app lam2 lf-instantiate-mvars swap parts2 -> outcome-ok prop prop }T
mv-natural new constant gz
prop prop 0 lf-term-bvar drop lam2 false lf-let-make drop constant let-fun
T{ gz let-fun lf-mvar-assign gz prop app lf-instantiate-mvars -> outcome-ok -1 outcome-unsupported }T
\ ?g alone, and ?g with no argument the let would meet, stay plain.
T{ gz lf-instantiate-mvars -> let-fun outcome-ok }T
\ A delayed assignment whose pending value still holds a metavariable is
\ left in place, its arguments instantiated (Lean's has_expr_mvar test).
1000 lf-term-capacity! drop
mv-natural new constant pend2  mv-natural new constant dm2  mv-natural new constant hole2
T{ pend2 x hole2 app lf-mvar-assign x lf-delay-fvar dm2 pend2 1 lf-mvar-delay
   -> outcome-ok outcome-ok outcome-ok }T
T{ dm2 f prop app app lf-instantiate-mvars swap parts2 -> outcome-ok dm2 prop }T
\ Lean instantiates an assigned head's beta result again, which here
\ would put in ?dm's value (?f9 := ?dm, ?f9 x): that second pass is not
\ ported, so unsupported (review of fe1c-lnorm, M1).
mv-natural new constant f9
T{ f9 dm lf-mvar-assign f9 x app lf-instantiate-mvars -> outcome-ok -1 outcome-unsupported }T
\ Two free variables take the arguments in order: ?dm4 over x, y2 with
\ ?p4 := x y2, so ?dm4 y2 x is y2 x.
prop lf-lctx-local drop constant y2
mv-natural new constant p4  mv-natural new constant dm4
T{ p4 x y2 app lf-mvar-assign x lf-delay-fvar y2 lf-delay-fvar dm4 p4 2 lf-mvar-delay
   -> outcome-ok outcome-ok outcome-ok outcome-ok }T
T{ dm4 y2 app x app lf-instantiate-mvars swap parts2 -> outcome-ok y2 x }T
\ The occurs check follows a delayed assignment to its pending
\ metavariable, as Lean's occursCheck: with ?dm6 delayed to ?p6, ?p6
\ occurs in x ?dm6, so ?p6 := x ?dm6 is refused (review of
\ fe1c-lnorm-2, L2); ?p6 := x is not.
mv-natural new constant p6  mv-natural new constant dm6
T{ x lf-delay-fvar dm6 p6 1 lf-mvar-delay p6 x dm6 app lf-mvar-occurs?
   -> outcome-ok outcome-ok true outcome-ok }T
T{ p6 x dm6 app lf-mvar-assign p6 x lf-mvar-assign -> outcome-invalid outcome-ok }T
\ The re-check of fe1c-lnorm (N2, N3): ?f10 ?dm with ?f10 := fun a => a y2
\ and ?dm ready needs Lean's second pass (P4): unsupported. Surplus
\ arguments are reduced in the delayed step (P12): ?dm7 y2 Prop with
\ ?p7 := fun b => b is Prop. A let in the delayed value would be
\ zeta-reduced (Q4): unsupported.
mv-natural new constant f10
T{ f10 prop 0 lf-term-bvar drop y2 app lam2 lf-mvar-assign f10 dm app lf-instantiate-mvars
   -> outcome-ok -1 outcome-unsupported }T
mv-natural new constant p7  mv-natural new constant dm7
T{ p7 prop 0 lf-term-bvar drop lam2 lf-mvar-assign x lf-delay-fvar dm7 p7 1 lf-mvar-delay
   -> outcome-ok outcome-ok outcome-ok }T
T{ dm7 y2 app prop app lf-instantiate-mvars -> prop outcome-ok }T
mv-natural new constant p8  mv-natural new constant dm8
y2 prop prop 0 lf-term-bvar drop lam2 lam2 false lf-let-make drop constant let-id
T{ p8 let-id lf-mvar-assign x lf-delay-fvar dm8 p8 1 lf-mvar-delay
   -> outcome-ok outcome-ok outcome-ok }T
T{ dm8 y2 app prop app lf-instantiate-mvars -> -1 outcome-unsupported }T
\ A pending value that holds its own application (P3b, review R3): Lean
\ finds it not ready, so ?d12 x stays, its argument instantiated.
mv-natural new constant p12  mv-natural new constant d12
T{ p12 x d12 y2 app app lf-mvar-assign x lf-delay-fvar d12 p12 1 lf-mvar-delay
   -> outcome-ok outcome-ok outcome-ok }T
T{ d12 x app lf-instantiate-mvars swap parts2 -> outcome-ok d12 x }T
\ A pending value beyond the term store (its terms given back after the
\ assignment, review R1): the walk reads no memo past its block and ends
\ invalid.
mv-natural new constant p11  mv-natural new constant d11
T{ x lf-delay-fvar d11 p11 1 lf-mvar-delay -> outcome-ok outcome-ok }T
d11 x app constant root11
create sm11 /lf-scratch allot
T{ sm11 lf-scratch-mark -> outcome-ok }T
\ (100,000 applications, so the value's index lies far past the memo.)
lf-term-count @ 200000 + lf-term-capacity! drop
: xapps ( t n -- t' ) 0 ?do x app loop ;
x 100000 xapps constant v11
T{ p11 v11 lf-mvar-assign sm11 lf-scratch-rollback -> outcome-ok outcome-ok }T
T{ root11 lf-instantiate-mvars -> -1 outcome-invalid }T
\ With no free variable (k = 0) the value takes the arguments: ?dm5 x
\ with ?p5 := fun a => a is x.
mv-natural new constant p5  mv-natural new constant dm5
T{ p5 prop 0 lf-term-bvar drop lam2 lf-mvar-assign dm5 p5 0 lf-mvar-delay
   -> outcome-ok outcome-ok }T
T{ dm5 x app lf-instantiate-mvars dm5 lf-instantiate-mvars -> x outcome-ok dm5 outcome-ok }T
T{ prop f app lf-instantiate-mvars nip -> outcome-ok }T
\ A new metavariable gets the current local context (plan FE1g-1, Lean's
\ mkFreshExprMVar): with x and y2 pushed on it, it sees both; one made
\ before sees neither, and the context set back is the empty one again.
mv-natural new constant blind
: local ( fvar -- local ) 0 0 lf-local-new ok? 0= abort" local" ;
: push ( view fvar -- view' ) local lf-view-push ok? 0= abort" push" ;
lf-mctx-view x push y2 push lf-mctx-view!
T{ mv-natural new dup x lf-mvar-sees? swap y2 lf-mvar-sees? -> true true }T
T{ blind x lf-mvar-sees? blind y2 lf-mvar-sees? -> false false }T
lf-view-empty lf-mctx-view!
T{ mv-natural new x lf-mvar-sees? -> false }T

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
\ A value that reaches the broken one: its occurs check ends invalid too,
\ and nothing is assigned.
mv-natural new constant m2
T{ m2 cy prop app lf-mvar-assign m2 lf-mvar-value -> outcome-invalid false }T
T{ prop lf-mvar-assignable? -> false }T

\ Level max: a part that changes is rebuilt, a level with none is kept,
\ and the occurs check looks through max.
lf-mctx-reset
T{ lf-level-mvar-new nip -> outcome-ok }T
lf-level-count @ 1- constant w
: lmax ( a b -- level ) lf-level-tag-max lf-level-binary 0= abort" max" ;
w one lmax constant wmax
one 0 lmax constant fixed
T{ w wmax lf-level-mvar-assign w lf-level-mvar-value -> outcome-invalid false }T
T{ w one lf-level-mvar-assign w 99999 lf-level-mvar-assign -> outcome-ok outcome-invalid }T
T{ wmax lf-level-instantiate-mvars swap dup wmax = swap mvl-first -> outcome-ok false one }T
T{ fixed lf-level-instantiate-mvars -> fixed outcome-ok }T
\ The occurs check follows an assigned level metavariable to its value;
\ a Sort over a level with none is kept.
T{ lf-level-mvar-new nip -> outcome-ok }T
lf-level-count @ 1- constant v
T{ v wmax lf-level-mvar-assign v lf-level-mvar-value -> outcome-ok wmax true }T
T{ one sort-of dup lf-instantiate-mvars swap rot = -> outcome-ok true }T
T{ 0 lf-level-mvar-value 5 mctx-epoch@ lf-level-mvar-leaf drop lf-level-mvar-live? -> false false }T
\ A broken (cyclic) level assignment, made by hand: the level, a Sort over
\ it and a constant over it all end invalid.
T{ lf-level-mvar-new nip -> outcome-ok }T
lf-level-count @ 1- constant cyl
cyl lf-level-succ drop cyl mvl-number mvl-decl mvl-value !
T{ cyl lf-level-instantiate-mvars -> -1 outcome-invalid }T
T{ cyl sort-of lf-instantiate-mvars -> -1 outcome-invalid }T
T{ cyl const-over lf-instantiate-mvars -> -1 outcome-invalid }T

\ Out of room in the stores: each refusal is full, never a term.
lf-mctx-reset
T{ lf-level-mvar-new nip -> outcome-ok }T
lf-level-count @ 1- constant s
T{ s one lf-level-mvar-assign -> outcome-ok }T
s sort-of constant ss
s const-over constant cs
s lf-level-succ drop constant s1
mv-natural new constant r1
r1 prop app constant r1p
T{ r1 prop prop app lf-mvar-assign -> outcome-ok }T
lf-term-capacity constant term-room
lf-level-capacity constant level-room
lf-cref-capacity constant cref-room
T{ lf-term-count @ lf-term-capacity! -> outcome-ok }T
T{ r1p lf-instantiate-mvars ss lf-instantiate-mvars -> -1 outcome-full -1 outcome-full }T
T{ prop mv-natural lf-mvar-new -> -1 outcome-full }T
\ The record claimed for it is given back: nothing changes (review L2).
T{ mv-exprs store-count @ prop mv-natural lf-mvar-new rot mv-exprs store-count @ =
   -> -1 outcome-full true }T
T{ cs lf-instantiate-mvars -> -1 outcome-full }T
T{ term-room lf-term-capacity! lf-cref-count @ lf-cref-capacity! -> outcome-ok outcome-ok }T
T{ cs lf-instantiate-mvars -> -1 outcome-full }T
T{ cref-room lf-cref-capacity! lf-level-count @ lf-level-capacity! -> outcome-ok outcome-ok }T
T{ s1 lf-level-instantiate-mvars lf-level-mvar-new -> -1 outcome-full -1 outcome-full }T
T{ mv-levels store-count @ lf-level-mvar-new rot mv-levels store-count @ =
   -> -1 outcome-full true }T
T{ level-room lf-level-capacity! -> outcome-ok }T
T{ r1p lf-instantiate-mvars nip -> outcome-ok }T
\ The free variables of delayed assignments, out of room.
T{ 1 mv-fvars store-limit! x lf-delay-fvar x lf-delay-fvar -> outcome-ok outcome-ok outcome-full }T
T{ 1 cells mv-limit mv-fvars store-limit! -> outcome-ok }T

\ Marks (Lean's checkpointDefEq): a rollback undoes the assignments made
\ since its mark, plain, level and delayed, and only those; a commit keeps
\ them for an outer mark; marks nest; the trail empties with the last.
\ A mark is a serial number, never given twice.
lf-mctx-reset
: lnew ( -- level ) lf-level-mvar-new ok? 0= abort" lnew" ;
: lfree? ( level -- flag ) lf-level-mvar-value dup if nip then 0= ;
: tfree? ( mvar -- flag ) lf-mvar-value dup if nip then 0= ;
: mark ( -- mark ) lf-mctx-mark ok? 0= abort" mark" ;
lnew constant lma  lnew constant lmb  mv-natural new constant ta  mv-natural new constant tb
lnew constant lmc  lnew constant lmd  lnew constant lme
variable mark-out  variable mark-in  variable mark-in2
T{ mark dup mark-out ! 0> lma one lf-level-mvar-assign -> true outcome-ok }T
T{ mark dup mark-in ! mark-out @ > ta prop lf-mvar-assign lmb one lf-level-mvar-assign
   -> true outcome-ok outcome-ok }T
T{ mark-in @ lf-mctx-rollback lma lfree? lmb lfree? ta tfree? -> outcome-ok false true true }T
T{ mv-trail slab-count lf-mctx-marks -> 1 1 }T
T{ mark-out @ lf-mctx-commit lma lfree? mv-trail slab-count lf-mctx-marks
   -> outcome-ok false 0 0 }T
\ An inner commit, then the outer rollback undoes both; a delayed
\ assignment is undone too.
T{ mark mark-out ! mark mark-in ! lmb one lf-level-mvar-assign -> outcome-ok }T
T{ mark-in @ lf-mctx-commit tb ta 0 lf-mvar-delay mark-out @ lf-mctx-rollback
   -> outcome-ok outcome-ok outcome-ok }T
T{ lmb lfree? tb lf-mvar-delayed lma lfree? -> true false false }T
\ Only the latest open mark closes: an inner mark committed and then
\ rolled back again, an outer mark while an inner is open, 0 (the
\ refused mark) or a number never given are refused, invalid, and change
\ nothing.
T{ mark mark-out ! lmc one lf-level-mvar-assign mark mark-in ! lmd one lf-level-mvar-assign
   -> outcome-ok outcome-ok }T
T{ mark-out @ lf-mctx-rollback mark-in @ lf-mctx-commit mark-in @ lf-mctx-rollback
   -> outcome-invalid outcome-ok outcome-invalid }T
T{ lmd lfree? lf-mctx-marks 0 lf-mctx-commit 99999 lf-mctx-rollback
   -> false 1 outcome-invalid outcome-invalid }T
\ A closed inner mark whose place a newer mark takes is still refused
\ (review of fe1c-lnorm-2, L1): the newer mark's assignment stays.
T{ mark mark-in2 ! lme one lf-level-mvar-assign mark-in @ lf-mctx-rollback lme lfree?
   -> outcome-ok outcome-invalid false }T
T{ mark-in2 @ lf-mctx-rollback mark-out @ lf-mctx-rollback lmc lfree? lmd lfree? lf-mctx-marks
   -> outcome-ok outcome-ok true true 0 }T
\ Without a mark nothing is noted; a rollback or commit with no mark open,
\ 0 among them, is refused.
T{ lmb one lf-level-mvar-assign mv-trail slab-count -> outcome-ok 0 }T
T{ mark-out @ lf-mctx-rollback 0 lf-mctx-commit lmb lfree? lf-mctx-marks
   -> outcome-invalid outcome-invalid false 0 }T
\ Back to a mark through every newer scope (review C1 of 2026-11-18):
\ plain and deep ones are undone and closed, the depths given back; a
\ depth scope, a closed mark, 0 or a number never given are refused and
\ change nothing; back to an inner mark keeps the outer one's changes.
variable dscope2
T{ mark mark-out ! lmc one lf-level-mvar-assign mark mark-in ! lmd one lf-level-mvar-assign
   -> outcome-ok outcome-ok }T
T{ lf-mctx-depth false lf-mctx-depth{ swap dscope2 ! lf-mctx-depth lf-mctx-marks
   -> 0 outcome-ok 1 3 }T
T{ dscope2 @ lf-mctx-rollback-to 0 lf-mctx-rollback-to 99999 lf-mctx-rollback-to lf-mctx-marks
   -> outcome-invalid outcome-invalid outcome-invalid 3 }T
T{ mark-out @ lf-mctx-rollback-to lmc lfree? lmd lfree? lf-mctx-marks lf-mctx-depth
   mv-trail slab-count -> outcome-ok true true 0 0 0 }T
T{ mark-out @ lf-mctx-rollback-to -> outcome-invalid }T
T{ mark mark-out ! lmc one lf-level-mvar-assign mark mark-in ! lmd one lf-level-mvar-assign
   mark drop -> outcome-ok outcome-ok }T
T{ mark-in @ lf-mctx-rollback-to lmc lfree? lmd lfree? lf-mctx-marks -> outcome-ok false true 1 }T
T{ mark-out @ lf-mctx-rollback lmc lfree? lf-mctx-marks -> outcome-ok true 0 }T
\ A refused assignment notes nothing: ?a is assigned already.
lma one lf-level-mvar-assign drop
T{ mark mark-out ! lma one lf-level-mvar-assign mv-trail slab-count -> outcome-invalid 0 }T
\ A mark from before lf-mctx-reset is refused by the marks after it.
T{ lf-mctx-reset mark mark-out @ lf-mctx-commit swap lf-mctx-commit lf-mctx-marks
   -> outcome-invalid outcome-ok 0 }T
\ So is one rolled back before a reset when the next reset's first mark
\ follows (review R2: a reset does not start the serials again).
T{ lf-mctx-reset mark dup mark-out ! lf-mctx-rollback lf-mctx-reset mark
   mark-out @ lf-mctx-commit swap lf-mctx-commit -> outcome-ok outcome-invalid outcome-ok }T
\ lf-mctx-latest: the latest open mark, 0 when none is open.
T{ lf-mctx-latest mark dup lf-mctx-latest = swap lf-mctx-rollback -> 0 true outcome-ok }T

\ Snapshots and switches (S1 §3, Lean's getMCtx and setMCtx): a tree of
\ states in one dscope; a switch leaves exactly the target's changes
\ (assignments, a kind, a delayed assignment's three fields), back and
\ forth; snapshots of a closed dscope, an outer one while an inner dscope
\ is open (except the inner's entry), 0 or none are refused.
lf-mctx-reset
lnew constant la  lnew constant lb
mv-natural new constant t1  mv-natural new constant t2  mv-natural new constant t3
variable s0  variable s1  variable s2  variable sc  variable inner
: snap ( -- snap ) lf-mctx-snapshot ok? 0= abort" snap" ;
: kind@ ( mvar -- kind ) lf-mvar-kind drop ;
: delayed? ( mvar -- flag ) lf-mvar-delayed dup if nip nip nip then ;
: pending ( mvar -- pending n ) lf-mvar-delayed drop nip ;
T{ lf-mctx-snapshot 0 lf-mctx-switch -> 0 outcome-invalid outcome-invalid }T
T{ mark sc ! snap s0 ! t1 prop lf-mvar-assign la one lf-level-mvar-assign
   t3 mv-synthetic lf-mvar-kind! -> outcome-ok outcome-ok outcome-ok }T
T{ snap s1 ! s0 @ lf-mctx-switch t1 tfree? la lfree? t3 kind@ -> outcome-ok true true mv-natural }T
T{ t2 t3 0 lf-mvar-delay lb one lf-level-mvar-assign snap s2 ! -> outcome-ok outcome-ok }T
T{ s1 @ lf-mctx-switch t1 tfree? la lfree? t3 kind@ t2 delayed? lb lfree?
   -> outcome-ok false false mv-synthetic false true }T
T{ s2 @ lf-mctx-switch t1 tfree? la lfree? t3 kind@ t2 pending lb lfree?
   -> outcome-ok true true mv-natural t3 0 false }T
T{ s2 @ lf-mctx-switch s1 @ lf-mctx-switch s1 @ lf-mctx-switch t1 tfree? t2 delayed?
   mv-trail slab-count -> outcome-ok outcome-ok outcome-ok false false 7 }T
\ An inner dscope: an outer snapshot is no target, the inner's entry is;
\ after the inner commit its snapshots are stale, the outer's are not.
T{ mark inner ! snap s0 ! s2 @ lf-mctx-switch -> outcome-invalid }T
T{ t2 prop lf-mvar-assign s0 @ lf-mctx-switch t2 tfree? t1 tfree? -> outcome-ok outcome-ok true false }T
T{ inner @ lf-mctx-commit s0 @ lf-mctx-switch s2 @ lf-mctx-switch t1 tfree? t2 delayed?
   -> outcome-ok outcome-invalid outcome-ok true true }T
\ Rolling the dscope back undoes every branch from wherever it stands; its
\ snapshots are stale and the trail is empty.
T{ sc @ lf-mctx-rollback t1 tfree? la lfree? lb lfree? t3 kind@ t2 delayed? mv-trail slab-count
   -> outcome-ok true true true mv-natural false 0 }T
T{ s1 @ lf-mctx-switch s2 @ lf-mctx-switch -> outcome-invalid outcome-invalid }T
\ A depth dscope keeps snapshots like a mark; at its end all is rolled back.
T{ false lf-mctx-depth{ drop sc ! snap s0 ! lb one lf-level-mvar-assign t1 prop lf-mvar-assign
   -> outcome-ok outcome-ok }T
T{ snap s1 ! s0 @ lf-mctx-switch t1 tfree? s1 @ lf-mctx-switch t1 tfree?
   -> outcome-ok true outcome-ok false }T
T{ sc @ }lf-mctx-depth t1 tfree? lb lfree? lf-mctx-depth -> outcome-ok true true 0 }T
\ A handle that names no live snapshot (review s1-meta-a M3): mark M,
\ snapshot a, inner mark I, snapshot b, I committed (b dropped), snapshot
\ c, t1 assigned. Neither b nor M (a mark) switches to the snapshot next
\ to it (c, a): both invalid, t1 still assigned.
T{ mark sc ! snap s0 ! mark inner ! snap s1 ! inner @ lf-mctx-commit snap s2 !
   t1 prop lf-mvar-assign -> outcome-ok outcome-ok }T
T{ s1 @ lf-mctx-switch sc @ lf-mctx-switch t1 tfree? -> outcome-invalid outcome-invalid false }T
T{ s2 @ lf-mctx-switch t1 tfree? sc @ lf-mctx-rollback t1 tfree? -> outcome-ok true outcome-ok true }T
lf-mctx-reset

\ A stale value: one the term store gave back after it was assigned (rolled
\ back past it) is no node of a walk, whose memo ends below it; the walk
\ ends invalid and never reads past its memo (review fe1ab L2).
create stale-mark /store-mark allot
lf-mctx-reset mv-natural new constant sm
T{ stale-mark lf-terms store-mark -> outcome-ok }T
prop prop app constant gone
T{ sm gone lf-mvar-assign stale-mark lf-term-rollback -> outcome-ok outcome-ok }T
T{ sm lf-instantiate-mvars -> -1 outcome-invalid }T
T{ sm sm lf-mvar-occurs? -> true outcome-invalid }T

\ Library constants whose types may unfold (review fe1ab L1; exported by
\ pinned Lean from tests/reference/front-unfold.lean): c : F Nat, F a
\ definition, and d : (fun α => α → α) Nat, a beta redex. Lean's whnf
\ gives each an explicit argument; the reader stops (73), never guesses.
T{ lfc-library-close s" tests/front/unfold-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" theorem t Nat explicit: x x c x = := x end t" nfails -> 73 1 29 }T
T{ s" theorem t Nat explicit: x x d x = := x end t" nfails -> 73 1 29 }T
T{ lf-author-code lf-author-outcome -> outcome-unsupported }T

T{ lfc-library-close -> }T
\ dag-walk.fs's memo bounds: a node is in a walk of size n when 0 <= node
\ < n; a negative node never is (review reuse-1a L1).
create dw-probe /dw allot  5 dw-probe dw-size !
T{ 0 dw-probe dw-in? 4 dw-probe dw-in? 5 dw-probe dw-in? -> true true false }T
T{ -1 dw-probe dw-in? max-n negate dw-probe dw-in? -> false false }T
\ A node beyond the memo is new and reads no cell past it (re-check of
\ fe1c-lnorm R1, fault fe-walk-new-unbounded): the cell past this memo
\ of five holds a made image, which an unbounded read would take as done.
create dw-probe-memo 6 cells allot  dw-probe-memo 6 cells erase
7 dw-probe-memo 3 cells + !  7 dw-probe-memo 5 cells + !  dw-probe-memo dw-probe dw-memo !
T{ 5 dw-probe dw-new? 3 dw-probe dw-new? 0 dw-probe dw-new? -> true false true }T
T{ 5 dw-probe dw-done? 3 dw-probe dw-done? 5 dw-probe dw-cycle? -> false true true }T

\ dag-walk.fs's two kinds of states (performance scan, 2026-11-18): a walk
\ of more than dw-array-most nodes keeps them in a memo of the nodes it
\ meets, a smaller one in an array of all. instantiateMVars and the occurs
\ check of 300 random terms (lambdas, pis, applications, Prop, a loose
\ variable, assigned and unassigned metavariables, assignments through
\ others) give the same terms (Expr.eqv) and answers with the array as
\ with the memo, after the store grew past the cut-over.
lf-author-begin lf-mctx-reset
T{ 0 lf-term-sort -> prop true }T
variable wt-seed  20261118 wt-seed !
: wt-rnd ( n -- u ) wt-seed @ 1103515245 * 12345 + 2147483647 and dup wt-seed ! 16 rshift
  swap mod ;
create wt-mvars 6 cells allot
: wt-mvar ( i -- m ) cells wt-mvars + @ ;
: wt-bvar ( -- t ) 0 lf-term-bvar 0= abort" bvar" ;
: wt-leaf ( limit -- t )
  dup 0> 2 wt-rnd and if wt-rnd wt-mvar else drop 3 wt-rnd if prop else wt-bvar then then ;
: wt-tag ( -- tag ) 3 wt-rnd dup 2 = if drop lf-tag-app else lf-tag-lam + then ;
defer wt-term ( depth limit -- t )
: wt-kids ( depth limit -- a b ) swap 1- swap 2dup wt-term >r wt-term r> ;
: wt-node ( depth limit -- t )
  over 0= 3 wt-rnd 0= or if nip wt-leaf else wt-kids wt-tag lf-term-binary 0= abort" bin" then ;
' wt-node is wt-term
: wt-mvars! ( -- ) 6 0 do mv-natural new i cells wt-mvars + ! loop ;
: wt-assign ( -- ) 6 1 do 2 wt-rnd if i wt-mvar 3 i wt-term lf-mvar-assign drop then loop ;
300 constant wt-n
create wt-terms wt-n 3 * cells allot
: wt-at ( i k -- addr ) swap 3 * + cells wt-terms + ;
: wt-inst ( t -- t' ) lf-instantiate-mvars ok? 0= abort" instantiate" ;
: wt-occurs ( t -- flag ) 1 wt-mvar swap lf-mvar-occurs? ok? 0= abort" occurs" ;
: wt-make ( i -- ) 4 6 wt-term 2dup swap 0 wt-at ! dup wt-inst 2 pick 1 wt-at !
  wt-occurs swap 2 wt-at ! ;
: wt-again? ( i -- flag )
  dup 0 wt-at @ dup wt-inst 2 pick 1 wt-at @ lf-meta-eqv drop
  swap wt-occurs rot 2 wt-at @ = and ;
: wt-all? ( -- flag ) true wt-n 0 do i wt-again? and loop ;
: wt-make-all ( -- ) wt-n 0 do i wt-make loop ;
wt-mvars! wt-assign wt-make-all
T{ lf-term-count @ dw-array-most < wt-all? -> true true }T
: wt-fill ( n -- ) 0 ?do i 7 + lf-term-bvar 2drop loop ;
dw-array-most wt-fill
T{ lf-term-count @ dw-array-most > wt-all? -> true true }T
\ Which kind a run uses: a build that answers 1 when it finds the array.
create wt-walk /dw allot  wt-walk /dw erase
:noname ( node walk -- child true | false ) 2drop false ; wt-walk dw-pending !
:noname ( node walk -- image ) nip dw-array? 1 and ; wt-walk dw-build !
: wt-kind ( size -- image outcome ) wt-walk dw-size ! 0 wt-walk dw-run ;
T{ dw-array-most wt-kind dw-array-most 1+ wt-kind -> 1 outcome-ok 0 outcome-ok }T
\ The shared walk words of reuse-d: dw-on-terms and dw-on-levels set the
\ two words and the size; dw-want-binary and dw-part-images walk a binary
\ term's parts, first part first; dw-made keeps a made result or refuses
\ the walk full with the image 0.
create rd-walk /dw allot  rd-walk /dw erase
' 2drop ' drop 2constant rd-hooks
T{ rd-hooks rd-walk dw-on-terms rd-walk = -> true }T
T{ rd-walk dw-build @ ' 2drop = rd-walk dw-pending @ ' drop = -> true true }T
T{ rd-walk dw-size @ lf-term-base lf-term-count @ + = -> true }T
T{ rd-hooks rd-walk dw-on-levels drop rd-walk dw-size @ lf-level-count @ = -> true }T
\ The image: a leaf its bound variable's index, a node its first part's
\ image times 10 plus its second's, so the order of the parts shows.
: rd-leaf ( node -- n ) lf-term-first@ ;
: rd-build ( node walk -- n )
  over lf-term-binary? if dw-part-images swap 10 * + else drop rd-leaf then ;
' rd-build ' dw-want-binary 2constant rd-sum
: rd-run ( term -- n outcome ) rd-sum rd-walk dw-on-terms dw-run ;
: rd-bv ( i -- t ) lf-term-bvar 0= abort" bvar" ;
T{ 1 rd-bv 2 rd-bv app 3 rd-bv app rd-run -> 123 outcome-ok }T
T{ 4 rd-bv rd-run -> 4 outcome-ok }T
T{ outcome-ok rd-walk dw-outcome !  7 true rd-walk dw-made rd-walk dw-ok? -> 7 true }T
T{ false rd-walk dw-made rd-walk dw-outcome @ -> 0 outcome-full }T
T{ outcome-unknown rd-walk dw-outcome !  false rd-walk dw-made rd-walk dw-outcome @
   -> 0 outcome-unknown }T
\ lf-meta-app-head (meta-spine.fs): Lean's getAppFn, down the first parts.
T{ 1 rd-bv 2 rd-bv app 3 rd-bv app lf-meta-app-head rd-leaf 6 rd-bv dup lf-meta-app-head = -> 1 true }T
\ lf-fvar-mvar-tag? (core/mvar-leaves.fs, reuse-b): a free variable's and
\ a metavariable's tag, no other tag from -2 to 40.
: fm-others ( -- n ) 0 41 -2 do i lf-fvar-mvar-tag? - loop ;
T{ lf-tag-fvar lf-fvar-mvar-tag? lf-tag-mvar lf-fvar-mvar-tag? fm-others -> true true 2 }T
T{ depth -> 0 }T
cr .( front.fs: all tests passed) cr
bye
