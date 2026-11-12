\ The notation table and the printer's notation (plan task 4.4.3; src/present/
\ notation-table.fs and print-notation.fs): the table's lookups, then terms
\ built with Lean's constants printed in each of the four modes, with
\ notation off (the kernel's term, as before) and on; precedences and
\ parentheses as Lean's; the rows that decline (another number of arguments,
\ a numeral that is no literal, a mode without a spelling) and the failures.
require ./build.fs
require ../../src/present/print-notation.fs

\ The table.
T{ s" HAdd.hAdd" lf-nt-find lf-nt-arity @ -> 6 }T
T{ s" Eq" lf-nt-find lf-nt-prec @ -> 50 }T
T{ s" And" lf-nt-find dup lf-nt-lprec @ swap lf-nt-rprec @ -> 36 35 }T
T{ s" Nat" lf-nt-find 3 lf-nt-sym s" ℕ" compare -> 0 }T
T{ s" Nat" lf-nt-find 1 lf-nt-sym nip -> 0 }T
T{ s" Not.not" lf-nt-find -> 0 }T
T{ lf-notation-version -> 1 }T

\ Terms.
: nat ( -- t ) s" Nat" t-const ;
: nlit ( u -- t ) lf-hterm-cell must drop ;
: num ( u -- t ) s" OfNat.ofNat" t-const nat t-app swap nlit t-app s" inst" t-const t-app ;
: arith ( c-addr u a b -- t )   \ C Nat Nat Nat inst a b
  2>r t-const nat t-app nat t-app nat t-app s" inst" t-const t-app 2r> >r t-app r> t-app ;
: rel ( c-addr u a b -- t )   \ C Nat inst a b
  2>r t-const nat t-app s" inst" t-const t-app 2r> >r t-app r> t-app ;
: eq ( a b -- t ) 2>r s" Eq" t-const nat t-app 2r> >r t-app r> t-app ;
: and. ( p q -- t ) 2>r s" And" t-const 2r> >r t-app r> t-app ;
: or. ( p q -- t ) 2>r s" Or" t-const 2r> >r t-app r> t-app ;
: not. ( p -- t ) s" Not" t-const swap t-app ;
: add ( a b -- t ) s" HAdd.hAdd" 2swap arith ;
: mul ( a b -- t ) s" HMul.hMul" 2swap arith ;
: sub ( a b -- t ) s" HSub.hSub" 2swap arith ;
: pow ( a b -- t ) s" HPow.hPow" 2swap arith ;
: v ( i -- t ) t-var ;
variable cur
: Setup ( -- ) fresh true lf-print-notation! cur @ mode ;

\ Off: the kernel's term, whatever the table says.
fresh false lf-print-notation!
lf-print-unicode mode
T{ fresh false lf-print-notation! lf-print-unicode mode 1 num 2 num add 0 num eq s" Eq Nat (HAdd.hAdd Nat Nat Nat inst (OfNat.ofNat Nat 1 inst) (OfNat.ofNat Nat 2 inst)) (OfNat.ofNat Nat 0 inst)"
   shows -> }T
\ Constants are hidden arguments of their heads only when declared (as before).

lf-print-unicode cur !
T{ Setup 2 num 3 num add s" 2 + 3" shows -> }T
T{ Setup 2 num 3 num add 4 num mul s" (2 + 3) * 4" shows -> }T
T{ Setup 2 num 3 num 4 num mul add s" 2 + 3 * 4" shows -> }T
T{ Setup 2 num 3 num sub 4 num sub s" 2 - 3 - 4" shows -> }T
T{ Setup 2 num 3 num 4 num sub sub s" 2 - (3 - 4)" shows -> }T
T{ Setup 2 num 3 num 4 num pow pow s" 2 ^ 3 ^ 4" shows -> }T
T{ Setup 2 num 3 num pow 4 num pow s" (2 ^ 3) ^ 4" shows -> }T
T{ Setup 1 num 2 num add 0 num eq s" 1 + 2 = 0" shows -> }T
T{ Setup 1 num 2 num eq 3 num 4 num eq and. s" 1 = 2 ∧ 3 = 4" shows -> }T
T{ Setup 1 num 2 num eq 3 num 4 num eq or. 5 num 6 num eq and. s" (1 = 2 ∨ 3 = 4) ∧ 5 = 6" shows -> }T
T{ Setup 1 num 2 num eq 3 num 4 num eq and. 5 num 6 num eq and. s" (1 = 2 ∧ 3 = 4) ∧ 5 = 6" shows -> }T
T{ Setup 1 num 2 num eq 3 num 4 num eq 5 num 6 num eq and. and. s" 1 = 2 ∧ 3 = 4 ∧ 5 = 6" shows -> }T
T{ Setup 1 num 2 num eq not. s" ¬1 = 2" shows -> }T
T{ Setup s" LE.le" 1 num 2 num rel s" 1 ≤ 2" shows -> }T
T{ Setup s" Dvd.dvd" 2 num 4 num rel s" 2 ∣ 4" shows -> }T
\ Nat.succ has no Lean spelling (Lean prints n.succ).
T{ Setup s" Nat.succ" t-const 2 num t-app s" Nat.succ 2" shows -> }T
T{ Setup nat s" Nat" shows -> }T

\ A bound variable, ∀ and ∃ with merged binders.
T{ Setup nat 0 v 0 num add 0 v eq t-pi s" n" ex. s" ∀ (n : Nat), n + 0 = n" states -> }T
T{ Setup s" Exists" t-const nat t-app
   nat 0 v 5 num eq t-lam s" y" ex. t-app s" ∃ y, y = 5" shows -> }T

\ ASCII, LaTeX and mathematical text.
lf-print-ascii cur !
T{ Setup 1 num 2 num add 3 num eq 4 num 5 num eq or. s" 1 + 2 = 3 \/ 4 = 5" shows -> }T
T{ Setup 1 num 2 num eq not. s" Not (1 = 2)" shows -> }T
T{ Setup s" LE.le" 1 num 2 num rel s" 1 <= 2" shows -> }T
\ No ASCII spelling: the kernel's term, with the arguments Lean hides shown.
T{ Setup s" Dvd.dvd" 2 num 4 num rel s" Dvd.dvd Nat inst 2 4" shows -> }T
lf-print-latex cur !
T{ Setup 2 num 3 num mul 4 num add s" 2 \cdot 3 + 4" shows -> }T
T{ Setup 2 num 3 num pow s" 2^{3}" shows -> }T
T{ Setup 2 num 3 num add 4 num pow s" (2 + 3)^{4}" shows -> }T
T{ Setup 1 num 2 num eq not. s" \neg (1 = 2)" shows -> }T
T{ Setup 1 num 2 num eq 3 num 4 num eq and. s" 1 = 2 \wedge 3 = 4" shows -> }T
T{ Setup nat s" \mathbb{N}" shows -> }T
T{ Setup nat 0 v 5 num eq t-lam s" y" ex. s" Exists" t-const nat t-app swap t-app
   s" \exists y,\ y = 5" shows -> }T
lf-print-mathtext cur !
T{ Setup 2 num 3 num mul 4 num add s" 2 · 3 + 4" shows -> }T
T{ Setup 2 num 3 num pow s" 2³" shows -> }T
T{ Setup 2 num 30 num pow s" 2^30" shows -> }T
T{ Setup 2 num 3 num add 2 num pow s" (2 + 3)²" shows -> }T
T{ Setup 2 num 3 num 4 num add pow s" 2^(3 + 4)" shows -> }T
T{ Setup 1 num 2 num eq not. s" ¬(1 = 2)" shows -> }T
T{ Setup nat 0 v 0 num add 0 v eq t-pi s" n" ex. s" ∀ (n : ℕ), n + 0 = n" states -> }T
T{ Setup s" Nat.succ" t-const 2 num t-app s" 2 + 1" shows -> }T
T{ Setup s" Nat.succ" t-const 2 num 3 num add t-app s" 2 + 3 + 1" shows -> }T

\ Declines: the wrong number of arguments, a numeral that is no literal.
lf-print-unicode cur !
T{ Setup s" Eq" t-const nat t-app s" Eq Nat" shows -> }T
T{ Setup nat s" OfNat.ofNat" t-const nat t-app 0 v t-app s" inst" t-const t-app t-lam s" x" ex.
   s" fun x ↦ OfNat.ofNat Nat x inst" shows -> }T
T{ Setup 0 num s" 0" shows -> }T

\ Fuel: a notation counts its operands as the kernel's term would.
lf-print-unicode cur !
T{ Setup 2 num 3 num add cap-reset 1 lf-print-term -> outcome-exhausted }T
T{ Setup 2 num 3 num add cap-reset fuel lf-print-term cap s" 2 + 3" compare -> outcome-ok 0 }T

\ The rows the tests above do not reach, in every mode they have a spelling
\ for (the review's test gap T1). Neg.neg is prefix:75 in Lean: a negation
\ of a negation is - -2, with a space, as Lean 4.35.0 prints it (--2 would
\ start a comment), here in every mode.
: neg ( a -- t ) s" Neg.neg" t-const nat t-app s" inst" t-const t-app swap t-app ;
: mem ( elem coll -- t )   \ Membership.mem Nat Nat inst coll elem: elem ∈ coll
  2>r s" Membership.mem" t-const nat t-app nat t-app s" inst" t-const t-app
  2r> swap >r t-app r> t-app ;
: iff. ( p q -- t ) 2>r s" Iff" t-const 2r> >r t-app r> t-app ;
: succ ( a -- t ) s" Nat.succ" t-const swap t-app ;
\ ∃ name : Nat, body (body under the new binder).
: ex1 ( body c-addr u -- t ) 2>r nat swap t-lam 2r> ex. s" Exists" t-const nat t-app swap t-app ;
\ The text of a term in a mode, the term made afresh by xt ( -- t ); the
\ same text in all four modes (Unicode, ASCII, LaTeX, mathematical text).
: in-mode ( xt mode -- c-addr u ) cur ! Setup execute cap-reset fuel lf-print-term must-ok cap ;
: same-in? ( xt c-addr u mode -- xt c-addr u flag ) 3 pick swap in-mode 2over compare 0= ;
: same4 ( xt c-addr u -- flag )
  true lf-print-mathtext 1+ 0 do i swap >r same-in? r> and loop nip nip nip ;
: n2 ( -- t ) 2 num neg ;
T{ ' n2 s" -2" same4 -> true }T
: nn2 ( -- t ) 2 num neg neg ;
T{ ' nn2 s" - -2" same4 -> true }T
: nnn2 ( -- t ) 2 num neg neg neg ;
T{ ' nnn2 s" - - -2" same4 -> true }T
: n-sum ( -- t ) 2 num 3 num add neg ;
T{ ' n-sum s" -(2 + 3)" same4 -> true }T
: sum-n ( -- t ) 2 num 3 num neg add ;
T{ ' sum-n s" 2 + -3" same4 -> true }T
: dif-n ( -- t ) 2 num 3 num neg sub ;
T{ ' dif-n s" 2 - -3" same4 -> true }T
: n-plus ( -- t ) 2 num neg 3 num add ;
T{ ' n-plus s" -2 + 3" same4 -> true }T
: n-pow ( -- t ) 2 num 3 num pow neg ;
T{ ' n-pow lf-print-unicode in-mode s" -2 ^ 3" compare -> 0 }T
T{ ' n-pow lf-print-mathtext in-mode s" -2³" compare -> 0 }T
: pow-n ( -- t ) 2 num neg 3 num pow ;
T{ ' pow-n lf-print-ascii in-mode s" (-2) ^ 3" compare -> 0 }T
T{ ' pow-n lf-print-latex in-mode s" (-2)^{3}" compare -> 0 }T
: n-mul ( -- t ) 2 num neg 3 num mul ;
T{ ' n-mul lf-print-mathtext in-mode s" -2 · 3" compare -> 0 }T
\ a ∈ b: both operands at 50; no ASCII spelling.
: mem2 ( -- t ) 2 num 3 num mem ;
T{ ' mem2 lf-print-unicode in-mode s" 2 ∈ 3" compare -> 0 }T
T{ ' mem2 lf-print-latex in-mode s" 2 \in 3" compare -> 0 }T
T{ ' mem2 lf-print-ascii in-mode s" Membership.mem Nat Nat inst 3 2" compare -> 0 }T
: in-eq ( -- t ) 1 num 2 num eq 3 num mem ;
T{ ' in-eq lf-print-unicode in-mode s" 1 = 2 ∈ 3" compare -> 0 }T
\ Iff (infix:20 of propositions), Ne (no ASCII spelling), GT and GE.
: iffs ( -- t ) 1 num 2 num eq 3 num 4 num eq iff. ;
T{ ' iffs lf-print-unicode in-mode s" 1 = 2 ↔ 3 = 4" compare -> 0 }T
T{ ' iffs lf-print-ascii in-mode s" 1 = 2 <-> 3 = 4" compare -> 0 }T
T{ ' iffs lf-print-latex in-mode s" 1 = 2 \leftrightarrow 3 = 4" compare -> 0 }T
: ne ( -- t ) 1 num 2 num 2>r s" Ne" t-const nat t-app 2r> >r t-app r> t-app ;
T{ ' ne lf-print-unicode in-mode s" 1 ≠ 2" compare -> 0 }T
T{ ' ne lf-print-ascii in-mode s" Ne Nat 1 2" compare -> 0 }T
T{ ' ne lf-print-latex in-mode s" 1 \ne 2" compare -> 0 }T
: gt ( -- t ) s" GT.gt" 1 num 2 num rel ;
T{ ' gt s" 1 > 2" same4 -> true }T
: ge ( -- t ) s" GE.ge" 1 num 2 num rel ;
T{ ' ge lf-print-unicode in-mode s" 1 ≥ 2" compare -> 0 }T
T{ ' ge lf-print-ascii in-mode s" 1 >= 2" compare -> 0 }T
T{ ' ge lf-print-latex in-mode s" 1 \ge 2" compare -> 0 }T
\ Nat.succ has a spelling only in the mathematical modes.
: succ2 ( -- t ) 2 num succ succ ;
T{ ' succ2 lf-print-unicode in-mode s" Nat.succ (Nat.succ 2)" compare -> 0 }T
T{ ' succ2 lf-print-ascii in-mode s" Nat.succ (Nat.succ 2)" compare -> 0 }T
T{ ' succ2 lf-print-latex in-mode s" 2 + 1 + 1" compare -> 0 }T
\ ¬ of a conjunction: parenthesized (And is infixr:35, below ¬'s 40).
: not-and ( -- t ) 1 num 2 num eq 3 num 4 num eq and. not. ;
T{ ' not-and lf-print-unicode in-mode s" ¬(1 = 2 ∧ 3 = 4)" compare -> 0 }T
T{ ' not-and lf-print-ascii in-mode s" Not (1 = 2 /\ 3 = 4)" compare -> 0 }T
T{ ' not-and lf-print-latex in-mode s" \neg (1 = 2 \wedge 3 = 4)" compare -> 0 }T
\ Three binders merged into one ∃; ASCII's exists.
: ex3 ( -- t ) 0 v 1 v eq s" z" ex1 s" y" ex1 s" x" ex1 ;
T{ ' ex3 lf-print-unicode in-mode s" ∃ x y z, z = y" compare -> 0 }T
T{ ' ex3 lf-print-ascii in-mode s" exists x y z, z = y" compare -> 0 }T
T{ ' ex3 lf-print-latex in-mode s" \exists x\ y\ z,\ z = y" compare -> 0 }T
\ Declines, printed as the kernel's term: a literal too big for a cell, a
\ string literal where OfNat.ofNat has its number, one argument more than
\ the row's (over-application; Lean may print it as (1 + 2) 3, a known
\ difference of the printer), and Exists applied to no lambda.
: big ( -- t )
  s" OfNat.ofNat" t-const nat t-app s" 123456789012345678901234567890" lf-hterm-decimal
  must drop t-app s" inst" t-const t-app ;
T{ ' big lf-print-unicode in-mode s" OfNat.ofNat Nat (literal of 2 limbs) inst" compare -> 0 }T
: strlit ( -- t )
  s" OfNat.ofNat" t-const nat t-app s" ab" lf-str-new must-ok drop t-app s" inst" t-const t-app ;
T{ ' strlit lf-print-unicode in-mode s\" OfNat.ofNat Nat \"ab\" inst" compare -> 0 }T
: over-app ( -- t ) 1 num 2 num add 3 num t-app ;
T{ ' over-app lf-print-unicode in-mode s" HAdd.hAdd Nat Nat Nat inst 1 2 3" compare -> 0 }T
: ex-nolam ( -- t ) s" Exists" t-const nat t-app s" p" t-const t-app ;
T{ ' ex-nolam lf-print-unicode in-mode s" Exists Nat p" compare -> 0 }T
\ A bound variable outside any binder, as an operand: invalid, as without
\ notation.
T{ Setup 0 v 1 num add cap-reset fuel lf-print-term -> outcome-invalid }T
T{ Setup 1 num 0 v add cap-reset fuel lf-print-term -> outcome-invalid }T
T{ Setup 0 v neg cap-reset fuel lf-print-term -> outcome-invalid }T
\ A head whose name is too long for the pool (one component more than
\ lf-name-default): no row, and the print ends full, as with notation off.
: deep-nm ( n -- id ) 0 swap 0 ?do i lf-name-num must loop ;
: deep-app ( -- t )
  lf-name-default 1+ deep-nm lf-name-generation @ cargs 0 lf-cref-new must lf-cterm-new must
  drop 1 num t-app 2 num t-app ;
T{ Setup 256 lf-name-capacity! -> outcome-ok }T
T{ Setup deep-app cap-reset fuel lf-print-term -> outcome-full }T
T{ fresh false lf-print-notation! deep-app cap-reset fuel lf-print-term -> outcome-full }T
T{ fresh lf-name-default lf-name-capacity! -> outcome-ok }T
\ The table names each constant once (lf-nt-find finds the first row).
: rows-unique? ( -- flag )
  true lf-nt-rows begin dup lf-nt-rows-end u< while
    dup lf-nt-name 2@ lf-nt-find over = rot and swap lf-nt-after repeat drop ;
T{ rows-unique? -> true }T
\ Superscript digits in mathematical text: every digit, and 10 as text.
: pow-d ( d -- t ) 2 num swap num pow ;
: sup ( d -- c-addr u ) lf-print-mathtext cur ! Setup pow-d cap-reset fuel lf-print-term must-ok cap ;
T{ 0 sup s" 2⁰" compare 1 sup s" 2¹" compare 2 sup s" 2²" compare 3 sup s" 2³" compare
   -> 0 0 0 0 }T
T{ 4 sup s" 2⁴" compare 5 sup s" 2⁵" compare 6 sup s" 2⁶" compare 7 sup s" 2⁷" compare
   -> 0 0 0 0 }T
T{ 8 sup s" 2⁸" compare 9 sup s" 2⁹" compare 10 sup s" 2^10" compare -> 0 0 0 }T
\ Only a numeral is raised: not another row's application with as many
\ arguments and a literal in the numeral's place.
: pow-ne ( -- t ) 2 num 3 nlit 4 nlit 2>r s" Ne" t-const nat t-app 2r> >r t-app r> t-app pow ;
T{ ' pow-ne lf-print-mathtext in-mode s" 2^(3 ≠ 4)" compare -> 0 }T
bye
