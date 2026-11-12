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
bye
