# Forth review of branch demos (20161fb..af64e27), 2026-11-12 — no blocking findings (condensed)
Trust boundary OK (no kernel file loads present/; notation off by default; --kernel). Tests pass on 1.0 and 0.7.3.
1. low: Neg of Neg prints `--a` (print-notation.fs:64, notation-table.fs:137); Lean prints `- -a`. Fix + test.
2. low: notation spells every constant head and scans 22 rows linearly (lf-pn-spell 25-27, lf-nt-find 155); restore of
   lf-pp-used skipped if lf-pp-name-to throws. Hash/first-char guard if profiling shows cost.
3. low: power row prints non-Nat exponents too (harmless).
4. style: deep stack juggling in lf-pn-infix 79-81, lf-pn-binary-body 122-125, lf-pn-power 112-114, lf-pn-binary
   126-128 (13 deep shuffles, 77 return-stack ops / 63 words); factor with a saved frame and named accessors.
5. style: lf-pn-sup-digit CASE ok, add a comment. 6. style: split lf-pn-numeral? (90-96) into ofnat?/literal-arg.
7. style: notation-table.fs:68 load-time variable cursor; :84 lf-nt-last invariant needs a comment; props/tight
   mutate the previous row implicitly.
9. test gaps: Neg, mem, Iff, Ne, GT/GE, Nat.succ in Unicode; ¬(a ∧ b); 3+ binder Exists, ASCII Exists; big literal;
   over-application; loose bound variables; OfNat with non-Nat literal; truncated name pool; table duplicates.
10. docs: text form skipped when LaTeX output is on (statement-forms.fs:169); say so.
