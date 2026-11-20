# Done check: the word divides (2026-11-20)
Checker: done-checker; main 996f686b, ulimit -u 500, nice -n 10, stdin /dev/null, one command at a time.

Verdict: DONE for "A user can write `a b divides` in a .lf theorem; it is Lean's `a ∣ b` (Dvd.dvd), the same term as Lean's sign and as `Dvd.dvd`; by-decide on it stops as documented." Stage: works end to end on Init's snapshot.

| Check | Command | Exit / seen | Result |
| --- | --- | --- | --- |
| 1a | check --snapshot init-1.lfsn --elab-data init.elab.ndjson --steps - divides-done/a.lf (`a b divides  b c divides /\`, by-exfalso by-assumption) | 0; "my_a: accepted ...; axioms: none"; goal "⊢ a ∣ b ∧ b ∣ c" | PASS |
| 1b | same on b.lf: my_b1 with the sign ∣ (copied from reference), my_b2 with `Dvd.dvd` | 0; both "accepted; axioms: none"; goal identical "a b c : Nat\nh : False\n⊢ a ∣ b ∧ b ∣ c" | PASS |
| 1c | same on c.lf `3 12 divides` by-decide | 2; "error 93 ... not supported yet (FE1c)", goal "⊢ 3 ∣ 12"; no verdict | PASS |
| 2 | pinned Lean 4.35.0 lean a.lean (`a ∣ b ∧ b ∣ c := by exfalso; assumption`) | 0, accepted | PASS |
| 3 | make reference-decide-init JOBS=2 | 0; "118 theorems of 11 files accepted ... axioms none, terms node for node pinned Lean's; 4 wrong twins refused; 2 not supported yet" | PASS |
| 3b | grep si_d10 si_d42 | both in sy-vars-init.lf (23, 212), Lean twins goal-layer.lean:205,226, golden :275-278 show Dvd.dvd.{0} Nat/Int + Nat.instDvd/Int.instDvd | PASS |
| 4 | gforth tests/front/front.fs; gforth-fast same | 0 and 0; "front.fs: all tests passed" | PASS |
| 4b | scripts/mutants.py --only rd-divides-other-constant,rd-own-name-unsealed,rd-own-name-meant | 0; 3 run, 3 caught | PASS |
| 5 | `a b |` in a statement (d.lf) | exit 4; "error 81 at 3:7 (token `|`): a tactic word belongs in a tactic proof, after := by" (matches reference's "error 81"); no divisibility read | PASS |
| 5b | divides in kernel-form text | skipped: reference gives no kernel-form divides example (line 711 says natural form only) | NOT RUN |
| 6 | newcomer read of reference, README, showcase | see below | PASS with remarks |

My files: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/divides-done/{a,b,c,d}.lf, a.lean. Equality of term across spellings is shown by the identical step-log goal and the golden terms for si_d10/si_d42 against Lean's dump (reference-decide-init), not by my own term diff.

## Wording (item 6)
- docs/user/LANGUAGE_REFERENCE.md:266 and 268-280: clear how to write `3 12 divides`, that it is a proposition and not `/`. Lines 270-271 say the two characters "the eye cannot tell apart, so do not try to" and give position rules (273 goal, 275 proof-line start): no sentence asks to tell them by eye. Pass.
- README.md:48: "Lean writes it with a sign that looks like the case bar; in LeanForth you type the word": no eye test; does not itself say how to read a bar in a goal vs at line start (only the reference does). Minor.
- decide-showcase.txt:40-43: clear; says "never with a bar". Does not explain the goal-bar rule there (the "How to read a goal" paragraph at 45 follows).
- Unclear point: the error for `3 12 |` (error 81) says "a tactic word belongs in a tactic proof, after := by"; it does not mention divides. Reference line 279-280 promises the refusal, which holds, but a user gets no hint to use `divides`. Suggest adding "(for divisibility write divides)" to the message or noting this at LANGUAGE_REFERENCE.md:280.
- LANGUAGE_REFERENCE.md:277-278 "Lean's sign is read too": shown by my_b1 in statement position (postfix after two values), fine.

## Limits
- Init snapshot only; no Mathlib. by-decide on divisibility not supported (documented README.md:56, reference 1519, showcase 42). Not run: tiers, CI, coverage, the Forth review log (not part of this check), kernel-form divides.

## Added by the coordinator (2026-11-20)

- The tier the checker did not run: `make tier` exit 0 on the branch's final head d586c746 (cover-changed, make test,
  make test-unit on gforth-fast, check-rest, the branch's 5 planted faults, all caught); `scripts/push.sh` recorded the
  push of 996f686b in docs/development/ci-results.log.
- Its two wording points: the README now says under its symbol table how to read a bar in a goal and a bar at the
  start of a proof line; the hint in error 81 ("for divisibility write divides") joins plan 9.4.8l (BD).

