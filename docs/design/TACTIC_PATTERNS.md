# Case patterns: obtain, rcases, rintro, subst, cases, injection (piece E)

Status (2026-11-22): **second version, after the independent review ([report](../development/design-reviews/2026-11-22-tactic-patterns.md), approve with changes; all applied, see the end); no code.** Plan row TB2, piece E. LeanForth paths are
relative to `src/front/`, Lean's to the pinned toolchain's `src/lean/`. All of it is untrusted front-end code: a
tactic only builds a term; only the kernel accepts a proof.

## 0. One page for the owner

**What the user can write after each slice** (full table in section 2).

| Slice | Lean | LeanForth |
|---|---|---|
| E1 | `obtain ⟨x, hx⟩ := h` ; `obtain ⟨x, hx⟩ := foo a` | `' h by-obtain[ << x hx >> ]` ; `' foo ' a $ by-obtain[ << x hx >> ]` |
| E1 | `rcases h with ⟨x, hx⟩ \| h'` ; `rcases n with _ \| n` | `' h by-rcases[ << x hx >> \| h' ]` ; `' n by-rcases[ _ \| n ]` |
| E2 | `subst h` ; `subst_vars` ; `obtain ⟨x, rfl⟩ := h` | `' h by-subst` ; `by-subst-vars` ; `' h by-obtain[ << x rfl >> ]` |
| E2 | `rintro ⟨a, b⟩ (c \| d)` ; `by_contra ⟨a, b⟩` | `by-rintro[ << a b >> c \| d ]` ; `by-contra[ << a b >> ]` |
| E3 | `cases h with \| inl hp => t \| inr hq => u` | `' h by-cases-with` / `\| inl hp => t` / `\| inr hq => u` / `by-end` |
| E4 | `injection h with h₁ h₂` ; `obtain ⟨⟩ := h` (h : n + 1 ≤ 0) | `' h by-injection[ h1 h2 ]` ; `' h by-obtain[ << >> ]` |

**How it works, in Forth terms.** Lean has two layers, and LeanForth ports both. Below, goal operations: *cases* (a
goal per constructor), *subst* (replace a variable by what an equation says), *unify* the equations a split leaves.
Above, tactics: `obtain`, `rcases`, `rintro` walk a pattern and call the lower *cases* per bracket; Lean's `cases`
tactic drives `by-induction`'s eliminator and adds equations it then unifies (probe p6: different proof terms, so
neither stands in for the other). Lean's walk is a chain of continuations; LeanForth's a flat loop over a task stack.
A pattern is read once, by a parsing bracket word, into a postfix run of nodes: children first, the parent after.

**Size.** About 2,150 Forth lines for E1-E4 and 2,370 with E5 (comments counted as today's files count them). By the
measured cost of the TB2 batches (1.13-1.53M tokens each, all in), expect 1.2-1.6M tokens per slice, 5-6.5M for E1-E4.

**Questions for the owner** (each with my recommendation):
1. Lean's `cases` as `' h by-cases` and `' h by-cases-with ... by-end`, beside Lean's `by_cases`, already `p by-cases:
   h`. *Recommend yes*: Lean's names, as you chose for `by-cases:`; a mix-up fails at once, and on a proposition with
   Lean's own hint "Consider using the 'by_cases' tactic".
2. `rcases` and `obtain` both, value first: `' h by-rcases[ pat ]`, `' h by-obtain[ pat ]` (Lean's `obtain pat := h`
   is exactly `rcases h with pat`). *Recommend both*: Mathlib users look for both names.
3. **Patterns: Lean's without commas and without parentheses.** A bar binds tighter than a space, so `a | b` is one
   item: `<< a b | c rfl >>` is Lean's `⟨a, b | c, rfl⟩`, `by-rintro[ a | b c ]` is Lean's `rintro (a | b) c`, and
   the one group Lean needs, alternatives inside alternatives, is a tuple: `<< a | b >> | c` is `(a | b) | c`
   (section 2). A spelling difference, not a difference in what is accepted. `(` stays Forth's comment; a bar in an
   open bracket list is a pattern bar, also at a line's start, and only outside brackets begins an alternative.
   *Recommend yes*: Lean users drop commas and parentheses. The price: a habitual `( a | b )` is a comment (section 7).
4. (For E5 only.) Typed pieces, `⟨k, hk : n = k + 1⟩` and rintro's `(x y : T)` (about 860 lines), and `@pat` (127):
   a postfix term has no end inside a pattern, so they need a group bracket word, proposed in E5. Until then they have
   no form. *Recommend deciding in E5* with a measured count.
5. (For E5 only.) `obtain pat : T := e` and `obtain pat : T`: proposed `T e by-obtain-as[ pat ]` and `T by-obtain-goal[
   pat ]`, after `by-have:` and `by-have-goal:`. *Recommend deciding in E5.*

**Risks.** (a) A name Lean hides or a tag Lean does not give, made usable, accepts text Lean rejects: section 6
names a twin or fault for each. (b) E1 is about 950 lines (cut line in section 5). (c) The tests need a new export.

## 1. The machinery: Lean's layers, what LeanForth has, what is new

| Lean (file:line) | What it does | LeanForth today | New, slice |
|---|---|---|---|
| `MVarId.cases` Meta/Tactic/Cases.lean:278-319; simple case :290-293; `inductionCasesOn` :252, `Nat.casesAuxOn` chosen when present :270 | the split under obtain, rcases, contradiction | none | meta-tactic/cases.fs, E1 (independent indices), E4 (indexed) |
| `MVarId.induction` Meta/Tactic/Induction.lean:203; `finalize` :57-122 (tag :84, names :110, extras :111); `getMajorTypeIndices` :136; `mkRecursorAppPrefix` :166 | revert indices, major premise and dependents; apply the recursor; re-introduce per alternative | `lf-goal-revert` (meta-tactic/revert.fs:101, preserveOrder false), `lf-goal-intro-n` (meta-tactic/goal.fs:294) | meta-tactic/meta-induction.fs, E1 |
| `mkRecursorInfo` Meta/RecursorInfo.lean:186-226 (major = the motive's last argument :105-110) | positions of parameters, motive, indices, major, minors, read from the declaration's type | `lf-elim-info` (meta-tactic/elim.fs:211), one target only | `lf-recursor-info`, E1 |
| `FVarSubst` Meta/Tactic/FVarSubst.lean | which old variable became which term | none | fvar-subst.fs, E1 |
| `MVarId.generalize` Meta/Tactic/Generalize.lean:28-76 | a term replaced by a new variable (instances transparency, then `isTypeCorrect`) | `lf-meta-kabstract` (kabstract.fs:6), `lf-mk-forall-fvars` (telescope.fs:42) | meta-tactic/generalize.fs, E1 |
| `RCasesPatt` Elab/Tactic/RCases.lean:66-78; `processConstructor(s)` :214/:237; `rcasesCore` :270; `rcasesContinue` :353; `finish` :377; `rcases` :423; `rintroCore` :483 | patterns and their walk | shapes and `lft-binders]` (tactic-syntax.fs:311), `lf-tac-intro1` (tactic-core.fs:248) | rcases.fs, pattern-syntax.fs, E1 (E2: `rfl`, rintro) |
| `substCore` Meta/Tactic/Subst.lean:17; `heqToEq` :122; `substVar` :144; `substEq` :173 (reduced side :181-196); `subst` :201; `substVars` :282-292; `evalSubst` Elab/Tactic/BuiltinTactic.lean:500 (let variable :503-513) | `Eq.rec`/`Eq.ndrec` over the reverted goal | `lf-mk-eq`, `lf-mk-eq-refl`, `lf-mk-eq-symm` (app-builder.fs:163-166), `lf-match-eq?` :319, `lf-match-heq?` :357, `lf-depends-on?` (mvars.fs:870) | meta-tactic/subst.fs, E2 |
| `elimEmptyInductive` Meta/Tactic/Contradiction.lean:66 | rule 6: cases repeated under fuel 16 | `lf-goal-contradiction` answers 99 there | E2 (no index), E4 (indexed) |
| `evalCasesCore` Elab/Tactic/Induction.lean:1105-1130 (equations :1117, `numEqs` :1130); `evalAlts` :340 | Lean's `cases` tactic | `lf-elim-for` (elim.fs:185), `lf-elim-app` :261, `lf-elim-set-motive` :283, `lf-eval-alts`, `tal-cleared` (tactic-alts.fs:161) | several targets, equations per alternative, E3 |
| `generalizeTargetsEq` Cases.lean:49; `unifyEq?` Meta/Tactic/UnifyEq.lean:48; `unifyEqs?` Cases.lean:231 | target equations and their unification | none | meta-tactic/cases.fs, unify-eq.fs, E3 (subst, skip), E4 (injection, offset) |
| `injectionCore` Meta/Tactic/Injection.lean:27; `mkNoConfusion` Meta/AppBuilder.lean:450; `isConstructorApp'?` Meta/CtorRecognizer.lean:46; `generalizeIndices'` Cases.lean:92 | constructor equations; indexed families | private constructor tests: contradiction.fs `mcd-ctors` :123, whnf.fs `wc-ctor-app?` :749 | ctor-app.fs, no-confusion.fs, injection.fs, E4 |
| `acyclic` Meta/Tactic/Acyclic.lean:27 | `x = c … x …` impossible, by `sizeOf` | none | E5 (99 until then) |

**Contradiction's two gaps.** Rule 6 is the lower *cases* after `exfalso`, repeated on new fields (fuel 16): closed
for types without index in E2, for indexed families (equations solved by injection and no-confusion) in E4. Rule 4
(different constructors equated) needs only `mkNoConfusion` (E4).

## 2. Words and forms

| Lean | LeanForth | Slice |
|---|---|---|
| `obtain pat := e` ; `rcases e with pat` | `e by-obtain[ pat ]` ; `e by-rcases[ pat ]` (one value; one pattern) | E1 |
| `rintro p₁ p₂ …` | `by-rintro[ p1 p2 ... ]` (one or more items) | E2 |
| `by_contra pat` (Batteries: `by_contra_core; rintro pat`) | `by-contra[ pat ]` | E2 |
| `subst h` ; `subst h₁ h₂` ; `subst_vars` | `' h by-subst` ; `by-subst[ h1 h2 ]` ; `by-subst-vars` | E2 |
| `cases e` ; `cases e with \| c x => tac …` (and induction's dependents) | `e by-cases` ; `e by-cases-with` / `\| c x => ...` / `by-end` | E3 |
| `injection h` ; `injection h with a b` | `' h by-injection` ; `' h by-injection[ a b ]` | E4 |
| `@pat`, typed pieces, `rcases h₁, h₂ with …`, obtain's typed forms, `cases h : e` | no form until E5 | E5 |

**Pattern grammar** (Lean's `rcasesPat`, Init/RCases.lean; each Lean alternative is one item, :68):

    item     := NAME | "_" | "-" | "rfl" | "<<" { element } ">>" | "⟨" { element } "⟩"
    element  := item { "|" item }          items joined by bars: Lean's alternatives (rcasesPatMed)
    by-obtain[ by-rcases[ by-contra[ :  exactly one element, then "]"
    by-rintro[                       :  one or more elements, then "]"  (each element one rintro pattern)

Two top levels, as Lean has (review 4): rcases, obtain and by-contra take one element (Lean's `rcases h with a b` is a
parse error, probe p2); rintro takes a sequence, each element one introduced pattern. Lean's rintro has no bare bar
(probe p3) and writes `(a | b)`; LeanForth's element is the same pattern without the parentheses. An untyped rintro
group `(x y)` is the same as its items in a row (rintroContinue), so it is written `x y`.

**Translation, both ways.**

| Lean | LeanForth | Why |
|---|---|---|
| `rcases h with a \| b` ; `rcases h with (a \| b)` | `by-rcases[ a \| b ]` | a top-level group is the pattern itself (`rcasesCore` unwraps `paren`) |
| `⟨a, b \| c, rfl⟩` ; `⟨a, (b \| c), rfl⟩` | `<< a b \| c rfl >>` | commas become spaces; a group as a field is its inside |
| `a \| (b \| c)` | `a \| b \| c` | the last constructor takes the remaining alternatives (`processConstructors` :245) |
| `(a \| b) \| c` | `<< a \| b >> \| c` | a group as an alternative is read through `asTuple` (:108-112), as a one-element tuple is |
| `⟨a \| b⟩` | `<< a \| b >>` | a tuple, as in Lean |
| `rintro (a \| b) c` ; `rintro (x y) -` | `by-rintro[ a \| b c ]` ; `by-rintro[ x y - ]` | rintro's group spelled as its inside |
| `(h : T)`, `⟨k, hk : T⟩`, `rintro (x y : T)`, `@⟨a, b⟩` | no form until E5 | question 4 |

Back to Lean: an element `a | b` is `a | b` at the top of rcases, `(a | b)` in rintro, `b | c` in a tuple;
`<< a | b >>` is `⟨a | b⟩`, which as an alternative equals `(a | b)` (from reading; E1's twins pin it).

**One rule for bars** (also added as a note to TACTIC_BLOCKS.md, whose consumers row at :111 said the reader's bar
word would ask an open bracket): inside an open bracket list a bar is that list's item (a pattern bar), also at a
line's start; outside brackets a bar at a line's start begins an alternative. The pattern bracket reads its own
tokens, so its bars never reach `lft-w-bar`; TACTIC_BLOCKS needs no change of mechanism.

**The reader** (pattern-syntax.fs): a plain loop without lookahead on batch 3c's multi-line list reader (which skips
`( … )` as Forth does; `|`, `-`, `_`, `rfl`, `<<`, `>>`, `⟨`, `⟩` are taken as items before its reserved-word stop).
An item ends the open element unless the join flag is set (then it joins and clears it); `|` sets the flag (error
with no element open or the flag set); `<<` pushes a reader frame; `>>`, `⟩`, `]` end the element and close their
frame (error with the flag set, on a mismatch, `]` with a tuple open); a LeanForth word as a NAME is 84. An element
of several items emits an *alts* node, `>>` a *tuple* node, postfix in the step's arguments with each node's span, so
a walker steps back over children's spans: a loop. A depth limit has its own error; `@` is refused until E5.

## 3. Lean fidelity

Each word is a port of the function named and is compared with pinned Lean node for node (the term) and goal for
goal (the step log). What must match exactly:

- **Goal order.** rcases: depth first (probe p4): for each subgoal of a split, in constructor order, the rest of the
  pattern list before the next subgoal; `align` (RCases.lean:336-343) matches patterns to subgoals by constructor
  name, skipping patterns of constructors whose goal was solved. The task stack is pushed in reverse to give this.
  cases: alternatives in constructor order, a solved one dropped.
- **Tags** (review 1). Meta induction tags each new goal with the parent's tag plus the constructor's name, **or the
  parent's tag alone when the recursor has one minor premise** (Induction.lean:84). So `obtain ⟨hp, hq⟩ := h` leaves
  no `intro` tag (probe p1: Lean's "Case tag `intro` not found"); splits nest as `inl.inl`, `inl.inr`, `inr.inl`,
  `inr.inr` (p4). Lean's `cases` tactic tags by `mkElimApp` (exists).
- **Names.** rcases passes `AltVarNames` with `explicit := true` (RCases.lean:248): the pattern names every field,
  except an implicit field without `@`, which gets `_` (:217). `finalize` introduces fields with `introN` and
  `useNamesForExplicitOnly := !explicit` (Induction.lean:110). `_` or a missing pattern gives the binder's own name,
  inaccessible (`lf-goal-intro-n`'s name 0). The last field takes the remaining patterns as a tuple (:225-227).
- **Hidden names stay hidden** (review 2). Lean's `introNP` keeps each reverted name as it was, inaccessible ones
  too (probe p1: `intro x h _; subst h; exact hx` is "Unknown identifier `hx`"); an anonymous binder gets a fresh
  inaccessible `a` (Intro.lean:116). LeanForth's flag lives on the local (lctx-views.fs:87), a reverted binder keeps
  only name and kind (telescope.fs:201); so revert returns names and flags and every name-keeping re-intro takes them
  back: substCore's rest, Meta induction's major and extras, generalizeIndices, heqToEq's and substReduced's.
- **Reverted and re-introduced.** substCore reverts variable, equation and dependents in order (Subst.lean:34),
  builds `Eq.rec` when the goal depends on the equation, else `Eq.ndrec` (the `_h : b = a` motive for symm false,
  :89-110), clears both, re-introduces the rest; nothing when it may skip (:44-56). The `FVarSubst` maps each old
  variable to its new term; rcases applies it to every pending target (RCases.lean:276).
- **substEq** (Subst.lean:173-199): heqToEq first; the right side after whnf a variable: eliminated (symm true); if
  whnf changed it, the reduced equation is asserted, re-introduced, the old one cleared, then substituted (:181-196,
  review 5); else the left side the same way; else Lean's error. `rfl` in a pattern calls this: `n = m` eliminates
  `m` (p4).
- **subst h** (BuiltinTactic.lean:500-517): each name in turn; a let variable unfolded (:503-513; LeanForth: 99 at
  first, revert.fs refuses lets); else an equation through substEq, an `HEq` through heqToEq, a variable through
  substVar (right side first). **subst_vars** (Subst.lean:282-292): each local in context order, the first that
  succeeds, repeated; a test pins the order with a variable declared before its equation.
- **unifyEq?** (UnifyEq.lean:48-140), in Lean's order: HEq to Eq; a variable side: substCore under `observing?` (its
  failure is caught, nothing else), else defeq skip, else acyclic, else "Dependent elimination failed"; two variables:
  the later-declared one eliminated (:127-133); two terms: defeq skip, offset, injection, whnf both and retry, error.
- **Clearing.** rcases clears `-` items and everything depending on them at the end of each goal (`tryClearMany'`
  :365), a refusal keeping the goal; cases try-clears its new targets (`tal-cleared`).
- **Nat** (review 6). rcases asks for `Nat.casesAuxOn` (Cases.lean:270), a plain definition (Init/Data/Nat/
  Basic.lean:49), when the environment has it: fields show as `0` and `n + 1`. Its recursor info is read from its
  type, the major premise being the motive's last argument (RecursorInfo.lean:105-110), so `lf-recursor-info` reads
  any declaration's type, never the inductive's record.
- **No-confusion sees only Lean's declarations.** `mkNoConfusion` looks up `T.ctorIdx` and `C.noConfusion` in the
  export's environment, never ctor-idx.fs's builder, which makes ctorIdx for twelve types Lean has none for.
- **Errors**: Lean's text (appendix B), a new code each in author/errors.fs, the goal after a blank line as
  `throwTacticEx` prints it; cases' are wrapped as "Tactic `cases` failed with a nested error:" and the inner message
  (Meta/Tactic/Util.lean:55-57). A target term that does not elaborate goes through `lf-tac-elab-fail`, the logged
  class of TACTIC_BLOCKS.md.

## 4. Reuse, new words, consumers, sizes

**Reused.** elim.fs's four words and tactic-alts.fs's `lf-eval-alts`, `lf-alt-run`, `lf-alts-missing`;
`lf-goal-revert` (revert.fs:101), `lf-goal-intro-n` (goal.fs:294), `lf-goal-clear!`, `lf-goal-try-clear`,
`lf-goal-assert`, `lf-goal-exfalso` (goal.fs:195, rule 6's first step), `lf-goal-new`, `lf-name-append-tag`;
`lf-mk-eq`, `lf-mk-eq-refl`, `lf-mk-eq-symm` (app-builder.fs:163-166), `lf-mk-app-m` (:301), `lf-mk-app-n`,
`lf-mk-false-elim`; `lf-match-eq?`, `lf-match-heq?`, `lf-match-const-induct` (meta-must.fs:214); `lf-commit-when`
(meta-must.fs:42: `observing?`/`commitWhen` in unifyEq?, rule 6, tryClear); `lf-meta-fun-info` (fun-info.fs:205:
`getFunInfo`); `lf-meta-offset`, `lf-meta-ctor-if-lit` (nat-offset.fs:236, :256); `lf-meta-level-normalize` (the
motive's universe); `lf-depends-on?`; `lf-meta-abstract`, `lf-meta-instantiate1`, `lf-meta-kabstract`,
`lf-mk-lambda-fvars`, `lf-mk-forall-fvars`, `lf-with-local-decl`, `lf-with-record`; lib/runs.fs for every list; the
library stack (FORTH_LIBRARY.md "Stacks, outcome loops and index checks") for tasks and reader frames; batch 3c's
list reader; rows, shapes, `lf-tactic-seq:`.

**New library words** (public, documented in the file header, tested in the file's own unit test):

| Word | Home | Slice |
|---|---|---|
| `lf-fsubst-insert ( fs fvar e -- fs' )`, `lf-fsubst-get ( fs fvar -- e )`, `lf-fsubst-apply ( fs e -- e' )`, `lf-fsubst-append ( fs1 fs2 -- fs )`, `lf-fsubst-erase ( fs fvar -- fs' )`; 0 is empty | new fvar-subst.fs (a run of pairs) | E1 |
| `lf-goal-revert-kept ( goal fvars -- goal' kept )` (order kept; kept: each reverted local's name and flags, a run); `lf-goal-intro-kept ( goal kept n -- goal' xs )` (introNP with those names and the inaccessible flag; an anonymous binder a fresh inaccessible `a`) | revert.fs, goal.fs | E1 |
| `lf-recursor-info ( d -- info )` (mkRecursorInfo from d's type); `lf-goal-induction ( goal major d names -- subgoals )` (subgoals: a run of goal, fields, substitution, constructor) | new meta-tactic/meta-induction.fs | E1 |
| `lf-goal-cases ( goal major names nat-aux? -- subgoals )` (independent indices in E1, 99 otherwise) | new meta-tactic/cases.fs | E1, E4 |
| `lf-goal-generalize ( goal args -- fvars goal' )` | new meta-tactic/generalize.fs | E1 |
| `lf-mk-eq-rec`, `lf-mk-eq-ndrec ( motive minor major -- e )`, `lf-mk-heq ( a b -- e )`, `lf-mk-heq-refl ( a -- h )`, `lf-mk-eq-of-heq`, `lf-mk-heq-of-eq ( h -- h' )`; `lf-replace-fvar ( e fvar v -- e' )` | app-builder.fs, instantiate.fs | E2 |
| `lf-goal-subst-core ( goal h fs flags -- fs' goal' )` (flags: symm, clear, try-skip), `lf-goal-heq-to-eq ( goal h -- h' goal' )`, `lf-goal-subst-eq ( goal h fs -- fs' goal' )`, `lf-goal-subst-var ( goal x -- goal' )`, `lf-goal-subst ( goal h -- goal' )`, `lf-goal-subst-vars ( goal -- goal' )` | new meta-tactic/subst.fs | E2 |
| `lf-goal-generalize-targets-eq ( goal motive-type targets -- goal' )`; `lf-goal-unify-eq ( goal eq fs ctor -- goal' fs' n true \| false )`, `lf-goal-unify-eqs ( goal n fs ctor -- goal' fs' true \| false )` | cases.fs, new meta-tactic/unify-eq.fs | E3 |
| `lf-ctor-app? ( e -- ctor args true \| false )`; `lf-mk-no-confusion ( target h -- e )`; `lf-goal-injection-core ( goal h -- goal' n true \| false )`, `lf-goal-injection ( goal h names -- goal' eqs names' true \| false )`; `lf-goal-generalize-indices ( goal fvar -- record )` | new ctor-app.fs, no-confusion.fs, meta-tactic/injection.fs, cases.fs | E4 |

**Elaborator layer** (LF_LIBRARIES.md's tactic library): rcases.fs (`lf-rcases ( goal targets pat -- goals )`,
`lf-rintro ( goal pats -- goals )`, processConstructors, the task loop, finish) and pattern-syntax.fs; tactic-syntax.fs
exports `tac-shape-new ( n k build-xt -- shape )` (private `lft-shape`, :281), so the reader adds no runner kind.

**Copies replaced.** `mcd-ctors` (contradiction.fs:123) and `wc-ctor-app?` (whnf.fs:749) by `lf-ctor-app?` (E4);
by-contra.fs's "rintro of one name is intro" by `lf-rintro` (E2); `tind-fvar`, `tind-independent`
(tactics/induction.fs:31-41) by E3's shared targets; E1 shares elim.fs's binder walk (`mel-head`, `mel-ends`,
:189-211) between `lf-elim-info` and `lf-recursor-info`.

**Consumers** (who else calls these layers):

| Later work | What it calls |
|---|---|
| contradiction rules 4 and 6 (E2, E4) | `lf-goal-cases`, `lf-mk-no-confusion`, `lf-goal-exfalso` |
| `intro ⟨a, b⟩`, `match` patterns (FE7) | the lower cases and subst, FVarSubst |
| `induction … generalizing`, `using` (E5) | `lf-goal-revert-kept`, `lf-goal-intro-kept` |
| `injections`, `subst_eqs`, `split` (later rows) | `lf-goal-injection`, `lf-goal-subst-eq`, `lf-goal-cases` |
| Mathlib `ext ⟨a, b⟩`, `fin_cases` (340 lines), `cases'` (2) | rintro patterns; `lf-goal-cases` |
| `by-intro[ ]` with patterns (TACTIC_STATUS row) | Lean's `intro` pattern is `match` (FE7), not rcases |

**Sizes.** Basis: ported files run at about 1.3 Forth lines per Lean code line (elim.fs: 284 lines for about 210
Lean lines; revert.fs: 112 for 84).

| Slice | Pieces | Forth lines |
|---|---|---|
| E1 | FVarSubst 50; revert-kept and intro-kept with the flag 60; recursor info 80; Meta induction 230; Meta cases, simple path 70; generalize 60; reader 90; rcases walk, finish, obtain and rcases rows 310 | **about 950** |
| E2 | app-builder words and replace-fvar 35; subst family with the reduced path 280; rows 25; `rfl` in the walk 15; rintro 50; by-contra pattern 10; rule 6 without indices 40 | **about 455** |
| E3 | unifyEq? (subst and skip) and unifyEqs? 90; generalizeTargetsEq 50; several targets in elim.fs 40; equations and clears in evalAlts 40; dependents for induction 40; rows 30 | **about 290** |
| E4 | ctor-app 40; mkNoConfusion 75; injection 115; unifyEq's offset and injection 50; generalizeIndices and the indexed path 150; rules 4 and 6 indexed 30 | **about 460** |
| E5 | acyclic 60; group bracket for typed pieces and `@` 80; several targets, obtain's typed forms, `cases h : e`, Quot 80 | **about 220** |

Tokens, from measured batch totals (the coordinator's cost table of 2026-11-21 and 22: implementer 600-940k, review 110-204k, fix
round 290-400k, checks about 100k): 1.2-1.6M per slice. E1, the largest, is likely at or above the top.

## 5. Slices

Each slice ends in `bin/leanforth check FILE.lf` on its `.lf` files and the pinned-Lean twin run (`NAME.lean`, and a
wrong twin `NAME-wrong.lean` that pinned Lean rejects), with `test.fs`, `check.py`, `steps.golden` and
`faults.d/batch-X.toml` in its folder, its TACTIC_STATUS.md rows, LANGUAGE_REFERENCE.md entries and `make
cover-changed`. Each library word's unit test includes a refusal sweep (`tests/support/meta-sweeps.fs`).

**The export.** tactic_check.py uses s2-slice by default, which lacks `Nat.casesAuxOn`; decide-slice has it, and
neither has `Nat.Internal.elimOffset` (text search). E1 adds `tests/front/patterns-slice` (a roots file, built as
decide-slice's was), which every E batch passes to `tactic_check.main`, holding `Nat.casesAuxOn`,
`Nat.Internal.elimOffset`, `noConfusion_of_Nat`, `T.ctorIdx` and `C.noConfusion` for the types tested (Or has no
ctorIdx), `Eq.rec`, `Eq.ndrec`, `Eq.symm`, `HEq`, `eq_of_heq`, `heq_of_eq`, `And`, `Or`, `Exists`, `Iff`, `Subtype`,
`Nat.le`, `False`, `Empty`, `List.Mem`; a unit test fails when its manifest lacks one.

**E1, `tests/front/tactics/batch-g/`: obtain and rcases (about 950 lines).** `by-obtain[ ]`, `by-rcases[ ]` with
names, `_`, `-`, tuples, alternatives, Nat; `rfl` answers 99. Mathlib: obtain 19,128 lines, rcases 8,512. Files:
`obtain.lf` (∃, ∧ nested, a term generalized, more and fewer patterns than fields, `-`), `rcases.lf` (three
alternatives, Or in And, `_ | n` on Nat), `nest.lf` (`<< a | b >> | c` and `a | b | c` on `(p ∨ q) ∨ r` and `p ∨ (q ∨
r)`, with Lean twins), `order.lf` (depth first; tags `inl.inl` to `inr.inr`), `hidden.lf`, `pattern-errors.lf` (each
reader refusal; `rcases h with a b`; not a free variable; not inductive; `( a | b )` pinned as a comment).
Wrong twins: `w-tag-intro` (`case intro =>` after a one-constructor obtain: 210 as Lean's "not found"),
`w-hidden-extra` (a dependent hypothesis with a hidden name, re-introduced by the split, then named), `w-clear-used`
(a `-` item named later), `w-order` (the second goal proved first). Faults:
`tag-ctor-on-single`, `intro-kept-drops-flag`, `bar-binds-looser`, `align-no-skip`, `last-field-no-rest`,
`tasks-in-text-order`, `clear-too-early`, `fsubst-not-applied`, `rcases-top-as-sequence`. Cut line if it runs long:
`-` and Nat move to E2. Starts after batch 3c merges (the reader); the Meta words can start now.

**E2, `tests/front/tactics/batch-h/`: subst, `rfl`, rintro, by-contra, rule 6 (about 455 lines).** `' h by-subst`,
`by-subst[ ]`, `by-subst-vars`, `rfl` in patterns, `by-rintro[ ]`, `by-contra[ ]`, `by-contradiction` on types without
constructor or index. Mathlib: rintro 7,776; `rfl` in 12,403 pattern lines; subst 1,087; subst_vars 115. Files:
`subst.lf` (both sides, two variables, a dependent goal and hypothesis, HEq, `h : n = id m` (reduced path), several
names; a let: 99), `subst-vars.lf`, `rfl.lf`, `rintro.lf`, `empty.lf`, `subst-errors.lf`. Wrong twins:
`w-hidden-subst` (probe p1's `intro x h _; subst h; exact hx`), `w-hidden-reduced`, `w-hidden-heq` (the same
through substReduced and heqToEq), `w-subst-var-used` (the eliminated variable named), `w-rintro-group` (a proof right
only if `a | b c` grouped as Lean's `(a | b c)`; Lean's `rintro (a | b) c` rejects it). Faults: `subst-left-first`,
`skip-rec-when-dependent`, `reduced-path-skipped`, `dependent-not-reintroduced`, `rintro-top-as-one`,
`subst-vars-order`.

**E3, `tests/front/tactics/batch-i/`: cases and induction's dependents (about 290 lines).** `by-cases`,
`by-cases-with`; `by-induction` with dependents and index targets. Mathlib: cases 4,532 (765 with `with`). Files:
`cases.lf` (Or, And, Exists, Nat, Bool, a structure, a dependent, names, missing and duplicate alternatives),
`cases-errors.lf`, `induction-deps.lf`. Wrong twin: `w-cases-old-target` (the cleared target used).
Faults: `eqs-not-unified`, `target-not-cleared`, `numeqs-off-by-one`, `observing-too-wide`. Needs blocks only for
`by-cases-with`: on TACTIC_BLOCKS slice 1's `tac-shape-block` it is a row; without it, a fixed kind beside `tac-k-with`
(10 lines in tactic-syntax.fs). Recommend E3 after blocks slice 1.

**E4, `tests/front/tactics/batch-j/`: indexed families, injection, contradiction (about 460 lines).** Words `'
h by-injection`, `' h by-injection[ ]`; the four pattern and cases words on indexed families; contradiction rules 4
and 6 complete. Files: `injection.lf` (fields, names, too many names, different constructors, literals), `indexed.lf`
(`obtain ⟨⟩ := h` with `h : n + 1 ≤ 0`, `cases` on `Nat.le`, an index that is not a variable), `contradiction.lf` (the
two gaps). Wrong twins: `w-dep-elim`, `w-hidden-indices` (generalizeIndices' re-intro), `w-noconf-decidable` (two constructors of
`Decidable`, which has no ctorIdx in Lean: Lean's "Missing Decidable.ctorIdx"). Faults: `noconf-equal-ctors`,
`prop-fields-counted`, `index-eq-dropped`, `aux-indices-kept`, `ctoridx-from-builder`, `solved-alt-kept`,
`solved-alt-unassigned`.

**E5, `tests/front/tactics/batch-k/`: the rest (about 220 lines).** acyclic, the group bracket for typed pieces and
`@`, several targets, obtain's typed forms, `cases h : e`, Quot; spellings decided first (questions 4, 5).

**Work in flight.** Batch 3c changes 19 source files (author/runner.fs, scopes.fs, elab-term.fs, tactic-syntax.fs
among them); its list reader stops at reserved words (3c's tactic-syntax.fs:319-321), so the pattern items change that
reader. That and the `tac-shape-new` export edit tactic-syntax.fs, which blocks slice 1 also changes: batch 3c first,
then blocks slice 1 or E1's reader commit, the other rebased. E1's Meta words touch none of these files.

## 6. Trust and gates

Nothing here changes `src/kernel`, `src/core` or the import path; no gate question arises. Every split assigns its goal
a term (`casesOn`, `Eq.rec`, `noConfusion`, `False.elim`) that the kernel checks at the end. Where LeanForth could
accept a text Lean rejects, and the guard by name:

| Risk | Guard |
|---|---|
| a tag Lean does not give (`intro` on one constructor) | twin `w-tag-intro`; fault `tag-ctor-on-single` |
| a hidden name made usable on a re-intro | twins `w-hidden-extra` (E1), `w-hidden-subst`, `w-hidden-reduced`, `w-hidden-heq` (E2), `w-hidden-indices` (E4); fault `intro-kept-drops-flag` |
| a cleared or eliminated hypothesis left | twins `w-clear-used` (E1), `w-subst-var-used` (E2), `w-cases-old-target` (E3) |
| goal order | twin `w-order` (E1); fault `tasks-in-text-order` |
| rintro's grammar (two top levels; a bar tighter than a space) | twin `w-rintro-group` (E2); faults `rintro-top-as-one`, `rcases-top-as-sequence`, `bar-binds-looser`; `rcases h with a b` refused in `pattern-errors.lf` |
| a goal dropped without a term | only a solved alternative and no-confusion drop a goal, each after assigning it; fault `solved-alt-unassigned` (E4) must end in the kernel's or `end NAME`'s refusal |
| a Lean error made a skip | unifyEq? catches only substCore's failure (`lf-commit-when`); fault `observing-too-wide` (E3); twin `w-dep-elim` ("Dependent elimination failed", E4) |
| no-confusion on a type Lean has no ctorIdx for | twin `w-noconf-decidable`; fault `ctoridx-from-builder` |
| a failure inside `by-try` | every new code registered as Lean's error or not (TACTIC_BLOCKS section 5); store refusals and fuel swept, never Lean's |

Answered unsupported (exit 2) at first: what each slice lists; acyclic; sparse casesOn (only match compilation asks
it); a let variable in `subst`; `rcases?`, `rintro?`, `cases'`.

## 7. Risks and what was not verified

- `( a | b )` from Lean habit inside a pattern is a comment: the pattern means something else, still kernel-checked;
  LANGUAGE_REFERENCE.md says so and `pattern-errors.lf` pins it. Refusing it would need a hook in 3c's token reader.
- E1's size (review about 850, here about 950); neither has ported the Meta split. Whether LeanForth's instantiation
  beta-reduces `?r i m extras` to `T.casesOn … extras` as Lean's does: E1's first test.
- Not verified: acyclic; Quot under rcases; the indexed share of Mathlib's uses (`⟨⟩` in 256 of 30,365 pattern lines,
  a proxy); the step-log goldens; `⟨ ⟩` as Gforth tokens (3c reads them in terms); the left-nested row `(a | b) | c`
  (from reading `processConstructors`, pinned by E1's twins); how decide-slice was built from its roots.

## Changes after review

1. Tags: the parent's tag alone with one minor premise; `intro` removed; twin `w-tag-intro`, fault `tag-ctor-on-single`.
2. Hidden names: revert returns names and flags, `lf-goal-intro-kept` re-introduces them, on all five paths; one twin
   per path; the "five-line change" claim removed.
3. Parentheses: none in patterns (coordinator's decision B); `(` stays a comment, its consequence in section 7;
   left-nested alternatives written with `<< >>`; translation table both ways.
4. Two top levels: rcases, obtain, by-contra take one element; rintro a sequence; faults and twins named.
5. subst: the let variable answers 99 (its error dropped from appendix B); the reduced-side path added with a test.
6. Nat: recursor info from the declaration's type; the export named, with its declaration list and a manifest test.
- Should-change: one bar rule written here and for TACTIC_BLOCKS.md; work in flight restated; typed tuple elements
  in question 4; the reader without lookahead; the reuse words added; `wc-ctor-app?` replaced too; line references
  corrected; consumers table; subst_vars' order pinned; no-confusion on Lean's declarations only; tokens from
  measured totals.
- Slices re-cut (coordinator's decision A): obtain and rcases first, subst with `rfl` and rintro second; rule 6 in E2.
- Not taken as given: "`(a | b) | c` is `a | b | c`". By `processConstructors` (RCases.lean:237-251) the two differ
  on `(p ∨ q) ∨ r` (the first splits the left disjunct, the second gives the right one the alternatives `b | c`); the
  left-nested group is `<< a | b >> | c`, pinned by `nest.lf`'s twins.
- Note for TACTIC_BLOCKS.md (its consumers row, :111), the same words as section 2: "Inside an open bracket list a bar
  is that list's item (a pattern bar), also at a line's start; outside brackets a bar at a line's start begins an
  alternative. A pattern bracket reads its own tokens, so `lft-w-bar` never sees its bars."

## Appendix A. Mathlib counts (one-line text greps of `.tools/mathlib/mathlib4/Mathlib`, 2026-11-22)

| Pattern | Lines |
|---|---|
| `obtain` at a line start ; with `:=` ; a bare name after `:=` ; a term or a continued line | 19,128 ; 18,960 ; 5,549 ; 13,411 |
| `rcases` at a line start ; `rcases NAME with` | 8,512 ; 2,494 |
| `rintro` at a line start ; names only | 7,776 ; 1,059 |
| obtain/rcases/rintro with `rfl` ; a bar ; `_` or `-` ; a nested tuple | 12,403 ; 7,587 ; 6,644 ; 2,805 |
| a typed piece `(x :` ; `@` | 864 ; 127 |
| `cases` plain ; `cases … with` ; `cases … <;>` | 2,621 ; 765 ; 662 |
| `subst` ; `subst_vars` ; `injection` | 1,087 ; 115 ; 266 |

## Appendix B. Errors kept (Lean's text; a new code each)

| Lean (file:line) | Text |
|---|---|
| Subst.lean:25, :32 | `argument must be an equality proof`; `'{a}' occurs at` and the term |
| Subst.lean:118, :179 | `invalid equality proof, it is not of the form (x = t)` (or `(t = x)`), `after WHNF, variable expected, but obtained`; `… of the form (x = t) or (t = x)` |
| Subst.lean:165 | `did not find equation for eliminating '{x}'` |
| UnifyEq.lean:58, :81, :123-124 | `Expected an equality, but found`; `Dependent elimination failed: Failed to solve equation`, with `at case` |
| Injection.lean:35, :68, :71; Elab/Tactic/Injection.lean | `equality expected`; `ill-formed noConfusion auxiliary construction`; `equality of constructor applications expected`; `too many identifiers provided, unused:` |
| Cases.lean:21, :97-99, :287; Util.lean:55-57 | `inductive type expected`; `indexed inductive type expected`; `ill-formed inductive datatype`; `not applicable to the given hypothesis`; `Tactic `cases` failed with a nested error:` |
| RCases.lean:275, :309 | `` Tactic `rcases` failed: `e` is not a free variable``; `` … `e : T` is not an inductive datatype`` |
| AppBuilder.lean:454, :457, :470, :479, :506 | mkNoConfusion: equality expected; inductive type expected; missing ctorIdx; missing noConfusion; no manifest constructors |

## Appendix C. Lean source notes

- `processConstructor` (RCases.lean:214-231): from `numParams`, an implicit field without `@` gets `_`; before the
  last field the next pattern and its `name?`; the last field: none `_`, one its name, several a tuple.
- `processConstructors` (:237-251): on the last constructor with several patterns left, they become one alternative
  list for it; each constructor's pattern is read through `asTuple`, which unwraps `paren` and `explicit` (:108-112).
- `rcasesCore` (:270-351): `rfl` runs substEq; a name nothing; `-` adds to `clears`; typed checks defeq then
  `replaceLocalDeclDefEq`; else whnfD the type: a quotient through `Quot.ind`, an inductive type through `g.cases`
  with `useNatCasesAuxOn := true` (:330), anything else the error.
- `rcases` (:423-445): one target takes the pattern; generalizeExceptFVar generalizes all but plain variables (an
  empty call leaves no trace); `finish` is the last continuation. `obtain` (:534-552) is rcases with the pattern.
- Meta `finalize` (Induction.lean:57-122): per minor premise, the tag (:84), `introN` with the given names (:110),
  `introNP` of the extras (:111), the substitution of every reverted local.
- `mkNoConfusion` (AppBuilder.lean:450-506): different constructors: `False.elim (noConfusion_of_Nat α T.ctorIdx a b
  h)`; equal constructors without fields: `fun P => P`; else `C.noConfusion` applied to the parameters, target, both
  field lists, `refl`s for index equations, then `h` or `heq_of_eq h`.
