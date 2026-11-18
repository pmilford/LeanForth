# S2 design note: $0 + n = n$ by induction and rewriting (FE1)

Plan slice S2 ([PLAN_DRAFT.md](../project/PLAN_DRAFT.md#phase-8-slices-owner-2026-11-13)). Status (2026-11-13):
**written and reviewed** (plan 9.4.7; [design review](../development/design-reviews/2026-11-13-s2.md): B1, B2, M1-M4 and
L1-L8 fixed in this text), **approved by the owner 2026-11-13** ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md), "Slice S2 approved").
It designs FE1g-5 to FE1g-8, FE1c's lazy delta, FE1d2's `_sunfold` bodies, `Meta.check` of the rewrite motive and FE1h
(FE1's done check) on top of S1 ([S1_INTERFACE.md](S1_INTERFACE.md), whose words it uses). Where
[FE1G_TACTICS.md](FE1G_TACTICS.md), [FRONT_END.md](FRONT_END.md) §8 or
[ELABORATION_DATA.md](../programming/ELABORATION_DATA.md) differ from it, this note wins for S2. Lean references are to
pinned Lean 4.35.0's `src/lean/Lean/`; the probes behind every "measured" are in appendix A.

## For the owner (one page)

**What S2 delivers: FE1, the first theorem proved by LeanForth's own tactics.** You write

```text
theorem zero_add''   Nat explicit: n   0 n + n =
:= by
  n by-induction-with
  | zero =>       by-rfl
  | succ k ih =>  by-rw[ ' Nat.add_succ ih ]
  by-end
end zero_add''
```

(Lean: `induction n with | zero => rfl | succ k ih => rw [Nat.add_succ, ih]`; in words: by induction on $n$, $0 + 0 =
0$ by computation, and $0 + (k + 1) = (0 + k) + 1 = k + 1$ by the definition of $+$ and the induction hypothesis.)
`bin/leanforth check --snapshot init.lfsnap --elab-data init.elab.ndjson --steps - tests/front/01-zero-add-rw.lf` prints
`zero_add'': accepted; axioms: none` and the proof's seven steps as data (what `leanforth print` will turn into English,
plan 8.6.12). LeanForth builds Lean's proof term node for node and its kernel checks it; no Lean tool runs. The plan's
other form of FE1 (`by-case:` and `by-exact` of `congrArg Nat.succ ih`) is accepted too. A wrong proof stops at the step
where Lean stops, with Lean's message and the goals, and nothing is checked.

**What we measured.** The rewriting proof needs Lean's unfolding of one small definition, `outParam`, as does every
statement with a variable such as `0 + n = n`, and S1's `#check` midpoint, but not S1's own theorem. The `case`/`exact`
form needs Lean's "smart unfolding" of `Nat.add`: one of 389 bodies Lean keeps beside `Init` that the export leaves out.

**Decisions** (each copies Lean; details in §1-§9):
1. Both forms of FE1 are S2's acceptance; FE1 is done only when the done checker runs both on all of `Init`.
2. Lazy unfolding is Lean's `isDefEqDelta`; unfolding one definition is Lean's `unfoldDefinition?`, smart path included.
3. All 389 smart-unfolding bodies join the elaboration data, so that "no record" means "none", as in Lean; the data's
   version goes to 3, so an older file is refused, never read as "no smart unfolding".
4. Lean's markers inside those bodies become a front-end-only node that the export writer refuses, like a hole.
5. Induction, alternatives and `case` port Lean's `induction` and `case`; a case's new hypotheses take their
   implicit/explicit marks from the eliminator's own declared type (S1's rule, extended).
6. Rewriting ports Lean's `rewrite` (find the pattern, build and type-check the motive, `congrArg`, `Eq.mpr`), then `rfl`.
7. The step log keeps only steps that took effect, is written only for accepted declarations, and nothing reads it.
8. Error numbers 200-229 are split between S2's branches; 230-249 stay for FE5.
9. Every form not ported (`using`, `generalizing`, `←`, `at h`, `Iff` rules, ...) answers "not supported yet" at its word.

**How it is built.** Three branches. `s2-unfold` (the unfolding and its data) in two merges: A right after S1's
library and instance branches and before S1's last branch, which needs it (a change to S1's approved order); B with
smart unfolding. `s2-tactics` (induction, `case`, rewriting) after s1-elab.
`s2-steps` (the log, `--steps`, the done check) last. Midpoints you can run: after A and s1-elab,
`03-zero-add-exact.lf` (`by-exact` of `Nat.zero_add n`); after B, `00-add-zero.lf` and `02-add-zero-rfl.lf` ($n + 0 =
n$); after s2-tactics, both FE1 files. Each is shown as a midpoint, never as "done".

**Gates.** [import] at merge A (new data the front end reads: data format 3, the `match_pattern` tag). [format] (the step log, and S1's deferred `by-sorry`
report wording) and [bypass] (no tactic result reaches the kernel unchecked) at S2's end. No kernel change.

**Questions for you** (§11): merge A before S1's last branch (recommended yes); both forms of FE1 in S2 (yes); the step
log's format (approve as designed); the [bypass] evidence (approve when shown).

## 1. What the two proofs need (measured)

| Step | Rewriting form (`01-zero-add-rw.lf`) | `case`/`exact` form (`01-zero-add.lf`) |
| --- | --- | --- |
| statement `0 + n = n` | lazy delta unfolds `outParam` 3 times: `binop%`'s `mkAppM HAdd #[Nat, Nat, Nat]` and `checkTypesAndAssign` of `?γ` at implicit transparency (`outParam (Type ?u) =?= Type`) | the same |
| `induction n` | `Nat.recAux` from the data; `setMotiveArg` assigns `?u := 0`; no unfolding | the same, names inaccessible |
| `zero`: `0 + 0 = 0` | `rfl` by `Nat` literals (`isDefEqNat`), no unfolding | the same |
| `succ` | `kabstract` at reducible: `0 + (k + 1) =?= ?n + Nat.succ ?m` by offsets; `k + 1 =?= 0 + k.succ` false, nothing unfolds; `Meta.check` of each motive (transparency all) unfolds `outParam` once | `0 + (k + 1) =?= Nat.succ ?x` unfolds `HAdd.hAdd`, `Add.add`, then `Nat.add` by `Nat.add._sunfold` (its matcher, `Nat.casesOn`, `Nat.rec`), assigning `?x := Nat.add 0 k`; `0 + k = k =?= Nat.add 0 k = k` unfolds `HAdd.hAdd` |
| closing `rfl` | `Nat.succ k =?= k + 1` at reducible, by offsets | — |

With `smartUnfolding false` the `case` form still elaborates but unfolds `Nat.add._f` and `Nat.brecOn` instead: smart
unfolding is Lean's default path, so LeanForth takes it. Of the existing files, `03-zero-add-exact.lf` and
`04-nested-ih.lf` need `outParam` only; `00-add-zero.lf` (`n Eq.refl` for $n + 0 = n$) and `02-add-zero-rfl.lf` need
`Nat.add`'s smart unfolding. **Finding for S1** (appendix A, p4): `theorem t : 0 + 0 = 0 := by rfl` unfolds nothing, as
S1 §2 says, but `#check 0 + 0 = 0`, S1's midpoint, unfolds `outParam` once, and FE1E's case C1 (`0 + n = n`, s1-elab's
golden) three or four times. LeanForth's `defeq.fs` answers unsupported at any unfoldable head today, and S1's
`lf-meta-whnf` cannot unfold any applied definition, because whether a `_sunfold` exists is unknown. Merge A gives
both the unfolding and that fact. S1's note is amended accordingly (its §11, amendment of 2026-11-13): s1-elab
merges after merge A, on slice data regenerated by merge A's exporter.

## 2. Lazy delta and unfolding (s2-unfold)

**Lazy delta.** `defeq.fs`'s `de-exp-delta` (unsupported today) becomes Lean's `isDefEqDelta` (ExprDefEq.lean:1849),
at Lean's place in `isExprDefEqExpensive` (2410-2421: after `whnfCore`, `isDefEqNat` and `isDefEqOffset`, before
structure eta and `isDefEqApp`), in a new file `defeq-delta.fs`: the candidates (`isDeltaCandidate?`, 1544:
`getUnfoldableConst?` at the configured transparency, `meta-env.fs`); one candidate: unfold it; two of one name:
`unfoldBothDefEq` (1697) with `tryHeuristic` (1632); two names: `unfoldNonProjFnDefEq` (1807, with
`packedInstanceOf?` for class projections), `unfoldReducibleDefEq` (1769), `unfoldDefEq` (1748, by definitional
height), `unfoldComparingHeadsDefEq` (1726). Each unfolding is followed by `whnfCore` and a new comparison, as a frame on
`defeq.fs`'s heap stack (no host recursion, plan 6.2.0 (b)) under the same checkpoint and the `--elab-fuel` budget.

**Unfolding one definition.** A new `unfold.fs` is Lean's `unfoldDefinition?` (WHNF.lean:844), used by lazy delta and
by S1's `lf-meta-whnf`. Applied constant: `getUnfoldableConst?` at the transparency, else `unfoldProjInstWhenInstances?`
(787, with `unfoldProjInst?`, 766, which it calls); the level count; if `f._sunfold` exists, the smart path; else a
matcher gives none; else `unfoldDefault` (821, with `backward.whnf.reducibleClassField`, default true). Bare constant:
`getUnfoldableConstNoEx?` first (914-918), then none if `f._sunfold` exists, else delta.
`whnfCore`'s projection reduces its structure with `whnf` (WHNF.lean:685, `proj := yesWithDelta`), so `instHAdd.1`
reduces.
- **Merge A:** all of the above except the smart path, which answers unsupported. That unfolds `outParam`, `HAdd.hAdd`,
  `instHAdd`, `Add.add` and `instAddNat`, none of which has a `_sunfold`. The exporter also writes the
  `@[match_pattern]` tag of each definition (same [import] gate; S3 needs it too).
- **Merge B:** the smart path: `f._sunfold`'s body (§3) instantiated with its markers, `smartUnfoldingReduce?` (720),
  `reduceMatcher?` (509) and `whnfMatcher` (494) with format 2's matcher records, `whnfCore`'s matcher and
  auxiliary-recursor steps (659, 670: `Nat.add.match_1`, `Nat.casesOn`; `whnf.fs` answers unsupported there today), the
  recursion-argument check (898-905, `getStructuralRecArgPos?` from the data), `reduceRec`'s literal-to-constructor and
  `Nat` offset clean-up (228-262: `toCtorIfLit`, `cleanupNatOffsetMajor`), `reduceNat?`'s guard (975: an argument with
  a free variable and no metavariable gives none, as for `Nat.add k 1`; folding literals stays S3), `unfoldProjInst?`
  (766) and `isDefEqProjInst` (ExprDefEq.lean:2356). At reducible, instances or implicit transparency Lean's
  `whnfMatcher` also unfolds `@[match_pattern]` definitions and 21 names Lean lists (`canUnfoldAtMatcher`,
  GetUnfoldableConst.lean:37-57: `OfNat.ofNat`, `NatCast.natCast`, `Zero.zero`, `One.one`, `decEq`, `Nat.decEq`,
  `Fin.ofNat`, `HMod.hMod`, `Mod.mod`, the `UIntN`, `Char` and `String` ones): the list is ported as a
  `meta-config.fs` bit, the tag read from merge A's data. Also `reduceMatcher?`'s `unfoldNestedDIte` at reducible,
  instances and implicit transparency (WHNF.lean:509-530) and `smartUnfoldingReduce?`'s retry of a stuck term through
  synthPending (743-749).

Not ported, changing no answer: caches and Lean's diagnostics counters.

## 3. The smart-unfolding records and their markers

- **Data.** Format 2's reserved kind `sunfold` as [ELABORATION_DATA.md](../programming/ELABORATION_DATA.md#smart-unfolding-bodies-designed-not-built)
  designs it, plus `"rec_arg": k` or `null` (Lean's `getStructuralRecArgPosImp?`,
  Elab/PreDefinition/Structural/Eqns.lean:191). `scripts/export_elab.lean` writes one record for **every** `f._sunfold`
  of the export's modules (389 in `Init`), so the header's count is the whole set and a definition no record names has
  none (Lean's `find?`, WHNF.lean:854): the fact merge A needs. **Format 3**: every format-2 file says `"sunfold":0`
  in its header, which would read as "no definition has a `_sunfold`" and unfold `Nat.add` by its `brecOn` value with
  no warning, so format 2 is refused as another format version (as format 1 is now) and S6's planned format becomes 4;
  `schemas/elab-data-3.schema.json`. Checks when read: ELABORATION_DATA.md's list (levels as a table like the
  nodes, not JSON trees, so that a line nests at most 8 deep); `rec_arg` is not bounded by `f`'s type, since Lean
  compares it with an application's arguments at use (WHNF.lean:900) and it can lie beyond the binders `f`'s type
  shows (`Nat.decidableExistsLT`, measured at merge A); a body naming a constant the export lacks makes that record
  unsupported at use, not the file invalid (merge A measured 25 of the 387 kept bodies, each naming a `_proof_N`
  lemma lean4export leaves out); data errors 41-45 (s1-synth took 39 and 40). Decoded into the term store at first
  use, memoized per run, like S1's `lib-decode.fs` (merge B). ELABORATION_DATA.md's kernel check of each body at first use
  is withdrawn: it would need a new kernel entry point on a scratch term ([kernel], [bypass]), and the trust argument
  below makes it unnecessary.
- **Markers.** Lean's `sunfoldMatch` and `sunfoldMatchAlt` annotations become one front-end-only node kind (new
  `src/core/annotations.fs`, beside `mvar-leaves.fs`): one child and a key, kept by instantiation and beta as Lean's
  `preserveMData`, stripped where `smartUnfoldingReduce?` strips them. Its data word (`core/terms.fs`, which gives an
  unknown tag "no data") is its child's. The walkers that carry it: instantiate, betaRev, the abstraction in
  `smartUnfoldingReduce?`'s lambdaTelescope and mapLetDecl, `consumeMData` in `reduceMatcher?`, `whnfEasyCases`; every
  other walker (`reach.fs`, the goal printer, the step log, `kabstract`) fails closed on it; `core/unsupported-forms.fs`
  names it; `kernel/` is untouched. The 8 `borrowed` entries (the compiler's mark, never read by Meta) are dropped at
  decode. The export writer (`author/export.fs:243`, `lfx-other`) and the audit refuse the node, unsupported (error
  200), as they refuse a metavariable (ADR 0021 D2). Lean can leave a marker under a `forallE` (WHNF.lean:723-734
  returns it unchanged), so error 200 is reachable: a recorded gap with Lean, not "never". Rejected: dropping markers at decode (smart unfolding could not find its
  matches); reserved metavariable leaves (whnf would see a stuck metavariable).
- **Trust ([import]).** The bodies are untrusted data, bound to the export by S1's manifest entry (M6). A wrong body can
  only change an elaborated term, which the kernel checks against the declarations it reads itself.

## 4. Induction, alternatives and `case` (FE1g-5, s2-tactics)

FE1G §5.4-5.5 stand: Lean's `evalInduction` (Elab/Tactic/Induction.lean:1005, inside `focus`), `evalInductionCore`
(977), `mkElimApp` (165), `setMotiveArg` (249), `evalAlts` (340) with `checkAltNames` (283) first, and `evalCase`
(BuiltinTactic.lean:595) with `findTag?` (535) and `renameInaccessibles`, on fe1g3's runner: the rows of
`by-induction`, `by-induction-with`, `|` and `by-case:` (`lf-tactic-action!`), blocks as frames. Settled here:
- **Target.** Elaborated by `lf-tac-elab` with no expected type (§7). A free variable that is not a let-variable;
  anything else is generalized in Lean (`elabElimTargets`, 898): 99, not supported yet (FE5).
- **Eliminator.** `elab-eliminator-for` (FE1d; `Nat.recAux` for `Nat`), else `C.rec` of a non-mutual, non-nested
  inductive type; a mutual or nested type is Lean's own error (Induction.lean:834-836), printed with Lean's text (209);
  otherwise Lean's "major premise type is not an inductive type" (205). `ElimInfo` (Meta/Tactic/ElimInfo.lean:57)
  from `forallTelescopeReducing` of its declared type, with fresh level metavariables.
- **Binder kinds (S1 §4 extended).** The fields of alternative k take their kinds from the leading binders of the domain
  of the eliminator's binder k, read from the tier's binder tags: `lf-menv-kinds-in ( d k -- addr n )`, beside
  s1-meta-b's `lf-menv-kinds`. `introN` takes them as data, never from the goal's instantiated type. S1's count of Lean's
  binder info against the export's (every binder of every `Init` type) covers them; `check_binder_kinds.py`'s required
  count of 0 extends from S1's declarations to `Nat.recAux`, `congrArg`, `Eq.mpr`, `id`, `Nat.add_succ`, `Nat.zero_add`.
- **Generalizing.** The hypotheses that depend on the target (`generalizeVars`, 604) are computed; any: 99 (FE5).
- **Fields.** `getNumExplicitFields` (317) runs `introN` under a trail mark and rolls it back (`withoutModifyingState`,
  S1 §3); more names than fields is 208; the target is cleared from each case (`tryClear`).
- **Order.** The main goal is assigned the eliminator application before any alternative runs (1000), names are checked
  before any runs, written alternatives run in text order, then "has not been provided" (207). Lean logs "too many
  variable names provided" at `case` and goes on; LeanForth stops there (211): it is Lean's first message.

## 5. Rewriting (FE1g-6, s2-tactics)

`by-rewrite[ ]` is Lean's `evalRewriteSeq` (Elab/Tactic/Rewrite.lean:124) at the goal; `by-rw[ ]` adds `try
(with_reducible rfl)` (Init/Tactics.lean:632) through fe1g3's `lf-tac-try` and S1's `by-rfl` at reducible
transparency. Rules run one at a time (`withRWRulesSeq`, 117): a hypothesis, or a theorem constant (a definition, whose
equation theorems Lean would use, is 99: FE8). As in `rewriteTarget` (53), each rule runs inside `Term.withSynthesize`:
`elabRewrite` (25) elaborates it with no expected type and postponing allowed (`elabTerm stx none true`, §7), the
occurs check (220), then `MVarId.rewrite`; only at the block's end do pending problems get synthesized with no
postponing, so default instances fire after `kabstract`, as in Lean; a problem still pending then is Lean's error.
`finishElabRewrite` (43) makes new proof goals synthetic opaque. `MVarId.rewrite` (Meta/Tactic/Rewrite.lean:28):
1. the rule's type, instantiated; `forallMetaTelescopeReducing` (Meta/Basic.lean:1791) on S1's whnf-forall words gives
   natural metavariables (an instance binder: 99, FE5); an `Iff` rule is 99 (`propext`, FE5); `matchEq?` (MatchUtil.lean:28)
   or "Invalid rewrite argument" (218); a metavariable-headed side is 219;
2. **`kabstract`** (KAbstract.lean:30, new `kabstract.fs`) under `Rewrite.Config` (Init/Meta/Defs.lean:1729:
   reducible, offsets on, all occurrences): a free-variable side is abstracted syntactically; otherwise a pre-order walk
   on heap frames tests a node only when it has no loose bound variable and its head index and argument count are the
   pattern's; every match is abstracted. With all occurrences the metavariable context is never switched back, so
   LIFO marks suffice (S1 §3's switch is for `occs`, FE5). No match: Lean's text (215);
3. the motive `fun (_a : α) => eAbst` passes **`Meta.check`** at transparency all (Check.lean:331, new `meta-check.fs`,
   with `checkApp`'s "Application type mismatch" inside Lean's text, 216; it needs merge A, since `HAdd.hAdd`'s
   arguments ask `outParam Type =?= Type`), then the dependence check (Rewrite.lean:73, 217);
4. the proof `congrArg.{u1, u2} α eType lhs rhs motive heq` (`getLevel`); a rule metavariable left unassigned or a
   `binderNameHint` (54) is 99;
5. `replaceTargetEq` (Meta/Tactic/Replace.lean:21): `Eq.mpr.{u}` of the goal's type *as stored*, `mkExpectedPropHint`
   (`id`), a new goal with the old tag.

`withInstancesTypeCheckNote` adds a note to a rewrite error when the target fails `Meta.check` at implicit
transparency (Check.lean:348), which a user's own statement can do: the note is ported (`meta-check.fs` takes the
mode) and a test pins one text with it and one without. The tactics' register
record `tb` becomes a step record on a slab stack (fe1g3 review M2), since `by-rw[ ]` runs `by-rfl` inside it.

## 6. The step log (FE1g-7, s2-steps)

- **What.** FE1G §6.1's fields (appendix C), one record per step that took effect. The runner records the kind, the
  source position, the parent step and the goals before and after (printed as `.goals` prints them and in kernel form);
  each tactic adds its rule fields (the eliminator; an alternative's tag and names; a rewrite's rule, direction and the
  path to the rewritten subterm; a closing term). A restore (a failed `lf-tac-try`) drops the records made since its
  save.
- **When.** Rendered to text at the hand-over, as `by-sorry`'s open parts are, since `lfc-empty` empties the stores
  before the kernel runs; written after the verdicts, only for declarations the kernel accepted.
- **Interface.** `check ... --steps FILE` writes NDJSON `leanforth-tactic-steps` version 1: per declaration one header
  line and one line per step, in text order (the same with `--jobs 2`); `--steps -` writes it to standard output after
  the report. JSON Schema `schemas/tactic-steps-1.schema.json`. Not inside `--json` (check-report 0.5 unchanged).
- **Trust.** Presentation data: nothing reads it to decide; it changes no verdict and no exit status.

## 7. What S2 needs from S1, and work in flight

| From | What | For |
| --- | --- | --- |
| fe1g3 (main) | the runner, blocks, `lf-tac-try`, `by-rfl` at a given transparency, codes 80-99 (99 for every form not ported, with the form named) | all tactics |
| s1-meta A (main) | the trail (§3), `lf-meta-whnf`, `-whnf-forall`, `-instantiate-forall`, `lf-meta-defeq-guarded`, `meta-config.fs` | telescopes, `setMotiveArg`, fields |
| s1-meta-b (in flight; committed 28dbeba4) | the library route, `lib-decode.fs`, `lf-menv-kinds`, `lf-menv-add`; stubs `lf-menv-smart?` (always unsupported), `lf-menv-matcher?`, `lf-menv-aux-recursor?` (meta-env.fs:274-304), which merge A fills | library constants, kinds |
| s1-synth (in flight) | the data's manifest binding (M6), data code 39 | trust of the `sunfold` records |
| s1-elab (not started) | `lf-tac-elab ( node expected postpone? -- term outcome )` taking expected -1 for none (0 is a term: review s1-elab M4) and Lean's `mayPostpone` flag (`elabTerm stx none true`), and a word for `Term.withSynthesize`'s end (synthesize with no postponing); the statement glue; `--elab-fuel` | targets, rules, statements |

**Blocks.** Merge A edits `defeq.fs`, `whnf.fs`, `meta-env.fs` (s1-meta-b's files) and `elab-data.fs` and the export
scripts (s1-synth's): it starts when both have merged. It shares no file with s1-elab except `meta-config.fs` and the
slice data; s1-elab's C1 golden and `#check` midpoint need it (§1), so s1-elab merges after it, with the slice data
regenerated by merge A's exporter (format 3). s2-tactics edits `tactic-basic.fs`, which s1-elab
changes (S1 §10): it starts after s1-elab. Files per branch: appendix D.

**Reuse** (AGENTS.md "Reuse first", owner 2026-11-13; the [library audit](../development/forth-reviews/2026-11-13-library-audit.md),
plan 9.4.8). S2 writes no general-purpose word of its own: its stacks use `slab-push`/`-pop` (9.4.8a), its loops over
outcomes `ok-each`/`ok-fold`, its tag tests `core/`'s predicates; `kabstract.fs` and `meta-check.fs` walk terms with
the library walk and memo of 9.4.8b; `defeq-delta.fs` and `unfold.fs` run on `frame.fs` frames once 9.4.8c lands.
`reuse-1` merges before merge A and `reuse-2` before merge B; appendix F lists each S2 file's libraries.

## 8. Error codes

| Codes | Branch | Use |
| --- | --- | --- |
| 200-204 | s2-unfold | 200 `lfa-e-annotation`: a smart-unfolding marker reached a declaration (unsupported); 201-204 kept |
| 205-214 | s2-tactics | 205 `-tac-not-inductive`; 206 `-tac-alt-name` (an invalid, duplicate or missing alternative name); 207 `-tac-alt-missing`; 208 `-tac-alt-names` (too many names at an alternative); 209 `-tac-mutual` (induction on a mutual or nested type, Lean's text); 210 `-tac-case-tag`; 211 `-tac-case-names`; 212 `-tac-elim-motive` (`setMotiveArg`'s type mismatch); 213-214 kept |
| 215-224 | s2-tactics | 215 `-tac-no-pattern`; 216 `-tac-motive` (not type correct); 217 `-tac-motive-dep`; 218 `-tac-not-eq`; 219 `-tac-mvar-pattern`; 220 `-tac-occurs`; 221-224 kept |
| 225-229 | s2-steps | kept (a step log out of room is 88, full) |
| 230-249 | FE5 | |
| data 41-49 | s2-unfold | the `sunfold` record checks (the elaboration data's own numbering): 41 a body named twice, 42 an index to no earlier entry, 43 a loose bound variable, 44 universe parameters other than the definition's, 45 an unknown annotation (unsupported); 46-49 kept; data 39 and 40 are s1-synth's |

All codes but 200 are invalid; each prints Lean's first message and, for a tactic error, the goals (as 89 and 97 do).
Merge A writes the sub-ranges into `author/errors.fs`'s header. A Meta step not ported stays 93 at a tactic.

## 9. Tests (FE1g-8 and FE1h, in the branch that needs them)

- **Node for node with pinned Lean.** Each `.lf` file has a Lean twin compiled with `-DwarningAsError=true` and exported
  (`check_tactics.py --lean`, `make reference-front`); the terms are compared with binder names' macro scopes erased
  (FE1G §2.3); `.goals` after each step against Lean's `trace_state` as terms. Files: `01-zero-add-rw.lf`,
  `01-zero-add.lf`, `03-zero-add-exact.lf`, `04-nested-ih.lf`, `00-add-zero.lf`, `02-add-zero-rfl.lf`, FE1G §2.4's
  `t6`/`t7` (every occurrence; a free-variable side). Meta: `check_defeq.py`, `check_whnf.py`, `check_unfold.py`
  cases for each lazy-delta and smart-unfolding step of appendix A (FE1c's `Nat.succ ?a =?= 0 + (k + 1)` assigns
  `Nat.add 0 k`; FE1d2's `whnf (Nat.add 0 (k + 1))`); the 20 cases `check_defeq.py` answers unsupported, re-measured.
- **Wrong proofs** (appendix A, p6, p7): each refused at Lean's step with Lean's first message and code, exit 4.
- **Classes 1-7** of [TEST_COVERAGE_REVIEW.md](../development/TEST_COVERAGE_REVIEW.md) as FE1G §8.2 lists them, plus:
  damaged `sunfold` records refused; a format-2 data file refused (stale data never read as "no `_sunfold`"); the
  annotation node refused by the writer and by each fail-closed walker; `--steps` validated by its schema,
  golden logs, no log for a refused declaration, the same log with `--jobs 2`; 1,000 nested `by-case:` blocks; a
  10,000-deep target for `kabstract` and `Meta.check`; fuel exhausted, never accepted.
- **Faults** (`tests/mutants/faults.toml`): FE1G §8.3's list (those not planted yet), plus `fe-delta-no-sunfold`
  (`Nat.add` by its `brecOn` value), `fe-delta-both-sides` (both unfolded where Lean unfolds one),
  `fe-offset-cleanup-skipped`, `fe-annotation-to-writer`, `fe-motive-unchecked` (p7's motive reaches the kernel, which
  rejects it), `fe-alt-kinds-from-node`, `fe-steps-rolled-back` (a failed attempt's step kept).
- **Done (FE1h).** The done checker runs both FE1 files, with `--steps -`, on the full `Init` snapshot and an
  `init.elab.ndjson` regenerated with the `sunfold` records; the user page in three forms gains induction and rewriting.

## 10. The S2 split

| # | Branch | Contents | Midpoint you can run | Gate |
| --- | --- | --- | --- | --- |
| 1A | `s2-unfold` merge A | §2 without the smart path (with `unfoldProjInst?`); §3's records and reader, data format 3, the `match_pattern` tag; `lf-menv-smart?` from them; the error ranges | with s1-elab: `03-zero-add-exact.lf` accepted; S1's `0 0 + 0 = #check` | [import] |
| 1B | `s2-unfold` merge B | §2's smart path, matchers (with `canUnfoldAtMatcher`'s list, `unfoldNestedDIte`), `reduceRec`'s clean-up; §3's markers and `annotations.fs` | `00-add-zero.lf`, `02-add-zero-rfl.lf` accepted | — |
| 2 | `s2-tactics` | §4, §5, `meta-check.fs`, `kabstract.fs`, M2's step records, codes 205-224, the user page | `01-zero-add-rw.lf` and `04-nested-ih.lf` accepted (A), `01-zero-add.lf` (with B) | — |
| 3 | `s2-steps` | §6, `--steps`, the schema, `COMMAND_LINE.md`, the done check | `--steps -` on both FE1 files | [format], [bypass] |

Order: s1-meta-b and s1-synth; 1A (s1-elab is built beside it and merges after it); s1-elab; then 1B and 2 in parallel (different files; 2's `case`
form waits for 1B); 3. Branches meet only in `author/errors.fs` (own ranges), `faults.toml`, the style baseline and
`src/main.fs`. Each branch runs its tier once at its end (core, cli and scripts: `make check` and `make coverage-check`).
Sizes, *speculative*: 1A M, 1B M, 2 L, 3 S-M; about 2,500 Forth lines in all and as much in tests.

## 11. Questions for the owner

1. **May S2's first piece come before S1's last branch?** Lean unfolds a small definition (`outParam`) in S1's `#check`
   midpoint and in every statement with a variable, such as `0 + n = n`; S1's own theorem does not need it. *Yes,
   recommended*: otherwise S1's midpoint and its main test cannot run as Lean runs them. This changes S1's approved
   order (s1-elab merges after merge A) and moves the elaboration data to version 3, at merge A's [import] gate.
2. **Both forms of FE1 in S2?** The rewriting form needs little unfolding; the `case`/`exact` form, which the plan's FE1
   row names, needs Lean's smart unfolding (merge B, about M). *Yes, recommended*: S3's `by-decide` needs the same
   unfolding, and FE1's done check then covers the plan's own file. The alternative, the `case` form in S3, saves no work.
3. **[format] The step log.** One JSON line per step (what was done, the goal before and after, the rule), written with
   `--steps FILE` (or `-`), only for accepted theorems, version 1 with a schema; with it S1's deferred `by-sorry`
   report wording (`open part K of NAME (by-sorry at line:col L:C):`, the goal, two notes). *Approve as designed*: it is
   what `leanforth print` needs, and a version number lets it grow.
4. **[bypass] Can a tactic make a false theorem pass?** No: tactics only build a term, the kernel checks it, a hole or a
   marker is refused before the kernel, a failed attempt is undone, and the log is never read. Evidence at S2's end: the
   planted faults of §9 caught (a wrong term rejected by the kernel, exit 1), every wrong proof stopping with nothing
   checked, and an old data file refused. *Approve when that evidence is shown.*

## Appendix A. Probes (2026-11-13)

Pinned Lean ran each file as `bash -c 'ulimit -u 500; timeout -k 5 120 nice -n 10
.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean FILE'` (files kept in the main checkout's
`.claude/work/s2-design/`; p1's and p7's outputs were re-run by the design reviewer, with the results below; the
reviewer's own probes q1 and q2, in `.claude/work/s2-review/`, confirm p4's finding). Traces: `set_option trace.Meta.isDefEq.delta true` (lines
`[Meta.isDefEq.delta.unfoldLeft] NAME`), `trace.Meta.isDefEq`, and `set_option diagnostics true` with
`diagnostics.threshold 0` (Meta's "unfolded declarations" counts).

| Probe | Text | Result |
| --- | --- | --- |
| p1 | §2.1's and §2.2's theorems of FE1G with `pp.all` and `#print` | both terms exactly as FE1G §2.1 and §2.2 print them; no axioms |
| p2a | the rewriting form, delta trace and diagnostics | Meta unfolds only `outParam` (9 in the header, 11 with the body); 5 `unfoldLeft outParam` lines |
| p2b | the `case`/`exact` form, the same | Meta unfolds `Add.add` 11, `HAdd.hAdd` 11, `Nat.rec` 9, `Nat.casesOn` 9, `OfNat.ofNat` 2, `outParam` 9; `unfoldRight`/`unfoldLeft` of `HAdd.hAdd`, `Add.add`, `Nat.add` |
| p3 | the `succ` case alone, `exact congrArg Nat.succ ih` and `rw [Nat.add_succ, ih]`, full `isDefEq` trace | §1's rows: `0 + (k + 1) =?= Nat.succ ?m.30` unfolds three heads, then `Nat.add 0 k =?= ?m.30`; `kabstract`'s `k + 1 =?= Nat.succ ?m` by `k =?= ?m`; `k + 1 =?= 0 + k.succ` false at `k =?= 0`; `outParam Type =?= Type` (Meta.check) unfolds `outParam` |
| p3n | p3 with `set_option smartUnfolding false` | still accepted; Meta unfolds `Nat.add._f` 40, `Nat.brecOn.go` 15, `Nat.brecOn` 8, `Nat.rec` 47: another path |
| p4, p4a-c | `theorem s1 : 0 + 0 = 0 := by rfl`; `#check 0 + 0 = 0`; `theorem s2h (n : Nat) : 0 + n = n := by exact Nat.zero_add n` | no delta line; one `unfoldLeft outParam`; three |
| p4d, p4f | p4b and p4c with `trace.Meta.isDefEq` | `outParam Type =?= Type` (`#check`); `outParam (Type ?u) =?= Type` after `?γ =?= Nat` raises transparency to implicit, and in `mkAppM` |
| p5 | `theorem (n : Nat) : n + 0 = n := Eq.refl n`, the same `:= by rfl`, FE1G's nested-`ih` proof | the first two unfold `HAdd.hAdd`, `Add.add`, `Nat.add` (Meta: `Nat.rec`, `Nat.casesOn`); the third `outParam` only |
| p6 | wrong proofs: claim `0 + n = n + 1`; `rw [Nat.mul_comm]`; `rw [Nat.add_succ]` alone; `case suc`; `case succ k ih extra`; `\| zero` twice; `rw [ih]` alone; `rw [Nat.lt_irrefl]` | first messages: `Tactic \`rfl\` failed` (case zero); `Did not find an occurrence of the pattern ?n * ?m`; `unsolved goals case succ ... ⊢ (0 + k).succ = k + 1`; `Case tag \`suc\` not found.` and a hint; `too many variable names provided`; `Duplicate alternative name \`zero\``; `Did not find ... 0 + k`; `Invalid rewrite argument: ... \`Nat.lt_irrefl ?n ?a✝\` is a proof of False` |
| p7 | `example (n : Nat) (x : Fin n) (h : n = 3) : x.val = x.val := by rw [h]` | `Tactic \`rewrite\` failed: motive is not type correct:` with `checkApp`'s "Application type mismatch" and Lean's explanation |

## Appendix B. Words and their Lean sources

| Word (file) | Lean |
| --- | --- |
| `lf-meta-delta ( t s -- r outcome )` (`defeq-delta.fs`) | `isDefEqDelta` and helpers, ExprDefEq.lean:1544-1849; `isDefEqProjInst` 2356 |
| `lf-meta-unfold ( e -- e' flag outcome )` (`unfold.fs`) | `unfoldDefinition?` WHNF.lean:844, `unfoldDefault` 821, `smartUnfoldingReduce?` 720, `unfoldProjInst?` 766, `unfoldProjInstWhenInstances?` 787 |
| `lf-meta-reduce-matcher ( e -- e' r outcome )` (`unfold.fs`) | `reduceMatcher?` 509, `whnfMatcher` 494, `canUnfoldAtMatcher` GetUnfoldableConst.lean:37 |
| `reduceRec`'s clean-up (`whnf.fs`) | `toCtorIfLit` WHNF.lean:23, `cleanupNatOffsetMajor` 216, `reduceRec` 228 |
| `lf-menv-smart? ( d -- flag outcome )`, `lf-menv-rec-arg ( d -- k flag outcome )` (`meta-env.fs`) | `find? (mkSmartUnfoldingNameFor f)` WHNF.lean:854, `getStructuralRecArgPos?` 46 |
| `lf-meta-elim-info ( d -- info outcome )` (`elim-info.fs`) | `getElimExprInfo` ElimInfo.lean:57, `getElimInfo` 93, `addImplicitTargets` 101, `getCustomEliminator?` 276 |
| `by-induction`, `by-induction-with`, `\|` (`tactic-induction.fs`) | Induction.lean: `evalInduction` 1005, `evalInductionCore` 977, `mkElimApp` 165, `setMotiveArg` 249, `checkAltNames` 283, `getNumExplicitFields` 317, `evalAlts` 340, `generalizeVars` 604, `checkInductionTargets` 954; `introNCore` Meta/Tactic/Intro.lean:123; `tryClear` Clear.lean:48 |
| `by-case:` (`tactic-induction.fs`) | `evalCase` BuiltinTactic.lean:595, `findTag?` 535, `renameInaccessibles` RenameInaccessibles.lean:11 |
| `lf-meta-kabstract ( e p -- e' flag outcome )` (`kabstract.fs`) | `kabstract` KAbstract.lean:30 |
| `lf-meta-check ( e mode -- outcome )` (`meta-check.fs`) | `check` Check.lean:331, `checkApp` 272, `isTypeCorrect` 365 |
| `by-rewrite[`, `by-rw[` (`tactic-rewrite.fs`) | `evalRewriteSeq` Elab/Tactic/Rewrite.lean:124, `withRWRulesSeq` 117, `elabRewrite` 25, `rewriteTarget` 53, `MVarId.rewrite` Meta/Tactic/Rewrite.lean:28, `replaceTargetEq` Replace.lean:21, `mkExpectedPropHint` AppBuilder.lean:29, the `rw` macro Init/Tactics.lean:632 |

## Appendix C. Step-log record, version 1

Header: `{"tactic_steps":{"axioms":[AXIOM,...],"cut":false,"declaration":NAME,"format":"leanforth-tactic-steps","format_version":1,"open_parts":P,"steps":N}}`
(review M2 and L4, 2026-11-17: the axioms and open parts say whether the declaration is proved; `cut` true, with `N` 0,
when the log ran out of room before its end, which never changes a verdict or the exit code). Step:
`step` (from 1, in the order taking effect), `parent` (0 for the proof), `tactic` (`induction`, `alternative`, `case`,
`rfl`, `exact`, `intro`, `rewrite`, `rfl-after-rw`, `sorry`), `rule` (`induction` with `eliminator` and `target`;
`case-split` with `case` and `names`; `defeq-refl`; `exact` with `term`; `intro` with `name`; `rewrite` with
`statement`, `direction` (`ltr`) and `location`, a path of argument indices; `sorry`), `goal_before` and `goals_after`
(each `tag`, `hyps` as `[name, type]`, `target`; printed, and under `kernel` in kernel form), `refs` (constants and
hypotheses used), `source` (`line:col`, and the label of ADR 0017 §11 if any). FE1G §6.2's example lines are this
form; the schema fixes every field and refuses others.

## Appendix D. Files by branch

| Branch | New | Changed |
| --- | --- | --- |
| s2-unfold A | `src/front/defeq-delta.fs`, `src/front/unfold.fs`, `schemas/elab-data-3.schema.json` | `defeq.fs`, `whnf.fs`, `meta-env.fs` (fills the stubs), `elab-data.fs` (format 3), `scripts/export_elab.lean` (`sunfold`, `match_pattern`), `export_elab.py`, `export-elab.sh`, `ELABORATION_DATA.md`, `author/errors.fs` (header, 200), `src/main.fs`, `tests/front/init-slice.elab.ndjson` and the slices' data |
| s2-unfold B | `src/core/annotations.fs` | `unfold.fs`, `whnf.fs`, `meta-config.fs` (the matcher list), `instantiate.fs`, `beta-inst.fs`, `lib-decode.fs`, `core/terms.fs` (the node's data word), the export writer's refusal (`author/`), `core/unsupported-forms.fs` |
| s2-tactics | `src/front/elim-info.fs`, `tactic-induction.fs`, `kabstract.fs`, `meta-check.fs`, `tactic-rewrite.fs` | `tactic-basic.fs` (M2), `tactic-run.fs` (rows), `meta-env.fs` (`lf-menv-kinds-in`), `author/errors.fs` (205-224), `tests/front/*.lf` and goldens, `check_tactics.py`, `docs/user/` |
| s2-steps | `src/front/step-log.fs`, `schemas/tactic-steps-1.schema.json` | `tactic-run.fs`, `cli/leanforth.fs`, `cli/check-lf.fs`, `docs/user/COMMAND_LINE.md`, `docs/programming/INTERFACE_CONTRACTS.md` |

## Appendix E. What later slices take from S2

| Slice | Takes |
| --- | --- |
| S3 (`by-decide`) | `unfold.fs` with smart unfolding, matchers, auxiliary recursors and `reduceRec`'s clean-up; lazy delta; `reduceNat?`'s guard; adds its folding of literals with the power threshold and, if `whnfMatcher` at reducible needs it, the `match_pattern` tag |
| S4 (`by-omega`) | S3's; the step log's rule `omega`; `exact` and `intro` through the runner |
| S5 (FE2 terms) | `kabstract.fs` (Lean's `h ▸ e` abstracts with it), `meta-check.fs`, lazy delta in every elaboration |
| FE5 | the step records (M2), and every 99 of §4 and §5: `using`, `generalizing`, `←`, `at h`, `Iff` rules, instance binders, `occs`, wildcard and `@` alternatives, `case a \| b`, `Term.withSynthesize` |
| FE9 (`simp`), 8.6.12 (`print`) | `replaceTargetEq`, `kabstract`; the step log version 1 |

## Appendix F. Libraries each S2 file uses

| File | Libraries and shared words |
| --- | --- |
| `defeq-delta.fs`, `unfold.fs` | `lib/slab.fs` push and pop, `lib/outcome.fs` (`ok-with`, `ok-each`), `lib/frame.fs` after 9.4.8c, `core/` term predicates, `meta-env.fs`, `meta-spine.fs` |
| `elab-data.fs` (format 3 records) | `lib/json.fs`, `lib/htab.fs`, `lib/memo.fs` (decoded bodies, 9.4.8b), `lib/decimal.fs` when 9.4.8d lands |
| `annotations.fs` | `core/terms.fs`'s node record; nothing general of its own |
| `elim-info.fs`, `tactic-induction.fs` | `lib/runs.fs` (contexts), `lib/slab.fs`, `lib/outcome.fs`, `goals.fs`, `lctx-views.fs` |
| `kabstract.fs`, `meta-check.fs` | the library walk with its memo (`lib/`, 9.4.8b), `lib/slab.fs`, `instantiate.fs` |
| `tactic-rewrite.fs`, `step-log.fs` | `lib/json-write.fs`, `lib/slab.fs` (the step records), `goal-print.fs` |


## Appendix G. The owner's proof set in Lean (2026-11-13)

The Lean forms S2 (and S3, S4) port for the owner's proof set ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md),
"A proof set for S2-S4"), using only S2's tactics (`induction … with`, `rw`, `rfl`, `exact`) and Init's lemmas, plus
`decide` (S3) and `omega` (S4). Pinned Lean 4.35.0 checks the file with exit 0 (2026-11-13, 23:34). The first six
depend on no axiom; `omega`'s proof of `n < n + 1` uses `propext` and `Quot.sound`, so S4's acceptance reports those two
axioms. The proofs by `rfl`, `decide` and `omega` alone name no lemma; the others rewrite with Init's `Nat.add_succ`
and `Nat.mul_succ`, the list lemmas `List.nil_append`, `List.cons_append`, `List.length_nil` and `List.length_cons`,
and the set's own earlier theorems.

```lean
theorem ps_add_zero (x : Nat) : x + 0 = x := by rfl
theorem ps_zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
theorem ps_succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) := by
  induction m with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih, Nat.add_succ]
theorem ps_add_comm (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => rw [ps_zero_add]; rfl
  | succ k ih => rw [Nat.add_succ, ih, ps_succ_add]
theorem ps_add_assoc (n m k : Nat) : n + (m + k) = (n + m) + k := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Nat.add_succ, Nat.add_succ, ih, Nat.add_succ]
theorem ps_mul_add (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ, ps_add_assoc]
theorem ps_length_append (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => rw [List.nil_append, List.length_nil, ps_zero_add]
  | cons x t ih => rw [List.cons_append, List.length_cons, List.length_cons, ih, ps_succ_add]
theorem ps_two_two : 2 + 2 = 4 := by decide
theorem ps_lt_succ (n : Nat) : n < n + 1 := by omega
```

What S2 needs beyond FE1 for these: tactic sequencing (`;`) inside an alternative, rewriting with the set's own earlier
theorems, the `List` notation and `++` through instance search (S1's synth), and `*` (`HMul`, `Nat.mul_succ`). Each
LeanForth file is compared node for node with this file's terms.
